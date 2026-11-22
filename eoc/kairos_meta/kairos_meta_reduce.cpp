#include "kairos_meta/kairos_meta_reduce.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <fstream>
#include <iostream>

#include "linear_patterns/linear_patterns.h"
#include "state.h"
#include "utils.h"

namespace ethos {

namespace {

std::string replaceAll(std::string str, const std::string& from, const std::string& to)
{
  size_t pos = 0;
  while ((pos = str.find(from, pos)) != std::string::npos)
  {
    str.replace(pos, from.length(), to);
    pos += to.length();
  }
  return str;
}

/** As LeanMetaReduce::cleanSmtId. */
std::string cleanSmtId(const std::string& id)
{
  if (id == "end" || id == "variable")
  {
    return "__eo_" + id;
  }
  std::string idc = id;
  idc = replaceAll(idc, "++", "concat");
  idc = replaceAll(idc, "+", "plus");
  idc = replaceAll(idc, "-", "neg");
  idc = replaceAll(idc, "*", "mult");
  idc = replaceAll(idc, "=>", "imp");
  idc = replaceAll(idc, "<=", "leq");
  idc = replaceAll(idc, "<", "lt");
  idc = replaceAll(idc, ">=", "geq");
  idc = replaceAll(idc, ">", "gt");
  idc = replaceAll(idc, "=", "eq");
  idc = replaceAll(idc, "/", "qdiv");
  idc = replaceAll(idc, "^", "exp");
  idc = replaceAll(idc, ".", "_");
  idc = replaceAll(idc, "@", "_at_");
  idc = replaceAll(idc, "$", "__");
  return idc;
}

/** As LeanMetaReduce::cleanId. */
std::string cleanId(const std::string& id) { return cleanSmtId(replaceAll(id, "-", "_")); }

std::string str(const Expr& e)
{
  std::stringstream ss;
  ss << e;
  return ss.str();
}

std::string indent(size_t n) { return std::string(n, ' '); }

using Sort = KairosMetaReduce::Sort;
/** Terms and proofs are ids in Kairos. */
bool isIdSort(Sort s) { return s == Sort::TERM || s == Sort::PROOF; }

std::string kindToString(Kind k)
{
  std::stringstream ss;
  ss << k;
  return ss.str();
}

/** The type an `eo::requires` guard guards. */
Expr unguard(const Expr& t)
{
  Expr s = t;
  while (s.getKind() == Kind::EVAL_REQUIRES && s.getNumChildren() == 3)
  {
    s = s[2];
  }
  return s;
}

/** A proof that the fact named `name` is in Γ, given Γ oldest first. */
std::string memProof(const std::vector<std::string>& gamma, const std::string& name)
{
  for (size_t i = gamma.size(); i-- > 0;)
  {
    if (gamma[i] == name)
    {
      size_t pos = gamma.size() - 1 - i;
      std::string s;
      for (size_t j = 0; j < pos; j++)
      {
        s += "(.tail _ ";
      }
      s += "(.head _)";
      for (size_t j = 0; j < pos; j++)
      {
        s += ")";
      }
      return s;
    }
  }
  AlwaysAssert(false) << "kairos-meta: no fact for " << name;
  return "";
}

std::string tupleType(const std::vector<std::string>& types)
{
  if (types.empty())
  {
    return "Unit";
  }
  std::string s;
  for (size_t i = 0; i < types.size(); i++)
  {
    s += (i ? " × " : "") + types[i];
  }
  return (types.size() == 1 && s.find(' ') == std::string::npos) ? s : "(" + s + ")";
}

std::string tupleVal(const std::vector<std::string>& vals)
{
  if (vals.empty())
  {
    return "()";
  }
  std::string s;
  for (size_t i = 0; i < vals.size(); i++)
  {
    s += (i ? ", " : "") + vals[i];
  }
  return vals.size() == 1 ? s : "(" + s + ")";
}

/** The Term constructors with fields that patterns and bodies use, with the
 * runtime primitive that matches them and their field kinds (I = id,
 * N:<type> = native). Leaves without fields are matched with `leaf`. */
struct CtorInfo
{
  std::string prim;
  std::vector<std::string> fields;
  std::string inv;
  std::string internLemma;
};
/** Term's constructors, filled from the signature (see emitTermModules). */
std::map<std::string, CtorInfo>& ctorTableRef()
{
  static std::map<std::string, CtorInfo> t;
  return t;
}
const std::map<std::string, CtorInfo>& ctorTable() { return ctorTableRef(); }

/** A Lean guard on a native field fixed by a pattern. */
std::string guardFor(const std::string& var, const std::string& val)
{
  return "kguard (" + var + " = " + val + ") (";
}

}  // namespace

KairosMetaReduce::KairosMetaReduce(State& s) : MetaReducePlugin(s)
{
  // As LeanMetaReduce's constructor: these decide how types and constructors
  // are classified, hence the case layout Logos's definitions have.
  d_typeToMetaKind["$eo_Term"] = MetaKind::EUNOIA;
  d_typeToMetaKind["$eo_Proof"] = MetaKind::PROOF;
  d_typeToMetaKind["$eo_Rule"] = MetaKind::CHECKER_RULE;
  d_typeToMetaKind["$eo_Cmd"] = MetaKind::CHECKER_CMD;
  d_prefixToMetaKind["r"] = MetaKind::CHECKER_RULE;
  d_prefixToMetaKind["cmd"] = MetaKind::CHECKER_CMD;
}

KairosMetaReduce::~KairosMetaReduce() {}

bool KairosMetaReduce::isBuiltinMetaSymbol(const std::string& sname) const
{
  return sname.compare(0, 5, "$smt_") == 0 || sname.compare(0, 8, "$native_") == 0
         || d_typeToMetaKind.find(sname) != d_typeToMetaKind.end();
}

void KairosMetaReduce::finalizeDecl(const Expr& e)
{
  if (!beginFinalizeDecl(e))
  {
    return;
  }
  std::string cnamek;
  MetaKind tk = getMetaKindFor(e, cnamek);
  d_declCount[metaKindToString(tk)]++;
  if (tk != MetaKind::EUNOIA || str(e) == "$eo_pf")
  {
    return;
  }
  std::string cname = cleanSmtId(cnamek);
  size_t uarity;
  if (isAtomicEo(e, cnamek, uarity))
  {
    d_userOps[uarity].push_back(cname);
    d_userOpArity[getName(e)] = uarity;
    return;
  }
  Expr ec = e;
  Expr ct = d_tc.getType(ec);
  std::vector<std::string> argTypes;
  if (d_state.getAttributeKind(e.getValue()) == Attr::OPAQUE)
  {
    for (size_t i = 0; i + 1 < ct.getNumChildren(); i++)
    {
      Expr typ = ct[i];
      if (typ.getKind() == Kind::QUOTE_TYPE)
      {
        Expr targ = typ[0];
        typ = d_tc.getType(targ);
      }
      argTypes.push_back(printType(typ));
    }
  }
  d_termCons.emplace_back(cname, argTypes);
}

/** As LeanMetaReduce::printMetaType, for the types of Term's fields. */
std::string KairosMetaReduce::printType(const Expr& t)
{
  MetaKind tk = getTypeMetaKindFor(t, MetaKind::EUNOIA, false);
  if (tk == MetaKind::SMT_BUILTIN)
  {
    Expr s = unguard(t);
    std::string n = s[1].getValue()->asLiteral()->d_str.toString();
    if (n.compare(0, 6, "UserOp") == 0)
    {
      return n;
    }
    return "native_" + cleanSmtId(n);
  }
  if (isEmbedMetaKind(tk))
  {
    return getEmbedTypeName(getEmbedTypeApp(t));
  }
  return "Term";
}

/** As LeanMetaReduce::isAtomicEo (with optionEoUserOp). */
bool KairosMetaReduce::isAtomicEo(const Expr& c, const std::string& cname, size_t& arity)
{
  Attr attr = d_state.getAttributeKind(c.getValue());
  if (getName(c).compare(0, 4, "$emb") == 0)
  {
    return false;
  }
  if (attr != Attr::OPAQUE)
  {
    if (cname == "Stuck" || cname == "Type" || cname == "FunType" || cname == "Bool"
        || cname.compare(0, 4, "$eo_") == 0)
    {
      return false;
    }
    arity = 0;
    return true;
  }
  Expr ct = c.getType();
  arity = ct.getNumChildren() - 1;
  return true;
}

bool KairosMetaReduce::echo(const std::string& msg)
{
  // Metadata for the Lean backend (lean-meta, lean-parser-op, ...).
  return msg.compare(0, 5, "lean-") != 0;
}

void KairosMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  if (prog.isNull())
  {
    return;
  }
  // As LeanMetaReduce::defineProgram: linearize the patterns first.
  for (const auto& lp : LinearPattern::linearize(d_state, v, prog))
  {
    d_progOrder.push_back(lp.first);
    d_progDef[lp.first] = lp.second;
  }
}

void KairosMetaReduce::define(const std::string& name, const Expr& e)
{
  // As LeanMetaReduce::define.
  if (isParseDefName(name) || name.compare(0, 4, "$eo_") != 0
      || !getEmbedTypeApp(e).isNull())
  {
    return;
  }
  Expr tmp;
  Expr prog;
  if (buildLambdaDefineProgram(name, e, tmp, prog))
  {
    d_progOrder.push_back(tmp);
    d_progDef[tmp] = prog;
    d_isDefine.insert(tmp);
  }
  else
  {
    Expr t = d_state.mkSymbol(Kind::PROGRAM_CONST, name, d_state.mkAny());
    d_progOrder.push_back(t);
    d_progDef[t] = e;
  }
}

KairosMetaReduce::ArgInfo KairosMetaReduce::argInfo(const Expr& t)
{
  ArgInfo a;
  MetaKind k = getTypeMetaKindFor(t, MetaKind::EUNOIA, false);
  if (k == MetaKind::EUNOIA)
  {
    a.sort = Sort::TERM;
    a.kType = "Id";
    a.lType = "Term";
  }
  else if (k == MetaKind::PROOF)
  {
    a.sort = Sort::PROOF;
    a.kType = "Id";
    a.lType = "Proof";
  }
  else if (k == MetaKind::CHECKER_RULE)
  {
    a.sort = Sort::NATIVE;
    a.kType = "CRule";
    a.lType = "CRule";
  }
  else if (k == MetaKind::CHECKER_EMBED)
  {
    std::string name = getEmbedTypeName(getEmbedTypeApp(t));
    if (name == "CIndexList")
    {
      a.sort = Sort::NATIVE;
      a.kType = name;
      a.lType = name;
    }
    else if (name == "CState")
    {
      a.sort = Sort::STATE;
      a.kType = "KState";
      a.lType = name;
    }
    else if (name == "CArgList")
    {
      a.sort = Sort::ARGS;
      a.kType = "KArgList";
      a.lType = name;
    }
  }
  else if (k == MetaKind::EO_EMBED)
  {
    // datatype declarations: Logos values on both sides
    a.sort = Sort::NATIVE;
    a.kType = getEmbedTypeName(getEmbedTypeApp(t));
    a.lType = a.kType;
  }
  else if (k == MetaKind::SMT_BUILTIN)
  {
    Expr s = unguard(t);
    const Literal* l = s.getNumChildren() > 1 ? s[1].getValue()->asLiteral() : nullptr;
    if (l != nullptr)
    {
      a.sort = Sort::NATIVE;
      a.kType = "native_" + cleanSmtId(l->d_str.toString());
      a.lType = a.kType;
    }
  }
  return a;
}

/** The layout of a program, as LeanMetaReduce::finalizeProgram prints it. */
void KairosMetaReduce::analyze(Prog& p)
{
  Expr vt = p.v.getType();
  if (p.def.getKind() != Kind::PROGRAM)
  {
    p.supported = false;
    p.why = "defined by a non-program definition";
    return;
  }
  if (vt.getKind() != Kind::PROGRAM_TYPE)
  {
    p.supported = false;
    p.why = "not a program type";
    return;
  }
  size_t nargs = vt.getNumChildren();
  std::vector<MetaKind> kinds;
  bool isChecker = false;
  for (size_t j = 0; j < nargs; j++)
  {
    kinds.push_back(getTypeMetaKindFor(vt[j], MetaKind::EUNOIA, false));
    isChecker |= isCheckerMetaKind(kinds.back());
  }
  for (size_t j = 0; j + 1 < nargs; j++)
  {
    p.args.push_back(argInfo(vt[j]));
  }
  p.ret = argInfo(vt[nargs - 1]);
  if (isChecker)
  {
    p.supported = false;
    p.why = "a checker definition";
  }
  if (isSmtMetaKind(kinds.back()))
  {
    p.supported = false;
    p.why = "an SMT-level definition";
  }
  const Expr& prog = p.def;
  size_t ncases = prog.getNumChildren();
  // macro arguments: non-term arguments that are the same parameter in every
  // case become parameters of the Lean definition
  size_t macroStart = 1;
  bool macroOk = true;
  while (macroOk && macroStart < nargs)
  {
    if (kinds[macroStart - 1] == MetaKind::EUNOIA)
    {
      break;
    }
    Expr v;
    for (size_t i = 0; i < ncases; i++)
    {
      Expr vn = prog[i][0][macroStart];
      if ((v.isNull() && vn.getKind() == Kind::PARAM) || v == vn)
      {
        v = vn;
        continue;
      }
      macroOk = false;
      break;
    }
    if (macroOk)
    {
      macroStart++;
    }
  }
  p.macroStart = macroStart;
  if (macroStart == nargs)
  {
    p.plainDef = true;
    p.alts.push_back({Alt::CASE, 0, 0});
    return;
  }
  MetaKind retk = kinds[nargs - 1];
  if (retk == MetaKind::EUNOIA && !p.isDefine && !isChecker)
  {
    for (size_t i = macroStart; i < nargs; i++)
    {
      if (kinds[i - 1] != MetaKind::EUNOIA)
      {
        continue;
      }
      bool matchesParam = false;
      for (size_t j = 0; j < ncases; j++)
      {
        if (prog[j][0][i].getKind() == Kind::PARAM)
        {
          matchesParam = true;
          break;
        }
      }
      if (matchesParam)
      {
        p.alts.push_back({Alt::GUARD, i, 0});
      }
    }
  }
  bool wasDefault = false;
  for (size_t i = 0; i < ncases; i++)
  {
    p.alts.push_back({Alt::CASE, 0, i});
    wasDefault = true;
    for (size_t j = macroStart; j < nargs; j++)
    {
      if (prog[i][0][j].getKind() != Kind::PARAM)
      {
        wasDefault = false;
      }
    }
  }
  if (!wasDefault && !isChecker
      && (retk == MetaKind::EUNOIA || retk == MetaKind::PROOF))
  {
    p.alts.push_back({Alt::DEFAULT, 0, 0});
  }
}

bool KairosMetaReduce::checkPattern(const Expr& e, Prog& p)
{
  Kind k = e.getKind();
  if (k == Kind::PARAM)
  {
    return true;
  }
  if (k == Kind::APPLY && e.getNumChildren() == 2 && !isProgramApp(e))
  {
    return checkPattern(e[0], p) && checkPattern(e[1], p);
  }
  if (k == Kind::FUNCTION_TYPE && e.getNumChildren() == 2)
  {
    return checkPattern(e[0], p) && checkPattern(e[1], p);
  }
  if (k == Kind::APPLY_OPAQUE && !isEmbedCons(e[0])
      && d_userOpArity.count(getName(e[0])) > 0)
  {
    for (size_t i = 1; i < e.getNumChildren(); i++)
    {
      if (!checkPattern(e[i], p))
      {
        return false;
      }
    }
    return d_userOpArity.at(getName(e[0])) + 1 == e.getNumChildren();
  }
  if (k == Kind::APPLY_OPAQUE && isEmbedCons(e[0]))
  {
    std::string cname;
    getMetaKindFor(e[0], cname);
    auto it = ctorTable().find(cname);
    if (it == ctorTable().end() || it->second.fields.size() + 1 != e.getNumChildren())
    {
      p.why = "pattern constructor " + cname;
      return false;
    }
    for (size_t i = 1; i < e.getNumChildren(); i++)
    {
      bool isId = it->second.fields[i - 1] == "I";
      if (!isId && e[i].getKind() != Kind::PARAM)
      {
        p.why = "a non-variable native field in a pattern";
        return false;
      }
      if (isId && !checkPattern(e[i], p))
      {
        return false;
      }
    }
    return true;
  }
  if (e.getNumChildren() == 0)
  {
    std::string node, term;
    if (k == Kind::CONST)
    {
      std::string cname;
      MetaKind mk = getMetaKindFor(e, cname);
      if (mk != MetaKind::EUNOIA || cname == "Stuck")
      {
        p.why = "pattern constant " + cname;
        return false;
      }
      Attr attr = d_state.getAttributeKind(e.getValue());
      if (attr == Attr::OPAQUE)
      {
        p.why = "indexed operator in a pattern";
        return false;
      }
    }
    return true;
  }
  p.why = "pattern kind " + kindToString(k);
  return false;
}

bool KairosMetaReduce::checkBody(const Expr& e, Sort expect, Prog& p)
{
  Kind k = e.getKind();
  if (k == Kind::PARAM)
  {
    if (expect == Sort::NATIVE)
    {
      Expr ec = e;
      Expr t = d_tc.getType(ec);
      if (getTypeMetaKindFor(t, MetaKind::EUNOIA, false) == MetaKind::EUNOIA)
      {
        p.why = "a term used as a native value";
        return false;
      }
    }
    return true;
  }
  if (expect == Sort::PROOF)
  {
    if (k == Kind::APPLY_OPAQUE && getName(e[0]) == "$eo_pf" && e.getNumChildren() == 2)
    {
      return checkBody(e[1], Sort::TERM, p);
    }
    p.why = "a proof that is not (pf F)";
    return false;
  }
  if (expect == Sort::NATIVE)
  {
    if (isProgramApp(e))
    {
      std::string cname = getName(e[0]);
      p.callees.insert(cname);
      auto it = d_progs.find(cname);
      if (it == d_progs.end() || !it->second.pure)
      {
        p.why = "a native-sorted call of " + cname;
        return false;
      }
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        if (!checkBody(e[i], Sort::NATIVE, p))
        {
          return false;
        }
      }
      return true;
    }
    if (k == Kind::APPLY_OPAQUE)
    {
      std::string sname = getName(e[0]);
      if (sname.compare(0, 14, "$native_apply_") != 0)
      {
        p.why = "a native-sorted " + sname;
        return false;
      }
      std::string nname = e.getNumChildren() > 1 && e[1].getValue()->asLiteral()
                              ? e[1].getValue()->asLiteral()->d_str.toString()
                              : "";
      for (size_t i = 2; i < e.getNumChildren(); i++)
      {
        Sort s = (nname == "teq") ? Sort::TERM : Sort::NATIVE;
        if (nname == "ite" && i > 2)
        {
          s = Sort::NATIVE;
        }
        if (!checkBody(e[i], s, p))
        {
          return false;
        }
      }
      return true;
    }
    p.why = "a native-sorted " + kindToString(k);
    return false;
  }
  // term-sorted
  if (e.getNumChildren() == 0)
  {
    if (k == Kind::CONST)
    {
      std::string cname;
      MetaKind mk = getMetaKindFor(e, cname);
      if (mk != MetaKind::EUNOIA)
      {
        p.why = "body constant " + cname;
        return false;
      }
      if (d_state.getAttributeKind(e.getValue()) == Attr::OPAQUE)
      {
        p.why = "indexed operator in a body";
        return false;
      }
    }
    else if (k == Kind::PROGRAM_CONST)
    {
      p.why = "a program used as a value";
      return false;
    }
    return true;
  }
  if (k == Kind::APPLY)
  {
    if (isProgramApp(e))
    {
      std::string cname = getName(e[0]);
      p.callees.insert(cname);
      auto it = d_progs.find(cname);
      if (it == d_progs.end())
      {
        p.why = "calls " + cname + ", which Logos does not define";
        return false;
      }
      const Prog& q = it->second;
      if (q.args.size() + 1 != e.getNumChildren())
      {
        p.why = "a partial application of " + cname;
        return false;
      }
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        if (q.args[i - 1].sort == Sort::OTHER || !checkBody(e[i], q.args[i - 1].sort, p))
        {
          return false;
        }
      }
      return true;
    }
    if (e.getNumChildren() != 2)
    {
      p.why = "an n-ary application";
      return false;
    }
    if (e.isEvaluatable())
    {
      p.callees.insert("$eo_mk_apply");
    }
    return checkBody(e[0], Sort::TERM, p) && checkBody(e[1], Sort::TERM, p);
  }
  if (k == Kind::APPLY_OPAQUE)
  {
    std::string sname = getName(e[0]);
    if (sname.compare(0, 14, "$native_apply_") == 0)
    {
      std::string nname = e[1].getValue()->asLiteral()
                              ? e[1].getValue()->asLiteral()->d_str.toString()
                              : "";
      if (nname != "ite")
      {
        p.why = "a term-sorted native " + nname;
        return false;
      }
      return checkBody(e[2], Sort::NATIVE, p) && checkBody(e[3], Sort::TERM, p)
             && checkBody(e[4], Sort::TERM, p);
    }
    if (d_userOpArity.count(sname) > 0)
    {
      if (d_userOpArity.at(sname) + 1 != e.getNumChildren())
      {
        p.why = "a partial indexed operator " + sname;
        return false;
      }
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        if (!checkBody(e[i], Sort::TERM, p))
        {
          return false;
        }
      }
      return true;
    }
    if (isEmbedCons(e[0]))
    {
      std::string cname;
      getMetaKindFor(e[0], cname);
      auto it = ctorTable().find(cname);
      if (it == ctorTable().end() || it->second.fields.size() + 1 != e.getNumChildren())
      {
        p.why = "body constructor " + cname;
        return false;
      }
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        Sort s = it->second.fields[i - 1] == "I" ? Sort::TERM : Sort::NATIVE;
        if (!checkBody(e[i], s, p))
        {
          return false;
        }
      }
      return true;
    }
    p.why = "body operator " + sname;
    return false;
  }
  if (k == Kind::FUNCTION_TYPE && e.getNumChildren() == 2)
  {
    return checkBody(e[0], Sort::TERM, p) && checkBody(e[1], Sort::TERM, p);
  }
  if (k == Kind::EVAL_IF_THEN_ELSE)
  {
    return checkBody(e[0], Sort::TERM, p) && checkBody(e[1], Sort::TERM, p)
           && checkBody(e[2], Sort::TERM, p);
  }
  if (isLiteralOp(k))
  {
    std::string kstr = kindToTerm(k);
    if (kstr.compare(0, 4, "eo::") != 0)
    {
      p.why = "literal op " + kstr;
      return false;
    }
    std::string pname = "$eo_" + kstr.substr(4);
    p.callees.insert(pname);
    auto it = d_progs.find(pname);
    if (it == d_progs.end() || it->second.args.size() != e.getNumChildren())
    {
      p.why = "builtin " + kstr;
      return false;
    }
    for (size_t i = 0; i < e.getNumChildren(); i++)
    {
      if (it->second.args[i].sort == Sort::OTHER
          || !checkBody(e[i], it->second.args[i].sort, p))
      {
        return false;
      }
    }
    return true;
  }
  p.why = "body kind " + kindToString(k);
  return false;
}

void KairosMetaReduce::checkSupported(Prog& p)
{
  if (!p.supported)
  {
    return;
  }
  for (const ArgInfo& a : p.args)
  {
    if (a.sort == Sort::OTHER)
    {
      p.supported = false;
      p.why = "an argument of a type not supported yet";
      return;
    }
  }
  if (p.ret.sort != Sort::TERM)
  {
    p.supported = false;
    p.why = "a result that is not a term";
    return;
  }
  for (size_t i = 0; i < p.def.getNumChildren(); i++)
  {
    const Expr& hd = p.def[i][0];
    for (size_t j = p.macroStart; j < hd.getNumChildren(); j++)
    {
      if (p.args[j - 1].sort == Sort::NATIVE && hd[j].getKind() != Kind::PARAM)
      {
        p.supported = false;
        p.why = "a native argument matched against a value";
        return;
      }
      if (p.args[j - 1].sort == Sort::TERM && !checkPattern(hd[j], p))
      {
        p.supported = false;
        return;
      }
      if (p.args[j - 1].sort == Sort::PROOF)
      {
        const Expr& q = hd[j];
        if (!(q.getKind() == Kind::APPLY_OPAQUE && getName(q[0]) == "$eo_pf"
              && q.getNumChildren() == 2 && checkPattern(q[1], p)))
        {
          p.supported = false;
          p.why = "a proof pattern that is not (pf F)";
          return;
        }
      }
    }
    if (!checkBody(p.def[i][1], Sort::TERM, p))
    {
      p.supported = false;
      return;
    }
  }
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

namespace {

/** A pattern variable or argument, as the body sees it. */
struct Var
{
  std::string name;
  bool isId;
};

/** The state of the right-hand side being compiled: the store and its
 * hypotheses, and the facts known (Γ, oldest first). */
struct Scope
{
  std::string sig, hI, hG;
  std::vector<std::string> gamma;
  std::map<std::string, Var> vars;
  std::map<const ExprValue*, std::string> memo;
};

/** Output under construction: code lines and proof lines. */
struct Out
{
  std::vector<std::string> code;
  std::vector<std::string> proof;
};

}  // namespace

std::string KairosMetaReduce::emitProgram(Prog& p,
                                          std::ostream& matchers,
                                          std::ostream& codeOut,
                                          std::ostream& specs,
                                          std::ostream& calls,
                                          std::ostream& steps,
                                          std::ostream* dispatchOut)
{
  const bool isDispatch = (dispatchOut != nullptr);
  // the dispatch lives above Gen.spec: it calls at a fixed fuel
  const std::string fuelVar = isDispatch ? "fuel" : "kfuel";
  // the callee's spec at the fuel of the call: from the induction
  // hypothesis within a recursive component, else its closed theorem
  auto specOf = [&](const Prog& q) -> std::string {
    if (!isDispatch && p.sccRecursive && q.scc == p.scc)
    {
      return "ih.s" + q.lname;
    }
    return std::string("(allS") + q.lname + (isDispatch ? " fuel)" : " kn)");
  };
  const std::string& f = p.lname;
  const std::string kf = "k" + f;
  const std::string sf = "S" + f;
  const std::string field = "s" + f;
  size_t nargs = p.args.size();
  std::vector<std::string> argNames;
  for (size_t i = 0; i < nargs; i++)
  {
    argNames.push_back("arg" + std::to_string(i + 1));
  }
  // the binders of the arguments, implicit, and their hypotheses
  std::stringstream implicitArgs, validHyps, decArgs, kArgs;
  std::vector<std::string> termArgs;
  for (size_t i = 0; i < nargs; i++)
  {
    implicitArgs << " {" << argNames[i] << " : " << p.args[i].kType << "}";
    kArgs << " " << argNames[i];
    if (isIdSort(p.args[i].sort))
    {
      validHyps << " → " << argNames[i] << " < σ.size";
      if (p.args[i].sort == Sort::PROOF)
      {
        decArgs << " (Proof.pf (σ.decode " << argNames[i] << "))";
      }
      else
      {
        decArgs << " (σ.decode " << argNames[i] << ")";
      }
      termArgs.push_back(argNames[i]);
    }
    else
    {
      decArgs << " " << argNames[i];
    }
  }
  // spec
  specs << "abbrev " << sf << " (n : Nat) : Prop :=\n  ∀ {σ : Store}" << implicitArgs.str()
        << ", Inv sem σ" << validHyps.str() << " →\n    Sim sem σ (" << kf << " n"
        << kArgs.str() << ") (" << f << decArgs.str() << ")\n\n";
  // call lemma
  {
    std::stringstream hdr, mem, valid, rw;
    calls << "theorem C" << f << " {n : Nat} (hf : " << sf << " n) {σ : Store} {Γ : List Fact}"
          << " (hI : Inv sem σ) (hΓ : Ctx σ Γ)";
    for (size_t i = 0; i < nargs; i++)
    {
      calls << " {" << argNames[i] << " : " << p.args[i].kType << "}";
      if (isIdSort(p.args[i].sort))
      {
        calls << " {A" << i + 1 << " : Term}";
      }
    }
    std::stringstream lhsArgs;
    for (size_t i = 0; i < nargs; i++)
    {
      if (isIdSort(p.args[i].sort))
      {
        calls << "\n    (p" << i + 1 << " : Fact.term " << argNames[i] << " A" << i + 1
              << " ∈ Γ)";
        valid << " (hΓ.valid p" << i + 1 << ")";
        rw << (rw.str().empty() ? "" : ", ") << "hΓ.dec p" << i + 1;
        if (p.args[i].sort == Sort::PROOF)
        {
          lhsArgs << " (Proof.pf A" << i + 1 << ")";
        }
        else
        {
          lhsArgs << " A" << i + 1;
        }
      }
      else
      {
        lhsArgs << " " << argNames[i];
      }
    }
    calls << " :\n    Sim sem σ (" << kf << " n" << kArgs.str() << ") (" << f << lhsArgs.str()
          << ") :=\n  (hf hI" << valid.str() << ").congr ";
    if (rw.str().empty())
    {
      calls << "rfl\n\n";
    }
    else
    {
      calls << "(by rw [" << rw.str() << "])\n\n";
    }
  }

  // fuel 0
  std::string zero = "    " + field + " := fun _";
  for (size_t i = 0; i < termArgs.size(); i++)
  {
    zero += " _";
  }
  zero += " => by simp only [" + kf + "]; exact Ok.throw";
  if (p.lifted)
  {
    codeOut << "/-- Lifted: Logos computes it on decoded arguments. -/\n";
    codeOut << "def " << kf << " : Nat";
    for (size_t i = 0; i < nargs; i++)
    {
      codeOut << " → " << p.args[i].kType;
    }
    codeOut << " → K Id\n  | 0";
    for (size_t i = 0; i < nargs; i++)
    {
      codeOut << ", _";
    }
    codeOut << " => throw .fuel\n  | _ + 1";
    for (const std::string& a : argNames)
    {
      codeOut << ", " << a;
    }
    codeOut << " => withStore fun σ => internTerm (" << f << decArgs.str() << ")\n\n";
    steps << "theorem step" << f << " {kn : Nat} : " << sf << " (kn + 1) := by\n"
          << "  intro σ";
    for (const std::string& a : argNames)
    {
      steps << " " << a;
    }
    steps << " hI";
    for (size_t i = 0; i < termArgs.size(); i++)
    {
      steps << " _";
    }
    steps << "\n  simp only [" << kf << "]\n  apply Sim.withStore\n  exact Sim.lift hI\n\n";
    return zero;
  }

  // --- matchers, and the program text by alternative ---
  std::stringstream kbody;   // the program's n+1 case body
  std::stringstream proof;   // the step proof
  size_t base = 4;           // indentation of the match chain in the program
  proof << "theorem step" << f << " {kn : Nat}"
        << (p.sccRecursive ? " (ih : Spec" + std::to_string(p.scc) + " kn)" : "") << " : " << sf
        << " (kn + 1) := by\n";
  proof << "  intro σ";
  for (size_t i = 0; i < nargs; i++)
  {
    proof << " " << argNames[i];
  }
  proof << " hI";
  std::map<std::string, std::string> argValid;
  for (size_t i = 0; i < nargs; i++)
  {
    if (isIdSort(p.args[i].sort))
    {
      argValid[argNames[i]] = "h" + std::to_string(i + 1);
      proof << " h" << i + 1;
    }
  }
  proof << "\n";
  // Γ: Stuck, then the term arguments
  std::vector<std::string> gamma0 = {"0"};
  {
    std::string ctx = "Ctx.stuck hI";
    for (const std::string& a : termArgs)
    {
      ctx = "Ctx.arg " + argValid[a] + " (" + ctx + ")";
      gamma0.push_back(a);
    }
    proof << "  have hΓ := " << ctx << "\n";
  }
  proof << "  simp only [" << kf << "]\n";
  if (p.cached)
  {
    // the arguments are valid: a term, so that no tactic sees the program
    std::string vl = "(fun _ h => absurd h List.not_mem_nil)";
    for (size_t i = termArgs.size(); i-- > 0;)
    {
      vl = "(List.forall_mem_cons.mpr ⟨" + argValid[termArgs[i]] + ", " + vl + "⟩)";
    }
    proof << "  apply cached_ctx hI " << vl << " rfl\n";
  }
  proof << "  apply Sim.withStore\n";

  size_t fresh = 0;
  auto freshName = [&](const std::string& pre) { return pre + std::to_string(fresh++); };

  // compile a body expression; see the Scope invariants above
  std::function<std::string(const Expr&, Scope&, Out&, bool)> compileTerm;
  std::function<std::string(const Expr&, Scope&, Out&, std::vector<std::string>&)> compileNative;
  // a proof argument: the id of its formula
  auto compileProof = [&](const Expr& e, Scope& sc, Out& out) -> std::string {
    if (e.getKind() == Kind::PARAM)
    {
      return sc.vars.at(cleanSmtId(str(e))).name;
    }
    return compileTerm(e[1], sc, out, false);
  };

  // emit a computation either as the final expression or as a step binding a
  // fresh id
  auto finish = [&](const std::string& code, const std::string& prf, Scope& sc, Out& out,
                    bool final) -> std::string {
    if (final)
    {
      out.code.push_back(code);
      out.proof.push_back("exact " + prf);
      return "";
    }
    std::string t = freshName("kt");
    std::string s = freshName("σ");
    std::string hI = freshName("hI");
    std::string hG = freshName("hΓ");
    // parenthesized: `do` would otherwise push the rest of the block into
    // the branches of a conditional
    out.code.push_back("let " + t + " ← (" + code + ")");
    // a computation with branches is named, so that its branch proofs are
    // elaborated against known code
    std::string named = code.find("(do ") != std::string::npos
                            ? " (m := (" + replaceAll(code, "kfuel", isDispatch ? "fuel" : "kn") + "))"
                            : "";
    out.proof.push_back("refine Sim.step" + named + " " + sc.hG + " (" + prf + ") fun " + t + " " + s
                        + " " + hI + " " + hG + " => ?_");
    sc.sig = s;
    sc.hI = hI;
    sc.hG = hG;
    sc.gamma.push_back(t);
    return t;
  };

  auto atomNode = [&](const Expr& c) -> std::string {
    Kind k = c.getKind();
    if (k == Kind::TYPE)
    {
      return ".Type";
    }
    if (k == Kind::BOOL_TYPE)
    {
      return ".Bool";
    }
    if (k == Kind::CONST)
    {
      std::string cname;
      getMetaKindFor(c, cname);
      std::string raw = getName(c);
      if (raw.compare(0, 4, "$emb") != 0 && cname != "Stuck" && cname != "Type"
          && cname != "FunType" && cname != "Bool" && cname.compare(0, 4, "$eo_") != 0)
      {
        return "(.UOp UserOp." + cleanSmtId(cname) + ")";
      }
      return "." + cleanSmtId(cname);
    }
    const Literal* l = c.getValue()->asLiteral();
    AlwaysAssert(l != nullptr) << "kairos-meta: atom " << c;
    if (k == Kind::BOOLEAN)
    {
      return std::string("(.Boolean ") + (l->d_bool ? "true" : "false") + ")";
    }
    if (k == Kind::NUMERAL)
    {
      const Integer& ci = l->d_int;
      if (ci.sgn() == -1)
      {
        return "(.Numeral (-" + (-ci).toString() + " : native_Int))";
      }
      return "(.Numeral " + ci.toString() + ")";
    }
    if (k == Kind::BINARY)
    {
      return "(.Binary " + std::to_string(l->d_bv.getSize()) + " "
             + l->d_bv.getValue().toString() + ")";
    }
    if (k == Kind::STRING)
    {
      std::string css = l->toString();
      return css.empty() ? "(.String [])" : "(.String (native_string_lit \"" + css + "\"))";
    }
    if (k == Kind::RATIONAL)
    {
      std::string rstr = str(c);
      bool isNeg = (l->d_rat.sgn() == -1);
      rstr = replaceAll(replaceAll(rstr, "/", " "), "-", "");
      return std::string("(.Rational ") + (isNeg ? "(- " : "") + "(native_mk_rational " + rstr
             + ")" + (isNeg ? ")" : "") + ")";
    }
    AlwaysAssert(false) << "kairos-meta: atom kind " << k;
    return "";
  };
  auto termOfNode = [](const std::string& node) {
    // `.Ctor` / `(.Ctor args)` as a Logos term
    if (node.compare(0, 2, "(.") == 0)
    {
      return "(Term." + node.substr(2);
    }
    return "Term" + node;
  };

  auto nativeName = [&](const Expr& oApp) -> std::string {
    const Literal* l = oApp[1].getValue()->asLiteral();
    std::string s = l->d_str.toString();
    bool isInt = !s.empty() && std::all_of(s.begin(), s.end(), ::isdigit);
    if (isInt || s == "true" || s == "false")
    {
      return s;
    }
    if (!s.empty() && s[0] == '"')
    {
      return s.size() == 2 ? "[]" : "(native_string_lit " + s + ")";
    }
    if (s.compare(0, 6, "UserOp") == 0)
    {
      return s;
    }
    return "native_" + cleanSmtId(s);
  };

  compileNative = [&](const Expr& e, Scope& sc, Out& out,
                      std::vector<std::string>& rewrites) -> std::string {
    if (e.getKind() == Kind::PARAM)
    {
      return sc.vars.at(cleanSmtId(str(e))).name;
    }
    if (isProgramApp(e))
    {
      std::string s = "(" + d_progs.at(getName(e[0])).lname;
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        s += " " + compileNative(e[i], sc, out, rewrites);
      }
      return s + ")";
    }
    std::string name = nativeName(e);
    if (e.getNumChildren() == 2)
    {
      return name;
    }
    std::string raw = e[1].getValue()->asLiteral()->d_str.toString();
    if (raw == "teq")
    {
      std::string a = compileTerm(e[2], sc, out, false);
      std::string b = compileTerm(e[3], sc, out, false);
      rewrites.push_back("knative_teq_ctx @@HI@@ @@HG@@ @@" + a + "@@ @@" + b + "@@");
      return "(knative_teq " + a + " " + b + ")";
    }
    std::string s = "(" + name;
    for (size_t i = 2; i < e.getNumChildren(); i++)
    {
      s += " " + compileNative(e[i], sc, out, rewrites);
    }
    return s + ")";
  };

  // rewrites mention facts by name; resolve them in the scope where they run
  auto resolve = [&](const std::string& rw, const Scope& sc) {
    std::string r = replaceAll(replaceAll(rw, "@@HI@@", sc.hI), "@@HG@@", sc.hG);
    size_t pos;
    while ((pos = r.find("@@")) != std::string::npos)
    {
      size_t end = r.find("@@", pos + 2);
      std::string nm = r.substr(pos + 2, end - pos - 2);
      r.replace(pos, end - pos + 2, memProof(sc.gamma, nm));
    }
    return r;
  };
  auto emitRewrites = [&](std::vector<std::string>& rws, const Scope& sc, Out& out) {
    for (const std::string& rw : rws)
    {
      out.proof.push_back("try rw [" + resolve(rw, sc) + "]");
    }
    rws.clear();
  };

  // render a sub-block (a branch) as code text and proof text
  // branches are rendered on one line, so that they nest at any depth
  auto renderBlock = [](const Out& o, size_t) {
    std::string code = "(do ";
    for (size_t i = 0; i < o.code.size(); i++)
    {
      code += (i ? "; " : "") + o.code[i];
    }
    return code + ")";
  };
  // in a branch, the term the branch computes is not known when a step is
  // taken: `apply` leaves it to be found, where `refine` would not
  auto renderProof = [](const Out& o, size_t) {
    std::string prf = "(by ";
    for (size_t i = 0; i < o.proof.size(); i++)
    {
      std::string l = o.proof[i];
      const std::string pre = "refine Sim.step";
      size_t f = l.rfind(" fun ");
      if (l.compare(0, pre.size(), pre) == 0 && f != std::string::npos
          && l.size() >= 5 && l.compare(l.size() - 5, 5, "=> ?_") == 0)
      {
        std::string binders = l.substr(f + 5, l.size() - 5 - (f + 5));
        l = "apply Sim.step" + l.substr(pre.size(), f - pre.size()) + "; intro " + binders;
      }
      prf += (i ? "; " : "") + l;
    }
    return prf + ")";
  };

  compileTerm = [&](const Expr& e, Scope& sc, Out& out, bool final) -> std::string {
    Kind k = e.getKind();
    if (k == Kind::PARAM)
    {
      const Var& v = sc.vars.at(cleanSmtId(str(e)));
      if (final)
      {
        out.code.push_back("pure " + v.name);
        out.proof.push_back("exact Sim.ret " + sc.hI + " " + sc.hG + " "
                            + memProof(sc.gamma, v.name));
      }
      return v.name;
    }
    if (!final)
    {
      auto it = sc.memo.find(e.getValue());
      if (it != sc.memo.end())
      {
        return it->second;
      }
    }
    std::string r;
    if (e.getNumChildren() == 0 && k == Kind::CONST)
    {
      std::string cname;
      getMetaKindFor(e, cname);
      if (cname == "Stuck")
      {
        if (final)
        {
          out.code.push_back("pure 0");
          out.proof.push_back("exact Sim.stuck " + sc.hI);
        }
        return "0";
      }
    }
    if (e.getNumChildren() == 0)
    {
      r = finish("intern " + atomNode(e), "intern_leaf " + sc.hI + " rfl", sc, out, final);
    }
    else if (k == Kind::APPLY && isProgramApp(e) && getName(e[0]) == "$eo_state_proven_nth")
    {
      std::string st = sc.vars.at(cleanSmtId(str(e[1]))).name;
      std::vector<std::string> rws;
      std::string n = compileNative(e[2], sc, out, rws);
      emitRewrites(rws, sc, out);
      r = finish("k_state_proven_nth " + st + " " + n,
                 "C_state_proven_nth " + sc.hI + " " + sc.hG + " " + memProof(sc.gamma, st) + " _",
                 sc, out, final);
    }
    else if (k == Kind::APPLY && isProgramApp(e) && getName(e[0]) == "$eo_mk_premise_list")
    {
      std::string fx = compileTerm(e[1], sc, out, false);
      std::vector<std::string> rws;
      std::string pl = compileNative(e[2], sc, out, rws);
      emitRewrites(rws, sc, out);
      std::string st = sc.vars.at(cleanSmtId(str(e[3]))).name;
      r = finish("k_mk_premise_list " + fuelVar + " " + fx + " " + pl + " " + st,
                 "C_mk_premise_list " + fuelVar + " " + sc.hI + " " + sc.hG + " "
                     + memProof(sc.gamma, fx) + " " + memProof(sc.gamma, st) + " _",
                 sc, out, final);
    }
    else if (k == Kind::APPLY && isProgramApp(e))
    {
      const Prog& q = d_progs.at(getName(e[0]));
      std::vector<std::string> ops;
      std::vector<std::string> rws;
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        if (q.args[i - 1].sort == Sort::TERM)
        {
          ops.push_back(compileTerm(e[i], sc, out, false));
        }
        else if (q.args[i - 1].sort == Sort::PROOF)
        {
          ops.push_back(compileProof(e[i], sc, out));
        }
        else
        {
          ops.push_back(compileNative(e[i], sc, out, rws));
        }
      }
      emitRewrites(rws, sc, out);
      std::string code = "k" + q.lname + " " + fuelVar;
      std::string prf = "C" + q.lname + " " + specOf(q) + " " + sc.hI + " " + sc.hG;
      for (size_t i = 0; i < ops.size(); i++)
      {
        code += " " + ops[i];
        if (isIdSort(q.args[i].sort))
        {
          prf += " " + memProof(sc.gamma, ops[i]);
        }
      }
      r = finish(code, prf, sc, out, final);
    }
    else if (k == Kind::APPLY)
    {
      if (e.isEvaluatable())
      {
        const Prog& q = d_progs.at("$eo_mk_apply");
        std::string a = compileTerm(e[0], sc, out, false);
        std::string b = compileTerm(e[1], sc, out, false);
        r = finish("k" + q.lname + " " + fuelVar + " " + a + " " + b,
                   "C" + q.lname + " " + specOf(q) + " " + sc.hI + " " + sc.hG + " " + memProof(sc.gamma, a)
                       + " " + memProof(sc.gamma, b),
                   sc, out, final);
      }
      else
      {
        std::string a = compileTerm(e[0], sc, out, false);
        std::string b = compileTerm(e[1], sc, out, false);
        r = finish("intern (.Apply " + a + " " + b + ")",
                   "intern_Apply " + sc.hI + " " + sc.hG + " " + memProof(sc.gamma, a) + " "
                       + memProof(sc.gamma, b),
                   sc, out, final);
      }
    }
    else if (k == Kind::FUNCTION_TYPE)
    {
      std::string a = compileTerm(e[0], sc, out, false);
      std::string b = compileTerm(e[1], sc, out, false);
      std::string ft = finish("intern .FunType", "intern_leaf " + sc.hI + " rfl", sc, out, false);
      std::string g = finish("intern (.Apply " + ft + " " + a + ")",
                             "intern_Apply " + sc.hI + " " + sc.hG + " " + memProof(sc.gamma, ft)
                                 + " " + memProof(sc.gamma, a),
                             sc, out, false);
      r = finish("intern (.Apply " + g + " " + b + ")",
                 "intern_Apply " + sc.hI + " " + sc.hG + " " + memProof(sc.gamma, g) + " "
                     + memProof(sc.gamma, b),
                 sc, out, final);
    }
    else if (k == Kind::APPLY_OPAQUE && getName(e[0]).compare(0, 14, "$native_apply_") == 0)
    {
      // native_ite on terms: evaluate the branch taken only
      std::vector<std::string> rws;
      std::string c = compileNative(e[2], sc, out, rws);
      emitRewrites(rws, sc, out);
      size_t ind = 6;
      Scope st = sc;
      Out ot;
      compileTerm(e[3], st, ot, true);
      Scope se = sc;
      Out oe;
      compileTerm(e[4], se, oe, true);
      std::string code =
          "if " + c + " then " + renderBlock(ot, ind) + " else " + renderBlock(oe, ind);
      std::string prf = "Sim.nite (fun _ => " + renderProof(ot, ind) + ") (fun _ => "
                        + renderProof(oe, ind) + ")";
      r = finish(code, prf, sc, out, final);
    }
    else if (k == Kind::APPLY_OPAQUE && d_userOpArity.count(getName(e[0])) > 0)
    {
      size_t ar = d_userOpArity.at(getName(e[0]));
      std::string ocname;
      getMetaKindFor(e[0], ocname);
      std::vector<std::string> ops;
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        ops.push_back(compileTerm(e[i], sc, out, false));
      }
      std::string code = "intern (.UOp" + std::to_string(ar) + " UserOp" + std::to_string(ar) + "."
                         + cleanSmtId(ocname);
      std::string prf = "intern_UOp" + std::to_string(ar) + " " + sc.hI + " " + sc.hG;
      for (const std::string& o : ops)
      {
        code += " " + o;
        prf += " " + memProof(sc.gamma, o);
      }
      r = finish(code + ")", prf, sc, out, final);
    }
    else if (k == Kind::APPLY_OPAQUE)
    {
      std::string cname;
      getMetaKindFor(e[0], cname);
      const CtorInfo& ci = ctorTable().at(cname);
      std::vector<std::string> ops;
      std::vector<std::string> rws;
      for (size_t i = 1; i < e.getNumChildren(); i++)
      {
        if (ci.fields[i - 1] == "I")
        {
          ops.push_back(compileTerm(e[i], sc, out, false));
        }
        else
        {
          ops.push_back(compileNative(e[i], sc, out, rws));
        }
      }
      emitRewrites(rws, sc, out);
      std::string code = "intern (." + cname;
      for (const std::string& o : ops)
      {
        code += " " + o;
      }
      code += ")";
      std::string prf;
      if (ci.internLemma.empty())
      {
        prf = "intern_leaf " + sc.hI + " rfl";
      }
      else
      {
        prf = ci.internLemma + " " + sc.hI + " " + sc.hG;
        for (size_t i = 0; i < ops.size(); i++)
        {
          if (ci.fields[i] == "I")
          {
            prf += " " + memProof(sc.gamma, ops[i]);
          }
        }
      }
      r = finish(code, prf, sc, out, final);
    }
    else if (k == Kind::EVAL_IF_THEN_ELSE)
    {
      std::string c = compileTerm(e[0], sc, out, false);
      size_t ind = 6;
      Scope st = sc;
      Out ot;
      compileTerm(e[1], st, ot, true);
      Scope se = sc;
      Out oe;
      compileTerm(e[2], se, oe, true);
      r = finish("k_ite " + c + " " + renderBlock(ot, ind) + " " + renderBlock(oe, ind),
                 "k_ite_sim " + sc.hI + " " + sc.hG + " " + memProof(sc.gamma, c) + " "
                     + renderProof(ot, ind) + " " + renderProof(oe, ind),
                 sc, out, final);
    }
    else if (isLiteralOp(k))
    {
      const Prog& q = d_progs.at("$eo_" + kindToTerm(k).substr(4));
      std::vector<std::string> ops;
      std::vector<std::string> rws;
      for (size_t i = 0; i < e.getNumChildren(); i++)
      {
        if (q.args[i].sort == Sort::TERM)
        {
          ops.push_back(compileTerm(e[i], sc, out, false));
        }
        else if (q.args[i].sort == Sort::PROOF)
        {
          ops.push_back(compileProof(e[i], sc, out));
        }
        else
        {
          ops.push_back(compileNative(e[i], sc, out, rws));
        }
      }
      emitRewrites(rws, sc, out);
      std::string code = "k" + q.lname + " " + fuelVar;
      std::string prf = "C" + q.lname + " " + specOf(q) + " " + sc.hI + " " + sc.hG;
      for (size_t i = 0; i < ops.size(); i++)
      {
        code += " " + ops[i];
        if (isIdSort(q.args[i].sort))
        {
          prf += " " + memProof(sc.gamma, ops[i]);
        }
      }
      r = finish(code, prf, sc, out, final);
    }
    else
    {
      AlwaysAssert(false) << "kairos-meta: unexpected body " << e;
    }
    if (!final)
    {
      sc.memo[e.getValue()] = r;
    }
    return r;
  };

  if (isDispatch)
  {
    std::ostream& out = *dispatchOut;
    // names: the macro arguments (the state) by their Logos names
    std::vector<std::string> names = argNames;
    for (size_t i = 0; i + 1 < p.macroStart; i++)
    {
      names[i] = cleanSmtId(str(p.def[0][0][i + 1]));
    }
    // patterns over checker values, printed as Lean patterns; bound
    // variables are collected in order
    struct DVar
    {
      std::string name;
      bool isId;
    };
    std::function<std::string(const Expr&, std::vector<DVar>&, std::string&)> dpat;
    // rc: the rcases pattern for the validity of an argument list
    dpat = [&](const Expr& e, std::vector<DVar>& vs, std::string& rc) -> std::string {
      if (e.getKind() == Kind::PARAM)
      {
        rc = "-";
        return cleanSmtId(str(e));
      }
      std::string raw = getName(e.getKind() == Kind::APPLY_OPAQUE ? e[0] : e);
      AlwaysAssert(raw.compare(0, 5, "$emb_") == 0) << "kairos-meta: dispatch pattern " << e;
      std::string rest = raw.substr(5);
      std::string pre = rest.substr(0, rest.find('.'));
      std::string ctor = rest.substr(rest.find('.') + 1);
      if (pre == "r")
      {
        std::string cname;
        getMetaKindFor(e, cname);
        rc = "-";
        return "CRule." + cleanSmtId(cname);
      }
      std::string ty = pre == "al" ? "KArgList" : "CIndexList";
      if (e.getKind() != Kind::APPLY_OPAQUE)
      {
        rc = "-";
        return ty + "." + ctor;
      }
      // cons: an element and a tail
      std::string hd;
      if (e[1].getKind() == Kind::PARAM)
      {
        hd = cleanSmtId(str(e[1]));
        vs.push_back({hd, pre == "al"});
      }
      else
      {
        AlwaysAssert(false) << "kairos-meta: dispatch element pattern " << e[1];
      }
      std::string rcTail;
      std::string tl = dpat(e[2], vs, rcTail);
      rc = pre == "al" ? "⟨w_" + hd + ", " + rcTail + "⟩" : "-";
      return "(" + ty + "." + ctor + " " + hd + " " + tl + ")";
    };
    std::stringstream def, thm;
    def << "def " << kf << " (fuel : Nat)";
    for (size_t i = 0; i + 1 < p.macroStart; i++)
    {
      def << " (" << names[i] << " : " << p.args[i].kType << ")";
    }
    def << " :";
    for (size_t i = p.macroStart - 1; i < nargs; i++)
    {
      def << " " << p.args[i].kType << " →";
    }
    def << " K Id\n";
    // the theorem's binders
    thm << "theorem " << kf << "_sim (fuel : Nat) {σ : Store} (hI : Inv sem σ)";
    std::vector<std::string> gamma = {"0"};
    std::string ctx = "Ctx.stuck hI";
    std::stringstream dec;
    for (size_t i = 0; i < nargs; i++)
    {
      const std::string& a = names[i];
      std::string h = "h" + std::to_string(i + 1);
      switch (p.args[i].sort)
      {
        case Sort::STATE:
          thm << " {" << a << " : KState} (" << h << " : " << a << ".valid σ)";
          ctx = "Ctx.cons (f := Fact.state " + a + " (" + a + ".dec σ)) ⟨" + h + ", rfl⟩ (" + ctx + ")";
          gamma.push_back(a);
          dec << " (" << a << ".dec σ)";
          break;
        case Sort::ARGS:
          thm << " {" << a << " : KArgList} (" << h << " : " << a << ".valid σ)";
          dec << " (" << a << ".dec σ)";
          break;
        case Sort::TERM:
          thm << " {" << a << " : Id} (" << h << " : " << a << " < σ.size)";
          ctx = "Ctx.arg " + h + " (" + ctx + ")";
          gamma.push_back(a);
          dec << " (σ.decode " << a << ")";
          break;
        default:
          thm << " (" << a << " : " << p.args[i].kType << ")";
          dec << " " << a;
          break;
      }
    }
    thm << " :\n    Sim sem σ (" << kf << " fuel";
    for (const std::string& a : names)
    {
      thm << " " << a;
    }
    thm << ")\n      (" << f << dec.str() << ") := by\n";
    thm << "  have hΓ := " << ctx << "\n  unfold " << kf << "\n  split\n";
    for (size_t ci = 0; ci < p.def.getNumChildren(); ci++)
    {
      const Expr& hd = p.def[ci][0];
      const Expr& body = p.def[ci][1];
      std::vector<DVar> vs;
      std::vector<std::string> pats;
      std::string argsRc;
      size_t argsPos = 0;
      bool allParams = true;
      for (size_t i = p.macroStart; i < hd.getNumChildren(); i++)
      {
        std::string rc;
        if (hd[i].getKind() == Kind::PARAM)
        {
          // named as the argument, which the code and the facts use
          pats.push_back(names[i - 1]);
          rc = "-";
        }
        else
        {
          pats.push_back(dpat(hd[i], vs, rc));
          allParams = false;
        }
        if (p.args[i - 1].sort == Sort::ARGS)
        {
          argsRc = rc;
          argsPos = i;
        }
      }
      def << "  |";
      for (size_t j = 0; j < pats.size(); j++)
      {
        def << (j ? ", " : " ") << pats[j];
      }
      def << " =>";
      std::string eqName = f + ".eq_" + std::to_string(ci + 1);
      Scope sc;
      sc.sig = "σ";
      sc.hI = "hI";
      sc.hG = "hΓ";
      sc.gamma = gamma;
      for (size_t i = 0; i < nargs; i++)
      {
        if (p.args[i].sort == Sort::STATE || p.args[i].sort == Sort::TERM)
        {
          sc.vars[names[i]] = {names[i], p.args[i].sort == Sort::TERM};
        }
      }
      // top-level parameters of this case alias the arguments
      for (size_t i = p.macroStart; i < hd.getNumChildren(); i++)
      {
        if (hd[i].getKind() == Kind::PARAM)
        {
          sc.vars[cleanSmtId(str(hd[i]))] = {names[i - 1], p.args[i - 1].sort == Sort::TERM};
        }
      }
      Out o;
      thm << "  · ";
      std::string pind = "    ";
      if (!allParams)
      {
        if (!vs.empty())
        {
          thm << "rename_i";
          for (const DVar& v : vs)
          {
            thm << " " << v.name;
          }
          thm << "\n" << pind;
        }
        std::string hctx = "hΓ";
        bool anyId = false;
        for (const DVar& v : vs)
        {
          sc.vars[v.name] = {v.name, v.isId};
          if (v.isId)
          {
            anyId = true;
          }
        }
        if (anyId)
        {
          thm << "obtain " << argsRc << " := h" << argsPos << "\n" << pind;
          for (const DVar& v : vs)
          {
            if (v.isId)
            {
              hctx = "Ctx.arg w_" + v.name + " (" + hctx + ")";
              sc.gamma.push_back(v.name);
            }
          }
          thm << "have hΓb := " << hctx << "\n" << pind;
          sc.hG = "hΓb";
        }
        thm << "simp only [KArgList.dec]\n" << pind;
      }
      thm << "rw [" << eqName << "]; kside\n";
      compileTerm(body, sc, o, true);
      def << " do\n";
      for (const std::string& l : o.code)
      {
        def << "    " << replaceAll(l, "\n", "\n    ") << "\n";
      }
      for (const std::string& l : o.proof)
      {
        thm << pind << replaceAll(l, "\n", "\n" + pind) << "\n";
      }
    }
    out << def.str() << "\n" << thm.str() << "\n";
    return "";
  }

  // --- the alternatives ---
  size_t nalts = p.alts.size();
  std::string hgCur = "hΓ";
  std::vector<std::string> gammaCur = gamma0;
  size_t depth = 0;
  for (size_t ai = 0; ai < nalts; ai++)
  {
    const Alt& alt = p.alts[ai];
    size_t eqIdx = ai + 1;
    std::string eqName = f + ".eq_" + std::to_string(eqIdx);
    std::string pi = indent(2);
    std::string ci = indent(base);
    Expr hd, body;
    if (alt.kind == Alt::CASE)
    {
      hd = p.def[alt.ci][0];
      body = p.def[alt.ci][1];
    }
    // the pattern variables bound at the top level alias the arguments
    std::map<std::string, Var> vars;
    for (size_t i = 0; i < nargs; i++)
    {
      if (alt.kind == Alt::CASE && hd[i + 1].getKind() == Kind::PARAM)
      {
        vars[cleanSmtId(str(hd[i + 1]))] = {argNames[i], isIdSort(p.args[i].sort)};
      }
      // (pf F): F is the argument itself
      if (alt.kind == Alt::CASE && p.args[i].sort == Sort::PROOF
          && hd[i + 1][1].getKind() == Kind::PARAM)
      {
        vars[cleanSmtId(str(hd[i + 1][1]))] = {argNames[i], true};
      }
    }
    // constrained positions
    std::vector<size_t> cpos;
    if (alt.kind == Alt::GUARD)
    {
      cpos.push_back(alt.arg - 1);
    }
    else if (alt.kind == Alt::CASE)
    {
      for (size_t i = 0; i < nargs; i++)
      {
        bool isVar = hd[i + 1].getKind() == Kind::PARAM
                     || (p.args[i].sort == Sort::PROOF
                         && hd[i + 1][1].getKind() == Kind::PARAM);
        if (!isVar)
        {
          cpos.push_back(i);
        }
      }
    }
    bool lastAlt = (ai + 1 == nalts);
    bool total = (alt.kind == Alt::DEFAULT) || (alt.kind == Alt::CASE && cpos.empty());
    std::string mname = "m" + f + "_" + std::to_string(eqIdx);

    // the right-hand side
    auto emitRhs = [&](Scope& sc, size_t cind, size_t pind, bool close = false) {
      Out out;
      if (alt.kind == Alt::CASE)
      {
        compileTerm(body, sc, out, true);
      }
      else
      {
        out.code.push_back("pure 0");
        out.proof.push_back("exact Sim.stuck " + sc.hI);
      }
      kbody << " do\n";
      for (size_t li = 0; li < out.code.size(); li++)
      {
        std::string ll = replaceAll(out.code[li], "\n", "\n" + indent(cind));
        kbody << indent(cind) << ll << (close && li + 1 == out.code.size() ? ")" : "") << "\n";
      }
      for (const std::string& l : out.proof)
      {
        std::string ll = replaceAll(l, "\n", "\n" + indent(pind));
        proof << indent(pind) << ll << "\n";
      }
    };

    if (total)
    {
      // no matcher: this alternative always applies
      Scope sc;
      sc.sig = "σ";
      sc.hI = "hI";
      sc.hG = hgCur;
      sc.gamma = gammaCur;
      sc.vars = vars;
      if (p.plainDef)
      {
        proof << pi << "rw [" << eqName << "]\n";
      }
      else
      {
        proof << pi << "rw [" << eqName << "]; kside\n";
      }
      kbody << ci << "--" << (alt.kind == Alt::DEFAULT ? " default" : " case")
            << "\n" << ci;
      emitRhs(sc, base + 2, 2);
      break;
    }
    AlwaysAssert(!lastAlt || alt.kind != Alt::CASE || !cpos.empty());

    // --- the matcher ---
    struct Bound
    {
      std::string name;
      std::string type;
      bool isId;
      std::string valid;  // the validity proof name, for ids
    };
    std::vector<Bound> bound;
    std::stringstream mdef;   // the chain
    std::string closeParens;
    std::vector<std::string> someLines, noneLines, ofViews, views;
    std::set<std::string> guardEqs;   // among views: operator equations
    std::vector<std::string> lpats;   // Logos patterns, by constrained position
    std::vector<std::string> spats;   // decoded patterns, for the some lemma
    size_t vk = 0;
    std::function<void(const Expr&, const std::string&, const std::string&, const std::string&,
                       std::string&, std::string&)>
        walk;
    // x: the id examined; wx: its validity; ex: the equation naming its
    // decoding (none lemma); out: its Logos pattern and its decoded pattern
    walk = [&](const Expr& e, const std::string& x, const std::string& wx, const std::string& ex,
               std::string& lp, std::string& sp) {
      Kind k = e.getKind();
      if (k == Kind::PARAM)
      {
        std::string nm = cleanSmtId(str(e));
        bound.push_back({nm, "Id", true, wx});
        lp = nm;
        sp = "(σ.decode " + nm + ")";
        return;
      }
      std::string v = "v" + std::to_string(vk++);
      views.push_back(v);
      if (e.getNumChildren() == 0)
      {
        std::string node = atomNode(e);
        mdef << "σ.leaf " << x << " " << node << " (";
        closeParens += ")";
        someLines.push_back("obtain ⟨" + v + ", h⟩ := leaf_some h");
        noneLines.push_back("have " + v + " := decode_leaf_inv (n := " + node
                            + ") (d := σ.decode) hI rfl " + ex);
        ofViews.push_back("leaf_of_view " + v);
        lp = termOfNode(node);
        sp = lp;
        return;
      }
      if (k == Kind::FUNCTION_TYPE)
      {
        // (-> A B) is Apply (Apply FunType A) B
        auto nameOf = [&](const Expr& c) {
          return c.getKind() == Kind::PARAM ? cleanSmtId(str(c))
                                            : "kp" + std::to_string(fresh++);
        };
        std::string g = "kp" + std::to_string(fresh++);
        std::string ft = "kp" + std::to_string(fresh++);
        std::string na = nameOf(e[0]), nb = nameOf(e[1]);
        std::string v2 = "v" + std::to_string(vk++);
        std::string v3 = "v" + std::to_string(vk++);
        views.push_back(v2);
        views.push_back(v3);
        mdef << "σ.m_Apply " << x << " fun " << g << " " << nb << " => σ.m_Apply " << g << " fun " << ft
             << " " << na << " => σ.leaf " << ft << " .FunType (";
        closeParens += ")";
        std::string wg = "w" + std::to_string(fresh++), wb = "w" + std::to_string(fresh++);
        std::string wft = "w" + std::to_string(fresh++), wa = "w" + std::to_string(fresh++);
        someLines.push_back("obtain ⟨" + g + ", " + nb + ", " + v + ", h⟩ := m_Apply_some h");
        someLines.push_back("have " + wg + " := valid_of_view (j := " + g + ") hI " + wx + " " + v
                            + " (by simp [Node.children])");
        someLines.push_back("have " + wb + " := valid_of_view (j := " + nb + ") hI " + wx + " " + v
                            + " (by simp [Node.children])");
        someLines.push_back("obtain ⟨" + ft + ", " + na + ", " + v2 + ", h⟩ := m_Apply_some h");
        someLines.push_back("have " + wft + " := valid_of_view (j := " + ft + ") hI " + wg + " "
                            + v2 + " (by simp [Node.children])");
        someLines.push_back("have " + wa + " := valid_of_view (j := " + na + ") hI " + wg + " "
                            + v2 + " (by simp [Node.children])");
        someLines.push_back("obtain ⟨" + v3 + ", h⟩ := leaf_some h");
        ofViews.push_back("m_Apply_of_view " + v);
        ofViews.push_back("m_Apply_of_view " + v2);
        ofViews.push_back("leaf_of_view " + v3);
        std::string eg = "e" + std::to_string(fresh++), eb = "e" + std::to_string(fresh++);
        std::string eft = "e" + std::to_string(fresh++), ea = "e" + std::to_string(fresh++);
        noneLines.push_back("obtain ⟨" + g + ", " + nb + ", " + v + ", " + eg + ", " + eb
                            + "⟩ := decode_Apply_inv hI " + ex);
        noneLines.push_back("obtain ⟨" + ft + ", " + na + ", " + v2 + ", " + eft + ", " + ea
                            + "⟩ := decode_Apply_inv hI " + eg);
        noneLines.push_back("have " + v3 + " := decode_leaf_inv (n := .FunType) (d := σ.decode) hI rfl "
                            + eft);
        std::string lpa, spa, lpb, spb;
        auto child = [&](const Expr& c, const std::string& nm, const std::string& w,
                         const std::string& ec, std::string& lpc, std::string& spc) {
          if (c.getKind() == Kind::PARAM)
          {
            bound.push_back({nm, "Id", true, w});
            lpc = nm;
            spc = "(σ.decode " + nm + ")";
          }
          else
          {
            walk(c, nm, w, ec, lpc, spc);
          }
        };
        child(e[0], na, wa, ea, lpa, spa);
        child(e[1], nb, wb, eb, lpb, spb);
        lp = "(Term.Apply (Term.Apply Term.FunType " + lpa + ") " + lpb + ")";
        sp = "(Term.Apply (Term.Apply Term.FunType " + spa + ") " + spb + ")";
        return;
      }
      std::string cname = "Apply";
      size_t fstart = 0;
      // an indexed user operator: UOp<n> with its operator fixed
      std::string fixedOp;
      if (k == Kind::APPLY_OPAQUE && !isEmbedCons(e[0]))
      {
        size_t ar = d_userOpArity.at(getName(e[0]));
        std::string ocname;
        getMetaKindFor(e[0], ocname);
        cname = "UOp" + std::to_string(ar);
        fixedOp = "UserOp" + std::to_string(ar) + "." + cleanSmtId(ocname);
        fstart = 1;
      }
      else if (k == Kind::APPLY_OPAQUE)
      {
        getMetaKindFor(e[0], cname);
        fstart = 1;
      }
      const CtorInfo& ci = ctorTable().at(cname);
      std::vector<std::string> fnames;
      std::vector<Expr> fexprs;
      size_t off = fixedOp.empty() ? 0 : 1;
      if (!fixedOp.empty())
      {
        fnames.push_back("ko" + std::to_string(fresh++));
        fexprs.push_back(Expr());
      }
      for (size_t i = fstart; i < e.getNumChildren(); i++)
      {
        Expr c = e[i];
        fexprs.push_back(c);
        if (c.getKind() == Kind::PARAM)
        {
          fnames.push_back(cleanSmtId(str(c)));
        }
        else
        {
          fnames.push_back("kp" + std::to_string(fresh++));
        }
      }
      mdef << "σ." << ci.prim << " " << x << " fun";
      for (const std::string& n : fnames)
      {
        mdef << " " << n;
      }
      mdef << " => ";
      if (!fixedOp.empty())
      {
        mdef << guardFor(fnames[0], fixedOp);
        closeParens += ")";
      }
      // some direction
      std::string ob = "obtain ⟨";
      for (const std::string& n : fnames)
      {
        ob += n + ", ";
      }
      someLines.push_back(ob + v + ", h⟩ := " + ci.prim + "_some h");
      if (!fixedOp.empty())
      {
        std::string g = "g" + std::to_string(fresh++);
        someLines.push_back("obtain ⟨" + g + ", h⟩ := kguard_some h");
        views.push_back(g);
        guardEqs.insert(g);
      }
      ofViews.push_back(ci.prim + "_of_view " + v);
      // none direction: invert; one equation per id field
      std::vector<std::string> eqs(fnames.size(), "");
      {
        std::string ids, es;
        for (size_t i = 0; i < fnames.size(); i++)
        {
          if (ci.fields[i] == "I")
          {
            ids += fnames[i] + ", ";
            eqs[i] = "e" + std::to_string(fresh++);
            es += ", " + eqs[i];
          }
        }
        if (ids.empty())
        {
          noneLines.push_back("have " + v + " := " + ci.inv + " hI " + ex);
        }
        else
        {
          noneLines.push_back("obtain ⟨" + ids + v + es + "⟩ := " + ci.inv + " hI " + ex);
        }
      }
      (void)off;
      // fields
      std::vector<std::string> lps, sps;
      for (size_t i = 0; i < fnames.size(); i++)
      {
        bool isId = ci.fields[i] == "I";
        std::string flp, fsp;
        if (isId)
        {
          std::string w = "w" + std::to_string(fresh++);
          someLines.push_back("have " + w + " := valid_of_view (j := " + fnames[i] + ") hI " + wx
                              + " " + v + " (by simp [Node.children])");
          if (fexprs[i].getKind() == Kind::PARAM)
          {
            bound.push_back({fnames[i], "Id", true, w});
            flp = fnames[i];
            fsp = "(σ.decode " + fnames[i] + ")";
          }
          else
          {
            walk(fexprs[i], fnames[i], w, eqs[i], flp, fsp);
          }
        }
        else if (i == 0 && !fixedOp.empty())
        {
          flp = fixedOp;
          fsp = fixedOp;
        }
        else
        {
          std::string ty = ci.fields[i].substr(2);
          bound.push_back({fnames[i], ty, false, ""});
          flp = fnames[i];
          fsp = fnames[i];
        }
        lps.push_back(flp);
        sps.push_back(fsp);
      }
      lp = "(Term." + cname;
      sp = "(Term." + cname;
      for (size_t i = 0; i < lps.size(); i++)
      {
        lp += " " + lps[i];
        sp += " " + sps[i];
      }
      lp += ")";
      sp += ")";
    };

    // the matcher's chain over the constrained positions
    std::vector<std::string> eqHyps;
    if (alt.kind == Alt::GUARD)
    {
      size_t i = alt.arg - 1;
      mdef << "Store.stuck " << argNames[i] << " (";
      closeParens += ")";
      lpats.push_back("Term.Stuck");
      spats.push_back("Term.Stuck");
    }
    else
    {
      for (size_t i : cpos)
      {
        std::string ex = "eq" + std::to_string(i + 1);
        eqHyps.push_back(ex);
        std::string lp, sp;
        Expr pat = p.args[i].sort == Sort::PROOF ? hd[i + 1][1] : hd[i + 1];
        walk(pat, argNames[i], argValid[argNames[i]], ex, lp, sp);
        lpats.push_back(lp);
        spats.push_back(sp);
      }
    }
    std::vector<std::string> bnames, btypes, bids;
    for (const Bound& b : bound)
    {
      bnames.push_back(b.name);
      btypes.push_back(b.type);
    }
    mdef << "some " << tupleVal(bnames) << closeParens;
    matchers << "def " << mname << " (σ : Store)";
    for (size_t i = 0; i < nargs; i++)
    {
      matchers << " (" << argNames[i] << " : " << p.args[i].kType << ")";
    }
    matchers << " : Option " << tupleType(btypes) << " :=\n  " << mdef.str() << "\n\n";
    // the _some lemma
    std::stringstream sl;
    sl << "theorem " << mname << "_some {σ : Store} (hI : Inv sem σ)";
    for (size_t i = 0; i < nargs; i++)
    {
      sl << " {" << argNames[i] << " : " << p.args[i].kType << "}";
    }
    for (const Bound& b : bound)
    {
      sl << " {r_" << b.name << " : " << b.type << "}";
    }
    for (size_t i = 0; i < nargs; i++)
    {
      if (isIdSort(p.args[i].sort))
      {
        sl << "\n    (" << argValid[argNames[i]] << " : " << argNames[i] << " < σ.size)";
      }
    }
    std::vector<std::string> rbn;
    for (const Bound& b : bound)
    {
      rbn.push_back("r_" + b.name);
    }
    sl << "\n    (h : " << mname << " σ";
    for (const std::string& a : argNames)
    {
      sl << " " << a;
    }
    sl << " = some " << tupleVal(rbn) << ") :\n    ";
    std::vector<std::string> concl;
    for (const Bound& b : bound)
    {
      if (b.isId)
      {
        concl.push_back("r_" + b.name + " < σ.size");
      }
    }
    std::vector<std::string> spatsR;
    for (size_t j = 0; j < spats.size(); j++)
    {
      std::string s = spats[j];
      for (const Bound& b : bound)
      {
        // patterns mention the bound names; the statement uses r_ names
        s = replaceAll(s, " " + b.name + ")", " r_" + b.name + ")");
        s = replaceAll(s, " " + b.name + " ", " r_" + b.name + " ");
      }
      spatsR.push_back(s);
      size_t i = alt.kind == Alt::GUARD ? alt.arg - 1 : cpos[j];
      concl.push_back("σ.decode " + argNames[i] + " = " + s);
    }
    for (size_t j = 0; j < concl.size(); j++)
    {
      sl << (j ? " ∧ " : "") << concl[j];
    }
    sl << " := by\n";
    if (alt.kind == Alt::GUARD)
    {
      sl << "  obtain ⟨e, -⟩ := stuck_some h; subst e; exact decode_zero hI\n\n";
    }
    else
    {
      sl << "  unfold " << mname << " at h\n";
      for (const std::string& l : someLines)
      {
        sl << "  " << l << "\n";
      }
      if (bound.size() == 1)
      {
        sl << "  simp only [Option.some.injEq] at h\n  subst h\n";
      }
      else if (bound.size() > 1)
      {
        sl << "  simp only [Option.some.injEq, Prod.mk.injEq] at h\n  obtain ⟨";
        for (size_t j = 0; j < bound.size(); j++)
        {
          sl << (j ? ", " : "") << "rfl";
        }
        sl << "⟩ := h\n";
      }
      std::string simpViews = "simp only [";
      for (size_t j = 0; j < views.size(); j++)
      {
        simpViews += (j ? ", " : "")
                     + (guardEqs.count(views[j]) ? views[j]
                                                 : std::string("decode_of_view hI ") + views[j]);
      }
      simpViews += ", Node.toTerm]";
      size_t nvalid = 0;
      if (concl.size() == 1)
      {
        sl << "  " << simpViews << "\n\n";
      }
      else
      {
      sl << "  refine ⟨";
      for (const Bound& b : bound)
      {
        if (b.isId)
        {
          sl << (nvalid++ ? ", " : "") << b.valid;
        }
      }
      for (size_t j = 0; j < spats.size(); j++)
      {
        sl << (nvalid++ ? ", " : "") << "?_";
      }
      sl << "⟩ <;> " << simpViews << "\n\n";
      }
    }
    matchers << sl.str();
    // the _none lemma
    std::stringstream nl;
    nl << "theorem " << mname << "_none {σ : Store} (hI : Inv sem σ)";
    for (size_t i = 0; i < nargs; i++)
    {
      nl << " {" << argNames[i] << " : " << p.args[i].kType << "}";
    }
    if (alt.kind == Alt::GUARD)
    {
      nl << " (" << argValid[argNames[alt.arg - 1]] << " : " << argNames[alt.arg - 1]
         << " < σ.size)";
    }
    nl << "\n    (h : " << mname << " σ";
    for (const std::string& a : argNames)
    {
      nl << " " << a;
    }
    nl << " = none) :\n    ";
    if (!bound.empty())
    {
      nl << "∀";
      for (const Bound& b : bound)
      {
        nl << " (" << b.name << " : " << (b.isId ? "Term" : b.type) << ")";
      }
      nl << ", ";
    }
    for (size_t j = 0; j < lpats.size(); j++)
    {
      size_t i = alt.kind == Alt::GUARD ? alt.arg - 1 : cpos[j];
      nl << "σ.decode " << argNames[i] << " = " << lpats[j] << " → ";
    }
    nl << "False := by\n";
    if (alt.kind == Alt::GUARD)
    {
      std::string hv = argValid[argNames[alt.arg - 1]];
      nl << "  intro e; have := decode_stuck_inv hI " << hv << " e; subst this\n";
      nl << "  simp [" << mname << ", stuck_of_zero] at h\n\n";
    }
    else
    {
      nl << "  intro";
      for (const Bound& b : bound)
      {
        nl << " " << b.name;
      }
      for (const std::string& e : eqHyps)
      {
        nl << " " << e;
      }
      nl << "\n";
      for (const std::string& l : noneLines)
      {
        nl << "  " << l << "\n";
      }
      nl << "  simp [" << mname << ", kguard";
      for (const std::string& o : ofViews)
      {
        nl << ", " << o;
      }
      nl << "] at h\n\n";
    }
    matchers << nl.str();

    // --- the program: match on the matcher ---
    std::vector<std::string> bpat;
    for (const Bound& b : bound)
    {
      bpat.push_back(b.name);
    }
    std::string funPat = bound.empty() ? "_" : tupleVal(bpat);
    kbody << ci << "kcase (" << mname << " σ";
    for (const std::string& a : argNames)
    {
      kbody << " " << a;
    }
    kbody << ") (fun " << funPat << " =>";
    // --- the proof of this alternative ---
    std::string hm = "hm" + std::to_string(eqIdx);
    std::string pin = indent(4);
    std::string vname = bound.size() == 1 ? bound[0].name : (bound.empty() ? "_" : "v");
    proof << pi << "refine kcase_sim (fun " << vname << " " << hm << " => ?_) (fun " << hm
          << " => ?_)\n";
    proof << pi << "· ";
    bool firstLine = true;
    auto pline = [&](const std::string& l) {
      proof << (firstLine ? "" : pin) << l << "\n";
      firstLine = false;
    };
    if (bound.size() > 1)
    {
      std::string ob = "obtain ⟨";
      for (size_t j = 0; j < bound.size(); j++)
      {
        ob += (j ? ", " : "") + bound[j].name;
      }
      pline(ob + "⟩ := v");
    }
    // the some lemma's conclusions
    std::vector<std::string> dnames;
    std::vector<std::string> vnames;
    {
      std::string pat = "⟨";
      size_t cnt = 0;
      for (const Bound& b : bound)
      {
        if (b.isId)
        {
          std::string w = "hb_" + b.name;
          vnames.push_back(w);
          pat += (cnt++ ? ", " : "") + w;
        }
      }
      for (size_t j = 0; j < spats.size(); j++)
      {
        std::string d = "d" + std::to_string(j + 1);
        dnames.push_back(d);
        pat += (cnt++ ? ", " : "") + d;
      }
      pat += "⟩";
      if (cnt == 1)
      {
        pat = dnames.empty() ? vnames[0] : dnames[0];
      }
      std::string l = std::string(cnt == 1 ? "have " : "obtain ") + pat + " := " + mname + "_some hI";
      for (size_t i = 0; i < nargs; i++)
      {
        if (isIdSort(p.args[i].sort))
        {
          l += " " + argValid[argNames[i]];
        }
      }
      pline(l + " " + hm);
    }
    Scope sc;
    sc.sig = "σ";
    sc.hI = "hI";
    sc.hG = hgCur;
    sc.gamma = gammaCur;
    sc.vars = vars;
    {
      std::string ctx = hgCur;
      size_t vi = 0;
      for (const Bound& b : bound)
      {
        if (b.isId)
        {
          ctx = "Ctx.arg " + vnames[vi++] + " (" + ctx + ")";
          sc.gamma.push_back(b.name);
        }
        sc.vars[b.name] = {b.name, b.isId};
      }
      if (vi > 0)
      {
        sc.hG = "hΓb";
        pline("have hΓb := " + ctx);
      }
    }
    pline("try dsimp only");
    {
      std::string l = "rw [";
      for (const std::string& d : dnames)
      {
        l += d + ", ";
      }
      pline(l + eqName + "]; kside");
    }
    emitRhs(sc, base + 4, 4, true);
    // the none branch continues the chain
    kbody << ci << "<|\n";
    proof << pi << "have n" << eqIdx << " := " << mname << "_none hI";
    if (alt.kind == Alt::GUARD)
    {
      proof << " " << argValid[argNames[alt.arg - 1]];
    }
    proof << " " << hm << "\n";
    depth++;
    if (lastAlt)
    {
      // a match that is not total in Kairos: Logos has no case left, so this
      // is unreachable; Lean still needs a value
      kbody << ci << "pure 0\n";
      proof << pi << "exact absurd rfl (n" << eqIdx << " _)\n";
    }
  }
  (void)depth;

  // --- the program ---
  codeOut << "def " << kf << " : Nat";
  for (size_t i = 0; i < nargs; i++)
  {
    codeOut << " → " << p.args[i].kType;
  }
  codeOut << " → K Id\n  | 0";
  for (size_t i = 0; i < nargs; i++)
  {
    codeOut << ", _";
  }
  codeOut << " => throw .fuel\n  | kfuel + 1";
  for (const std::string& a : argNames)
  {
    codeOut << ", " << a;
  }
  codeOut << " =>";
  if (p.cached)
  {
    codeOut << " cached " << p.pid << " [";
    for (size_t i = 0; i < termArgs.size(); i++)
    {
      codeOut << (i ? ", " : "") << termArgs[i];
    }
    codeOut << "] <|";
  }
  codeOut << " withStore fun σ =>\n" << kbody.str() << "\n";
  steps << proof.str() << "\n";
  return zero;
}

/** Kairos's view of Logos's Term: Node, its matcher primitives, and interning
 * of Logos terms. All are mechanical in Term's constructors. */
void KairosMetaReduce::emitTermModules()
{
  const char* calcEnv = std::getenv("KAIROS_CALC");
  std::string calc = calcEnv != nullptr ? calcEnv : "Cpc";
  const std::string hdr =
      "-- This file is auto-generated by install/install-cpc.sh (kairos-eoc) from the\n"
      "-- signature of the pinned Logos. Do not edit.\n";
  auto fieldNames = [](const std::vector<std::string>& ts, const std::string& pre) {
    std::vector<std::string> ns;
    for (size_t i = 0; i < ts.size(); i++)
    {
      ns.push_back(pre + std::to_string(i + 1));
    }
    return ns;
  };
  auto join = [](const std::vector<std::string>& xs, const std::string& sep) {
    std::string r;
    for (size_t i = 0; i < xs.size(); i++)
    {
      r += (i ? sep : "") + xs[i];
    }
    return r;
  };
  // --- Gen/Term.lean ---
  {
    std::stringstream o;
    o << hdr << "import " << calc << ".Logos\nimport Std.Data.HashMap\n\n"
      << "namespace Kairos\nopen Eo SmtEval\n\n/-- A store id. -/\nabbrev Id := Nat\n\n";
    o << "deriving instance Hashable for UserOp\n";
    for (const auto& [ar, ops] : d_userOps)
    {
      if (ar > 0)
      {
        o << "deriving instance Hashable for UserOp" << ar << "\n";
      }
    }
    o << "\n/-- Datatype declarations are stored as Logos values. Their hash is coarse on\n"
      << "purpose (equality decides); interning them is future work. -/\n"
      << "instance : Hashable DatatypeDecl := ⟨fun _ => 0⟩\n\n"
      << "/-- One level of a Logos `Term`; `Term` children are store ids. -/\n"
      << "inductive Node where\n";
    for (const auto& [c, ts] : d_termCons)
    {
      o << "  | " << c;
      std::vector<std::string> fs = fieldNames(ts, "f");
      for (size_t i = 0; i < ts.size(); i++)
      {
        o << " (" << fs[i] << " : " << (ts[i] == "Term" ? "Id" : ts[i]) << ")";
      }
      o << "\n";
    }
    o << "  deriving DecidableEq, Hashable, Inhabited\n\nnamespace Node\n\n"
      << "/-- The store ids a node refers to. -/\ndef children : Node → List Id\n";
    bool anyNonLeaf = false;
    for (const auto& [c, ts] : d_termCons)
    {
      std::vector<std::string> ids;
      std::vector<std::string> pats;
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          pats.push_back("f" + std::to_string(i + 1));
          ids.push_back("f" + std::to_string(i + 1));
        }
        else
        {
          pats.push_back("_");
        }
      }
      if (!ids.empty())
      {
        anyNonLeaf = true;
        o << "  | ." << c << " " << join(pats, " ") << " => [" << join(ids, ", ") << "]\n";
      }
    }
    o << "  | _ => []\n\n";
    (void)anyNonLeaf;
    o << "/-- The Logos term a node stands for, given how to read its children. -/\n"
      << "def toTerm (d : Id → Term) : Node → Term\n";
    for (const auto& [c, ts] : d_termCons)
    {
      std::vector<std::string> fs = fieldNames(ts, "f");
      o << "  | ." << c << (fs.empty() ? "" : " ") << join(fs, " ") << " => ." << c;
      for (size_t i = 0; i < ts.size(); i++)
      {
        o << (ts[i] == "Term" ? " (d " + fs[i] + ")" : " " + fs[i]);
      }
      o << "\n";
    }
    o << "\ntheorem toTerm_congr {d d' : Id → Term} (n : Node)\n"
      << "    (h : ∀ j ∈ n.children, d j = d' j) : n.toTerm d = n.toTerm d' := by\n"
      << "  cases n <;> simp_all [toTerm, children]\n\n"
      << "/-- Two nodes whose children read the same, injectively, are equal. -/\n"
      << "theorem toTerm_inj {d : Id → Term} (n m : Node)\n"
      << "    (hinj : ∀ a ∈ n.children, ∀ b ∈ m.children, d a = d b → a = b)\n"
      << "    (h : n.toTerm d = m.toTerm d) : n = m := by\n"
      << "  cases n <;> cases m <;> simp_all [toTerm, children]\n\n"
      << "end Node\n\nend Kairos\n";
    std::ofstream(getOutputPath("kairos/Kairos/Gen/Term.lean")) << o.str();
  }
  // --- Gen/Prims.lean: one matcher primitive per constructor with fields ---
  {
    std::stringstream o;
    o << hdr << "import Kairos.Runtime.Match\n\nset_option linter.unusedVariables false\n\n"
      << "namespace Kairos\nopen Eo Store SmtEval\n\nvariable {sem : Sem} {σ : Store} {Γ : List Fact}\n\n";
    for (const auto& [c, ts] : d_termCons)
    {
      if (ts.empty())
      {
        continue;
      }
      std::vector<std::string> fs = fieldNames(ts, "f");
      std::vector<std::string> kts;
      std::vector<std::string> lts;
      for (const std::string& t : ts)
      {
        kts.push_back(t == "Term" ? "Id" : t);
        lts.push_back(t);
      }
      std::string kty = join(kts, " → ") + " → Option α";
      std::string fsj = join(fs, " ");
      std::string P = "m_" + c;
      o << "@[inline] def Store." << P << " {α : Type} (σ : Store) (x : Id) (k : " << kty
        << ") : Option α :=\n  match σ.view x with\n  | ." << c << " " << fsj << " => k " << fsj
        << "\n  | _ => none\n\n";
      o << "theorem " << P << "_some {α : Type} {x : Id} {k : " << kty << "} {r : α}\n"
        << "    (h : σ." << P << " x k = some r) : ∃ " << fsj << ", σ.view x = ." << c << " "
        << fsj << " ∧ k " << fsj << " = some r := by\n"
        << "  unfold Store." << P << " at h; split at h\n"
        << "  · rename_i " << fsj << " hv; exact ⟨" << join(fs, ", ") << ", hv, h⟩\n"
        << "  · simp at h\n\n";
      o << "theorem " << P << "_of_view {α : Type} {x : Id}";
      for (size_t i = 0; i < ts.size(); i++)
      {
        o << " {" << fs[i] << " : " << kts[i] << "}";
      }
      o << " {k : " << kty << "}\n    (hv : σ.view x = ." << c << " " << fsj << ") : σ." << P
        << " x k = k " << fsj << " := by\n  simp [Store." << P << ", hv]\n\n";
      // inversion: fields of type Term are ids reading as the Logos fields
      std::vector<std::string> Fs = fieldNames(ts, "F");
      std::vector<std::string> ids, viewArgs, decs, eNames;
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          ids.push_back(fs[i]);
          viewArgs.push_back(fs[i]);
          decs.push_back("σ.decode " + fs[i] + " = " + Fs[i]);
        }
        else
        {
          viewArgs.push_back(Fs[i]);
        }
        eNames.push_back("e" + std::to_string(i + 1));
      }
      o << "theorem decode_" << c << "_inv (hI : Inv sem σ) {x : Id}";
      for (size_t i = 0; i < ts.size(); i++)
      {
        o << " {" << Fs[i] << " : " << lts[i] << "}";
      }
      o << "\n    (h : σ.decode x = ." << c << " " << join(Fs, " ") << ") :\n    ";
      if (!ids.empty())
      {
        o << "∃ " << join(ids, " ") << ", ";
      }
      o << "σ.view x = ." << c << " " << join(viewArgs, " ");
      for (const std::string& d : decs)
      {
        o << " ∧ " << d;
      }
      o << " := by\n  rw [decode_view' hI x] at h\n"
        << "  cases hv : σ.view x <;> simp only [hv, Node.toTerm, reduceCtorEq, Term." << c
        << ".injEq] at h\n  rename_i " << fsj << "\n";
      if (ts.size() == 1)
      {
        o << "  have " << eNames[0] << " := h\n";
      }
      else
      {
        o << "  obtain ⟨" << join(eNames, ", ") << "⟩ := h\n";
      }
      std::vector<std::string> wit;
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] != "Term")
        {
          o << "  subst " << eNames[i] << "\n";
        }
      }
      std::vector<std::string> parts;
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          parts.push_back(fs[i]);
        }
      }
      parts.push_back("rfl");
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          parts.push_back(eNames[i]);
        }
      }
      if (parts.size() == 1)
      {
        o << "  exact rfl\n\n";
      }
      else
      {
        o << "  exact ⟨" << join(parts, ", ") << "⟩\n\n";
      }
      // intern
      if (!ids.empty())
      {
        o << "theorem intern_" << c << " (hI : Inv sem σ) (hΓ : Ctx σ Γ)";
        std::vector<std::string> mems, vals, decsR, args, targs;
        for (size_t i = 0; i < ts.size(); i++)
        {
          o << " {" << fs[i] << " : " << kts[i] << "}";
          if (ts[i] == "Term")
          {
            o << " {" << Fs[i] << " : Term}";
          }
        }
        for (size_t i = 0; i < ts.size(); i++)
        {
          if (ts[i] == "Term")
          {
            o << "\n    (p" << i + 1 << " : Fact.term " << fs[i] << " " << Fs[i] << " ∈ Γ)";
            vals.push_back("hΓ.valid p" + std::to_string(i + 1));
            decsR.push_back("hΓ.dec p" + std::to_string(i + 1));
            targs.push_back(Fs[i]);
          }
          else
          {
            targs.push_back(fs[i]);
          }
        }
        o << " :\n    Sim sem σ (intern (." << c << " " << fsj << ")) (." << c << " "
          << join(targs, " ") << ") :=\n  (intern_sim hI (by simp [Node.children, "
          << join(vals, ", ") << "])).congr\n    (by simp [Node.toTerm, " << join(decsR, ", ")
          << "])\n\n";
      }
    }
    o << "end Kairos\n";
    std::ofstream(getOutputPath("kairos/Kairos/Gen/Prims.lean")) << o.str();
  }
  // --- Gen/Intern.lean: interning a Logos term ---
  {
    std::stringstream o;
    o << hdr << "import Kairos.Runtime.Prog\n\nset_option linter.unusedVariables false\n\n"
      << "namespace Kairos\nopen Eo Store SmtEval\n\nvariable {sem : Sem} {σ : Store}\n\n"
      << "/-- Intern a Logos term, bottom up. -/\ndef internTerm : Term → K Id\n";
    std::stringstream prf;
    prf << "theorem internTerm_sim : (t : Term) → ∀ {σ : Store}, Inv sem σ →\n"
        << "    Sim sem σ (internTerm t) t\n";
    for (const auto& [c, ts] : d_termCons)
    {
      std::vector<std::string> fs = fieldNames(ts, "f");
      std::string pat = "." + c + (fs.empty() ? "" : " " + join(fs, " "));
      if (c == "Stuck")
      {
        o << "  | " << pat << " => pure 0\n";
        prf << "  | " << pat << ", σ, hI => by simp only [internTerm]; exact Sim.stuck hI\n";
        continue;
      }
      std::vector<std::string> ids;
      std::vector<std::string> nargs;
      for (size_t i = 0; i < ts.size(); i++)
      {
        nargs.push_back(ts[i] == "Term" ? "i" + std::to_string(i + 1) : fs[i]);
        if (ts[i] == "Term")
        {
          ids.push_back(fs[i]);
        }
      }
      if (ids.empty())
      {
        o << "  | " << pat << " => intern (." << c << (fs.empty() ? "" : " " + join(fs, " "))
          << ")\n";
        prf << "  | " << pat << ", σ, hI => by simp only [internTerm]; exact intern_leaf hI rfl\n";
        continue;
      }
      o << "  | " << pat << " => do\n";
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          o << "    let i" << i + 1 << " ← internTerm " << fs[i] << "\n";
        }
      }
      o << "    intern (." << c << " " << join(nargs, " ") << ")\n";
      prf << "  | " << pat << ", σ, hI => by\n    simp only [internTerm]\n";
      std::string hG = "(Ctx.nil σ)";
      std::string hIc = "hI";
      size_t k = 0;
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          k++;
          prf << "    refine Sim.step " << hG << " (internTerm_sim " << fs[i] << " " << hIc
              << ") fun i" << i + 1 << " σ" << k << " hI" << k << " hΓ" << k << " => ?_\n";
          hG = "hΓ" + std::to_string(k);
          hIc = "hI" + std::to_string(k);
        }
      }
      // the ids, newest first in Γ
      std::vector<std::string> mems;
      size_t pos = ids.size();
      for (size_t i = 0; i < ts.size(); i++)
      {
        if (ts[i] == "Term")
        {
          pos--;
          std::string m;
          for (size_t j = 0; j < pos; j++)
          {
            m += "(.tail _ ";
          }
          m += "(.head _)";
          for (size_t j = 0; j < pos; j++)
          {
            m += ")";
          }
          mems.push_back(m);
        }
      }
      prf << "    exact intern_" << c << " " << hIc << " " << hG << " " << join(mems, " ") << "\n";
    }
    o << "\n" << prf.str() << "\n"
      << "/-- A program computed by Logos on decoded arguments. -/\n"
      << "theorem Sim.lift {t : Term} (hI : Inv sem σ) : Sim sem σ (internTerm t) t :=\n"
      << "  internTerm_sim t hI\n\nend Kairos\n";
    std::ofstream(getOutputPath("kairos/Kairos/Gen/Intern.lean")) << o.str();
  }
}

void KairosMetaReduce::finalize()
{
  for (const auto& [cname, types] : d_termCons)
  {
    CtorInfo ci;
    ci.prim = "m_" + cname;
    ci.inv = "decode_" + cname + "_inv";
    bool anyId = false;
    for (const std::string& t : types)
    {
      ci.fields.push_back(t == "Term" ? "I" : "N:" + t);
      anyId |= (t == "Term");
    }
    ci.internLemma = anyId ? "intern_" + cname : "";
    ctorTableRef()[cname] = ci;
  }
  emitTermModules();
  // collect the programs Logos defines in its signature module
  for (const Expr& v : d_progOrder)
  {
    std::string ename = getName(v);
    if (ename == "$eo_ite" || ename == "$eo_hash" || ename.compare(0, 9, "$eo_model") == 0
        || ename.compare(0, 10, "$eo_to_smt") == 0 || ename.compare(0, 5, "$smtx") == 0)
    {
      continue;
    }
    if (d_progs.find(ename) != d_progs.end())
    {
      continue;
    }
    Prog p;
    p.v = v;
    p.def = d_progDef[v];
    p.ename = ename;
    p.lname = cleanId(ename);
    p.isDefine = d_isDefine.count(v) > 0;
    d_names.push_back(ename);
    d_progs[ename] = p;
  }
  for (const std::string& n : d_names)
  {
    analyze(d_progs[n]);
    if (n == "$eo_cmd_step_proven" || n == "$eo_cmd_step_pop_proven")
    {
      Prog& p = d_progs[n];
      p.dispatch = true;
      p.supported = true;
      p.why.clear();
    }
  }
  // programs over native values only are Logos's own functions to Kairos
  for (const std::string& n : d_names)
  {
    Prog& p = d_progs[n];
    bool allNative = p.ret.sort == Sort::NATIVE;
    for (const ArgInfo& a : p.args)
    {
      allNative &= (a.sort == Sort::NATIVE);
    }
    if (allNative && p.why.empty())
    {
      p.pure = true;
    }
  }
  // a program whose types are supported but whose body is not can be
  // lifted: Logos computes it on decoded arguments
  auto liftable = [&](const Prog& p) {
    if (p.ret.sort != Sort::TERM || !p.why.empty())
    {
      return false;
    }
    for (const ArgInfo& a : p.args)
    {
      if (a.sort == Sort::OTHER)
      {
        return false;
      }
    }
    return true;
  };
  for (const std::string& n : d_names)
  {
    Prog& p = d_progs[n];
    if (p.pure || p.dispatch)
    {
      continue;
    }
    bool typesOk = liftable(p);
    checkSupported(p);
    if (!p.supported && typesOk)
    {
      p.supported = true;
      p.lifted = true;
    }
  }
  // a program calling an unsupported one is lifted, or unsupported
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (const std::string& n : d_names)
    {
      Prog& p = d_progs[n];
      if (!p.supported || p.lifted || p.pure || p.dispatch)
      {
        continue;
      }
      for (const std::string& c : p.callees)
      {
        auto it = d_progs.find(c);
        if (it == d_progs.end() || !it->second.supported)
        {
          std::string why = "calls " + c;
          p.why.clear();
          if (liftable(p))
          {
            p.lifted = true;
          }
          else
          {
            p.supported = false;
          }
          p.why = why;
          changed = true;
          break;
        }
      }
    }
  }
  // recursion, by reachability in the call graph; cache recursive programs
  // over terms only (the cache is keyed by ids)
  size_t pid = 0;
  for (const std::string& n : d_names)
  {
    Prog& p = d_progs[n];
    if (!p.supported)
    {
      continue;
    }
    std::set<std::string> seen;
    std::vector<std::string> todo(p.callees.begin(), p.callees.end());
    while (!todo.empty())
    {
      std::string c = todo.back();
      todo.pop_back();
      if (!seen.insert(c).second)
      {
        continue;
      }
      if (c == n)
      {
        p.recursive = true;
        break;
      }
      for (const std::string& d : d_progs[c].callees)
      {
        todo.push_back(d);
      }
    }
    bool allTerms = !p.args.empty();
    for (const ArgInfo& a : p.args)
    {
      allTerms &= (a.sort == Sort::TERM);
    }
    if (p.recursive && allTerms && !p.lifted)
    {
      p.cached = true;
      p.pid = pid++;
    }
  }

  // the programs emitted to Programs.lean, and their strongly connected
  // components (Tarjan: a component comes after every one it calls)
  std::vector<std::string> emitted;
  for (const std::string& n : d_names)
  {
    const Prog& p = d_progs[n];
    if (p.supported && !p.pure && !p.dispatch)
    {
      emitted.push_back(n);
    }
  }
  std::vector<std::vector<std::string>> sccs;
  {
    std::map<std::string, size_t> index, low;
    std::set<std::string> onStack;
    std::vector<std::string> stack;
    size_t counter = 0;
    std::function<void(const std::string&)> visit = [&](const std::string& v) {
      index[v] = low[v] = counter++;
      stack.push_back(v);
      onStack.insert(v);
      const Prog& pv = d_progs[v];
      if (!pv.lifted)
      {
        for (const std::string& w : pv.callees)
        {
          const Prog& pw = d_progs[w];
          if (!pw.supported || pw.pure || pw.dispatch)
          {
            continue;
          }
          if (index.find(w) == index.end())
          {
            visit(w);
            low[v] = std::min(low[v], low[w]);
          }
          else if (onStack.count(w))
          {
            low[v] = std::min(low[v], index[w]);
          }
        }
      }
      if (low[v] == index[v])
      {
        std::vector<std::string> comp;
        std::string w;
        do
        {
          w = stack.back();
          stack.pop_back();
          onStack.erase(w);
          comp.push_back(w);
        } while (w != v);
        std::reverse(comp.begin(), comp.end());
        sccs.push_back(comp);
      }
    };
    for (const std::string& n : emitted)
    {
      if (index.find(n) == index.end())
      {
        visit(n);
      }
    }
  }
  for (size_t i = 0; i < sccs.size(); i++)
  {
    bool rec = sccs[i].size() > 1;
    for (const std::string& n : sccs[i])
    {
      const Prog& p = d_progs[n];
      rec |= (!p.lifted && p.callees.count(n) > 0);
    }
    for (const std::string& n : sccs[i])
    {
      d_progs[n].scc = i;
      d_progs[n].sccRecursive = rec;
    }
  }

  std::stringstream matchers, sem, skipped, lifted, body;
  size_t npure = 0, nlifted = 0, ndispatch = 0, nsupp = 0, nmutual = 0;
  for (const std::string& n : d_names)
  {
    Prog& p = d_progs[n];
    if (p.pure)
    {
      npure++;
    }
    else if (!p.supported)
    {
      skipped << "  " << p.lname << ": " << p.why << "\n";
    }
    else if (p.lifted)
    {
      lifted << "  " << p.lname << ": " << p.why << "\n";
      nlifted++;
    }
    if (p.supported && !p.pure && !p.dispatch)
    {
      nsupp++;
    }
    if (p.cached)
    {
      sem << "  | " << p.pid << ", [";
      for (size_t i = 0; i < p.args.size(); i++)
      {
        sem << (i ? ", " : "") << "a" << i + 1;
      }
      sem << "] => some (" << p.lname;
      for (size_t i = 0; i < p.args.size(); i++)
      {
        sem << " a" << i + 1;
      }
      sem << ")\n";
    }
  }
  for (size_t ci = 0; ci < sccs.size(); ci++)
  {
    const std::vector<std::string>& comp = sccs[ci];
    bool rec = d_progs[comp[0]].sccRecursive;
    std::stringstream code, specs, calls, steps;
    std::vector<std::string> zeros;
    for (const std::string& n : comp)
    {
      zeros.push_back(emitProgram(d_progs[n], matchers, code, specs, calls, steps));
    }
    body << "/-! ### " << (rec ? "Recursive component " : "") << comp.size()
         << (comp.size() == 1 ? " program" : " programs") << ": "
         << d_progs[comp[0]].lname << (comp.size() > 1 ? ", ..." : "") << " -/\n\n";
    if (rec)
    {
      nmutual++;
      body << "mutual\n\n" << code.str() << "end\n\n";
    }
    else
    {
      body << code.str();
    }
    body << specs.str() << calls.str();
    std::string spec = "Spec" + std::to_string(ci);
    if (rec)
    {
      body << "structure " << spec << " (n : Nat) : Prop where\n";
      for (const std::string& n : comp)
      {
        body << "  s" << d_progs[n].lname << " : S" << d_progs[n].lname << " n\n";
      }
      body << "\n";
    }
    body << steps.str();
    if (rec)
    {
      body << "theorem spec" << ci << " : ∀ n, " << spec << " n\n  | 0 => {\n";
      for (const std::string& z : zeros)
      {
        body << z << "\n";
      }
      body << "    }\n  | n + 1 =>\n    have ih := spec" << ci << " n\n    {\n";
      for (const std::string& n : comp)
      {
        body << "    s" << d_progs[n].lname << " := step" << d_progs[n].lname << " ih\n";
      }
      body << "    }\n\n";
      for (const std::string& n : comp)
      {
        const std::string& l = d_progs[n].lname;
        body << "theorem allS" << l << " (n : Nat) : S" << l << " n := (spec" << ci << " n).s" << l
             << "\n\n";
      }
    }
    else
    {
      const std::string& l = d_progs[comp[0]].lname;
      std::string z = zeros[0];
      z = z.substr(z.find(":= ") + 3);
      body << "theorem allS" << l << " : ∀ n, S" << l << " n\n  | 0 => " << z
           << "\n  | _ + 1 => step" << l << "\n\n";
    }
  }
  std::stringstream dispatch;
  for (const std::string& n : d_names)
  {
    Prog& p = d_progs[n];
    if (p.dispatch)
    {
      std::stringstream dm, dc, ds, dcl, dst;
      emitProgram(p, dm, dc, ds, dcl, dst, &dispatch);
      ndispatch++;
    }
  }

  std::stringstream outText;
  outText << "-- This file is auto-generated by install/install-cpc.sh (kairos-eoc) from the\n"
          << "-- signature of the pinned Logos. Do not edit.\n"
          << "import Kairos.Runtime.Val\n\n"
          << "set_option linter.unusedVariables false\n"
          << "set_option linter.unusedSimpArgs false\n"

          << "set_option maxHeartbeats 0\n"
          << "set_option maxRecDepth 100000\n\n"
          << "namespace Kairos.Gen\nopen Eo Kairos Store SmtEval\n\n"
          << "/-! Generated " << nsupp << " of " << d_names.size() << " programs (" << nlifted
          << " lifted); " << npure << " over native values are Logos's own. Left out:\n"
          << skipped.str() << "\nLifted (Logos computes them on decoded arguments):\n"
          << lifted.str() << "-/\n\n"
          << "/-- Cached programs, by id, with their Logos meaning. -/\n"
          << "def sem : Sem\n" << sem.str() << "  | _, _ => none\n\n"
          << "macro \"kside\" : tactic => `(tactic| all_goals try (kdis; done))\n\n"
          << "/-! ## Matchers -/\n\n" << matchers.str()
          << "/-! ## Programs, by component of the call graph (" << nmutual
          << " recursive) -/\n\n" << body.str() << "end Kairos.Gen\n";
  std::string path = getOutputPath("kairos/Kairos/Gen/Programs.lean");
  {
    // the directory exists once a resource is emitted; emit the manifest
    // first, which creates it
    std::stringstream kinds;
    const char* sep = "  ";
    for (const auto& [k, c] : d_declCount)
    {
      kinds << sep << "(\"" << k << "\", " << c << ")\n";
      sep = ", ";
    }
    emitResourceFile("kairos_meta/templates/Manifest.lean", "kairos/Kairos/Gen/Manifest.lean",
                     {{"$KAIROS_DECL_KINDS$", kinds.str()},
                      {"$KAIROS_PROGRAMS$", "  (\"generated\", " + std::to_string(nsupp)
                                                + ")\n, (\"total\", "
                                                + std::to_string(d_names.size()) + ")\n"}});
  }
  std::ofstream os(path);
  os << outText.str();
  std::ofstream ds(getOutputPath("kairos/Kairos/Gen/Dispatch.lean"));
  ds << "-- This file is auto-generated by install/install-cpc.sh (kairos-eoc) from the\n"
     << "-- signature of the pinned Logos. Do not edit.\n"
     << "-- The rule dispatch: " << ndispatch << " programs.\n"
     << "import Kairos.Checker.Base\n\n"
     << "set_option linter.unusedVariables false\n\n"
     << "namespace Kairos.Checker\nopen Eo Kairos Store SmtEval Kairos.Gen\n\n"
     << dispatch.str() << "end Kairos.Checker\n";
}

}  // namespace ethos
