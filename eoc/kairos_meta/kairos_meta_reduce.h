/*
 * KairosMetaReduce: the Kairos code-generation stage.
 *
 * It runs on the same final signature (lean-<calc>-final.eo) that Ethos's
 * lean-meta stage compiles into Logos. For each program Logos defines, it
 * emits a Kairos program over hash-consed ids together with its proof of
 * simulation: matchers with their lemmas, the program, its spec, and a step
 * lemma proving the spec at fuel n+1 from the spec at fuel n. See
 * Kairos/Proto/Golden.lean for the format, written by hand.
 *
 * The case layout of every program (macro arguments, stuck guards, the
 * default case) follows LeanMetaReduce::finalizeProgram exactly, since the
 * proofs rewrite with Lean's equation lemmas `f.eq_k` of Logos's definitions,
 * which are numbered by that layout.
 *
 * Programs using a construct not supported yet are left out, together with
 * every program that calls them; the generated file lists them.
 */
#ifndef KAIROS_META_REDUCE_H
#define KAIROS_META_REDUCE_H

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "meta_reduce_plugin.h"

namespace ethos {

class KairosMetaReduce : public MetaReducePlugin
{
 public:
  KairosMetaReduce(State& s);
  ~KairosMetaReduce() override;
  void defineProgram(const Expr& v, const Expr& prog) override;
  void define(const std::string& name, const Expr& e) override;
  bool echo(const std::string& msg) override;
  void finalize() override;

  /** Whether an argument or result is a term (an id in Kairos), a native
   * value (the same Lean value on both sides), or something unsupported. */
  enum class Sort
  {
    TERM,
    /** A Logos `Proof`; in Kairos, the id of its formula. */
    PROOF,
    NATIVE,
    /** A checker state (KState) or argument list (KArgList). */
    STATE,
    ARGS,
    OTHER
  };
  struct ArgInfo
  {
    Sort sort = Sort::OTHER;
    /** The Lean type: "Id" for terms, the native type otherwise. */
    std::string kType;
    /** The Logos type: "Term" for terms, the native type otherwise. */
    std::string lType;
  };
  /** An alternative of the Lean match Logos prints, numbered as `eq_k`. */
  struct Alt
  {
    enum Kind
    {
      GUARD,
      CASE,
      DEFAULT
    } kind;
    /** For GUARD: the argument (1-based) checked for Stuck. */
    size_t arg = 0;
    /** For CASE: the case index in the program. */
    size_t ci = 0;
  };
  struct Prog
  {
    Expr v;
    Expr def;
    std::string ename;
    std::string lname;
    bool isDefine = false;
    /** Logos prints a plain definition (no match), see macroStart. */
    bool plainDef = false;
    std::vector<ArgInfo> args;
    ArgInfo ret;
    size_t macroStart = 1;
    std::vector<Alt> alts;
    bool supported = true;
    std::string why;
    std::set<std::string> callees;
    bool recursive = false;
    bool cached = false;
    size_t pid = 0;
    /** Over native values only: Kairos calls Logos's function. */
    bool pure = false;
    /** Not compiled yet: Kairos runs Logos's function on decoded arguments. */
    bool lifted = false;
    /** The rule dispatch: emitted to Kairos/Gen/Dispatch.lean. */
    bool dispatch = false;
  };

 protected:
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  void finalizeDecl(const Expr& e) override;

 private:
  void analyze(Prog& p);
  void checkSupported(Prog& p);
  bool checkPattern(const Expr& e, Prog& p);
  bool checkBody(const Expr& e, Sort expect, Prog& p);
  ArgInfo argInfo(const Expr& t);
  std::string emitProgram(Prog& p,
                          std::ostream& matchers,
                          std::ostream& code,
                          std::ostream& specs,
                          std::ostream& calls,
                          std::ostream& steps,
                          std::ostream* dispatchOut = nullptr);

  /** Programs in the order they were defined. */
  std::vector<Expr> d_progOrder;
  std::map<Expr, Expr> d_progDef;
  std::set<Expr> d_isDefine;
  std::map<std::string, Prog> d_progs;
  std::vector<std::string> d_names;
  /** Declarations seen, for the manifest. */
  std::map<std::string, size_t> d_declCount;
};

}  // namespace ethos

#endif
