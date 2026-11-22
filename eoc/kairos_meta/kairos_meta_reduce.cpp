#include "kairos_meta/kairos_meta_reduce.h"

#include <sstream>
#include <vector>

#include "state.h"
#include "utils.h"

namespace ethos {

namespace {

/** A Lean string literal for s. */
std::string leanString(const std::string& s)
{
  std::stringstream ss;
  ss << '"';
  for (char c : s)
  {
    if (c == '"' || c == '\\')
    {
      ss << '\\';
    }
    ss << c;
  }
  ss << '"';
  return ss.str();
}

}  // namespace

KairosMetaReduce::KairosMetaReduce(State& s) : MetaReducePlugin(s) {}

KairosMetaReduce::~KairosMetaReduce() {}

bool KairosMetaReduce::isBuiltinMetaSymbol(const std::string& sname) const
{
  return false;
}

void KairosMetaReduce::finalizeDecl(const Expr& e)
{
  if (!beginFinalizeDecl(e))
  {
    return;
  }
  std::string cname;
  MetaKind k = getMetaKindFor(e, cname);
  d_declsByKind[metaKindToString(k)].insert(getName(e));
}

void KairosMetaReduce::defineProgram(const Expr& v, const Expr& prog)
{
  // A program is a list of (pattern, body) cases.
  d_programs[getName(v)] = prog.getNumChildren();
}

bool KairosMetaReduce::echo(const std::string& msg)
{
  // The final signature carries metadata for the Lean backend as echoes
  // (lean-meta, lean-parser-op, lean-parser-rule). They are addressed to the
  // stage, not to the user. The stub drops them; the fork will read them.
  return msg.compare(0, 5, "lean-") != 0;
}

void KairosMetaReduce::finalize()
{
  std::stringstream kinds;
  const char* sep = "  ";
  for (const auto& [kind, names] : d_declsByKind)
  {
    kinds << sep << "(" << leanString(kind) << ", " << names.size() << ")\n";
    sep = ", ";
  }
  std::stringstream progs;
  sep = "  ";
  for (const auto& [name, ncases] : d_programs)
  {
    progs << sep << "(" << leanString(name) << ", " << ncases << ")\n";
    sep = ", ";
  }
  emitResourceFile("kairos_meta/templates/Manifest.lean",
                   "kairos/Kairos/Gen/Manifest.lean",
                   {{"$KAIROS_DECL_KINDS$", kinds.str()},
                    {"$KAIROS_PROGRAMS$", progs.str()}});
}

}  // namespace ethos
