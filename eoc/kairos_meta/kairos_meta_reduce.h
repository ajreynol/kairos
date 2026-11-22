/*
 * KairosMetaReduce: the Kairos code-generation stage.
 *
 * It runs on the same final signature (lean-<calc>-final.eo) that Ethos's
 * lean-meta stage compiles into Logos, and emits Kairos's generated Lean
 * (Kairos/Gen/). Milestone 1 stub: it classifies the declarations exactly as
 * the meta-reduction backends do and emits a manifest of them, which proves
 * the pipeline end to end. The fork of lean_meta_reduce.cpp (see FORK_BASE)
 * replaces this in milestone 2.
 */
#ifndef KAIROS_META_REDUCE_H
#define KAIROS_META_REDUCE_H

#include <map>
#include <set>
#include <string>

#include "meta_reduce_plugin.h"

namespace ethos {

class KairosMetaReduce : public MetaReducePlugin
{
 public:
  KairosMetaReduce(State& s);
  ~KairosMetaReduce() override;
  void defineProgram(const Expr& v, const Expr& prog) override;
  bool echo(const std::string& msg) override;
  void finalize() override;

 protected:
  bool isBuiltinMetaSymbol(const std::string& sname) const override;
  void finalizeDecl(const Expr& e) override;

 private:
  /** Declared symbols by meta-kind name, ordered for deterministic output. */
  std::map<std::string, std::set<std::string>> d_declsByKind;
  /** Programs defined (by name) with their number of cases. */
  std::map<std::string, size_t> d_programs;
};

}  // namespace ethos

#endif
