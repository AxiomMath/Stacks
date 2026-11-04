module

public import StacksFrontier.RingTheory.Depth.Defs
public import StacksFrontier.RingTheory.Depth.Nakayama

/-!
# The unqualified depth of a module over a local ring

`moduleDepth R M` is defined by cases, as the `𝔪`-depth of `M` when `𝔪 • M ≠ M` and `⊤`
otherwise. For a nonzero finite module over a local ring Nakayama's lemma rules out the second
branch, so the two agree. For `M = R` the second branch is excluded outright, since `𝔪 • R = 𝔪`
is a proper ideal, and no finiteness or nontriviality hypothesis is needed.

## Main results

* `moduleDepth_eq_depth`: for a nonzero finite module over a local ring, the unqualified depth is
  the depth relative to the maximal ideal.
* `ringDepth_eq_depth_maximalIdeal`: for a local ring, the depth of the ring is the depth of the
  ring as a module over itself relative to its maximal ideal.

## Implementation notes

`moduleDepth_eq_depth` was proved twice, in `StacksFrontier/Algebra/Module/Reflexive.lean` and
privately in `StacksFrontier/RingTheory/Dualizing/CanonicalModuleDepth.lean`, neither of which the
other imports. `ringDepth_eq_depth_maximalIdeal` was proved privately three times more, in
`StacksFrontier/RingTheory/Henselian/PermanenceOfProperties.lean`,
`StacksFrontier/RingTheory/LocalCohomology/CutoffCompletionSerre.lean` and
`StacksFrontier/RingTheory/Serre/CohenMacaulay.lean` and, under the name
`ringDepth_eq_depth_maximalIdeal_self`, in
`StacksFrontier/RingTheory/Etale/LocalRingPropertyList.lean`, and publicly in
`StacksFrontier/RingTheory/LocalCohomology/HartshorneConnectednessHenselian.lean`, which is
downstream of the first of those, so none of them could reach it. Both live here instead, beside
the Nakayama lemma and the definition of `moduleDepth` that are their whole content, in a module
importing nothing else -- so the merge costs each consumer a single module in its closure.
-/

@[expose] public section

/-- **For a nonzero finite module over a local ring the unqualified depth is the depth relative
to the maximal ideal.** Nakayama's lemma excludes the `⊤` branch of `moduleDepth`. -/
public lemma moduleDepth_eq_depth {R X : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup X] [Module R X] [Module.Finite R X] [Nontrivial X] :
    moduleDepth R X = Module.depth R (IsLocalRing.maximalIdeal R) X := by
  simp only [moduleDepth, Module.depth, ite_eq_right (Module.maximalIdeal_smul_top_ne_top _)]
  rfl

/-- For a local ring, the depth of the ring agrees with the depth of the ring as a module over
itself relative to its maximal ideal: the exceptional branch `𝔪 • A = A` of `Module.depth` is
never taken, since `𝔪 • A = 𝔪`. -/
public theorem ringDepth_eq_depth_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    ringDepth R = Module.depth R (IsLocalRing.maximalIdeal R) R := by
  have hmax : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  unfold ringDepth moduleDepth Module.depth
  split
  · contradiction
  · rfl

end
