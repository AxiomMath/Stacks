module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Filtration

/-!
# Concatenating bounded dévissage filtrations

The Noetherian induction of [Stacks, Tag 01YF] takes a coherent module apart along short exact
sequences and reassembles the pieces. Against the inductive predicate
`Stacks.AlgebraicGeometry.DevissageBounded.IsIdealDevissable` the reassembly is the constructor
`IsIdealDevissable.ext`; against the *filtration* predicate
`Stacks.AlgebraicGeometry.DevissageBounded.HasDevissageWith`, which is what the irreducible step
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage` is phrased with, it is a
genuine obligation, named as such in the implementation notes of
`StacksFrontier/AlgebraicGeometry/DevissageNoetherian/Basic.lean`: "the source's phrase
*splicing them yields one for `F`* is a genuine obligation — preimages of subobjects along the
epimorphism, and a comparison of cokernels".

This file discharges it. Nothing here is about schemes: it is the statement, in the abelian
category of sheaves of modules, that a filtration of a submodule and a filtration of the
quotient concatenate to a filtration of the module.

## Main results

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.cokernelToPreimageOfSubIso`: for a
  monomorphism `ι : A ⟶ F` and a subobject `m : D ⟶ F / A`, the preimage of `D` in `F` has
  quotient `D` by `A`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.cokernelPullbackSndIso`: the quotient of `F` by
  that preimage is the quotient of `F / A` by `D`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_trans'`: **two filtrations
  spliced.** If `A` carries a bounded dévissage filtration with quotients in `Q` and so does
  `cokernel ι`, then so does `F`.

## Implementation notes

**The preimage is the pullback.** `pullback m (cokernel.π ι)` is the preimage of `D` in `F`; its
second projection is the inclusion into `F`, mono because `m` is, and its first projection is
the surjection onto `D`, epi because `cokernel.π ι` is — the latter by
`CategoryTheory.Abelian.epi_pullback_of_epi_g`, which holds in an abelian category and not in a
general category with pullbacks.

The two cokernel identifications are proved as universal properties rather than by diagram
chase. `A` is exhibited as a *kernel* of the first projection, directly from the pullback's
universal property together with `CategoryTheory.Abelian.monoLift`, and the first projection is
then a cokernel of `A` by `CategoryTheory.Abelian.epiIsCokernelOfKernel` — an epimorphism in an
abelian category is the cokernel of its kernel. For the other identification, `cokernel.π ι ≫
cokernel.π m` is shown to be a cokernel of the inclusion of the preimage outright: a map out of
`F` killing the preimage kills `A`, hence factors through `F / A`, and the factorisation kills
`D` because the first projection is epi.

**The splice is an induction on the length of the second filtration, not a concatenation of
index families.** Peeling the top step of the filtration of `cokernel ι` gives a subobject
`D ⟶ cokernel ι` whose own filtration is one shorter; its preimage `E` sits between `A` and `F`
with `E / A ≅ D` and `F / E` the top quotient, so the induction hypothesis applies to
`A ⟶ E` and one application of
`Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_snoc` finishes. Concatenating
the two `ℕ`-indexed families directly would have required a second piecewise construction on top
of the one `hasDevissageWith_snoc` already pays for.

At length zero the quotient is a zero module, so `ι` is epi as well as mono, hence an
isomorphism — `CategoryTheory.isIso_of_mono_of_epi`, again abelian-specific — and the
filtration of `A` transports.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Preimage

variable {A F D : X.Modules} (ι : A ⟶ F) (m : D ⟶ cokernel ι)

/-- The canonical map from `A` into the preimage in `F` of a subobject `m : D ⟶ F / A`. -/
def toPreimageOfSub : A ⟶ pullback m (cokernel.π ι) :=
  pullback.lift 0 ι (by simp)

/-- The composite of `toPreimageOfSub ι m` with the projection to `D` is zero. -/
@[reassoc (attr := simp)]
theorem toPreimageOfSub_fst :
    toPreimageOfSub ι m ≫ pullback.fst m (cokernel.π ι) = 0 :=
  pullback.lift_fst _ _ _

/-- The composite of `toPreimageOfSub ι m` with the projection to `F` is `ι`. -/
@[reassoc (attr := simp)]
theorem toPreimageOfSub_snd :
    toPreimageOfSub ι m ≫ pullback.snd m (cokernel.π ι) = ι :=
  pullback.lift_snd _ _ _

/-- If `ι` is a monomorphism, then so is `toPreimageOfSub ι m`. -/
instance mono_toPreimageOfSub [Mono ι] : Mono (toPreimageOfSub ι m) :=
  mono_of_mono_fac (toPreimageOfSub_snd ι m)

/-- `A` is the kernel of the projection of the preimage onto `D`. -/
def isLimitKernelForkPreimage [Mono ι] :
    IsLimit (KernelFork.ofι (toPreimageOfSub ι m) (toPreimageOfSub_fst ι m)) :=
  KernelFork.IsLimit.ofι' _ _ fun {W} k hk => by
    refine ⟨Abelian.monoLift ι (k ≫ pullback.snd m (cokernel.π ι)) ?_, ?_⟩
    · rw [Category.assoc, pullback.condition.symm, ← Category.assoc, hk, zero_comp]
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, toPreimageOfSub_fst, comp_zero, hk]
      · rw [Category.assoc, toPreimageOfSub_snd, Abelian.monoLift_comp]

/-- The quotient of the preimage by `A` is `D`. -/
def cokernelToPreimageOfSubIso [Mono ι] : cokernel (toPreimageOfSub ι m) ≅ D :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (isLimitKernelForkPreimage ι m))

/-- The quotient of `F` by the preimage is the quotient of `F / A` by `D`. -/
def isColimitCokernelCoforkPreimage [Mono ι] [Mono m] :
    IsColimit (CokernelCofork.ofπ (f := pullback.snd m (cokernel.π ι))
      (cokernel.π ι ≫ cokernel.π m) (by
        rw [← Category.assoc, ← pullback.condition, Category.assoc, cokernel.condition,
          comp_zero])) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {W} k hk => by
    have hιk : ι ≫ k = 0 := by
      rw [← toPreimageOfSub_snd ι m, Category.assoc, hk, comp_zero]
    refine ⟨cokernel.desc m (cokernel.desc ι k hιk) ?_, ?_⟩
    · rw [← cancel_epi (pullback.fst m (cokernel.π ι)), ← Category.assoc, pullback.condition,
        Category.assoc, cokernel.π_desc, hk, comp_zero]
    · rw [Category.assoc, cokernel.π_desc, cokernel.π_desc]

/-- The quotient of `F` by the preimage is the quotient of `F / A` by `D`. -/
def cokernelPullbackSndIso [Mono ι] [Mono m] :
    cokernel (pullback.snd m (cokernel.π ι)) ≅ cokernel m :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (isColimitCokernelCoforkPreimage ι m)

end Preimage

/-! ### Concatenation -/

/-- **Two filtrations spliced**, by induction on the length `q` of the filtration of the
quotient. The filtration data for `cokernel ι` is taken apart into its components so that the
induction can be run on `q`; `hasDevissageWith_trans'` is the usable form. -/
theorem hasDevissageWith_trans {Q : X.Modules → Prop}
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N) :
    ∀ (q : ℕ) {A F : X.Modules} (ι : A ⟶ F), Mono ι → F.IsCoherent →
      HasDevissageWith Q A →
      ∀ (K : ℕ → X.Modules) (f : ∀ i, K i ⟶ K (i + 1)), (∀ i, i < q → Mono (f i)) →
        IsZero (K 0) → (∀ i, i ≤ q → (K i).IsCoherent) →
        (∀ i, i < q → (cokernel (f i)).IsCoherent) → (K q ≅ cokernel ι) →
        (∀ i, i < q → Q (cokernel (f i))) → HasDevissageWith Q F := by
  intro q
  induction q with
  | zero =>
    intro A F ι hm hFc hA K _ _ hzero _ _ e _
    have hzc : IsZero (cokernel ι) := hzero.of_iso e.symm
    have := hm
    have hepi : Epi ι := by
      rw [Preadditive.epi_iff_cancel_zero]
      intro W g hg
      rw [← cokernel.π_desc ι g hg, hzc.eq_zero_of_src (cokernel.desc ι g hg), comp_zero]
    have : IsIso ι := isIso_of_mono_of_epi ι
    exact hasDevissageWith_of_iso (asIso ι) hA
  | succ q IH =>
    intro A F ι hm hFc hA K f hmono hzero hcoh hcoker e hq
    have := hm
    -- the top step of the filtration of `F / A`, as a subobject of `F / A`
    have hmq : Mono (f q) := hmono q (by omega)
    have hmm : Mono (f q ≫ e.hom) := mono_comp _ _
    -- the quotient of `F` by the preimage of `K q` is the top quotient
    have hiso : cokernel (pullback.snd (f q ≫ e.hom) (cokernel.π ι)) ≅ cokernel (f q) :=
      (cokernelPullbackSndIso ι (f q ≫ e.hom)).trans (cokernelCompIsIso (f q) e.hom)
    have hjmono : Mono (pullback.snd (f q ≫ e.hom) (cokernel.π ι)) := inferInstance
    have hQj := hQ hiso.symm (hq q (by omega))
    have hcj := isCoherent_of_iso' hiso (hcoker q (by omega))
    -- the preimage is coherent, being the sub of a short exact sequence with coherent ends
    have hEc : (pullback (f q ≫ e.hom) (cokernel.π ι)).IsCoherent :=
      AlgebraicGeometry.CoherentAbelian.isCoherent_X₁_of_shortExact
        (S := ShortComplex.mk (pullback.snd (f q ≫ e.hom) (cokernel.π ι))
          (cokernel.π _) (cokernel.condition _))
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
          mono_f := hjmono
          epi_g := inferInstanceAs
            (Epi (cokernel.π (pullback.snd (f q ≫ e.hom) (cokernel.π ι)))) } hFc hcj
    refine hasDevissageWith_snoc hQ (pullback.snd (f q ≫ e.hom) (cokernel.π ι)) hFc hcj hQj ?_
    exact IH (toPreimageOfSub ι (f q ≫ e.hom)) inferInstance hEc hA K f
      (fun i hi => hmono i (by omega)) hzero (fun i hi => hcoh i (by omega))
      (fun i hi => hcoker i (by omega))
      (cokernelToPreimageOfSubIso ι (f q ≫ e.hom)).symm (fun i hi => hq i (by omega))

/-- **Two filtrations spliced.** If a coherent `F` has a monomorphic submodule `A` such that
both `A` and `F / A` carry bounded dévissage filtrations with quotients in `Q`, then so does
`F`. The class `Q` is required only to be invariant under isomorphism. -/
theorem hasDevissageWith_trans' {Q : X.Modules → Prop}
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    {A F : X.Modules} (ι : A ⟶ F) [Mono ι] (hFc : F.IsCoherent)
    (hA : HasDevissageWith Q A) (hC : HasDevissageWith Q (cokernel ι)) :
    HasDevissageWith Q F := by
  obtain ⟨q, K, f, hmono, hzero, hcoh, hcoker, ⟨e⟩, hq⟩ := hC
  exact hasDevissageWith_trans hQ q ι ‹_› hFc hA K f hmono hzero hcoh hcoker e hq

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
