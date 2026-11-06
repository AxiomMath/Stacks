module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineReflexivePowerTilde
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SequentialModuleColimit
public import StacksFrontier.AlgebraicGeometry.Modules.TildeReflexiveRank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre

/-!
# The colimit clause of [Stacks, Tag 0EBN] on global sections of an affine scheme

Let `A` be a Noetherian normal domain, `M` a finite reflexive `A`-module and `s ∈ M`, and let
`U ⊆ Spec A` be the open locus of [Stacks, Tag 0EBN] for the sheaf `M^~`.  The colimit clause of
that tag says `j_*𝒪_U = colim (M^~)^{[n]}`, and its proof checks the assertion on the sections
over each affine open.  **`⊤` is one of those affine opens**, so the proof gives, with no
further work,

`Γ(U, 𝒪_U) = colim_n Γ(Spec A, (M^~)^{[n]})`

as a colimit of `A`-modules.  That is what this file records.  It is the half of the second
display of [Stacks, Tag 0EBQ] that is about the colimit; the identification of the terms
`Γ(Spec A, (M^~)^{[n]})` with the module-level reflexive powers `M^{[n]}` is
`AlgebraicGeometry.reflexivePowerTildeIso` together with the `tilde`-global sections adjunction.

## Main definitions

* `AlgebraicGeometry.gammaReflexivePowerCocone`: the cocone of `A`-modules obtained by applying
  `AlgebraicGeometry.moduleSpecΓFunctor` to the cocone of [Stacks, Tag 0EBN].

## Main results

* `AlgebraicGeometry.isNormal_spec`: `Spec` of a normal domain is a normal scheme, at the
  `CommRingCat` spelling, so that it can serve as an instance here.
* `AlgebraicGeometry.isColimitGammaReflexivePowerCocone`: **that cocone is a colimit.**

## Implementation notes

**Why no new mathematics is needed.**  The two conditions of the colimit criterion are exactly
`Stacks.AlgebraicGeometry.ReflexivePowers.exists_leg_app_eq_of_isAffineOpen'` and
`…exists_map_app_eq_zero_of_cocone_ι_app_eq_zero`, both already proved for an *arbitrary* affine
open; taking that open to be `⊤` and feeding the two conditions to the `ℕ`-indexed colimit
criterion for modules, `AlgebraicGeometry.isColimitOfJointlySurjectiveOfKer`, is the whole
argument.  The module-level criterion is needed because
`Stacks.AlgebraicGeometry.ReflexivePowers.nonempty_isColimit_reflexivePowerSystemPushforwardCocone`
is a statement about sheaves, and global sections do not preserve colimits of sheaves in
general — it is only because the colimit here is *checked* on sections over affine opens that
the sections over `⊤` form a colimit at all.

**The instances on `Spec A`.** `IsIntegral` and `IsLocallyNoetherian` are found by instance
search from `[IsDomain A]` and `[IsNoetherianRing A]`; normality is not, because the library's
lemma is stated for `Spec (CommRingCat.of A)` with `A` a type, which does not unify with
`Spec R` for `R : CommRingCat`.  `isNormal_spec` is that lemma at the spelling instance search
can use, and it is made a local instance here rather than a global one.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexivePowers

universe u

namespace AlgebraicGeometry

/-- `Spec` of a normal domain is a normal scheme, written for `R : CommRingCat` so that
instance search can use it. -/
theorem isNormal_spec (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] :
    IsNormal (Spec R) :=
  AlgebraicGeometry.isNormal_spec_of_isIntegrallyClosed (R : Type u)

attribute [local instance] isNormal_spec
attribute [local instance] AlgebraicGeometry.tilde_isCoherent_of_finite

variable {R : CommRingCat.{u}} [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
  (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]

/-- The cocone of [Stacks, Tag 0EBN] read on the global sections of `Spec R`: a cocone of
`R`-modules with vertex `Γ(U, 𝒪_U)` and `n`-th leg the sections of the `n`-th reflexive power. -/
def gammaReflexivePowerCocone (σ : (tilde M).sections)
    [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen (Spec R) (tilde M) σ).toScheme] :
    Cocone (reflexivePowerSystem (tilde M) σ ⋙ moduleSpecΓFunctor) :=
  moduleSpecΓFunctor.mapCocone (reflexivePowerSystemPushforwardCocone (tilde M) σ)

set_option backward.isDefEq.respectTransparency false in
/-- **The colimit clause of [Stacks, Tag 0EBN] on the global sections of `Spec R`.**
`Γ(U, 𝒪_U)` is the colimit of the sections of the reflexive powers.  The legs are jointly
surjective and have the required kernels because `⊤` is an affine open of `Spec R`, which is
precisely the hypothesis under which the two conditions were proved. -/
def isColimitGammaReflexivePowerCocone (σ : (tilde M).sections)
    [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen (Spec R) (tilde M) σ).toScheme] :
    IsColimit (gammaReflexivePowerCocone M σ) := by
  have hF : IsReflexive (tilde M) := isReflexive_tilde M
  have hgU : genericPoint (Spec R) ∈
      AlgebraicGeometry.sectionIsomorphismOpen (Spec R) (tilde M) σ :=
    genericPoint_mem_sectionIsomorphismOpen (X := Spec R) (F := tilde M) (s := σ)
  refine isColimitOfJointlySurjectiveOfKer _ (fun w => ?_) (fun n u h => ?_)
  · exact exists_leg_app_eq_of_isAffineOpen' (tilde M) σ hF ⊤ (isAffineOpen_top (Spec R)) w
  · exact exists_map_app_eq_zero_of_cocone_ι_app_eq_zero (tilde M) σ hF hgU ⊤ n u h

end AlgebraicGeometry

end
