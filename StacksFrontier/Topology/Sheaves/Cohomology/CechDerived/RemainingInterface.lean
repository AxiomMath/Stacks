module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.EffaceabilityInput
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The remaining interface of Stacks 01EN

Stacks 01EN says that the Čech cohomology functors `Ȟᵖ(𝒰, -)` on presheaves of
`O_X`-modules are canonically isomorphic, as a δ-functor, to the right derived functors of
`Ȟ⁰(𝒰, -) : PMod(O_X) ⥤ Mod_{O_X(U)}`.  `StacksDraft.Ch20.Sec13.Tag01EN` and
`StacksDraft.Ch20.Sec13.Tag01ENEffaceable` prove this modulo three hypotheses, carried as
arguments: `EnoughInjectives` on presheaves of modules (Stacks 01DV), effaceability of the
Čech δ-functor (Stacks 01EL plus 01EM), and a δ-functor `G` realizing the right derived
functors of degree-zero Čech cohomology.  The first is discharged here, from Mathlib, for a
space and structure presheaf in `Type 0`; the other two are not available, so the tag is not
attached.  Besides that discharge, this file sharpens the shape in which the third hypothesis
is demanded and records the consequence that consumers of 01EN actually use.

The sharpening is `DeltaFunctor.isUniversal_of_functor_iso_rightDerived`
(`StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Transport`) in place of
`Stacks.Cohomology.CechDerived.isUniversal_of_functor_eq_rightDerived`: it asks for an
*isomorphism* of `Gⁿ⁺¹` with `(G⁰).rightDerived (n + 1)` in *positive* degrees only, rather
than an equality in every degree, and likewise the degree-zero hypothesis becomes an
isomorphism rather than an equality.  This is what a `G` produced by transport —
`DeltaFunctor.ofIso`, or the corepresentability route of
`ModuleSheafCohomology.selfDerivedDeltaFunctor` — naturally comes with.

## Main definitions

* `cechDeltaIsoRightDerivedOfIso`: the 01EN comparison with its degree-zero and
  right-derived hypotheses weakened from equalities to isomorphisms, the latter required only
  in positive degrees.
* `cechDeltaIsoRightDerivedOfIso₀`: the same comparison over `Type 0`, with the
  `EnoughInjectives` hypothesis discharged, so that effaceability and `G` are the only
  remaining inputs.
* `cechCohomologyIsoRightDerived`: the degreewise form `Ȟⁿ(𝒰, -) ≅ Rⁿ Ȟ⁰(𝒰, -)`, which is the
  statement 01EO and 01EP quote from 01EN.

## Main results

* `cechDeltaIsoRightDerivedOfIso_app_zero`: the comparison is the given degree-zero
  isomorphism in degree zero, so it is the normalized one.

## What is still missing

Exactly the three hypotheses above, in the `PresheafOfModules` setting of
`Stacks.Cohomology.CechDerived`:

* `EnoughInjectives (Stacks.Cohomology.CechDerived.Modules R)` — this one is now *available*:
  Mathlib's `PresheafOfModules.instIsGrothendieckAbelian` and
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` (Stacks 079H) give it by instance
  search, but only with all four universes of `PresheafOfModules` equal; since
  `Stacks.Cohomology.CechDerived.Modules` pins the module universe to `0` while leaving the
  site and ring universes free, the instance fires only for `Y : TopCat.{0}` and
  `R : (Opens Y)ᵒᵖ ⥤ RingCat.{0}`.  Relaxing that abbreviation from `PresheafOfModules.{0} R`
  to `PresheafOfModules.{u} R` over `RingCat.{u}` would make it fire at every universe; that
  is an edit to `StacksDraft.Ch20.Sec13.Tag01EN`, not made here.
* `(Stacks.Cohomology.CechDerived.cechDeltaFunctor R 𝒰).Effaceable` — the vanishing of the
  higher Čech cohomology of an injective *presheaf* of modules.  The project's 01EL and 01EM
  are stated for the bespoke `StacksCechPresheaf.ModPresheaf X`, which carries only `Category`
  and `Preadditive`; see the `What is still missing` section of
  `StacksDraft.Ch20.Sec13.Tag01ENEffaceable`.
* a `G : DeltaFunctor (Modules R) (SectionModules R 𝒰)` with `G⁰ ≅ Ȟ⁰(𝒰, -)` and
  `Gⁿ⁺¹ ≅ (G⁰).rightDerived (n + 1)`.  `Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor`
  of Stacks 01FF is *not* such a `G`: it is a δ-functor on `SheafOfModules R` valued in
  `AddCommGrpCat`, with degree-zero part the sections functor `secF R U`, whereas 01EN needs
  one on `PresheafOfModules R` valued in `ModuleCat (R(U))` with degree-zero part degree-zero
  Čech cohomology of the covering.  The obstruction is categorical, not universe-level.
  The route that *could* supply such a `G` is
  `CategoryTheory.Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal` (Stacks 05TE, in
  `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective`), fed by the
  canonical δ-functor structure of `DerivedCategory.exists_deltaFunctorStructure_δ_eq`
  (Stacks 0152) transported along `Functor.DeltaFunctorStructure.precomp` and `….comp`; its
  components are `Functor.rightDerivedPlus`, which is why the isomorphism-valued hypotheses
  above are the usable ones.  It too assumes `EnoughInjectives`, and its universality half
  assumes the same Čech acyclicity that the effaceability input asks for.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechDerived Stacks.Cohomology.CechEffaceable

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.CechDerivedFull

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]

variable [EnoughInjectives A]

/-- **Equal additive functors have equal right derived functors.** The two `Functor.Additive`
instances the two sides carry are proofs of propositions, so they are identified once the
functors are; this is the congruence that `rw` cannot perform on
`CategoryTheory.Functor.rightDerived`, whose instance argument depends on the functor. -/
theorem rightDerived_congr {F F' : A ⥤ B} [F.Additive] [F'.Additive] (h : F = F') (n : ℕ) :
    F.rightDerived n = F'.rightDerived n := by
  subst h
  rfl

end Abstract

section Cech

variable {Y : TopCat} (R : (Opens Y)ᵒᵖ ⥤ RingCat) (𝒰 : CechOpenCover Y)

/-- **The Čech-to-derived δ-functor comparison of Stacks 01EN, with isomorphism-valued
hypotheses.** Let `G` be a δ-functor whose degree-zero part is *isomorphic* to degree-zero Čech
cohomology and whose *positive-degree* components are *isomorphic* to the right derived functors
of its own degree-zero part. If the Čech δ-functor is effaceable then the two are isomorphic as
δ-functors, by the unique isomorphism inducing the given one in degree zero.

This is `Stacks.Cohomology.CechEffaceable.cechDeltaIsoRightDerived` with both equalities
relaxed to isomorphisms and the second asked for only in positive degrees: the universality of
`G` comes from `CategoryTheory.DeltaFunctor.isUniversal_of_functor_iso_rightDerived` instead of
`Stacks.Cohomology.CechDerived.isUniversal_of_functor_eq_rightDerived`. It is the shape a `G`
obtained by transporting the δ-functor structure of `Ext` naturally has. -/
@[sga "3 I 5.2.1" "special case"]
def cechDeltaIsoRightDerivedOfIso [EnoughInjectives (Modules R)]
    [(cechDeltaFunctor R 𝒰).Effaceable]
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (e₀ : cechCohomologyFunctor R 𝒰 0 ≅ G.functor 0)
    (e : ∀ n : ℕ, G.functor (n + 1) ≅ (G.functor 0).rightDerived (n + 1)) :
    cechDeltaFunctor R 𝒰 ≅ G :=
  letI := CechEffaceable.cechDeltaFunctor_isUniversal R 𝒰
  letI := DeltaFunctor.isUniversal_of_functor_iso_rightDerived G e
  DeltaFunctor.IsUniversal.isoOfIso (F := cechDeltaFunctor R 𝒰) (G := G) e₀

/-- The comparison of `cechDeltaIsoRightDerivedOfIso` induces the given isomorphism in degree
zero; this is the normalization that makes it unique. -/
theorem cechDeltaIsoRightDerivedOfIso_app_zero [EnoughInjectives (Modules R)]
    [(cechDeltaFunctor R 𝒰).Effaceable]
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (e₀ : cechCohomologyFunctor R 𝒰 0 ≅ G.functor 0)
    (e : ∀ n : ℕ, G.functor (n + 1) ≅ (G.functor 0).rightDerived (n + 1)) :
    (cechDeltaIsoRightDerivedOfIso R 𝒰 G e₀ e).hom.app 0 = e₀.hom :=
  let := CechEffaceable.cechDeltaFunctor_isUniversal R 𝒰
  let := DeltaFunctor.isUniversal_of_functor_iso_rightDerived G e
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (F := cechDeltaFunctor R 𝒰) (G := G) e₀

/-- **The degreewise form of Stacks 01EN.** Given the three inputs of 01EN, degree-`n` Čech
cohomology of the covering is isomorphic to the `n`-th right derived functor of degree-zero
Čech cohomology. This is the identification `Ȟⁿ(𝒰, -) = Rⁿ Ȟ⁰(𝒰, -)` that Stacks 01EO and
01EP quote from 01EN; it is the degree-`n` component of the δ-functor comparison, read through
the hypotheses identifying the components of `G`. -/
def cechCohomologyIsoRightDerived [EnoughInjectives (Modules R)]
    [(cechDeltaFunctor R 𝒰).Effaceable]
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (hG0 : G.functor 0 = cechCohomologyFunctor R 𝒰 0)
    (hG : ∀ n, G.functor n = (G.functor 0).rightDerived n) (n : ℕ) :
    cechCohomologyFunctor R 𝒰 n ≅ (cechCohomologyFunctor R 𝒰 0).rightDerived n :=
  CategoryTheory.DeltaFunctor.appIso (CechEffaceable.cechDeltaIsoRightDerived R 𝒰 G hG0 hG) n ≪≫
    eqToIso ((hG n).trans (rightDerived_congr hG0 n))

end Cech

section CechZero

variable {Y : TopCat.{0}} (R : (Opens Y)ᵒᵖ ⥤ RingCat.{0}) (𝒰 : CechOpenCover Y)

/-- **The 01EN comparison over `Type 0`, with `EnoughInjectives` discharged.** The same
statement as `cechDeltaIsoRightDerivedOfIso` with the first of 01EN's three inputs found by
instance search (Mathlib's `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`), which
exhibits exactly what 01EN still needs: effaceability of the Čech δ-functor, and a δ-functor `G`
realizing the right derived functors of degree-zero Čech cohomology. -/
def cechDeltaIsoRightDerivedOfIso₀ [(cechDeltaFunctor R 𝒰).Effaceable]
    (G : DeltaFunctor (Modules R) (SectionModules R 𝒰))
    (e₀ : cechCohomologyFunctor R 𝒰 0 ≅ G.functor 0)
    (e : ∀ n : ℕ, G.functor (n + 1) ≅ (G.functor 0).rightDerived (n + 1)) :
    cechDeltaFunctor R 𝒰 ≅ G :=
  cechDeltaIsoRightDerivedOfIso R 𝒰 G e₀ e

end CechZero

end Stacks.Cohomology.CechDerivedFull

end
