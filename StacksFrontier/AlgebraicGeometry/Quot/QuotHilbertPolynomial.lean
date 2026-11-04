/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# `Quot^P_{F/X/B}` as a subfunctor of the Quot presheaf, and its being a proper algebraic space

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `F` a quasi-coherent
`𝒪_X`-module, `L` an invertible `𝒪_X`-module and `P : ℤ → ℤ`.  Remark 0DP6 of the Stacks project
forms the subfunctor `Quot^P_{F/X/B} ⊆ Quot_{F/X/B}` of the quotients `F_T ⟶ 𝒬` which have
Hilbert polynomial `P` with respect to `L`, that is,

`P(n) = χ(X_t, 𝒬_t ⊗ L_t^{⊗ n})`  for all `n ∈ ℤ` and all `t ∈ T`

(Stacks 0DNF at `I = ℤ` and `E_n = L^{⊗ n}`).  The condition is
`AlgebraicGeometry.Space.CoherentObject.HasHilbertPolynomial`, read on the object `(T, 𝒬)` of
`Coh_{X/B}` the quotient gives, and it is inherited along the morphisms of `Coh_{X/B}`
(`AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`); so it cuts out a subfunctor of the Quot
presheaf by `AlgebraicGeometry.Space.QuotSituation.quotCondition`.

Lemmas 0DPA, 0DPB and 0DPC say that this subfunctor is an algebraic space proper over `B`.  A
subfunctor of the Quot presheaf takes values one universe above the schemes of the site, so
"is an algebraic space" is said of a model of it in the universe of the site, exactly as for the
Quot presheaf itself (`AlgebraicGeometry.Space.QuotSitePresheafModel`, Stacks 09TU).

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.hilbertPolynomialQuot`: `Quot^P_{F/X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.SubfunctorModel`: a model in `Type u` of a subfunctor
  of the Quot presheaf, with its canonical morphism `toBase` to `B`; every subfunctor has one,
  `AlgebraicGeometry.Space.QuotSituation.SubfunctorModel.canonical`.
* `AlgebraicGeometry.Space.QuotSituation.IsProperAlgebraicSpaceOver`: a subfunctor of the Quot
  presheaf is an algebraic space proper over `B`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.mem_hilbertPolynomialQuot_iff`: membership unfolded.
* `AlgebraicGeometry.Space.QuotSituation.SubfunctorModel.isoOfModel`: two models are isomorphic
  over `B`, so `IsProperAlgebraicSpaceOver` does not depend on the model
  (`AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_iff_forall`).

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Having Hilbert polynomial `P` is inherited along morphisms of `Coh_{X/B}`**: the twisted
Euler characteristic at `t` of the source of a morphism is the one of its target at the image
of `t` (`AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`). -/
theorem CoherentObject.hasHilbertPolynomial_of_coherentHom {D : CoherentSituation B S hS}
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) {A' A : CoherentObject D} (m : CoherentHom A' A)
    (h : CoherentObject.HasHilbertPolynomial L P A) : CoherentObject.HasHilbertPolynomial L P A' :=
  fun t n => (h (m.baseScheme t) n).trans (m.twistedEuler_eq L t n).symm

namespace QuotSituation

variable (D : QuotSituation B S hS)

section HilbertPolynomial

variable (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
  (P : ℤ → ℤ)

/-- **`Quot^P_{F/X/B}`** (Stacks 0DP6 with the condition of Stacks 0DNF at `E_n = L^{⊗ n}`): the
subfunctor of the Quot presheaf of the quotients `F_T ⟶ 𝒬` with
`P(n) = χ(X_t, 𝒬_t ⊗ L_t^{⊗ n})` for every `n ∈ ℤ` and every point `t` of `T`. -/
def hilbertPolynomialQuot : Subfunctor D.quotSitePresheaf :=
  letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS D.toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  D.quotCondition (CoherentObject.HasHilbertPolynomial L P)
    (fun {A' A} m h =>
      @CoherentObject.hasHilbertPolynomial_of_coherentHom B S hS D.toCoherentSituation L this P
        A' A m h)

/-- Membership in `Quot^P_{F/X/B}`, unfolded. -/
theorem mem_hilbertPolynomialQuot_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : D.quotSitePresheaf.obj T) :
    letI : Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B S hS D.toCoherentSituation.X.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
    x ∈ (D.hilbertPolynomialQuot L P).obj T ↔
      ∀ (t : x.cohObject.testScheme) (n : ℤ), P n = x.cohObject.twistedEuler L t n :=
  Iff.rfl

end HilbertPolynomial

/-! ### Models of subfunctors, and being a proper algebraic space over `B` -/

/-- A model of a subfunctor `Q` of the Quot presheaf in the universe of the big fppf site: a
presheaf of `Type u` whose universe lift is isomorphic to `Q`. -/
structure SubfunctorModel (Q : Subfunctor D.quotSitePresheaf) where
  /-- The small presheaf. -/
  presheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its universe lift is `Q`. -/
  iso : presheaf ⋙ uliftFunctor.{u + 1, u} ≅ Q.toFunctor

namespace SubfunctorModel

variable {D} {Q : Subfunctor D.quotSitePresheaf} (M : D.SubfunctorModel Q)

/-- The canonical morphism from a model of a subfunctor of the Quot presheaf to `B`, sending a
quotient to the morphism to `B` it lies over. -/
def toBase : M.presheaf ⟶ D.Y.obj where
  app T := ↾fun z ↦ (D.quotSitePresheafToBase.app T (Q.ι.app T (M.iso.hom.app T ⟨z⟩))).down
  naturality {T T'} g := by
    ext z
    have h := types_congr_hom ((M.iso.hom ≫ Q.ι ≫ D.quotSitePresheafToBase).naturality g)
      (ULift.up.{u + 1} z)
    exact congrArg ULift.down h

/-- The morphism to `B`, lifted to the universe of `Q`, is the inclusion of `Q` followed by the
canonical morphism of the Quot presheaf. -/
theorem whiskerRight_toBase :
    Functor.whiskerRight M.toBase uliftFunctor.{u + 1, u} =
      M.iso.hom ≫ Q.ι ≫ D.quotSitePresheafToBase := by
  ext T z
  rfl

/-- **Two models of a subfunctor of the Quot presheaf are isomorphic.** -/
def isoOfModel (M M' : D.SubfunctorModel Q) : M.presheaf ≅ M'.presheaf :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso (Equiv.ulift.symm.trans
      (((M.iso ≪≫ M'.iso.symm).app T).toEquiv.trans Equiv.ulift))) fun {T T'} g ↦ by
    ext z
    exact congrArg ULift.down (types_congr_hom ((M.iso ≪≫ M'.iso.symm).hom.naturality g)
      (ULift.up.{u + 1} z))

/-- The isomorphism of two models lies over `B`. -/
theorem isoOfModel_hom_comp_toBase (M M' : D.SubfunctorModel Q) :
    (isoOfModel M M').hom ≫ M'.toBase = M.toBase := by
  ext T z
  show (D.quotSitePresheafToBase.app T (Q.ι.app T (M'.iso.hom.app T
    (M'.iso.inv.app T (M.iso.hom.app T ⟨z⟩))))).down = _
  rw [show M'.iso.hom.app T (M'.iso.inv.app T (M.iso.hom.app T ⟨z⟩)) = M.iso.hom.app T ⟨z⟩ from
    types_congr_hom (M'.iso.inv_hom_id_app T) _]
  rfl

/-- **The canonical model of a subfunctor of the Quot presheaf**: its sections over a scheme of
the site are a copy in `Type u` of those of the subfunctor, which form a small set because the
quotients classified by the Quot functor do
(`AlgebraicGeometry.Space.QuotSituation.small_quotFamilyOver`). -/
def canonical (Q : Subfunctor D.quotSitePresheaf) : D.SubfunctorModel Q :=
  have : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} (Q.toFunctor.obj T) := fun T =>
    have : Small.{u} (D.quotSitePresheaf.obj T) := D.small_quotFamilyOver T.unop
    small_subtype _ _
  ⟨shrinkSitePresheaf Q.toFunctor, shrinkSitePresheafIso Q.toFunctor⟩

end SubfunctorModel

/-- **A subfunctor `Q` of the Quot presheaf is an algebraic space proper over `B`**: it has a
model in the universe of the site which is an algebraic space and whose canonical morphism to `B`
is proper.  By `AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_iff_forall`
this does not depend on the model. -/
def IsProperAlgebraicSpaceOver (Q : Subfunctor D.quotSitePresheaf) : Prop :=
  ∃ M : D.SubfunctorModel Q, IsAlgebraicSpace B S hS M.presheaf ∧ IsProper B S hS M.toBase

/-- Being a proper algebraic space over `B` holds for one model exactly when it holds for every
model. -/
theorem isProperAlgebraicSpaceOver_iff_forall (Q : Subfunctor D.quotSitePresheaf) :
    D.IsProperAlgebraicSpaceOver Q ↔
      Nonempty (D.SubfunctorModel Q) ∧ ∀ M : D.SubfunctorModel Q,
        IsAlgebraicSpace B S hS M.presheaf ∧ IsProper B S hS M.toBase := by
  refine ⟨fun ⟨M, hM, hp⟩ ↦ ⟨⟨M⟩, fun M' ↦ ?_⟩, fun ⟨⟨M⟩, h⟩ ↦ ⟨M, h M⟩⟩
  refine ⟨hM.of_iso (SubfunctorModel.isoOfModel M M'), ?_⟩
  rw [← SubfunctorModel.isoOfModel_hom_comp_toBase M' M]
  exact isProper_comp' B S hS _ _ hM D.Y.property (isProper_of_isIso B S hS _) hp

end QuotSituation

end AlgebraicGeometry.Space
