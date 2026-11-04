module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image and bounded below direct sums

[Stacks, Tag 0GIW] says that for a quasi-compact and quasi-separated morphism of schemes
`f : X ⟶ Y` and a family `K_i`, `i ∈ I`, of objects of `D(X_étale)` such that `H^n(K_i) = 0` for
`n < a` and all `i`, one has `Rf_*(⨁_i K_i) = ⨁_i Rf_* K_i`.

The source's argument: choose complexes `ℱ_i^•` representing `K_i` with `ℱ_i^n = 0` for `n < a`;
their termwise direct sum represents `⨁ K_i` ([Stacks, Tag 07D9]), and `R^p f_*` commutes with it
because it is the filtered colimit of the finite direct sums ([Stacks, Tag 0GIV]). Here the
complexes are taken to consist of injective sheaves; then each `ℱ_i^•`, and their termwise direct
sum, is a bounded below complex of `f_*`-acyclic sheaves — the terms of the direct sum are
acyclic because every `R^q f_*` commutes with direct sums
(`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`,
which is where quasi-compactness and quasi-separatedness of `f` are used) — so `Rf_*` is computed
termwise on each of them by Leray's acyclicity lemma, [Stacks, Tag 015E], and termwise `f_*`
commutes with the direct sum.

## Main results

* `Stacks.EtaleCohomology.preservesColimit_of_isGE_of_isRightDerivedFunctor` — the statement for
  any unbounded right derived functor of a left exact functor between Grothendieck abelian
  categories whose ordinary right derived functors commute with the direct sum.
* `Stacks.EtaleCohomology.preservesColimit_etaleAbelianDerivedDirectImage_of_isGE` — **the tag**,
  for the unbounded derived direct image `Rf_* : D(X_étale) ⥤ D(Y_étale)` of abelian sheaves.
* `Stacks.EtaleCohomology.isIso_sigmaComparison_etaleAbelianDerivedDirectImage_of_isGE` — the
  same, read as invertibility of the canonical map `⨁ Rf_* K_i ⟶ Rf_*(⨁ K_i)`.

## Implementation notes

*The category.* The statement is made in the unbounded derived categories, as in the source, for
`Stacks.EtaleCohomology.etaleAbelianDerivedDirectImage`, the right derived functor of `f_*` on
`D(X_étale)` built from K-injective resolutions. The direct sum is the coproduct in `D(X_étale)`,
and the conclusion is about the coproduct in `D(Y_étale)`; the bounded below derived categories do
not appear.

*Direct sums.* "Commutes with the direct sum" is `CategoryTheory.Limits.PreservesColimit` for the
discrete diagram of the family: `Rf_*` carries a coproduct cocone of the `K_i` to a coproduct
cocone, which is the source's `Rf_*(⨁ K_i) = ⨁ Rf_* K_i` through the canonical comparison. The
corollary states the invertibility of `CategoryTheory.Limits.sigmaComparison` itself.

*The index universe.* `I` ranges over `Type (max (u + 1) v)`, the universe controlling the
Grothendieck axioms of the categories of abelian sheaves `AddCommGrpCat.{max (u + 1) v}` on the
small étale sites; it is the universe in which those categories, and their derived categories,
have direct sums.

## References

* [Stacks Project, Tag 0GIW](https://stacks.math.columbia.edu/tag/0GIW)
* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ZeroObject

universe w v₁ v₂ u₁ u₂ z₁ z₂ v u

namespace Stacks.EtaleCohomology

section Machinery

/-- An object of the derived category that is cohomologically bounded below by `a` is represented
by a complex of injective objects that is strictly bounded below by `a`. -/
theorem exists_injective_isStrictlyGE_iso {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{z₁} A] (K : DerivedCategory A) (a : ℤ)
    [hK : K.IsGE a] :
    ∃ (M : CochainComplex A ℤ) (_ : M.IsStrictlyGE a) (_ : ∀ n, Injective (M.X n)),
      Nonempty (DerivedCategory.Q.obj M ≅ K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  let P : ObjectProperty A := fun X => Injective X
  have : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
  obtain ⟨M, g, hg, hM, _, hge⟩ := CochainComplex.exists_quasiIso_prop_isStrictlyGE P
    (fun X => ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) a L
  exact ⟨M, hge, hM, ⟨(asIso (DerivedCategory.Q.map g)).symm ≪≫ e.symm⟩⟩

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{z₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
  [HasDerivedCategory.{z₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] {I : Type w}

omit [IsGrothendieckAbelian.{w} B] in
/-- The terms of a direct sum of complexes of injective objects are right acyclic for `F` as soon
as all the ordinary right derived functors of `F` commute with direct sums of that shape. -/
theorem rightAcyclic_X_coproduct_of_injective
    (hsums : ∀ p : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived p))
    (M : I → CochainComplex A ℤ) (hinj : ∀ i n, Injective ((M i).X n)) (n : ℤ) :
    F.rightAcyclic ((∐ M).X n) := by
  have hev := isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
    (coproductIsCoproduct M)
  let e' : (∐ M).X n ≅ ∐ (fun i ↦ (M i).X n) :=
    ((isColimitMapCoconeCofanMkEquiv _ _ _) hev).coconePointUniqueUpToIso
      (coproductIsCoproduct (fun i ↦ (M i).X n))
  exact ObjectProperty.prop_of_iso _ e'.symm
    (Stacks.Cohomology.CompactExtensionByZero.rightAcyclic_coproduct_of_injectives F I
      (fun i ↦ (M i).X n) (fun i ↦ hinj i n) hsums)

/-- **An unbounded right derived functor of a left exact functor commutes with a direct sum of a
family admitting a common lower bound**, as soon as all the ordinary right derived functors
commute with direct sums of that shape.

Each member of the family is represented by a complex of injective objects that is strictly
bounded below by the common bound; the termwise direct sum of those complexes is again strictly
bounded below and has right acyclic terms, so the comparison of `RF` with termwise `F` is
invertible on every member and on the direct sum (Leray's acyclicity lemma, through
`Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic`), and termwise `F` commutes with the
direct sum. -/
theorem preservesColimit_of_isGE_of_isRightDerivedFunctor
    (hsums : ∀ p : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived p))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : I → DerivedCategory A) (a : ℤ) (hK : ∀ i, (K i).IsGE a) :
    PreservesColimit (Discrete.functor K) RF := by
  classical
  have : EnoughInjectives A := IsGrothendieckAbelian.enoughInjectives
  choose M hM hinj e using fun i ↦ exists_injective_isStrictlyGE_iso (K i) a (hK := hK i)
  have := hsums 0
  have hF : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  have hFM : PreservesColimitsOfShape (Discrete I)
      (F.mapHomologicalComplex (ComplexShape.up ℤ)) := by
    constructor
    intro E
    constructor
    intro s hs
    refine ⟨HomologicalComplex.isColimitOfEval _ _ (fun i ↦ ?_)⟩
    have : PreservesColimit E (HomologicalComplex.eval A (ComplexShape.up ℤ) i ⋙ F) :=
      comp_preservesColimit _ _
    exact isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) i ⋙ F) hs
  let β := Stacks.Injectives.complexUnit F RF α
  have hβ (L : CochainComplex A ℤ) (hL : L.IsStrictlyGE a) (hLac : ∀ n, F.rightAcyclic (L.X n)) :
      IsIso (β.app L) := by
    have := Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic F RF α L ⟨a, hL⟩ hLac
    rw [Stacks.Injectives.complexUnit_app]
    exact IsIso.comp_isIso' ((DerivedCategory.quotientCompQhIso B).symm.app _).isIso_hom
      (IsIso.comp_isIso' this (RF.mapIso ((DerivedCategory.quotientCompQhIso A).app L)).isIso_hom)
  have hlegs (j : Discrete I) : IsIso (β.app ((Discrete.functor M).obj j)) :=
    hβ (M j.as) (hM j.as) fun n ↦ have := hinj j.as n; F.rightAcyclic_of_injective _
  have hapex : IsIso (β.app (∐ M)) := hβ (∐ M) (CochainComplex.isStrictlyGE_coproduct M a)
    (rightAcyclic_X_coproduct_of_injective F hsums M hinj)
  have := CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck (A := A) I
  have := CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck (A := B) I
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := B)
  have hH : IsColimit ((DerivedCategory.Q (C := A) ⋙ RF).mapCocone
      (colimit.cocone (Discrete.functor M))) :=
    isColimitMapCoconeOfIsIso (Discrete.functor M) (colimit.cocone (Discrete.functor M)) G
      (DerivedCategory.Q ⋙ RF) β hlegs hapex (isColimitOfPreserves G (colimit.isColimit _))
  have hQ : IsColimit ((DerivedCategory.Q (C := A)).mapCocone
      (colimit.cocone (Discrete.functor M))) :=
    isColimitOfPreserves _ (colimit.isColimit _)
  have : PreservesColimit (Discrete.functor M ⋙ DerivedCategory.Q) RF :=
    preservesColimit_of_preserves_colimit_cocone hQ hH
  let eK : Discrete.functor M ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
    Discrete.natIso fun j ↦ (e j.as).some
  exact preservesColimit_of_iso_diagram RF eK

end Machinery

section Etale

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0GIW].** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes, let `K : I → D(X_étale)` be a family of objects of the derived category of abelian
sheaves on the small étale site of `X`, and let `a : ℤ` be such that `H^n(K i) = 0` for `n < a`
and all `i`, that is `(K i).IsGE a`. Then `Rf_*(⨁ i, K i) = ⨁ i, Rf_*(K i)`: the unbounded
derived direct image `Rf_* : D(X_étale) ⥤ D(Y_étale)` preserves the direct sum of the family.

Nothing is assumed beyond the source's hypotheses. That each `R^q f_*` commutes with direct sums
is `preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`, where
quasi-compactness and quasi-separatedness of `f` are used. -/
@[stacks 0GIW]
theorem preservesColimit_etaleAbelianDerivedDirectImage_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (max (u + 1) v)}
    (K : I → DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (a : ℤ) (hK : ∀ i, (K i).IsGE a) :
    PreservesColimit (Discrete.functor K) (etaleAbelianDerivedDirectImage.{u, v} f) :=
  preservesColimit_of_isGE_of_isRightDerivedFunctor (etaleAbelianDirectImage.{u, v} f)
    (fun p ↦ preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{v} f p I)
    _ (etaleAbelianDerivedDirectImageUnit.{u, v} f) K a hK

/-- **[Stacks, Tag 0GIW], as the canonical map.** Under the hypotheses of
`preservesColimit_etaleAbelianDerivedDirectImage_of_isGE`, the canonical map
`⨁ i, Rf_*(K i) ⟶ Rf_*(⨁ i, K i)` is an isomorphism. -/
theorem isIso_sigmaComparison_etaleAbelianDerivedDirectImage_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (max (u + 1) v)}
    (K : I → DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (a : ℤ) (hK : ∀ i, (K i).IsGE a) :
    IsIso (sigmaComparison (etaleAbelianDerivedDirectImage.{u, v} f) K) :=
  have := preservesColimit_etaleAbelianDerivedDirectImage_of_isGE.{v} f K a hK
  inferInstance

end Etale

end Stacks.EtaleCohomology

end
