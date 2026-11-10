module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BaseChangeExcessFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupFormulaHomogeneous
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionSelfIntersection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcessDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalConormalClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalProductClass
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The self-intersection of the diagonal

Let `X` be a smooth projective scheme over a field `k`, equidimensional of dimension `d`, with
diagonal `Δ : X ⟶ X × X`. This file proves the right-hand equality of Stacks 0FHS,

  `deg(Δ · Δ) = deg(c_d(𝒯_{X/k}))`,

where `Δ · Δ ∈ CH^{2d}(X × X)` is the intersection product of Stacks 0FC0 of the class
`[Δ] ∈ CH^d(X × X)` of the diagonal with itself, `𝒯_{X/k} = 𝓗om(Ω_{X/k}, 𝒪_X)` is the tangent
sheaf, and `deg(c_d(𝒯_{X/k}))` is the degree of the zero cycle class `c_d(𝒯_{X/k}) ∩ [X]`.

The proof is the source's:

* `[Δ] · [Δ] = Δ_*(Δ^![Δ])` by Stacks 0FFE
  (`Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin`),
  and proper pushforward preserves degrees (`codimensionDegree_diag_mul_diag`);
* `Δ^![Δ] = c_d(𝒩) ∩ [X]` for the normal sheaf `𝒩` of `Δ`, the excess intersection formula
  (Stacks 0FBM) in the form of the self-intersection formula of a regular closed immersion
  (`Stacks.Chow.regularImmersionGysin_closedSubschemeClass_self`), and `𝒩 = 𝒯_{X/k}` because the
  conormal sheaf of `Δ` is `Ω_{X/k}` (Stacks 08S2) (`zeroDegree_regularImmersionGysin_diag`).

## Main definitions

* `Stacks.Chow.zeroDegree`: the degree of zero cycle classes (Stacks 0AZ1) on `CH_n` for `n = 0`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.tangentSheaf`: `𝒯_{X/k} = 𝓗om(Ω_{X/k}, 𝒪_X)`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.zeroDegree_regularImmersionGysin_diag`:
  `deg(Δ^![Δ]) = deg(c_d(𝒯_{X/k}) ∩ [X])`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.codimensionDegree_diag_mul_diag`:
  `deg([Δ] · [Δ]) = deg(Δ^![Δ])`.

## References

* [Stacks Project, Tag 0FHS](https://stacks.math.columbia.edu/tag/0FHS)
* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Stacks.AlgebraicGeometry.ReflexiveModules RingedSpaceModuleAdjunction

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {E Z' : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE]
  (sZ : Z' ⟶ C.S) [LocallyOfFiniteType sZ] (π : E ⟶ Z') [LocallyOfFiniteType π]
  [AlgebraicGeometry.Flat π] (hπ : π ≫ sZ = sE) (s : ℕ)
  (hrel : AlgebraicGeometry.RelativeDimension π s)

/-- Fundamental classes in equal degrees, for equal structure morphisms, are heterogeneously
equal. -/
theorem fundamentalChowClass_heq_of_structure_eq {T : Scheme.{u}} {sT sT' : T ⟶ C.S}
    [LocallyOfFiniteType sT] [LocallyOfFiniteType sT'] (h : sT = sT') {n n' : ℤ} (hn : n = n') :
    fundamentalChowClass C sT n ≍ fundamentalChowClass C sT' n' := by
  subst h hn
  rfl

section Degree

variable (k : Type u) [Field k]

/-- The degree of a zero cycle class (Stacks 0AZ1), on `CH_n` for `n = 0`. -/
def zeroDegree {T : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S) [IsProper sT] {n : ℤ}
    (hn : n = 0) : chowGroup (fieldChowSituation k) sT n →+ ℤ :=
  (chowDegree (fieldChowSituation k) (fun _ ↦ rfl) sT
      (genericPoint (fieldChowSituation k).S)).comp
    (chowGroupDegreeEquiv _ _ hn).toAddMonoidHom

variable {k}

/-- The degree does not depend on how the structure morphism, the degree or the class are
written. -/
theorem zeroDegree_heq {T : Scheme.{u}} {sT sT' : T ⟶ (fieldChowSituation k).S} [IsProper sT]
    [IsProper sT'] (h : sT = sT') {n n' : ℤ} (hn : n = 0) (hn' : n' = 0)
    {γ : chowGroup (fieldChowSituation k) sT n} {γ' : chowGroup (fieldChowSituation k) sT' n'}
    (hγ : γ ≍ γ') : zeroDegree k sT hn γ = zeroDegree k sT' hn' γ' := by
  subst h
  obtain rfl : n = n' := hn.trans hn'.symm
  obtain rfl := eq_of_heq hγ
  rfl

/-- **Proper pushforward preserves degrees** of zero cycle classes. -/
theorem zeroDegree_properChowPushforward {A B : Scheme.{u}} (sA : A ⟶ (fieldChowSituation k).S)
    (sB : B ⟶ (fieldChowSituation k).S) [IsProper sA] [IsProper sB] (f : A ⟶ B) [IsProper f]
    (hf : f ≫ sB = sA) {n : ℤ} (hn : n = 0)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation k) sA sB f hf n)
    (γ : chowGroup (fieldChowSituation k) sA n) :
    zeroDegree k sB hn (properChowPushforward (fieldChowSituation k) sA sB f hf n hfac γ) =
      zeroDegree k sA hn γ := by
  subst hf hn
  have h := DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k) (f ≫ sB) sB
    (𝟙 _) f sB rfl (Category.comp_id sB) 0 hfac
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)) γ
  rw [AddMonoidHom.comp_apply] at h
  change (chowDegree (fieldChowSituation k) (fun _ ↦ rfl) sB _)
      (properChowPushforward (fieldChowSituation k) (f ≫ sB) sB f rfl 0 hfac γ) =
    (chowDegree (fieldChowSituation k) (fun _ ↦ rfl) (f ≫ sB) _) γ
  simp only [chowDegree, AddMonoidHom.comp_apply]
  exact congrArg _ h

/-- **Pushforward along an isomorphism preserves degrees.** -/
theorem zeroDegree_chowPushforwardOfIso {A B : Scheme.{u}} (sA : A ⟶ (fieldChowSituation k).S)
    (sB : B ⟶ (fieldChowSituation k).S) [IsProper sA] [IsProper sB] (f : A ⟶ B) [IsIso f]
    (hf : f ≫ sB = sA) {n : ℤ} (hn : n = 0) (γ : chowGroup (fieldChowSituation k) sA n) :
    zeroDegree k sB hn (chowPushforwardOfIso (fieldChowSituation k) sA sB f hf n γ) =
      zeroDegree k sA hn γ :=
  zeroDegree_properChowPushforward sA sB f hf hn _ γ

/-- **Restriction along an isomorphism preserves degrees.** -/
theorem zeroDegree_chowGroupRestrict_of_isIso {A B : Scheme.{u}}
    (sA : A ⟶ (fieldChowSituation k).S) (sB : B ⟶ (fieldChowSituation k).S) [IsProper sA]
    [IsProper sB] (e : B ⟶ A) [IsIso e] (he : e ≫ sA = sB) {n : ℤ} (hn : n = 0)
    (γ : chowGroup (fieldChowSituation k) sA n) :
    zeroDegree k sB hn (chowGroupRestrict (fieldChowSituation k) sA sB e he n γ) =
      zeroDegree k sA hn γ := by
  rw [chowGroupRestrict_of_isIso, zeroDegree_chowPushforwardOfIso]

/-- The pushforward of the fundamental class along a closed immersion is the class of the closed
subscheme. -/
theorem properChowPushforward_fundamentalChowClass_of_isClosedImmersion {Y Z : Scheme.{u}}
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] (i : Z ⟶ Y)
    [IsClosedImmersion i] (m : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence (fieldChowSituation k) (i ≫ sY)
      sY i rfl m) :
    properChowPushforward (fieldChowSituation k) (i ≫ sY) sY i rfl m hfac
        (fundamentalChowClass (fieldChowSituation k) (i ≫ sY) m) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY i m) := by
  rw [fundamentalChowClass, fundamentalCycle, properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_id]
  rfl

end Degree

end Stacks.Chow

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The tangent sheaf `𝒯_{X/k} = 𝓗om_{𝒪_X}(Ω_{X/k}, 𝒪_X)`** of a smooth projective scheme over
`k`: the dual of the sheaf of relative differentials. -/
@[ega "IV 16.5.7" "special case", sga "1 III 5.2" "special case", sga "1 III 6.9" "special case"]
def tangentSheaf : X.obj.left.Modules :=
  dualSheaf (Scheme.Hom.relativeDifferentials X.obj.hom)

/-- The sheaf of relative differentials `Ω_{X/k}` of a smooth projective scheme is finite locally
free. -/
instance : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (Scheme.Hom.relativeDifferentials X.obj.hom) :=
  Scheme.Hom.isFiniteLocallyFree_relativeDifferentials X.obj.hom

/-- The tangent sheaf `𝒯_{X/k}` of a smooth projective scheme is finite locally free. -/
instance : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (tangentSheaf X) :=
  isFiniteLocallyFree_dualSheaf_of_schemeOpens _ inferInstance

/-- The diagonal of a smooth projective scheme is a regular immersion. -/
@[sga "1 II 4.18" "special case", sga "6 VII 1.10" "special case", sga "6 VIII 2.4" "special case"]
theorem isRegularImmersion_diag :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion (diag X).hom.left :=
  isRegularImmersion_diagonal_of_smooth X.obj.hom

/-- The diagonal is a morphism over `k`. -/
alias diag_comp_hom := diag_left_comp_hom

variable {X} in
/-- **`deg(Δ^![Δ]) = deg(c_d(𝒯_{X/k}) ∩ [X])`.** For `X` of dimension `d`, the Gysin map of the
regular immersion `Δ : X ⟶ X × X` carries the class `[Δ] ∈ CH^d(X × X)` of the diagonal to a zero
cycle class on `X` of the degree of `c_d(𝒯_{X/k}) ∩ [X]_d`. -/
theorem zeroDegree_regularImmersionGysin_diag {d : ℕ} (hX : RelativeDimension X.obj.hom d) :
    zeroDegree k ((diag X).hom.left ≫ (prod X X).obj.hom) (sub_self _)
        (regularImmersionGysin (prod X X).obj.hom (diag X).hom.left (isRegularImmersion_diag X) d d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) =
      zeroDegree k X.obj.hom (sub_self _)
        (chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _) X.obj.hom d
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) X.obj.hom (tangentSheaf X) d) d
          (fundamentalChowClass (fieldChowSituation k) X.obj.hom d)) := by
  have hP : RelativeDimension (prod X X).obj.hom (d + d) :=
    relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX
  have hY : RelativeDimension ((diag X).hom.left ≫ (prod X X).obj.hom) d :=
    RelativeDimension.congr (diag_comp_hom X).symm hX
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (tangentSheaf X) d :=
    isFiniteLocallyFreeOfRank_dualSheaf _ d
      (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension _ hX)
  -- the normal sheaf of the diagonal is the tangent sheaf (Stacks 08S2)
  let eN : dualSheaf (conormalModule (diag X).hom.left) ≅ tangentSheaf X :=
    dualSheafIsoOfIso (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal X.obj.hom)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (conormalModule (diag X).hom.left)) d :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} eN.symm inferInstance
  -- the self-intersection formula `Δ^![Δ] = c_d(𝒩) ∩ [X]`
  rw [regularImmersionGysin_closedSubschemeClass_self (prod X X).obj.hom (diag X).hom.left
    (isRegularImmersion_diag X) d d (d + d) rfl hP hY]
  refine zeroDegree_heq (diag_comp_hom X) _ _ ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  refine (chernCap_heq_of_iso _ (diag_comp_hom X) d eN _ _
    (fundamentalChowClass_heq_of_structure_eq _ (diag_comp_hom X) rfl)).trans ?_
  refine HEq.trans ?_ (chowCohomologyCap_totalChernOfFiniteLocallyFree_heq (fieldChowSituation k)
    X.obj.hom (tangentSheaf X) d (d : ℤ)
    (fundamentalChowClass (fieldChowSituation k) X.obj.hom d)).symm
  rw [GenuineChern.chernFamily_apply_of_le _ _ _ d d le_rfl]
  have key : ∀ j j' : Fin (d + 1), j = j' →
      GenuineChern.chernCap (fieldChowSituation k) d X.obj.hom (tangentSheaf X) d j
          (fundamentalChowClass (fieldChowSituation k) X.obj.hom d) ≍
        GenuineChern.chernCap (fieldChowSituation k) d X.obj.hom (tangentSheaf X) d j'
          (fundamentalChowClass (fieldChowSituation k) X.obj.hom d) := by
    rintro j _ rfl
    rfl
  exact key _ _ (Fin.ext rfl)

/-- The degree on `CH^e(Y)` is the degree of the component on the part `Y_e`. -/
theorem codimensionDegree_eq_zeroDegree (Y : (SmoothProjectiveScheme k).FullSubcategory) (e : ℕ)
    (α : codimensionChowGroup k Y.obj.hom e) :
    codimensionDegree Y e α = zeroDegree k (partBase Y.obj.hom e) (sub_self _) (α e) :=
  rfl

variable {X} in
/-- **`deg([Δ] · [Δ]) = deg(Δ^![Δ])`.** For `X` of dimension `d`, the intersection product of the
class of the diagonal with itself in `CH^{2d}(X × X)` has the degree of `Δ^![Δ]`: by Stacks 0FFE,
`[Δ] · [Δ] = Δ_*(Δ^![Δ])`, and proper pushforward preserves degrees. -/
theorem codimensionDegree_diag_mul_diag {d : ℕ} (hX : RelativeDimension X.obj.hom d) :
    codimensionDegree (prod X X) (d + d)
        (codimensionIntersectionProduct k (prod X X).obj.hom d d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) =
      zeroDegree k ((diag X).hom.left ≫ (prod X X).obj.hom) (sub_self _)
        (regularImmersionGysin (prod X X).obj.hom (diag X).hom.left (isRegularImmersion_diag X) d d
          (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) := by
  have hP : RelativeDimension (prod X X).obj.hom (d + d) :=
    relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX
  have := isIso_dimPart_self_ι _ hP
  have hY : RelativeDimension ((diag X).hom.left ≫ (prod X X).obj.hom) d := by
    have key : ∀ (s : X.obj.left ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType s],
        s = X.obj.hom → RelativeDimension s d := by
      rintro s _ rfl
      exact hX
    exact key _ (diag_comp_hom X)
  -- Stacks 0FFE: `[Δ] · Δ_*[X]_d = Δ_*(Δ^![Δ])`
  have E := intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin
    (prod X X).obj.hom (diag X).hom.left (isRegularImmersion_diag X) d hY d
    (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
  have E' := congrArg (chowGroupRestrict (fieldChowSituation k) (prod X X).obj.hom
    (partBase (prod X X).obj.hom (d + d)) (dimPart (prod X X).obj.hom (d + d)).ι rfl _) E
  -- the degree on `X × X` is read on its part of dimension `2d`
  have h1 : codimensionDegree (prod X X) (d + d)
      (codimensionIntersectionProduct k (prod X X).obj.hom d d
        (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
        (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)) =
      zeroDegree k (partBase (prod X X).obj.hom (d + d)) (by ring)
        (chowGroupRestrict (fieldChowSituation k) (prod X X).obj.hom
          (partBase (prod X X).obj.hom (d + d)) (dimPart (prod X X).obj.hom (d + d)).ι rfl _
          (codimensionDimensionIntersectionProduct k (prod X X).obj.hom d d
            (closedSubschemeClass (prod X X).obj.hom (diag X).hom.left d)
            (properChowPushforward (fieldChowSituation k) _ (prod X X).obj.hom (diag X).hom.left
              rfl d (properPushforwardDescends _ _ _ _ _ _)
              (fundamentalChowClass (fieldChowSituation k) _ d)))) := by
    rw [chowGroupRestrict_codimensionDimensionIntersectionProduct,
      codimensionDegree_eq_zeroDegree, codimensionIntersectionProduct_apply]
    refine zeroDegree_heq rfl _ _ ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm))
    refine selfIntersectionProduct_heq_of_heq _ _ _ rfl (by push_cast; ring) HEq.rfl ?_
    rw [closedSubschemeClass_apply, properChowPushforward_fundamentalChowClass_of_isClosedImmersion]
    exact chowGroupRestrict_heq_of_eq _ _ _ rfl rfl rfl _ _ (by push_cast; ring) _ _
      (mk_cycleAssociatedToClosedSubscheme_heq _ _ _ (by push_cast; ring))
  rw [h1, E', zeroDegree_chowGroupRestrict_of_isIso, zeroDegree_properChowPushforward]

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
