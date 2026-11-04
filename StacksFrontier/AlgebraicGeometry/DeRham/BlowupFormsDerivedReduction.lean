module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedComparison
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic

/-!
# Reducing clause (3) of Stacks 0FUU to the restriction of forms to the exceptional divisor

The comparison `Rb_*Ω^a_{X'/S} ⟶ Ri_*Rp_*Ω^a_{E/S}` of clause (3) of [Stacks, Tag 0FUU] is
`Stacks.DeRham.formsDerivedSquareComparison`.  It is `Rb_*` of the restriction
`Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}` followed by isomorphisms: `j_* = Rj_*` on quasi-coherent modules
because `j` is affine ([Stacks, Tag 0G9R]), and the rest are composition isomorphisms.  So
clause (3) in degree `q` is invertibility of `H^q(Rb_*(Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}))`.  This is a
statement about a map of quasi-coherent modules, and flat base change of `H^q(Rb_*(-))`, which is
natural in the module, transfers it along étale charts and restrictions to opens.

## Main results

* `Stacks.DeRham.isIso_pushforwardSingleToDerived`: `g_*N ≅ Rg_*N` for `g` affine and `N`
  quasi-coherent.
* `Stacks.DeRham.isIso_homology_formsDerivedSquareComparison_iff`: the comparison is invertible
  in degree `q` exactly when `H^q(Rb_*)` of the restriction of forms is.
* `Stacks.DeRham.isIso_formsRestrictionHomology_iff`: flat base change of that map, for a
  cartesian square on the blowup side, a commutative square on the exceptional side with
  invertible base-change map, and invertible canonical maps on forms.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0G9R](https://stacks.math.columbia.edu/tag/0G9R)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SchemeCohomology (hom)
open Stacks.AlgebraicGeometry.FlatBaseChangeDerived
  (homologyDerivedPushforwardBaseChange homologyDerivedPushforwardBaseChange_naturality
    isIso_homologyDerivedPushforwardBaseChange)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardCompIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-- For an affine morphism and a quasi-coherent module, `g_*N ⟶ Rg_*N` is an isomorphism. -/
instance isIso_pushforwardSingleToDerived {X Y : Scheme.{u}} (g : X ⟶ Y) [IsAffineHom g]
    (N : X.Modules) [N.IsQuasicoherent] : IsIso (pushforwardSingleToDerived g N) := by
  have hqc : ∀ n,
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj N).X
        n).IsQuasicoherent := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact (HomologicalComplex.single_obj_X_self (V := X.Modules) (c := ComplexShape.up ℤ) 0
        N).symm ▸ inferInstance
    · exact Stacks.Duality.isQuasicoherent_of_isZero _
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  have := isIso_to_rightDerived_of_termwise_acyclic g
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj N) hqc
    (fun n => have := hqc n; rightAcyclic_pushforward_of_isAffineHom g _)
    (schemeDerivedPushforward g) (schemeDerivedPushforwardUnit g)
  have h : IsIso ((schemeDerivedPushforwardUnit g).app
      ((HomotopyCategory.singleFunctor X.Modules 0).obj N)) := this
  unfold pushforwardSingleToDerived
  infer_instance

/-- **The comparison of a square in degree `q` is the restriction of forms in degree `q`.**  The
comparison `Rb_*Ω^a ⟶ Ri_*Rp_*Ω^a` of a commutative square `j ≫ b = p ≫ i` with `j` affine is
invertible in degree `q` exactly when `H^q(Rb_*(Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}))` is. -/
theorem isIso_homology_formsDerivedSquareComparison_iff {S X X' Z E : Scheme.{u}} (f : X ⟶ S)
    {j : E ⟶ X'} {b : X' ⟶ X} {p : E ⟶ Z} {i : Z ⟶ X} (w : j ≫ b = p ≫ i) [IsAffineHom j]
    (a : ℕ) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
        (formsDerivedSquareComparison f w (a : ℤ))) ↔
      IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
        ((schemeDerivedPushforward b).map ((DerivedCategory.singleFunctor X'.Modules 0).map
          (Scheme.Hom.formsDirectImageComparison j (b ≫ f) (a : ℤ))))) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (j ≫ b ≫ f) a
  have hP : IsIso ((schemeDerivedPushforward b).map (pushforwardSingleToDerived j
      (Scheme.Hom.relativeDifferentialForms (j ≫ b ≫ f) (a : ℤ)))) := inferInstance
  unfold formsDerivedSquareComparison
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, isIso_comp_right_iff]

/-- The map `H^q(Rb_*(Ω^a_{Y/S} ⟶ j_*Ω^a_{E/S}))` on cohomology sheaves. -/
abbrev formsRestrictionHomology {S X Y E : Scheme.{u}} (b : Y ⟶ X) (j : E ⟶ Y) (p : Y ⟶ S)
    (a : ℕ) (q : ℤ) :=
  (DerivedCategory.homologyFunctor X.Modules q).map
    ((schemeDerivedPushforward b).map ((DerivedCategory.singleFunctor Y.Modules 0).map
      (Scheme.Hom.formsDirectImageComparison j p (a : ℤ))))

section Transfer

variable {X X₁ Y Y₁ E E₁ S S₁ : Scheme.{u}} {b : Y ⟶ X} {b' : Y₁ ⟶ X₁} {g : X₁ ⟶ X}
  {g' : Y₁ ⟶ Y} (H : IsPullback g' b' b g) {j : E ⟶ Y} {j' : E₁ ⟶ Y₁} {h : E₁ ⟶ E}
  (w : h ≫ j = j' ≫ g') (p : Y ⟶ S) (p' : Y₁ ⟶ S₁) (s : S₁ ⟶ S) (hs : g' ≫ p = p' ≫ s)

include H in
/-- **Flat base change of `H^q(Rb_*(Ω^a ⟶ j_*Ω^a))`.**  Take a cartesian square
`g' ≫ b = b' ≫ g` with `g` flat and `b` quasi-compact and quasi-separated, and a commutative
square `h ≫ j = j' ≫ g'` whose base-change map at the forms is invertible.  Suppose also that the
canonical maps on forms along `g'` and `h` are invertible.  Then the inverse image along `g` of
`H^q(Rb_*(Ω^a ⟶ j_*Ω^a))` is invertible exactly when the same map for `b'` and `j'` is. -/
theorem isIso_formsRestrictionHomology_iff [Flat g] [QuasiCompact b] [QuasiSeparated b]
    [QuasiCompact j] [QuasiSeparated j] (a : ℕ) (q : ℤ)
    [IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (Scheme.Hom.relativeDifferentialForms (j ≫ p) (a : ℤ)))]
    [IsIso (Scheme.Hom.relativeDifferentialFormsMap g' p p' s hs (a : ℤ))]
    [IsIso (Scheme.Hom.relativeDifferentialFormsMap h (j ≫ p) (j' ≫ p') s
      (forms_square_comm_aux j j' g' h w p p' s hs) (a : ℤ))] :
    IsIso ((Scheme.Modules.pullback g).map (formsRestrictionHomology b j p a q)) ↔
      IsIso (formsRestrictionHomology b' j' p' a q) := by
  have hF := Scheme.Hom.isQuasicoherent_relativeDifferentialForms p a
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (j ≫ p) a
  have hG := AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward j
    (Scheme.Hom.relativeDifferentialForms (j ≫ p) (a : ℤ)) inferInstance
  have hnat := homologyDerivedPushforwardBaseChange_naturality
    H (Scheme.Hom.formsDirectImageComparison j p (a : ℤ)) q
  let Φ : Y₁.Modules ⥤ X₁.Modules := DerivedCategory.singleFunctor Y₁.Modules 0 ⋙
    schemeDerivedPushforward b' ⋙ DerivedCategory.homologyFunctor X₁.Modules q
  have hsq := formsDirectImageComparison_baseChange j j' g' h w p p' s hs (a : ℤ)
  have hΦ := congrArg Φ.map hsq
  simp only [Functor.map_comp] at hΦ
  have hBF := isIso_homologyDerivedPushforwardBaseChange
    H (Scheme.Hom.relativeDifferentialForms p (a : ℤ)) q
  have hBG := isIso_homologyDerivedPushforwardBaseChange
    H ((Scheme.Modules.pushforward j).obj (Scheme.Hom.relativeDifferentialForms (j ≫ p) (a : ℤ))) q
  show IsIso ((Scheme.Modules.pullback g).map (formsRestrictionHomology b j p a q)) ↔
    IsIso (Φ.map (Scheme.Hom.formsDirectImageComparison j' p' (a : ℤ)))
  rw [← isIso_comp_right_iff _ (homologyDerivedPushforwardBaseChange H
      ((Scheme.Modules.pushforward j).obj
        (Scheme.Hom.relativeDifferentialForms (j ≫ p) (a : ℤ))) q),
    hnat, isIso_comp_left_iff, ← isIso_comp_left_iff (Φ.map
      (Scheme.Hom.relativeDifferentialFormsMap g' p p' s hs (a : ℤ))), ← hΦ,
    ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]
  rfl

end Transfer

end Stacks.DeRham
