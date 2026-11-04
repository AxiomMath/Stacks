module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InversePointReadingSquares

/-!
# The cocycle of Stacks 03LU behind the comparison of fibres of `𝐏(ℰ)` and `𝐏(g^*ℰ)`

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points,
`h : T' ⟶ T` with `v ≫ g = u ∘ h`, and `f' : Z ⟶ T'`. This file proves, at these points, the
one-space half of the cocycle of the comparisons of inverse images of Stacks 03LU along `f'`, `v`,
`g` and along `f'`, `h`, `u` that identifies `((u ∘ h ∘ f')^*ℰ)` with `(v ∘ f')^* g^*ℰ` and with
`(f' ∘ h)^* u^*ℰ`. The morphisms of represented algebraic spaces and the scheme points spell the
represented algebraic spaces differently; every such change of spelling is carried by its own
identification.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_app_inv_pointHom_yonedaMap_comp`: the comparison
  along `v ∘ f'` and `g`, in the spelling of the represented algebraic space of `Z` used by
  `representedSpaceMap` (the hypothesis `hψ` of the two-space half).
* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_pointHom_comp_representedSpaceMap`: the
  one-space half.
* `AlgebraicGeometry.Space.pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso`: the two-space
  half.
* `AlgebraicGeometry.Space.pointTwoSpaceCompIso_hom_comp`: the cocycle, the two halves pasted.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- A morphism `f = e ≫ m` followed by `n`, with `e ≫ m ≫ n = e' ≫ k`, in a bare category. -/
theorem CategoryTheory.comp_eq_of_eq_comp_of_comp_comp_eq {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ B₀ C₀ D₀ : 𝒞} (f : A₀ ⟶ A₁) (e : A₀ ⟶ B₀) (m : B₀ ⟶ A₁) (n : A₁ ⟶ C₀)
    (e' : A₀ ⟶ D₀) (k : D₀ ⟶ C₀) (H₁ : f = e ≫ m) (H₂ : e ≫ m ≫ n = e' ≫ k) :
    f ≫ n = e' ≫ k := by
  rw [H₁, Category.assoc, H₂]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Heq

/-- The identification of inverse images along equal morphisms, for heterogeneously equal
morphisms out of equal spaces. -/
theorem eqToHom_app_modulePullback_congr_heq {Y Y₀ X₀ : AlgebraicSpaces B S hS} (hY : Y = Y₀)
    (d₁ d₂ : Y ⟶ X₀) (e₁ e₂ : Y₀ ⟶ X₀) (h₁ : HEq d₁ e₁) (h₂ : HEq d₂ e₂) (p : d₁ = d₂)
    (q : e₁ = e₂) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    HEq ((eqToHom (congrArg (modulePullback B S hS) p)).app M)
      ((eqToHom (congrArg (modulePullback B S hS) q)).app M) := by
  subst hY
  obtain rfl := eq_of_heq h₁
  obtain rfl := eq_of_heq h₂
  obtain rfl : q = p := Subsingleton.elim _ _
  exact HEq.rfl

end Heq

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T' : BigFppfOver B S hS}
  (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T) (hvh : v ≫ g.hom = yoneda.map h ≫ u)
  {Z : BigFppfOver B S hS} (f' : Z ⟶ T')

/-- The point `x ∘ f` of `Y` is the composite of `f` and `x`, in the represented spaces. -/
private theorem pointHom_yonedaMap_comp_eq {Y : AlgebraicSpaces B S hS} {A A' : BigFppfOver B S hS}
    (f : A' ⟶ A) (x : yoneda.obj A ⟶ Y.1) :
    pointHom (X := Y) (yoneda.map f ≫ x) = representedSpaceMap B S hS f ≫ pointHom x :=
  ObjectProperty.hom_ext _ rfl

/-- The point `v ∘ f'` of `X'` is the composite of `f'` and `v`, its source read as the represented
algebraic space of `Z`. -/
theorem modulePullback_obj_pointHom_yonedaMap_comp_eq (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (modulePullback B S hS
        (X := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
      (pointHom (X := X') (yoneda.map f' ≫ v))).obj N =
      (modulePullback B S hS (representedSpaceMap B S hS f' ≫ pointHom v)).obj N :=
  rfl

/-- The point `u ∘ h` of `X` is the composite of `h` and `u`. -/
theorem modulePullback_obj_pointHom_representedSpaceMap_comp_eq :
    (modulePullback B S hS (pointHom (X := X) (yoneda.map h ≫ u))).obj E =
      (modulePullback B S hS (representedSpaceMap B S hS h ≫ pointHom u)).obj E :=
  rfl

/-- The point `u ∘ h ∘ f'` of `X` is the composite of `f'` and `u ∘ h`, its source read as the
represented algebraic space of `Z`. -/
theorem modulePullback_obj_pointTwoSpace_comp_eq :
    (modulePullback B S hS
        (X := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
      (pointHom (X := X) (yoneda.map (f' ≫ h) ≫ u))).obj E =
      (modulePullback B S hS (representedSpaceMap B S hS f' ≫
        pointHom (X := X) (yoneda.map h ≫ u))).obj E := by
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- The point `u ∘ h ∘ f'` of `X` is the composite of `f'`, `h` and `u`, its source read as the
represented algebraic space of `Z`. -/
theorem modulePullback_obj_pointTwoSpace_comp_comp_eq :
    (modulePullback B S hS
        (X := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
      (pointHom (X := X) (yoneda.map (f' ≫ h) ≫ u))).obj E =
      (modulePullback B S hS ((representedSpaceMap B S hS f' ≫ representedSpaceMap B S hS h) ≫
        pointHom u)).obj E := by
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- The identification `(g ∘ (v ∘ f'))^*ℰ ≅ (v ∘ f')^* g^*ℰ`, read through the spelling of the
represented algebraic space of `Z` used by `representedSpaceMap`. -/
theorem modulePullbackCompIso_app_inv_pointHom_yonedaMap_comp :
    ((modulePullbackCompIso B S hS (pointHom (yoneda.map f' ≫ v)) g).app E).inv =
      (modulePullbackCompIso B S hS
        (X := (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS))
        (pointHom (yoneda.map f' ≫ v)) g).inv.app E := by
  refine eq_of_heq ?_
  refine modulePullbackCompIso_app_inv_heq ?_ ?_ _ _ ?_ _ _ ?_ ?_
  · exact rfl
  · exact rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact rfl

/-- The comparison along `f'` and `h`, at `u^*ℰ` read through the spelling of the represented
algebraic space of `T` used by `representedSpaceMap`. -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap_modulePullback_pointHom :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (representedSpaceMap B S hS h)).hom.app ((modulePullback B S hS (pointHom u)).obj E) =
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (representedSpaceMap B S hS h)).hom.app ((modulePullback B S hS
            (X := (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))
            (pointHom u)).obj E) :=
  eq_of_heq (congr_arg_heq (fun P => (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
    (representedSpaceMap B S hS h)).hom.app P) rfl)

/-- The identification along `u ∘ h = h ≫ u`, under the inverse image along `f'`, read through the
spelling of the represented algebraic space of `T'` used by `representedSpaceMap`. -/
theorem modulePullback_map_eqToHom_pointHom_representedSpaceMap_comp :
    (modulePullback B S hS (representedSpaceMap B S hS f')).map
        (eqToHom (modulePullback_obj_pointHom_representedSpaceMap_comp_eq X E u h)) =
      (modulePullback B S hS (representedSpaceMap B S hS f')).map
        (@eqToHom _ _ ((modulePullback B S hS
          (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
          (pointHom (X := X) (yoneda.map h ≫ u))).obj E) _
        (modulePullback_obj_pointHom_representedSpaceMap_comp_eq X E u h)) :=
  rfl

/-- **The one-space half of the cocycle of Stacks 03LU at the points**: the comparison along `f'`
and `u ∘ h`, followed by the identification `u ∘ h = h ≫ u` and the comparisons along `h`, `u`
and along `f'`, `h`, is the comparison along `f' ≫ h` and `u`. -/
theorem modulePullbackCompIso_inv_app_pointHom_comp_representedSpaceMap :
    eqToHom (modulePullback_obj_pointTwoSpace_comp_eq X E u h f') ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (pointHom (X := X) (yoneda.map h ≫ u))).inv.app E ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          (eqToHom (modulePullback_obj_pointHom_representedSpaceMap_comp_eq X E u h)) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom u)).inv.app E) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (representedSpaceMap B S hS h)).hom.app ((modulePullback B S hS (pointHom u)).obj E) =
      eqToHom (modulePullback_obj_pointTwoSpace_comp_comp_eq X E u h f') ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f' ≫ representedSpaceMap B S hS h)
          (pointHom u)).inv.app E := by
  rw [modulePullback_map_eqToHom_pointHom_representedSpaceMap_comp (E := E) (u := u) (h := h)
      (f' := f'),
    modulePullbackCompIso_hom_app_representedSpaceMap_modulePullback_pointHom (E := E) (u := u)
      (h := h) (f' := f')]
  exact modulePullbackCompIso_inv_app_map_eqToHom_comp (representedSpaceMap B S hS f')
    (representedSpaceMap B S hS h) (pointHom u)
    (pointHom_yonedaMap_comp_eq h u) E
    (modulePullback_obj_pointHom_representedSpaceMap_comp_eq X E u h)
    (modulePullback_obj_pointTwoSpace_comp_eq X E u h f')
    (modulePullback_obj_pointTwoSpace_comp_comp_eq X E u h f')

section TwoSpace

include hvh

/-- **The two-space half of the cocycle of Stacks 03LU at the points**: the identification
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, followed by the comparisons along `f'`, `v` and along `v`,
`g` and the identification along `v ≫ g = u ∘ h`, is the comparison along `f'` and `u ∘ h`. -/
theorem pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso :
    (pointTwoSpaceCompIso X E u g v h hvh f').hom ≫
        eqToHom (modulePullback_obj_pointHom_yonedaMap_comp_eq v f'
          ((modulePullback B S hS g).obj E)) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (pointHom v)).inv.app ((modulePullback B S hS g).obj E) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((modulePullbackCompIso B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g).hom.app E) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((eqToHom (congrArg (modulePullback B S hS
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
            (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
              (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E) =
      eqToHom (modulePullback_obj_pointTwoSpace_comp_eq X E u h f') ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (pointHom (X := X) (yoneda.map h ≫ u))).inv.app E := by
  rw [pointTwoSpaceCompIso_eq X E u g v h hvh f']
  exact modulePullbackCompObjIso_twoSpace_comp (representedSpaceMap B S hS f') (pointHom v) g
    (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
      (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
      (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u))
    (pointHom_yonedaMap_comp_eq f' v) E
    (modulePullback_obj_pointHom_twoSpace_eq X E u g v h hvh f')
    (modulePullback_obj_pointHom_yonedaMap_comp_eq v f' ((modulePullback B S hS g).obj E))
    (modulePullback_obj_pointTwoSpace_comp_eq X E u h f')

/-- **The cocycle of Stacks 03LU at the points**: the identification
`(u ∘ h ∘ f')^*ℰ ≅ (v ∘ f')^* g^*ℰ`, followed by the comparisons along `f'`, `v` and along `v`,
`g`, the identification `v ≫ g = u ∘ h = h ≫ u` and the comparisons along `h`, `u` and along
`f'`, `h`, is the comparison along `f' ≫ h` and `u`. -/
theorem pointTwoSpaceCompIso_hom_comp :
    CategoryStruct.comp (Y := ((modulePullback B S hS
          (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
          (pointHom (X := X) (yoneda.map h ≫ u)) ⋙
          modulePullback B S hS (representedSpaceMap B S hS f')).obj E))
      ((pointTwoSpaceCompIso X E u g v h hvh f').hom ≫
        eqToHom (modulePullback_obj_pointHom_yonedaMap_comp_eq v f'
          ((modulePullback B S hS g).obj E)) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (pointHom v)).inv.app ((modulePullback B S hS g).obj E) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((modulePullbackCompIso B S hS
            (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
            (pointHom v) g).hom.app E) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((eqToHom (congrArg (modulePullback B S hS
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS)))
            (ObjectProperty.hom_ext _ hvh : CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS))
              (pointHom v) g = pointHom (X := X) (yoneda.map h ≫ u)))).app E))
      ((modulePullback B S hS (representedSpaceMap B S hS f')).map
          (eqToHom (modulePullback_obj_pointHom_representedSpaceMap_comp_eq X E u h)) ≫
        (modulePullback B S hS (representedSpaceMap B S hS f')).map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom u)).inv.app E) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f')
          (representedSpaceMap B S hS h)).hom.app ((modulePullback B S hS (pointHom u)).obj E)) =
      eqToHom (modulePullback_obj_pointTwoSpace_comp_comp_eq X E u h f') ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS f' ≫ representedSpaceMap B S hS h)
          (pointHom u)).inv.app E :=
  CategoryTheory.comp_eq_of_eq_comp_of_comp_comp_eq _ _ _ _ _ _
    (pointTwoSpaceCompIso_hom_comp_modulePullbackCompIso X E u g v h hvh f')
    (modulePullbackCompIso_inv_app_pointHom_comp_representedSpaceMap X E u h f')

end TwoSpace

end AlgebraicGeometry.Space

end
