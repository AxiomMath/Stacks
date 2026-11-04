module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.AmbientSolution

/-!
# Isomorphic flat deformations give isomorphic solutions

For a flat deformation `D = (f' : X' ⟶ Y', i : X ⟶ X')` of `f : X ⟶ Y` over the first order
thickening `Y ⊂ Y'`, `Deformation.ambientSolution` is the solution
`0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'} → 𝒪_X → 0` of the extension problem of [Stacks Project, Tag 0D17].
An isomorphism `e : X'_D ≅ X'_E` of deformations, over `Y'` and under `X`, induces
`e^♯ : i_E⁻¹𝒪_{X'_E} = i_D⁻¹e⁻¹𝒪_{X'_E} ⟶ i_D⁻¹𝒪_{X'_D}`, compatible with the reductions and with
the maps from the thickened base (Stacks 03G8); since the prescribed map `c` of the problem is
universal, it is an isomorphism of solutions. So the construction descends to a map from the
isomorphism classes of deformations to the isomorphism classes of solutions.

## Main definitions

* `classesMap`: the map from isomorphism classes of flat deformations of `f` to isomorphism
  classes of solutions of the extension problem, `[D] ↦ [Deformation.ambientSolution D]`.

## Main results

* `Deformation.isomorphic_ambientSolution_of_hom`: isomorphic deformations have isomorphic
  solutions.

## References
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}

/-- If `w = c ≫ m' ≫ n'`, `x ≫ y' = z ≫ F.map c` and `m ≫ y = y' ≫ F.map m'`, then
`x ≫ m ≫ y ≫ F.map n' = z ≫ F.map w`: the categorical shape of
`inverseImageStructureSheafMap_comp_comp`. -/
theorem comp_comp_aux {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒟 ⥤ 𝒞)
    {P₀ Q₀ R₀ : 𝒞} {E₁ E₂ E₃ O₁ : 𝒟}
    (x : P₀ ⟶ Q₀) (m : Q₀ ⟶ R₀) (y : R₀ ⟶ F.obj E₃) (y' : Q₀ ⟶ F.obj E₂) (z : P₀ ⟶ F.obj E₁)
    (c : E₁ ⟶ E₂) (m' : E₂ ⟶ E₃) (n' : E₃ ⟶ O₁) (w : E₁ ⟶ O₁)
    (hw : w = c ≫ m' ≫ n') (ha : x ≫ y' = z ≫ F.map c) (hn : m ≫ y = y' ≫ F.map m') :
    x ≫ m ≫ y ≫ F.map n' = z ≫ F.map w := by
  rw [hw, F.map_comp, F.map_comp, ← Category.assoc z, ← ha]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]

/-- For composable morphisms with `L₁ ≫ L₂ ≫ M₁ ≫ M₂ = R` and an endo-equality `r : A₄ = A₄`,
`(a ≫ q ≫ L₁ ≫ L₂) ≫ (eqToHom r ≫ M₁ ≫ M₂) = a ≫ q ≫ R`. -/
theorem eqToHom_chain_two {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : 𝒞} (a : A₀ ⟶ A₁)
    (q : A₁ ⟶ A₂) (L₁ : A₂ ⟶ A₃) (L₂ : A₃ ⟶ A₄) (r : A₄ = A₄) (M₁ : A₄ ⟶ A₅) (M₂ : A₅ ⟶ A₆)
    (R : A₂ ⟶ A₆) (h : L₁ ≫ L₂ ≫ M₁ ≫ M₂ = R) :
    (a ≫ q ≫ L₁ ≫ L₂) ≫ (eqToHom r ≫ M₁ ≫ M₂) = a ≫ q ≫ R := by
  subst h; simp

section Generic

variable {W X₁ X₂ : AlgebraicSpaces B S hS} (i : X ⟶ X₁) (e : X₁ ⟶ X₂) (g : X₂ ⟶ Y')

omit hZ in
/-- The inverse image along `i` of `(e ≫ g)^♯`, through Stacks 03G8, is the inverse image along
`i ≫ e` of `g^♯` followed by that along `i` of `e^♯`. -/
theorem inverseImageStructureSheafMap_comp_comp :
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS (i ≫ e) g).inv.app
        (smallEtaleRingedTopos B S hS Y').O ≫
      (smallEtaleInverseImageRing B S hS (i ≫ e)).map
        (smallEtaleRingedToposHom B S hS g).fSharpInverseImage ≫
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i e).inv.app
        (smallEtaleRingedTopos B S hS X₂).O ≫
      (smallEtaleInverseImageRing B S hS i).map
        (smallEtaleRingedToposHom B S hS e).fSharpInverseImage =
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i (e ≫ g)).inv.app
        (smallEtaleRingedTopos B S hS Y').O ≫
      (smallEtaleInverseImageRing B S hS i).map
        (smallEtaleRingedToposHom B S hS (e ≫ g)).fSharpInverseImage := by
  have hsh := smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS e g
  have hsh' : (smallEtaleRingedToposHom B S hS (e ≫ g)).fSharpInverseImage =
      (smallEtaleRingedToposHom_compInverseImageRingIso B S hS e g).inv.app
          (smallEtaleRingedTopos B S hS Y').O ≫
        (smallEtaleInverseImageRing B S hS e).map
          (smallEtaleRingedToposHom B S hS g).fSharpInverseImage ≫
        (smallEtaleRingedToposHom B S hS e).fSharpInverseImage := by
    rw [← hsh, Iso.inv_hom_id_app_assoc]
  exact comp_comp_aux (smallEtaleInverseImageRing B S hS i) _ _ _ _ _ _ _ _ _ hsh'
    (smallEtaleRingedToposHom_compInverseImageRingIso_inv_assoc B S hS i e g
      (smallEtaleRingedTopos B S hS Y').O)
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i e).inv.naturality
      (smallEtaleRingedToposHom B S hS g).fSharpInverseImage)

omit hZ in
/-- The base maps of two deformations related by an isomorphism `e`, through `e^♯`. -/
theorem ambientBaseMap_transport (f₀ : X ⟶ W) (t : W ⟶ Y') {iE : X ⟶ X₂} {fD : X₁ ⟶ Y'}
    (hiE : i ≫ e = iE) (hfD : e ≫ g = fD) (wE : f₀ ≫ t = iE ≫ g) (wD : f₀ ≫ t = i ≫ fD) :
    ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f₀ t).hom.app (smallEtaleRingedTopos
        B S hS Y').O ≫ eqToHom (inverseImage_congr wE (smallEtaleRingedTopos B S hS Y').O) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS iE g).inv.app
            (smallEtaleRingedTopos B S hS Y').O ≫
        (smallEtaleInverseImageRing B S hS iE).map (smallEtaleRingedToposHom B S hS
            g).fSharpInverseImage) ≫
      (eqToHom (congrArg (inverseImageStructureSheaf B S hS) hiE.symm) ≫
        inverseImageStructureSheafMap B S hS i e) =
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f₀ t).hom.app (smallEtaleRingedTopos B
        S hS Y').O ≫ eqToHom (inverseImage_congr wD (smallEtaleRingedTopos B S hS Y').O) ≫
        (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i fD).inv.app
            (smallEtaleRingedTopos B S hS Y').O ≫
        (smallEtaleInverseImageRing B S hS i).map (smallEtaleRingedToposHom B S hS
            fD).fSharpInverseImage := by
  subst hiE hfD
  exact eqToHom_chain_two _ _ _ _ _ _ _ _ (inverseImageStructureSheafMap_comp_comp i e g)

end Generic

namespace Deformation

variable {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)}

/-- **Isomorphic deformations have isomorphic solutions**: an isomorphism `e : D ⟶ E` induces
`e^♯ : i_E⁻¹𝒪_{X'_E} ⟶ i_D⁻¹𝒪_{X'_D}`, which is compatible with the reductions and with the maps
from the thickened base, hence an isomorphism of solutions since `c` is universal. -/
theorem isomorphic_ambientSolution_of_hom {D E : Deformation f} (e : D ⟶ E) :
    CompatibleFirstOrderThickening.Isomorphic.{u, u + 1, u, u, u + 1, u}
      (E.ambientSolution hZ) (D.ambientSolution hZ) :=
  isomorphic_of_hom_of_universal (cIsUniversal_problem hZ f)
    (eqToHom (congrArg (inverseImageStructureSheaf B S hS) e.compat.symm) ≫
      inverseImageStructureSheafMap B S hS D.i e.hom.hom)
    (by
      rw [ambientSolution_reduction, ambientSolution_reduction]
      exact (Category.assoc _ _ _).trans ((congrArg _
        (inverseImageStructureSheafMap_comp_structureSharpInverseImage B S hS D.i e.hom.hom)).trans
        (structureSharpInverseImage_eqToHom B S hS e.compat.symm)))
    (by
      rw [ambientSolution_baseMap, ambientSolution_baseMap]
      exact ambientBaseMap_transport D.i e.hom.hom E.f' f (subspaceInclusion B S hS Y' Z)
        e.compat e.hom_f' E.isPullback.w.symm D.isPullback.w.symm)

end Deformation

variable (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The map from isomorphism classes of flat deformations to isomorphism classes of
solutions**, `[D] ↦ [0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'} → 𝒪_X → 0]`. -/
def classesMap :
    Classes f → CompatibleFirstOrderThickening.IsomorphismClasses.{u, u + 1, u, u, u + 1, u}
      (problem f hZ) :=
  Quotient.lift (s := setoid f)
    (fun D => Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid.{u, u + 1, u, u, u + 1,
        u} _)
      (D.ambientSolution hZ))
    (fun _ _ ⟨e⟩ => Quotient.sound
      ((CompatibleFirstOrderThickening.isomorphicSetoid.{u, u + 1, u, u, u + 1, u} _).iseqv.symm
        (Deformation.isomorphic_ambientSolution_of_hom hZ e)))

/-- `classesMap` sends the class of a deformation `D` to the class of
`Deformation.ambientSolution D`. -/
theorem classesMap_mk (D : Deformation f) :
    classesMap hZ f (Quotient.mk (setoid f) D) =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid.{u, u + 1, u, u, u + 1, u} _)
          (D.ambientSolution hZ) :=
  rfl

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
