module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf.LiftSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf.ConormalRestriction

/-!
# The sheaf of lifts at all three conditions

This file proves that condition (3) of [Stacks, Tag 061A] is étale local, states it for
arbitrary closed subspaces together with its restriction stability, defines the rule of
[Stacks, Tag 061B] at all three conditions and proves that it is a sheaf, and that condition (3)
is vacuous when the conormal module of `Y ⊂ Y'` vanishes ([Stacks, Tag 061D]).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u v

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-! ### Locality of the equality of condition (3) along an étale covering -/

section ConormalLocality

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

variable {X' Y' W : AlgebraicSpaces C S hS}

/-- **The two sides of condition (3) agree after restriction along an étale restriction
edge, with the ambient algebraic spaces handed over in arguments.**  If the outer conormal map
upstairs factors through the restriction edge `cmR` as the inverse image of `cmU` (`hO`), the
structural map upstairs factors as the inverse image of `cmE` (`hGG`), the restriction edge is
invertible and the conormal condition holds upstairs (`hup`), then the two sides of the
conormal condition downstairs have the same inverse image along `r`. -/
theorem conormalMap_restriction_map_eq_of_heq
    (Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS)
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (pa : Z₁s ⟶ YHs) (qa : Z₂s ⟶ YHs)
    (hr : r ≫ p = q) (hpa : p ≫ α = pa) (hqa : r ≫ pa = qa)
    (MH : Modules.{u, u} C S hS YHs.1 YHs.2)
    (NG : Modules.{u, u} C S hS ZGs.1 ZGs.2)
    (M₂ : Modules.{u, u} C S hS Z₂s.1 Z₂s.2)
    (M₁ : Modules.{u, u} C S hS Z₁s.1 Z₁s.2)
    (A : (modulePullback C S hS α).obj MH ⟶ NG)
    (cmO : (modulePullback C S hS qa).obj MH ⟶ M₂)
    (cmG : (modulePullback C S hS q).obj NG ⟶ M₂)
    (cmR : (modulePullback C S hS r).obj M₁ ⟶ M₂) (hR : IsIso cmR)
    (cmU : (modulePullback C S hS pa).obj MH ⟶ M₁)
    (cmE : (modulePullback C S hS p).obj NG ⟶ M₁)
    (cp : (modulePullback C S hS pa).obj MH ⟶
      (modulePullback C S hS p).obj ((modulePullback C S hS α).obj MH))
    (cq : (modulePullback C S hS qa).obj MH ⟶
      (modulePullback C S hS q).obj ((modulePullback C S hS α).obj MH))
    (hcp : HEq cp ((modulePullbackCompIso C S hS p α).inv.app MH))
    (hcq : HEq cq ((modulePullbackCompIso C S hS q α).inv.app MH))
    (hO : cmO = (modulePullbackTriangle C S hS hqa).hom.app MH ≫
      (modulePullback C S hS r).map cmU ≫ cmR)
    (hGG : cmG = (modulePullbackTriangle C S hS hr).hom.app NG ≫
      (modulePullback C S hS r).map cmE ≫ cmR)
    (hup : cmO = cq ≫ (modulePullback C S hS q).map A ≫ cmG) :
    (modulePullback C S hS r).map cmU =
      (modulePullback C S hS r).map (cp ≫ (modulePullback C S hS p).map A ≫ cmE) := by
  have h := conormalMap_comp_restriction_chase_of_heq C S hS Z₂s Z₁s ZGs YHs r p q α pa qa hr hpa
    hqa MH NG M₂ M₁ A
    ((modulePullbackTriangle C S hS hqa).hom.app MH ≫
      (modulePullback C S hS r).map (cp ≫ (modulePullback C S hS p).map A ≫ cmE) ≫ cmR)
    cmG cmR (cp ≫ (modulePullback C S hS p).map A ≫ cmE) cmE cp cq hcp hcq rfl hGG rfl
  rw [← hup, hO] at h
  exact ((asIso cmR).cancel_iso_hom_right _ _).1
    ((((modulePullbackTriangle C S hS hqa).app MH).cancel_iso_hom_left _ _).1 h.symm)

variable {W₂ : AlgebraicSpaces C S hS}

/-- **Locality of the equality of condition (3) along an étale covering.**  Let `Z ⊆ X'` and
`ZH ⊆ Y'` be closed subspaces, `α : Z ⟶ ZH` an edge between them and
`A : α^*𝒞_{ZH/Y'} ⟶ 𝒞_{Z/X'}` a prescribed map.  If `(ψ i : W i ⟶ W)` is an étale covering and
for every `i` the morphism `ψ i ≫ a'` induces `A` on conormal modules over `ψ i ≫ φ`, then `a'`
induces `A` over `φ`. -/
theorem conormalMap_eq_of_isEtaleCovering (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZH) ⟶
      conormalModule C S hS X' Z)
    (a' : W ⟶ Y')
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ Z) ≫ a' =
      (preimageProjection C S hS φ Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH)
    {I : Type v} (Wi : I → AlgebraicSpaces C S hS) (ψ : ∀ i, Wi i ⟶ W)
    (hcov : IsEtaleCovering C S hS (fun i => (Wi i).1) (fun i => (ψ i).hom))
    (hsq₂ : ∀ i, subspaceInclusion C S hS (Wi i) (preimageSubspace C S hS (ψ i ≫ φ) Z) ≫
        ψ i ≫ a' =
      (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH)
    (hup : ∀ i, conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z) ZH (ψ i ≫ a')
        (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α) (hsq₂ i) =
      (modulePullbackCompIso C S hS (preimageProjection C S hS (ψ i ≫ φ) Z) α).inv.app
          (conormalModule C S hS Y' ZH) ≫
        (modulePullback C S hS (preimageProjection C S hS (ψ i ≫ φ) Z)).map A ≫
          conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z) Z (ψ i ≫ φ)
            (preimageProjection C S hS (ψ i ≫ φ) Z)
            (conormalEtaleRestrictionSquare C S hS (ψ i ≫ φ) Z)) :
    conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
        (preimageProjection C S hS φ Z ≫ α) hsq =
      (modulePullbackCompIso C S hS (preimageProjection C S hS φ Z) α).inv.app
          (conormalModule C S hS Y' ZH) ≫
        (modulePullback C S hS (preimageProjection C S hS φ Z)).map A ≫
          conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
            (preimageProjection C S hS φ Z)
            (conormalEtaleRestrictionSquare C S hS φ Z) := by
  have key := QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering.{u, v} C S hS
    (X := (⟨(Z.1.preimage φ.hom).toFunctor,
      (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS))
    (fun i => (⟨(Z.1.preimage (ψ i ≫ φ).hom).toFunctor,
      (isClosedSubspace_preimage C S hS (ψ i ≫ φ).hom Z.1 X'.2 (Wi i).2 Z.2).1⟩ :
      AlgebraicSpaces C S hS))
    (fun i => restrictionProjection C S hS (ψ i) φ Z)
    (isEtaleCovering_preimageProjection C S hS Wi ψ hcov (preimageSubspace C S hS φ Z))
    (h := fun i =>
    conormalMap_restriction_map_eq_of_heq C S hS
      (Z₂s := (⟨(Z.1.preimage (ψ i ≫ φ).hom).toFunctor,
        (isClosedSubspace_preimage C S hS (ψ i ≫ φ).hom Z.1 X'.2 (Wi i).2 Z.2).1⟩ :
        AlgebraicSpaces C S hS))
      (Z₁s := (⟨(Z.1.preimage φ.hom).toFunctor,
        (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS))
      (ZGs := (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))
      (YHs := (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
      (r := (restrictionProjection C S hS (ψ i) φ Z))
      (p := (preimageProjection C S hS φ Z))
      (q := (preimageProjection C S hS (ψ i ≫ φ) Z))
      (α := α)
      (pa := (preimageProjection C S hS φ Z ≫ α))
      (qa := (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α))
      (hr := (restrictionProjection_comp C S hS (ψ i) φ Z))
      (hpa := rfl)
      (hqa := (restrictionProjection_comp_assoc C S hS (ψ i) φ Z α))
      (MH := (conormalModule C S hS Y' ZH))
      (NG := (conormalModule C S hS X' Z))
      (M₂ := (conormalModule C S hS (Wi i) (preimageSubspace C S hS (ψ i ≫ φ) Z)))
      (M₁ := (conormalModule C S hS W (preimageSubspace C S hS φ Z)))
      (A := A)
      (cmO := (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z) ZH (ψ i ≫ a')
        (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α) (hsq₂ i)))
      (cmG := (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z) Z (ψ i ≫ φ)
        (preimageProjection C S hS (ψ i ≫ φ) Z)
        (conormalEtaleRestrictionSquare C S hS (ψ i ≫ φ) Z)))
      (cmR := (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z)
        (preimageSubspace C S hS φ Z) (ψ i) (restrictionProjection C S hS (ψ i) φ Z)
        (conormalEtaleRestrictionSquare C S hS (ψ i) (preimageSubspace C S hS φ Z))))
      (cmU := (conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
        (preimageProjection C S hS φ Z ≫ α) hsq))
      (cmE := (conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
        (preimageProjection C S hS φ Z) (conormalEtaleRestrictionSquare C S hS φ Z)))
      (cp := ((modulePullbackCompIso C S hS (preimageProjection C S hS φ Z) α).inv.app
        (conormalModule C S hS Y' ZH)))
      (cq := ((modulePullbackCompIso C S hS (preimageProjection C S hS (ψ i ≫ φ) Z) α).inv.app
        (conormalModule C S hS Y' ZH)))
      (hcp := HEq.rfl)
      (hcq := HEq.rfl)
      (hO := (conormalMap_comp_triangle_of_spaces C S hS (ψ i) a'
        (preimageSubspace C S hS (ψ i ≫ φ) Z) (preimageSubspace C S hS φ Z) ZH
        (restrictionProjection C S hS (ψ i) φ Z) (preimageProjection C S hS φ Z ≫ α)
        (conormalEtaleRestrictionSquare C S hS (ψ i) (preimageSubspace C S hS φ Z)) hsq
        (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α) (hsq₂ i)
        (⟨(Z.1.preimage (ψ i ≫ φ).hom).toFunctor,
          (isClosedSubspace_preimage C S hS (ψ i ≫ φ).hom Z.1 X'.2 (Wi i).2 Z.2).1⟩ :
          AlgebraicSpaces C S hS)
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS)
        (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
        (restrictionProjection C S hS (ψ i) φ Z) (preimageProjection C S hS φ Z ≫ α)
        (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α)
        (restrictionProjection_comp_assoc C S hS (ψ i) φ Z α)
        (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z)
          (preimageSubspace C S hS φ Z) (ψ i) (restrictionProjection C S hS (ψ i) φ Z)
          (conormalEtaleRestrictionSquare C S hS (ψ i) (preimageSubspace C S hS φ Z)))
        (conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
          (preimageProjection C S hS φ Z ≫ α) hsq)
        (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z) ZH (ψ i ≫ a')
          (preimageProjection C S hS (ψ i ≫ φ) Z ≫ α) (hsq₂ i))
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl))
      (hGG := (conormalMap_comp_triangle_of_spaces C S hS (ψ i) φ
        (preimageSubspace C S hS (ψ i ≫ φ) Z) (preimageSubspace C S hS φ Z) Z
        (restrictionProjection C S hS (ψ i) φ Z) (preimageProjection C S hS φ Z)
        (conormalEtaleRestrictionSquare C S hS (ψ i) (preimageSubspace C S hS φ Z))
        (conormalEtaleRestrictionSquare C S hS φ Z)
        (preimageProjection C S hS (ψ i ≫ φ) Z)
        (conormalEtaleRestrictionSquare C S hS (ψ i ≫ φ) Z)
        (⟨(Z.1.preimage (ψ i ≫ φ).hom).toFunctor,
          (isClosedSubspace_preimage C S hS (ψ i ≫ φ).hom Z.1 X'.2 (Wi i).2 Z.2).1⟩ :
          AlgebraicSpaces C S hS)
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS)
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
        (restrictionProjection C S hS (ψ i) φ Z) (preimageProjection C S hS φ Z)
        (preimageProjection C S hS (ψ i ≫ φ) Z) (restrictionProjection_comp C S hS (ψ i) φ Z)
        (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z)
          (preimageSubspace C S hS φ Z) (ψ i) (restrictionProjection C S hS (ψ i) φ Z)
          (conormalEtaleRestrictionSquare C S hS (ψ i) (preimageSubspace C S hS φ Z)))
        (conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
          (preimageProjection C S hS φ Z) (conormalEtaleRestrictionSquare C S hS φ Z))
        (conormalMap C S hS (preimageSubspace C S hS (ψ i ≫ φ) Z) Z (ψ i ≫ φ)
          (preimageProjection C S hS (ψ i ≫ φ) Z)
          (conormalEtaleRestrictionSquare C S hS (ψ i ≫ φ) Z))
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl))
      (hR := isIso_conormalMap_of_isEtale C S hS (ψ i) (hcov.etale i) (preimageSubspace C S hS φ Z))
      (hup := hup i))
  exact key

end ConormalLocality

/-- **The commutativity of the restricted square, in a bare category.**  The square of the
inverse image along a composite commutes as soon as the two squares it is pasted from do. -/
private theorem comp_eq_of_restricted_square {𝓓 : Type*} {_ : Category 𝓓}
    {P Q R Z₁s T Hs : 𝓓}
    (i₂ : P ⟶ Q) (ψ : Q ⟶ R) (a' : R ⟶ T) (r : P ⟶ Z₁s) (i₁ : Z₁s ⟶ R)
    (pa : Z₁s ⟶ Hs) (iH : Hs ⟶ T) (qa : P ⟶ Hs)
    (h1 : i₂ ≫ ψ = r ≫ i₁) (h2 : i₁ ≫ a' = pa ≫ iH) (h3 : r ≫ pa = qa) :
    i₂ ≫ ψ ≫ a' = qa ≫ iH := by
  rw [← h3, ← Category.assoc, h1, Category.assoc, h2, Category.assoc]

/-! ### Condition (3) at closed subspaces, and its restriction stability -/

section ConormalSubspaceCondition

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

variable {X' Y' W₂ W : AlgebraicSpaces C S hS}

/-- **The square of condition (3) restricts, for a pair of closed subspaces.**  If the square of
inclusions over `a' : W ⟶ Y'` commutes above `φ : W ⟶ X'` for an edge `α : Z ⟶ ZH` between
closed subspaces `Z ⊆ X'` and `ZH ⊆ Y'`, then the square above `ψ ≫ φ` commutes over `ψ ≫ a'`:
the inverse image of `Z` along `ψ ≫ φ` is the inverse image along `ψ` of the one along `φ`, and
the two squares paste. -/
theorem preimageSquare_comp (ψ : W₂ ⟶ W) (φ : W ⟶ X') (a' : W ⟶ Y')
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ Z) ≫ a' =
      (preimageProjection C S hS φ Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH) :
    subspaceInclusion C S hS W₂ (preimageSubspace C S hS (ψ ≫ φ) Z) ≫ ψ ≫ a' =
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH :=
  comp_eq_of_restricted_square
    (subspaceInclusion C S hS W₂ (preimageSubspace C S hS (ψ ≫ φ) Z)) ψ a'
    (preimageProjection C S hS ψ (preimageSubspace C S hS φ Z))
    (subspaceInclusion C S hS W (preimageSubspace C S hS φ Z))
    (preimageProjection C S hS φ Z ≫ α)
    (subspaceInclusion C S hS Y' ZH) (preimageProjection C S hS (ψ ≫ φ) Z ≫ α)
    (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)) hsq
    (Category.assoc _ _ _).symm

/-- **The condition (3) of [Stacks, Tag 061A], for a pair of closed subspaces.**  Let `Z ⊆ X'`
and `ZH ⊆ Y'` be closed subspaces, `α : Z ⟶ ZH` an edge between them and
`A : α^*𝒞_{ZH/Y'} ⟶ 𝒞_{Z/X'}` a prescribed map of `𝒪_Z`-modules.  A morphism `a' : W ⟶ Y'`
satisfies the conormal condition over `φ : W ⟶ X'` when the square of inclusions
```
φ⁻¹(Z) ⟶ W
  |       |
  |       | a'
  v       v
  ZH ⟶   Y'
```
whose left-hand morphism is the projection of `φ⁻¹(Z)` to `Z` followed by `α`, commutes, and the
canonical map of conormal modules of [Stacks, Tag 04CP] attached to that square is the inverse
image of `A` along the projection, read into `𝒞_{φ⁻¹(Z)/W}` by the same canonical map taken at
the square of `φ` itself.

The source's condition is the case `Z := ⟨G, hG.1⟩`, `ZH := ⟨H, hH.1⟩` and `α := a` for the two
thickenings, the prescribed `a` and the prescribed `A`, with `φ` the structure morphism
`U' ⟶ X'`. -/
structure IsConormalLiftAtSubspace (Z : ClosedSubspaces C S hS X'.1)
    (ZH : ClosedSubspaces C S hS Y'.1)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZH) ⟶
      conormalModule C S hS X' Z)
    (φ : W ⟶ X') (a' : W ⟶ Y') : Prop where
  /-- The square of inclusions over `a'` above `φ` commutes. -/
  square : subspaceInclusion C S hS W (preimageSubspace C S hS φ Z) ≫ a' =
    (preimageProjection C S hS φ Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH
  /-- The canonical map of conormal modules of that square is the inverse image of `A`. -/
  conormal : conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
        (preimageProjection C S hS φ Z ≫ α) square =
      (modulePullbackCompIso C S hS (preimageProjection C S hS φ Z) α).inv.app
          (conormalModule C S hS Y' ZH) ≫
        (modulePullback C S hS (preimageProjection C S hS φ Z)).map A ≫
          conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
            (preimageProjection C S hS φ Z)
            (conormalEtaleRestrictionSquare C S hS φ Z)

/-- **Restriction stability of condition (3) of [Stacks, Tag 061A], for a pair of closed
subspaces.**  If `a' : W ⟶ Y'` induces the prescribed map `A` on conormal modules over
`φ : W ⟶ X'`, then `ψ ≫ a'` induces `A` over `ψ ≫ φ`, for every `ψ : W₂ ⟶ W`. -/
theorem IsConormalLiftAtSubspace.comp (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZH) ⟶
      conormalModule C S hS X' Z)
    (a' : W ⟶ Y') (h : IsConormalLiftAtSubspace C S hS Z ZH α A φ a') :
    IsConormalLiftAtSubspace C S hS Z ZH α A (ψ ≫ φ) (ψ ≫ a') where
  square := preimageSquare_comp C S hS ψ φ a' Z ZH α h.square
  conormal := conormalMap_comp_restriction C S hS ψ φ Z ZH α A a' h.square
    (preimageSquare_comp C S hS ψ φ a' Z ZH α h.square) h.conormal

/-- **Condition (3) of [Stacks, Tag 061A] is étale local, for a pair of closed subspaces.**  If
`(ψ i : W i ⟶ W)` is an étale covering, the square of inclusions over `a'` above `φ` commutes,
and every `ψ i ≫ a'` induces the prescribed `A` over `ψ i ≫ φ`, then `a'` induces `A` over `φ`. -/
theorem IsConormalLiftAtSubspace.of_isEtaleCovering (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZH) ⟶
      conormalModule C S hS X' Z)
    (a' : W ⟶ Y')
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ Z) ≫ a' =
      (preimageProjection C S hS φ Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH)
    {I : Type v} (Wi : I → AlgebraicSpaces C S hS) (ψ : ∀ i, Wi i ⟶ W)
    (hcov : IsEtaleCovering C S hS (fun i => (Wi i).1) (fun i => (ψ i).hom))
    (h : ∀ i, IsConormalLiftAtSubspace C S hS Z ZH α A (ψ i ≫ φ) (ψ i ≫ a')) :
    IsConormalLiftAtSubspace C S hS Z ZH α A φ a' where
  square := hsq
  conormal := conormalMap_eq_of_isEtaleCovering C S hS φ Z ZH α A a' hsq Wi ψ hcov
    (fun i => (h i).square) (fun i => (h i).conormal)

end ConormalSubspaceCondition

section ConormalSubspaceThickening

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

variable {X' Y' W₂ W : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
variable (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)

/-- **Restriction stability of condition (3) of [Stacks, Tag 061A], at the two thickenings of
this file.**  This is `AlgebraicGeometry.Space.IsConormalLiftAtSubspace.comp` at
`Z := ⟨G, hG.1⟩`, `ZH := ⟨H, hH.1⟩` and `α := a`, for the prescribed map `a : X ⟶ Y` between the
two closed subspaces underlying the thickenings and a prescribed `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}`. -/
theorem IsConormalLiftAtSubspace.comp_of_isThickening
    (A : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
      conormalModule C S hS X' ⟨G, hG.1⟩)
    (ψ : W₂ ⟶ W) (φ : W ⟶ X') (a' : W ⟶ Y')
    (h : IsConormalLiftAtSubspace C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A φ a') :
    IsConormalLiftAtSubspace C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A (ψ ≫ φ) (ψ ≫ a') :=
  IsConormalLiftAtSubspace.comp C S hS ψ φ ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A a' h

end ConormalSubspaceThickening

/-! ### The rule of the source at all three of its conditions -/

section ConormalLiftRule

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
variable (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)
  (A : (modulePullback C S hS a).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
    conormalModule C S hS X' ⟨G, hG.1⟩)

/-- **The rule of lifts satisfying conditions (1), (2) and (3).** Let `X ⊂ X'` and `Y ⊂ Y'` be
thickenings of algebraic spaces over a base `T`, let `a : X ⟶ Y` be a morphism and let
`A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules. The rule sending an algebraic space
`U'` étale over `X'` to the set of morphisms `a' : U' ⟶ Y'` such that
1. `a'` is a morphism over `T`,
2. `a'|_U = a|_U` on `U = X ×_{X'} U'`, and
3. the map `a^*𝒞_{Y/Y'}|_U ⟶ 𝒞_{X/X'}|_U` induced by `a'` is the restriction of `A` to `U`,

as a subfunctor of the presheaf of morphisms into `Y'` on the spaces-étale site of `X'`, with
restriction along `V' ⟶ U'` given by `a' ↦ a'|_{V'}`.

Conditions (1) and (2) are `AlgebraicGeometry.Space.IsLiftOver`, the membership condition of
`AlgebraicGeometry.Space.liftSubfunctor`, and condition (3) is
`AlgebraicGeometry.Space.IsConormalLiftAtSubspace` at the two closed subspaces underlying the
thickenings, the prescribed `a` and the prescribed `A`, over the structure morphism `U' ⟶ X'`.

No hypothesis is placed on the thickenings, on `a` or on `A`; in particular the conormal module
of `Y ⊂ Y'` is not assumed to vanish. -/
@[stacks 061B "the rule U' ↦ {a' : U' → Y' satisfying (1), (2), (3)}, as a subfunctor of the \
presheaf of morphisms into Y' on the spaces-étale site of X', for arbitrary thickenings, a and A"]
def conormalLiftSubfunctor : Subfunctor (spacesEtaleHomPresheaf C S hS X' Y') where
  obj U' := {a' | IsLiftOver C S hS hG hH pX' pY' a (unop U') a' ∧
    IsConormalLiftAtSubspace C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A
      ((SpacesEtale.inclusion C S hS X').obj (unop U')).hom a'}
  map {U' V'} k a' ha' := by
    refine ⟨(liftSubfunctor C S hS hG hH pX' pY' a).map k ha'.1, ?_⟩
    have h := IsConormalLiftAtSubspace.comp_of_isThickening C S hS hG hH a A
      ((SpacesEtale.toSpaces C S hS X').map k.unop) _ a' ha'.2
    rw [SpacesEtale.toSpaces_map_comp_structure C S hS X' k.unop] at h
    exact h

/-- Every section of the rule of [Stacks, Tag 061B] is a lift in the sense of conditions (1)
and (2): the three-condition rule is a subfunctor of `AlgebraicGeometry.Space.liftSubfunctor`. -/
theorem conormalLiftSubfunctor_le_liftSubfunctor :
    conormalLiftSubfunctor C S hS hG hH pX' pY' a A ≤ liftSubfunctor C S hS hG hH pX' pY' a :=
  fun _ _ h => h.1

/-- **Condition (3) is vacuous when the conormal module of the target vanishes.** When
`𝒞_{Y/Y'}` vanishes, condition (3) holds for every lift in the sense of conditions (1) and (2),
whatever the prescribed `A` is, and the rule of [Stacks, Tag 061B] is
`AlgebraicGeometry.Space.liftSubfunctor`. -/
theorem conormalLiftSubfunctor_eq_liftSubfunctor_of_isZero
    (hzero : IsZero (conormalModule C S hS Y' ⟨H, hH.1⟩)) :
    conormalLiftSubfunctor C S hS hG hH pX' pY' a A = liftSubfunctor C S hS hG hH pX' pY' a := by
  refine le_antisymm (conormalLiftSubfunctor_le_liftSubfunctor C S hS hG hH pX' pY' a A) ?_
  intro U' a' h
  have hsq := preimageSquare_of_isLiftOver C S hS hG hH pX' pY' a (unop U') a' h
  refine ⟨h, hsq, ?_⟩
  have hadd := modulePullback_additive (preimageProjection C S hS
    ((SpacesEtale.inclusion C S hS X').obj (unop U')).hom ⟨G, hG.1⟩ ≫ a)
  exact (@Functor.map_isZero _ _ _ _ _ _ _
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ hadd) _ hzero).eq_of_src _ _

/-- For `Y = Y'` the rule of [Stacks, Tag 061A] is just the rule
`U' ↦ {a' : U' ⟶ Y' over T with a'|_U = a|_U}`: condition (3) is vacuous, the map `A` being always
zero. -/
@[stacks 061D "for Y = Y' the rule of 061A is the rule U' ↦ {a' : U' → Y over B with \
a'|_U = a|_U}, condition (3) being vacuous"]
theorem conormalLiftSubfunctor_eq_liftSubfunctor_of_eq_top (hHtop : H = ⊤) :
    conormalLiftSubfunctor C S hS hG hH pX' pY' a A = liftSubfunctor C S hS hG hH pX' pY' a := by
  subst hHtop
  exact conormalLiftSubfunctor_eq_liftSubfunctor_of_isZero C S hS hG hH pX' pY' a A
    (isZero_conormalModule_top C S hS Y')

/-- **Condition (3) is étale local.**  Let `(f i : U'ᵢ ⟶ U')` be a covering family of the
spaces-étale site of `X'` and `a' : U' ⟶ Y'` a lift in the sense of conditions (1) and (2).  If
every restriction `a'|_{U'ᵢ}` satisfies condition (3), then so does `a'`. -/
theorem isConormalLiftAtSubspace_of_isEtaleCovering {U' : SpacesEtale C S hS X'}
    {I : Type (u + 1)} (Xi : I → SpacesEtale C S hS X') (f : ∀ i, Xi i ⟶ U')
    (hcov : IsEtaleCovering C S hS (fun i => ((SpacesEtale.toSpaces C S hS X').obj (Xi i)).1)
      (fun i => ((SpacesEtale.toSpaces C S hS X').map (f i)).hom))
    (a' : (SpacesEtale.toSpaces C S hS X').obj U' ⟶ Y')
    (ha' : IsLiftOver C S hS hG hH pX' pY' a U' a')
    (hi : ∀ i, IsConormalLiftAtSubspace C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A
      ((SpacesEtale.inclusion C S hS X').obj (Xi i)).hom
      ((SpacesEtale.toSpaces C S hS X').map (f i) ≫ a')) :
    IsConormalLiftAtSubspace C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A
      ((SpacesEtale.inclusion C S hS X').obj U').hom a' := by
  have hi' : ∀ i, IsConormalLiftAtSubspace C S hS ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A
      ((SpacesEtale.toSpaces C S hS X').map (f i) ≫
        ((SpacesEtale.inclusion C S hS X').obj U').hom)
      ((SpacesEtale.toSpaces C S hS X').map (f i) ≫ a') := fun i => by
    rw [SpacesEtale.toSpaces_map_comp_structure C S hS X' (f i)]
    exact hi i
  exact IsConormalLiftAtSubspace.of_isEtaleCovering C S hS
    ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ⟨H, hH.1⟩ a A a'
    (preimageSquare_of_isLiftOver C S hS hG hH pX' pY' a U' a' ha')
    (fun i => (SpacesEtale.toSpaces C S hS X').obj (Xi i))
    (fun i => (SpacesEtale.toSpaces C S hS X').map (f i)) hcov hi'

/-- The rule of [Stacks, Tag 061B] — `U' ↦ {a' : U' ⟶ Y'}` satisfying (1) `a'` is a morphism
over `T`, (2) `a'|_U = a|_U` and (3) the map `a^*𝒞_{Y/Y'}|_U ⟶ 𝒞_{X/X'}|_U` induced by `a'` is
the restriction of `A` — is a sheaf of sets on the spaces-étale site of `X'`, for arbitrary
thickenings `X ⊂ X'`, `Y ⊂ Y'`, an arbitrary morphism `a` and an arbitrary map `A`. -/
@[stacks 061A "the sheaf property of the rule 061B with all three conditions"]
theorem isSheaf_conormalLiftSubfunctor :
    Presieve.IsSheaf (SpacesEtale.topology C S hS X')
      (conormalLiftSubfunctor C S hS hG hH pX' pY' a A).toFunctor := by
  have hF := isSheaf_spacesEtaleHomPresheaf C S hS X' Y'
  have hL := isSheaf_liftSubfunctor C S hS hG hH pX' pY' a
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hF hL ⊢
  intro V R hR
  have hFR := hF R hR
  have hLR := hL R hR
  obtain ⟨E, rfl, hE⟩ := hR
  let L := conormalLiftSubfunctor C S hS hG hH pX' pY' a A
  have hle := conormalLiftSubfunctor_le_liftSubfunctor C S hS hG hH pX' pY' a A
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono L.ι hFR.isSeparatedFor, fun x hx => ?_⟩
  obtain ⟨t, ht, -⟩ := hFR (x.map L.ι) (hx.map L.ι)
  obtain ⟨t', ht', -⟩ := hLR (x.map (Subfunctor.homOfLe hle)) (hx.map _)
  have htt : t'.1 = t := hFR.isSeparatedFor (x.map L.ι) t'.1 t
    (fun W r hr => congrArg Subtype.val (ht' r hr)) ht
  have hlift : IsLiftOver C S hS hG hH pX' pY' a V t := htt ▸ t'.2
  refine ⟨⟨t, hlift, isConormalLiftAtSubspace_of_isEtaleCovering C S hS hG hH pX' pY' a A
    E.X E.f (SpacesEtale.isEtaleCovering_of_isCovering C S hS X' E.X E.f hE) t hlift
    fun i => ?_⟩, .of_mono _ ht⟩
  have hti : (SpacesEtale.toSpaces C S hS X').map (E.f i) ≫ t =
      (x (E.f i) (Presieve.ofArrows.mk i)).1 := ht (E.f i) (Presieve.ofArrows.mk i)
  rw [hti]
  exact (x (E.f i) (Presieve.ofArrows.mk i)).2.2

end ConormalLiftRule

end AlgebraicGeometry.Space

end
