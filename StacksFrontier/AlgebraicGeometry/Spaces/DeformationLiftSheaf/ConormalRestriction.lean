module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# Restriction stability of the conormal condition (3)

This file proves that the canonical conormal map of [Stacks, Tag 04CP] is compatible with
restriction along a further morphism, which gives the restriction stability of condition (3) of
[Stacks, Tag 061A], and studies the inverse image of a closed subspace along an étale morphism:
its cartesian square, the invertibility of its conormal map and the covering its projections
form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u v

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-! ### Restriction stability of the conormal condition (3) -/

section Restriction

/-- **The algebra of the chase, in a bare pair of categories.**  Given the composition law of
the outer rectangle (`h1`), the conormal condition downstairs (`h2`), the composition law of the
lower stack (`h3`), the naturality of the splitting comparison at the prescribed map (`h4`) and
the head relation (`h5`), the conormal condition upstairs follows. -/
private theorem comp_eq_of_restriction_paste {𝓓 𝓔 : Type*} {_ : Category 𝓓} {_ : Category 𝓔}
    (F : 𝓓 ⥤ 𝓔) {P P₁ P₂ P₃ : 𝓓} {Q Q₁ Q₂ R : 𝓔}
    (cmO : Q ⟶ R) (Dinv : Q ⟶ Q₁) (aq : Q₁ ⟶ Q₂) (cmG : Q₂ ⟶ R)
    (t : Q ⟶ F.obj P) (n : Q₁ ⟶ F.obj P₁) (s : Q₂ ⟶ F.obj P₂) (w : F.obj P₃ ⟶ R)
    (u : P ⟶ P₃) (c : P ⟶ P₁) (d : P₁ ⟶ P₂) (e : P₂ ⟶ P₃)
    (h1 : cmO = t ≫ F.map u ≫ w) (h2 : u = c ≫ d ≫ e)
    (h3 : cmG = s ≫ F.map e ≫ w) (h4 : aq ≫ s = n ≫ F.map d)
    (h5 : t ≫ F.map c = Dinv ≫ n) :
    cmO = Dinv ≫ aq ≫ cmG := by
  subst h1
  subst h2
  subst h3
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h4, ← Category.assoc, h5, Category.assoc]

/-- **The comparison of [Stacks, Tag 03LU] is the equation-indexed comparison at `rfl`.**  This
is `AlgebraicGeometry.Space.modulePullbackTriangle_rfl` read at a single module. -/
theorem modulePullbackTriangle_rfl_hom_app {V U Z : AlgebraicSpaces C S hS} (f : V ⟶ U)
    (g : U ⟶ Z) (M : Modules.{u, u} C S hS Z.1 Z.2) :
    (modulePullbackTriangle C S hS (rfl : f ≫ g = f ≫ g)).hom.app M =
      (modulePullbackCompIso C S hS f g).inv.app M :=
  congrArg (fun i : modulePullback C S hS (f ≫ g) ≅
      modulePullback C S hS g ⋙ modulePullback C S hS f => i.hom.app M)
    (modulePullbackTriangle_rfl f g)

/-- **The head relation of the restriction chase, with all four edges indexed by equations.**
For `r`, `p`, `α` composable and `q`, `pa`, `qa` morphisms with `r ≫ p = q`, `p ≫ α = pa`,
`r ≫ pa = qa` and `q ≫ α = qa`, the comparison along the outer lower edge followed by the
inverse image along `r` of the comparison along the lower edge downstairs is the comparison of
the outer rectangle followed by the comparison of the structural factorisation. -/
theorem modulePullbackTriangle_hom_app_comp
    (Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS)
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (pa : Z₁s ⟶ YHs) (qa : Z₂s ⟶ YHs)
    (hr : r ≫ p = q) (hpa : p ≫ α = pa) (hqa : r ≫ pa = qa) (hQA : q ≫ α = qa)
    (M : Modules.{u, u} C S hS YHs.1 YHs.2) :
    (modulePullbackTriangle C S hS hqa).hom.app M ≫
        (modulePullback C S hS r).map ((modulePullbackTriangle C S hS hpa).hom.app M) =
      (modulePullbackTriangle C S hS hQA).hom.app M ≫
        (modulePullbackTriangle C S hS hr).hom.app ((modulePullback C S hS α).obj M) :=
  Iso.inv_comp_inv_eq
    ((modulePullback C S hS r).mapIso ((modulePullbackTriangle C S hS hpa).app M)).symm
    ((modulePullbackTriangle C S hS hqa).app M).symm
    ((modulePullbackTriangle C S hS hr).app ((modulePullback C S hS α).obj M)).symm
    ((modulePullbackTriangle C S hS hQA).app M).symm
    (modulePullbackTriangle_inv_app_assoc C S hS hr hpa hqa hQA M)

/-- **The head relation of the restriction chase.**  For three composable morphisms
`r`, `p`, `α` of algebraic spaces, the comparison of [Stacks, Tag 03LU] along `r ≫ p` followed
by the splitting comparison of the two lower edges is the comparison of the triple composite
followed by the inverse image along `r` of the comparison along `p`. -/
theorem modulePullbackTriangle_hom_app_compIso_inv_app
    (Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS)
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (hq : r ≫ p = q) (hqα : r ≫ p ≫ α = q ≫ α)
    (M : Modules.{u, u} C S hS YHs.1 YHs.2) :
    (modulePullbackTriangle C S hS hqα).hom.app M ≫
        (modulePullback C S hS r).map ((modulePullbackCompIso C S hS p α).inv.app M) =
      (modulePullbackCompIso C S hS q α).inv.app M ≫
        (modulePullbackTriangle C S hS hq).hom.app ((modulePullback C S hS α).obj M) := by
  rw [← modulePullbackTriangle_rfl_hom_app C S hS p α M,
    ← modulePullbackTriangle_rfl_hom_app C S hS q α M]
  exact modulePullbackTriangle_hom_app_comp C S hS Z₂s Z₁s ZGs YHs r p q α (p ≫ α) (q ≫ α)
    hq rfl hqα rfl M

/-- **The chase of restriction stability of condition (3), with the four ambient algebraic spaces
handed over in arguments.**  Let `r`, `p`, `q`, `α` be morphisms of algebraic spaces with
`r ≫ p = q`, let `A` be a morphism of modules over the target of `p`, and let `cmO`, `cmG`,
`cmR`, `cmU`, `cmE` be the five canonical maps of [Stacks, Tag 04CP] that condition (3) of
[Stacks, Tag 061A] compares — the two over the upper space, the one of the restriction edge and
the two over the lower space.  If the outer map and the structural map upstairs both factor
through the restriction edge (`hO`, `hGG`), and the outer map downstairs is the inverse image of
`A` read through the comparison of [Stacks, Tag 03LU] (`hU`), then so is the outer map upstairs. -/
theorem conormalMap_comp_restriction_chase_of_spaces
    (Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS)
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (hr : r ≫ p = q) (hrα : r ≫ p ≫ α = q ≫ α)
    (MH : Modules.{u, u} C S hS YHs.1 YHs.2)
    (NG : Modules.{u, u} C S hS ZGs.1 ZGs.2)
    (M₂ : Modules.{u, u} C S hS Z₂s.1 Z₂s.2)
    (M₁ : Modules.{u, u} C S hS Z₁s.1 Z₁s.2)
    (A : (modulePullback C S hS α).obj MH ⟶ NG)
    (cmO : (modulePullback C S hS (q ≫ α)).obj MH ⟶ M₂)
    (cmG : (modulePullback C S hS q).obj NG ⟶ M₂)
    (cmR : (modulePullback C S hS r).obj M₁ ⟶ M₂)
    (cmU : (modulePullback C S hS (p ≫ α)).obj MH ⟶ M₁)
    (cmE : (modulePullback C S hS p).obj NG ⟶ M₁)
    (hO : cmO = (modulePullbackTriangle C S hS hrα).hom.app MH ≫
      (modulePullback C S hS r).map cmU ≫ cmR)
    (hGG : cmG = (modulePullbackTriangle C S hS hr).hom.app NG ≫
      (modulePullback C S hS r).map cmE ≫ cmR)
    (hU : cmU = (modulePullbackCompIso C S hS p α).inv.app MH ≫
      (modulePullback C S hS p).map A ≫ cmE) :
    cmO = (modulePullbackCompIso C S hS q α).inv.app MH ≫
      (modulePullback C S hS q).map A ≫ cmG :=
  comp_eq_of_restriction_paste (modulePullback C S hS r) _ _ _ _ _ _ _ _ _ _ _ _ hO hU hGG
    ((modulePullbackTriangle C S hS hr).hom.naturality A)
    (modulePullbackTriangle_hom_app_compIso_inv_app C S hS Z₂s Z₁s ZGs YHs r p q α hr hrα MH)

section Chase

variable {X' Y' : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}

/-- **The chase of restriction stability of condition (3) of [Stacks, Tag 061A].**  For the two
nested inverse images of the thickening — `φ⁻¹(X) ⊆ W` and `(ψ ≫ φ)⁻¹(X) ⊆ W₂` — the conormal
condition over `ψ ≫ φ` follows from the conormal condition over `φ`, given the head relation of
the two splitting comparisons at the prescribed map. -/
theorem conormalMap_comp_restriction_chase (hG : IsThickening C S hS X' G)
    (hH : IsThickening C S hS Y' H)
    {W₂ W : AlgebraicSpaces C S hS} (ψ : W₂ ⟶ W) (φ : W ⟶ X') (a' : W ⟶ Y')
    (r : (⟨(preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).1.toFunctor,
        (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).2.1⟩ :
        AlgebraicSpaces C S hS) ⟶
      (⟨(preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).1.toFunctor,
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).2.1⟩ :
        AlgebraicSpaces C S hS))
    (p : (⟨(preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).1.toFunctor,
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).2.1⟩ :
        AlgebraicSpaces C S hS) ⟶
      (⟨(⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.toFunctor,
        (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2.1⟩ : AlgebraicSpaces C S hS))
    (q : (⟨(preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).1.toFunctor,
        (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).2.1⟩ :
        AlgebraicSpaces C S hS) ⟶
      (⟨(⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.toFunctor,
        (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2.1⟩ : AlgebraicSpaces C S hS))
    (pa : (⟨(preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).1.toFunctor,
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).2.1⟩ :
        AlgebraicSpaces C S hS) ⟶
      (⟨(⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).1.toFunctor,
        (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).2.1⟩ : AlgebraicSpaces C S hS))
    (qa : (⟨(preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).1.toFunctor,
        (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)).2.1⟩ :
        AlgebraicSpaces C S hS) ⟶
      (⟨(⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).1.toFunctor,
        (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1).2.1⟩ : AlgebraicSpaces C S hS))
    (hr : r ≫ p = q) (hqa : r ≫ pa = qa)
    (N : Modules.{u, u} C S hS
      (⟨(⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.toFunctor,
        (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2.1⟩ : AlgebraicSpaces C S hS).1
      (⟨(⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).1.toFunctor,
        (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1).2.1⟩ : AlgebraicSpaces C S hS).2)
    (A : N ⟶ (conormalModule C S hS X' ⟨G, hG.1⟩))
    (hψ : subspaceInclusion C S hS W₂
        (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)) ≫ ψ =
      r ≫ subspaceInclusion C S hS W
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)))
    (hφ : subspaceInclusion C S hS W
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)) ≫ φ =
      p ≫ subspaceInclusion C S hS X' ⟨G, hG.1⟩)
    (hφ₂ : subspaceInclusion C S hS W₂
        (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)) ≫ ψ ≫ φ =
      q ≫ subspaceInclusion C S hS X' ⟨G, hG.1⟩)
    (hsq : subspaceInclusion C S hS W
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)) ≫ a' =
      pa ≫ subspaceInclusion C S hS Y' ⟨H, hH.1⟩)
    (hsq₂ : subspaceInclusion C S hS W₂
        (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)) ≫ ψ ≫ a' =
      qa ≫ subspaceInclusion C S hS Y' ⟨H, hH.1⟩)
    (cp : (modulePullback C S hS pa).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
      (modulePullback C S hS p).obj N)
    (cq : (modulePullback C S hS qa).obj (conormalModule C S hS Y' ⟨H, hH.1⟩) ⟶
      (modulePullback C S hS q).obj N)
    (hhead : (modulePullbackTriangle C S hS hqa).hom.app (conormalModule C S hS Y' ⟨H, hH.1⟩) ≫
          (modulePullback C S hS r).map cp =
        cq ≫ (modulePullbackTriangle C S hS hr).hom.app N)
    (heq : conormalMap C S hS (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
      (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1) a' pa hsq =
      cp ≫ (modulePullback C S hS p).map A ≫ conormalMap C S hS
        (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
        (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1) φ p hφ) :
    conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
      (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1) (ψ ≫ a') qa hsq₂ =
      cq ≫ (modulePullback C S hS q).map A ≫
        conormalMap C S hS
          (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
          (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1) (ψ ≫ φ) q hφ₂ :=
  comp_eq_of_restriction_paste (modulePullback C S hS r) _ _ _ _ _ _ _ _ _ _ _ _
    (conormalMap_comp_triangle C S hS ψ a'
      (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
      (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
      (⟨H, hH.1⟩ : ClosedSubspaces C S hS Y'.1) r pa hψ hsq qa hqa hsq₂)
    heq
    (conormalMap_comp_triangle C S hS ψ φ
      (preimageSubspace C S hS (ψ ≫ φ) (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
      (preimageSubspace C S hS φ (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1))
      (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1) r p hψ hφ q hr hφ₂)
    ((modulePullbackTriangle C S hS hr).hom.naturality A)
    hhead

end Chase

end Restriction

/-! ### The inverse image of a closed subspace along an étale covering -/

section PreimageCovering

variable {V U : AlgebraicSpaces C S hS}

/-- The inverse image of a closed subspace of `U` along `ψ : V ⟶ U`, as an algebraic space
over `S`: the source of `AlgebraicGeometry.Space.preimageProjection`. -/
noncomputable abbrev preimageSpace (ψ : V ⟶ U) (Z : ClosedSubspaces C S hS U.1) :
    AlgebraicSpaces C S hS :=
  ⟨(Z.1.preimage ψ.hom).toFunctor,
    (isClosedSubspace_preimage C S hS ψ.hom Z.1 U.2 V.2 Z.2).1⟩

/-- **The square of [Stacks, Tag 09ZX] is cartesian in algebraic spaces.** The inclusion of the
inverse image `ψ⁻¹(Z)` into `V` and its projection to `Z` exhibit `ψ⁻¹(Z)` as the fibre product
`Z ×_U V`. -/
theorem isPullback_preimageProjection (ψ : V ⟶ U) (Z : ClosedSubspaces C S hS U.1) :
    IsPullback (preimageProjection C S hS ψ Z)
      (subspaceInclusion C S hS V (preimageSubspace C S hS ψ Z))
      (subspaceInclusion C S hS U Z) ψ :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι fun F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace C S hS F)
    (Subfunctor.isPullback_preimage ψ.hom Z.1)

/-- **The projection of an inverse image along an étale morphism is étale.** -/
theorem isEtale_preimageProjection (ψ : V ⟶ U) (hψ : IsEtale C S hS ψ.hom)
    (Z : ClosedSubspaces C S hS U.1) :
    IsEtale C S hS (preimageProjection C S hS ψ Z).hom :=
  isEtale_of_isPullback C S hS
    (subspaceInclusion C S hS V (preimageSubspace C S hS ψ Z))
    (preimageProjection C S hS ψ Z) ψ (subspaceInclusion C S hS U Z)
    (isPullback_preimageProjection C S hS ψ Z).flip hψ

/-- **The conormal map of the inverse image of a closed subspace along an étale morphism is an
isomorphism.** This is the flat clause of [Stacks, Tag 04CQ] at an étale morphism. -/
theorem isIso_conormalMap_of_isEtale (ψ : V ⟶ U) (hψ : IsEtale C S hS ψ.hom)
    (Z : ClosedSubspaces C S hS U.1) :
    IsIso (conormalMap C S hS (preimageSubspace C S hS ψ Z) Z ψ
      (preimageProjection C S hS ψ Z) (conormalEtaleRestrictionSquare C S hS ψ Z)) :=
  isIso_conormalMap_of_isFlat C S hS ψ Z
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat C S hS ψ).1 (isFlat_of_isEtale C S hS hψ))

/-- **The inverse images of a closed subspace along an étale covering cover it.** For an étale
covering `(ψ i : V i ⟶ U)` of algebraic spaces and a closed subspace `Z ⊆ U`, the projections
`ψ i⁻¹(Z) ⟶ Z` form an étale covering of `Z`. -/
theorem isEtaleCovering_preimageProjection {I : Type v} (Vi : I → AlgebraicSpaces C S hS)
    (ψ : ∀ i, Vi i ⟶ U)
    (hcov : IsEtaleCovering C S hS (fun i => (Vi i).1) (fun i => (ψ i).hom))
    (Z : ClosedSubspaces C S hS U.1) :
    IsEtaleCovering C S hS (fun i => (preimageSpace C S hS (ψ i) Z).1)
      (fun i => (preimageProjection C S hS (ψ i) Z).hom) := by
  refine ⟨Z.2.1, fun i => (preimageSpace C S hS (ψ i) Z).2,
    fun i => isEtale_preimageProjection C S hS (ψ i) (hcov.etale i) Z, ?_⟩
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov.jointly_surjective
    (pointsMap C S hS _ (subspaceInclusion C S hS U Z).hom z))
  obtain ⟨t, ht, -⟩ := exists_point_of_isPullback C S hS
    (isPullback_preimageProjection C S hS (ψ i) Z) z w hw.symm
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨t, ht⟩⟩

end PreimageCovering

/-! ### The restriction edge of condition (3), at a uniform spelling -/

section RestrictionUniform

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor

variable {X' Y' W₂ W : AlgebraicSpaces C S hS}

/-- **The restriction projection `(ψφ)⁻¹(Z) ⟶ φ⁻¹(Z)`**, with its source and target declared as
the two `AlgebraicGeometry.Space.preimageSpace`s: the projection
`AlgebraicGeometry.Space.preimageProjection` at the nested inverse image. -/
noncomputable def restrictionProjection (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) :
    preimageSpace C S hS (ψ ≫ φ) Z ⟶ preimageSpace C S hS φ Z :=
  preimageProjection C S hS ψ (preimageSubspace C S hS φ Z)

/-- **The structural factorisation of the restriction edge**: restricting to `φ⁻¹(Z)` and then
projecting to `Z` is projecting to `Z` along the composite. -/
theorem restrictionProjection_comp (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) :
    restrictionProjection C S hS ψ φ Z ≫ preimageProjection C S hS φ Z =
      preimageProjection C S hS (ψ ≫ φ) Z :=
  rfl

/-- **The outer factorisation of the restriction edge**, for an arbitrary morphism `b` out of
the subspace `Z`. -/
theorem restrictionProjection_comp_assoc (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) {Zt : AlgebraicSpaces C S hS}
    (b : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Zt) :
    restrictionProjection C S hS ψ φ Z ≫ preimageProjection C S hS φ Z ≫ b =
      preimageProjection C S hS (ψ ≫ φ) Z ≫ b :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun m => m ≫ b) (restrictionProjection_comp C S hS ψ φ Z))

/-- **The composition law of [Stacks, Tag 04G2] on the outer rectangle of the restriction
configuration.**  For a closed subspace `Z ⊆ X'`, a closed subspace `ZH ⊆ Y'`, morphisms
`ψ : W₂ ⟶ W`, `φ : W ⟶ X'`, `a' : W ⟶ Y'` and an edge `α : Z ⟶ ZH` making the square over `φ`
commute, the conormal map of the rectangle over `ψ ≫ φ` is the comparison of [Stacks, Tag 03LU]
along the restriction edge, followed by the inverse image of the conormal map over `φ`, followed
by the conormal map of the restriction square. -/
theorem conormalMap_comp_restriction_outer (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1) (a' : W ⟶ Y')
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ Z) ≫ a' =
      (preimageProjection C S hS φ Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH)
    (hsq₂ : subspaceInclusion C S hS W₂ (preimageSubspace C S hS (ψ ≫ φ) Z) ≫ ψ ≫ a' =
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH) :
    conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) ZH (ψ ≫ a')
        (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂ =
      (modulePullbackTriangle C S hS
            (restrictionProjection_comp_assoc C S hS ψ φ Z α)).hom.app
          (conormalModule C S hS Y' ZH) ≫
        (modulePullback C S hS (restrictionProjection C S hS ψ φ Z)).map
          (conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
            (preimageProjection C S hS φ Z ≫ α) hsq) ≫
          conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
            (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
            (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)) :=
  conormalMap_comp_triangle_of_spaces C S hS ψ a'
    (preimageSubspace C S hS (ψ ≫ φ) Z) (preimageSubspace C S hS φ Z) ZH
    (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z ≫ α)
    (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)) hsq
    (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂
    (preimageSpace C S hS (ψ ≫ φ) Z) (preimageSpace C S hS φ Z)
    (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
    (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z ≫ α)
    (preimageProjection C S hS (ψ ≫ φ) Z ≫ α)
    (restrictionProjection_comp_assoc C S hS ψ φ Z α)
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
      (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
      (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)))
    (conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
      (preimageProjection C S hS φ Z ≫ α) hsq)
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) ZH (ψ ≫ a')
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **The composition law of [Stacks, Tag 04G2] on the structural rectangle of the restriction
configuration.**  The conormal map of the étale restriction square along `ψ ≫ φ` is the
comparison of [Stacks, Tag 03LU] along the restriction edge, followed by the inverse image of
the conormal map of the square along `φ`, followed by the conormal map of the restriction
square. -/
theorem conormalMap_comp_restriction_structural (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) :
    conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) Z (ψ ≫ φ)
        (preimageProjection C S hS (ψ ≫ φ) Z)
        (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z) =
      (modulePullbackTriangle C S hS (restrictionProjection_comp C S hS ψ φ Z)).hom.app
          (conormalModule C S hS X' Z) ≫
        (modulePullback C S hS (restrictionProjection C S hS ψ φ Z)).map
          (conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
            (preimageProjection C S hS φ Z)
            (conormalEtaleRestrictionSquare C S hS φ Z)) ≫
          conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
            (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
            (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)) :=
  conormalMap_comp_triangle_of_spaces C S hS ψ φ
    (preimageSubspace C S hS (ψ ≫ φ) Z) (preimageSubspace C S hS φ Z) Z
    (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z)
    (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z))
    (conormalEtaleRestrictionSquare C S hS φ Z)
    (preimageProjection C S hS (ψ ≫ φ) Z)
    (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z)
    (preimageSpace C S hS (ψ ≫ φ) Z) (preimageSpace C S hS φ Z)
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
    (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z)
    (preimageProjection C S hS (ψ ≫ φ) Z) (restrictionProjection_comp C S hS ψ φ Z)
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
      (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
      (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)))
    (conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
      (preimageProjection C S hS φ Z) (conormalEtaleRestrictionSquare C S hS φ Z))
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) Z (ψ ≫ φ)
      (preimageProjection C S hS (ψ ≫ φ) Z)
      (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z))
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **The chase of restriction stability of condition (3), at the uniform telescope.**  This is
`AlgebraicGeometry.Space.conormalMap_comp_restriction_chase_of_spaces` with the two nested
inverse images of a closed subspace `Z` put in for its four space variables, at the spelling
whose every space is the declared source or target of the projection on its edge:
`AlgebraicGeometry.Space.restrictionProjection` on the restriction edge and
`AlgebraicGeometry.Space.preimageProjection` on the two projections to `Z`; the head relation
`hhead` of the two splitting comparisons `cp`, `cq` is a hypothesis. -/
theorem conormalMap_comp_restriction_chase_of_uniform (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) {YHs : AlgebraicSpaces C S hS}
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ YHs)
    (pa : preimageSpace C S hS φ Z ⟶ YHs) (qa : preimageSpace C S hS (ψ ≫ φ) Z ⟶ YHs)
    (hr : restrictionProjection C S hS ψ φ Z ≫ preimageProjection C S hS φ Z =
      preimageProjection C S hS (ψ ≫ φ) Z)
    (hqa : restrictionProjection C S hS ψ φ Z ≫ pa = qa)
    (MH : Modules.{u, u} C S hS YHs.1 YHs.2)
    (NG : Modules.{u, u} C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).2)
    (M₁ : Modules.{u, u} C S hS (preimageSpace C S hS φ Z).1 (preimageSpace C S hS φ Z).2)
    (M₂ : Modules.{u, u} C S hS (preimageSpace C S hS (ψ ≫ φ) Z).1
      (preimageSpace C S hS (ψ ≫ φ) Z).2)
    (A : (modulePullback C S hS α).obj MH ⟶ NG)
    (cmO : (modulePullback C S hS qa).obj MH ⟶ M₂)
    (cmG : (modulePullback C S hS (preimageProjection C S hS (ψ ≫ φ) Z)).obj NG ⟶ M₂)
    (cmR : (modulePullback C S hS (restrictionProjection C S hS ψ φ Z)).obj M₁ ⟶ M₂)
    (cmU : (modulePullback C S hS pa).obj MH ⟶ M₁)
    (cmE : (modulePullback C S hS (preimageProjection C S hS φ Z)).obj NG ⟶ M₁)
    (cp : (modulePullback C S hS pa).obj MH ⟶
      (modulePullback C S hS (preimageProjection C S hS φ Z)).obj
        ((modulePullback C S hS α).obj MH))
    (cq : (modulePullback C S hS qa).obj MH ⟶
      (modulePullback C S hS (preimageProjection C S hS (ψ ≫ φ) Z)).obj
        ((modulePullback C S hS α).obj MH))
    (hO : cmO = (modulePullbackTriangle C S hS hqa).hom.app MH ≫
      (modulePullback C S hS (restrictionProjection C S hS ψ φ Z)).map cmU ≫ cmR)
    (hGG : cmG = (modulePullbackTriangle C S hS hr).hom.app NG ≫
      (modulePullback C S hS (restrictionProjection C S hS ψ φ Z)).map cmE ≫ cmR)
    (hU : cmU = cp ≫ (modulePullback C S hS (preimageProjection C S hS φ Z)).map A ≫ cmE)
    (hhead : (modulePullbackTriangle C S hS hqa).hom.app MH ≫
        (modulePullback C S hS (restrictionProjection C S hS ψ φ Z)).map cp =
      cq ≫ (modulePullbackTriangle C S hS hr).hom.app ((modulePullback C S hS α).obj MH)) :
    cmO = cq ≫ (modulePullback C S hS (preimageProjection C S hS (ψ ≫ φ) Z)).map A ≫ cmG :=
  comp_eq_of_restriction_paste _ _ _ _ _ _ _ _ _ _ _ _ _ hO hU hGG
    ((modulePullbackTriangle C S hS hr).hom.naturality A) hhead

end RestrictionUniform

/-! ### The chase with the two splitting comparisons as variables -/

section RestrictionComparisons

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

/-- **The chase of restriction stability of condition (3), with the two splitting comparisons
carried as variables.**  This is
`AlgebraicGeometry.Space.conormalMap_comp_restriction_chase_of_spaces` with the two components
of `AlgebraicGeometry.Space.modulePullbackCompIso` that appear in its hypothesis `hU` and in its
conclusion replaced by morphism variables `cp`, `cq` whose values are given by the separate
equations `hcp`, `hcq`.  It is therefore strictly more general: that lemma is this one at
`cp := (modulePullbackCompIso C S hS p α).inv.app MH`,
`cq := (modulePullbackCompIso C S hS q α).inv.app MH` and `hcp := rfl`, `hcq := rfl`. -/
theorem conormalMap_comp_restriction_chase_of_comparisons
    (Z₂s Z₁s ZGs YHs : AlgebraicSpaces C S hS)
    (r : Z₂s ⟶ Z₁s) (p : Z₁s ⟶ ZGs) (q : Z₂s ⟶ ZGs) (α : ZGs ⟶ YHs)
    (hr : r ≫ p = q) (hrα : r ≫ p ≫ α = q ≫ α)
    (MH : Modules.{u, u} C S hS YHs.1 YHs.2)
    (NG : Modules.{u, u} C S hS ZGs.1 ZGs.2)
    (M₂ : Modules.{u, u} C S hS Z₂s.1 Z₂s.2)
    (M₁ : Modules.{u, u} C S hS Z₁s.1 Z₁s.2)
    (A : (modulePullback C S hS α).obj MH ⟶ NG)
    (cmO : (modulePullback C S hS (q ≫ α)).obj MH ⟶ M₂)
    (cmG : (modulePullback C S hS q).obj NG ⟶ M₂)
    (cmR : (modulePullback C S hS r).obj M₁ ⟶ M₂)
    (cmU : (modulePullback C S hS (p ≫ α)).obj MH ⟶ M₁)
    (cmE : (modulePullback C S hS p).obj NG ⟶ M₁)
    (cp : (modulePullback C S hS (p ≫ α)).obj MH ⟶
      (modulePullback C S hS p).obj ((modulePullback C S hS α).obj MH))
    (cq : (modulePullback C S hS (q ≫ α)).obj MH ⟶
      (modulePullback C S hS q).obj ((modulePullback C S hS α).obj MH))
    (hcp : cp = (modulePullbackCompIso C S hS p α).inv.app MH)
    (hcq : cq = (modulePullbackCompIso C S hS q α).inv.app MH)
    (hO : cmO = (modulePullbackTriangle C S hS hrα).hom.app MH ≫
      (modulePullback C S hS r).map cmU ≫ cmR)
    (hGG : cmG = (modulePullbackTriangle C S hS hr).hom.app NG ≫
      (modulePullback C S hS r).map cmE ≫ cmR)
    (hU : cmU = cp ≫ (modulePullback C S hS p).map A ≫ cmE) :
    cmO = cq ≫ (modulePullback C S hS q).map A ≫ cmG := by
  subst hcp
  subst hcq
  exact conormalMap_comp_restriction_chase_of_spaces C S hS Z₂s Z₁s ZGs YHs r p q α hr hrα
    MH NG M₂ M₁ A cmO cmG cmR cmU cmE hO hGG hU

end RestrictionComparisons

/-! ### Restriction stability of the equality of condition (3) -/

section RestrictionDischarge

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor modulePullbackCompIso

variable {X' Y' W₂ W : AlgebraicSpaces C S hS}

/-- **The chase of restriction stability of condition (3), with the two lower edges
equation-indexed and the two splitting comparisons `HEq`-fixed.**  The lower edges `pa`, `qa`
are variables fixed by the equations `hpa`, `hqa`, the splitting comparisons `cp`, `cq` are typed
over them and fixed by heterogeneous equalities, and the head relation is not a hypothesis. -/
theorem conormalMap_comp_restriction_chase_of_heq
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
    (cmR : (modulePullback C S hS r).obj M₁ ⟶ M₂)
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
    (hU : cmU = cp ≫ (modulePullback C S hS p).map A ≫ cmE) :
    cmO = cq ≫ (modulePullback C S hS q).map A ≫ cmG := by
  subst hpa
  obtain rfl : qa = q ≫ α := by rw [← hqa, ← hr, Category.assoc]
  obtain rfl := eq_of_heq hcp
  obtain rfl := eq_of_heq hcq
  exact conormalMap_comp_restriction_chase_of_spaces C S hS Z₂s Z₁s ZGs YHs r p q α hr hqa
    MH NG M₂ M₁ A cmO cmG cmR cmU cmE hO hGG hU

/-- **Restriction stability of the equality of condition (3) of [Stacks, Tag 061A].**  Let
`Z ⊆ X'` and `ZH ⊆ Y'` be closed subspaces, `α : Z ⟶ ZH` an edge between them, and
`A : α^*𝒞_{ZH/Y'} ⟶ 𝒞_{Z/X'}` a prescribed map of modules.  If a morphism `a' : W ⟶ Y'` induces
`A` on conormal modules over `φ : W ⟶ X'`, then `ψ ≫ a'` induces `A` over `ψ ≫ φ`, for every
`ψ : W₂ ⟶ W`.

This is the equality half of restriction stability of
`AlgebraicGeometry.Space.IsConormalLiftAtSubspace`; the commutativity half is
`AlgebraicGeometry.Space.preimageSquare_comp`. -/
theorem conormalMap_comp_restriction (ψ : W₂ ⟶ W) (φ : W ⟶ X')
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS α).obj (conormalModule C S hS Y' ZH) ⟶
      conormalModule C S hS X' Z)
    (a' : W ⟶ Y')
    (hsq : subspaceInclusion C S hS W (preimageSubspace C S hS φ Z) ≫ a' =
      (preimageProjection C S hS φ Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH)
    (hsq₂ : subspaceInclusion C S hS W₂ (preimageSubspace C S hS (ψ ≫ φ) Z) ≫ ψ ≫ a' =
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) ≫ subspaceInclusion C S hS Y' ZH)
    (hdown : conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
        (preimageProjection C S hS φ Z ≫ α) hsq =
      (modulePullbackCompIso C S hS (preimageProjection C S hS φ Z) α).inv.app
          (conormalModule C S hS Y' ZH) ≫
        (modulePullback C S hS (preimageProjection C S hS φ Z)).map A ≫
          conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
            (preimageProjection C S hS φ Z)
            (conormalEtaleRestrictionSquare C S hS φ Z)) :
    conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) ZH (ψ ≫ a')
        (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂ =
      (modulePullbackCompIso C S hS (preimageProjection C S hS (ψ ≫ φ) Z) α).inv.app
          (conormalModule C S hS Y' ZH) ≫
        (modulePullback C S hS (preimageProjection C S hS (ψ ≫ φ) Z)).map A ≫
          conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) Z (ψ ≫ φ)
            (preimageProjection C S hS (ψ ≫ φ) Z)
            (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z) :=
  conormalMap_comp_restriction_chase_of_heq C S hS
    (⟨(Z.1.preimage (ψ ≫ φ).hom).toFunctor,
      (isClosedSubspace_preimage C S hS (ψ ≫ φ).hom Z.1 X'.2 W₂.2 Z.2).1⟩ :
      AlgebraicSpaces C S hS)
    (⟨(Z.1.preimage φ.hom).toFunctor,
      (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS)
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
    (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS)
    (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z)
    (preimageProjection C S hS (ψ ≫ φ) Z) α
    (preimageProjection C S hS φ Z ≫ α) (preimageProjection C S hS (ψ ≫ φ) Z ≫ α)
    (restrictionProjection_comp C S hS ψ φ Z) rfl
    (restrictionProjection_comp_assoc C S hS ψ φ Z α)
    (conormalModule C S hS Y' ZH) (conormalModule C S hS X' Z)
    (conormalModule C S hS W₂ (preimageSubspace C S hS (ψ ≫ φ) Z))
    (conormalModule C S hS W (preimageSubspace C S hS φ Z))
    A
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) ZH (ψ ≫ a')
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂)
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) Z (ψ ≫ φ)
      (preimageProjection C S hS (ψ ≫ φ) Z)
      (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z))
    (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
      (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
      (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)))
    (conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
      (preimageProjection C S hS φ Z ≫ α) hsq)
    (conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
      (preimageProjection C S hS φ Z) (conormalEtaleRestrictionSquare C S hS φ Z))
    ((modulePullbackCompIso C S hS (preimageProjection C S hS φ Z) α).inv.app
      (conormalModule C S hS Y' ZH))
    ((modulePullbackCompIso C S hS (preimageProjection C S hS (ψ ≫ φ) Z) α).inv.app
      (conormalModule C S hS Y' ZH))
    HEq.rfl HEq.rfl
    (conormalMap_comp_triangle_of_spaces C S hS ψ a'
      (preimageSubspace C S hS (ψ ≫ φ) Z) (preimageSubspace C S hS φ Z) ZH
      (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z ≫ α)
      (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)) hsq
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂
      (⟨(Z.1.preimage (ψ ≫ φ).hom).toFunctor,
        (isClosedSubspace_preimage C S hS (ψ ≫ φ).hom Z.1 X'.2 W₂.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS)
      (⟨(Z.1.preimage φ.hom).toFunctor,
        (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS)
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
      (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z ≫ α)
      (preimageProjection C S hS (ψ ≫ φ) Z ≫ α)
      (restrictionProjection_comp_assoc C S hS ψ φ Z α)
      (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
        (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
        (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)))
      (conormalMap C S hS (preimageSubspace C S hS φ Z) ZH a'
        (preimageProjection C S hS φ Z ≫ α) hsq)
      (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) ZH (ψ ≫ a')
        (preimageProjection C S hS (ψ ≫ φ) Z ≫ α) hsq₂)
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
    (conormalMap_comp_triangle_of_spaces C S hS ψ φ
      (preimageSubspace C S hS (ψ ≫ φ) Z) (preimageSubspace C S hS φ Z) Z
      (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z)
      (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z))
      (conormalEtaleRestrictionSquare C S hS φ Z)
      (preimageProjection C S hS (ψ ≫ φ) Z)
      (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z)
      (⟨(Z.1.preimage (ψ ≫ φ).hom).toFunctor,
        (isClosedSubspace_preimage C S hS (ψ ≫ φ).hom Z.1 X'.2 W₂.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS)
      (⟨(Z.1.preimage φ.hom).toFunctor,
        (isClosedSubspace_preimage C S hS φ.hom Z.1 X'.2 W.2 Z.2).1⟩ : AlgebraicSpaces C S hS)
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) rfl rfl rfl
      (restrictionProjection C S hS ψ φ Z) (preimageProjection C S hS φ Z)
      (preimageProjection C S hS (ψ ≫ φ) Z) (restrictionProjection_comp C S hS ψ φ Z)
      (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z)
        (preimageSubspace C S hS φ Z) ψ (restrictionProjection C S hS ψ φ Z)
        (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z)))
      (conormalMap C S hS (preimageSubspace C S hS φ Z) Z φ
        (preimageProjection C S hS φ Z) (conormalEtaleRestrictionSquare C S hS φ Z))
      (conormalMap C S hS (preimageSubspace C S hS (ψ ≫ φ) Z) Z (ψ ≫ φ)
        (preimageProjection C S hS (ψ ≫ φ) Z)
        (conormalEtaleRestrictionSquare C S hS (ψ ≫ φ) Z))
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
    hdown

end RestrictionDischarge

end AlgebraicGeometry.Space

end
