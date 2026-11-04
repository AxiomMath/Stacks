module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTwist

/-!
# The comparison of the twists along the base change of a projective bundle, as a morphism

Let `g : X' ⟶ X` be a morphism of schemes, `E` a quasi-coherent `𝒪_X`-module, `E' ≅ g^*E`, and
`b : 𝐏(E') ⟶ 𝐏(E)` the morphism of projective bundles over `g` (Tag 01O3). For twist data `D` on
`𝐏(E)` and `D'` on `𝐏(E')` (Tag 01NR) the local comparisons of the twists glue to a morphism of
`𝒪_{𝐏(E)}`-modules `θ♭ : 𝒪_{𝐏(E)}(n) ⟶ b_* 𝒪_{𝐏(E')}(n)` for every integer `n`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaFlat`: the morphism
  `𝒪_{𝐏(E)}(n) ⟶ b_* 𝒪_{𝐏(E')}(n)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaLoc_smul`: the local values are
  linear over the structure sheaf.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaGlue_eq`: the comparison glued over
  the inverse image of an affine open of the base does not depend on that affine open.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaFlat_app`: the value of `θ♭` over the
  inverse image of an affine open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjTwists
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.TwistExistence

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (schemeSheafGradedAlgebra E' hqc'))

/-- **The local values of the comparison are linear**: a function `r` on `V` acts on the local
value through `b^♯`. -/
public theorem thetaLoc_smul (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens)
    (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U) (n : ℤ)
    (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (r : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.obj.obj (op V))
    (x : (D.algebra.piece n).val.obj (op V)) :
    thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V (r • x) =
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme.ringCatSheaf.obj.map
          (homOfLE (inf_le_left : bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
            (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W ≤
              bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V)).op
          (show (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme.ringCatSheaf.obj.obj
              (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V)) from
            ((bundleBaseChange g E hqc E' hqc' hE).app V).hom r) •
        thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x := by
  refine (bijective_chartPush D' W hW n _ inf_le_right).1 ?_
  refine (chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V (r • x)).trans ?_
  refine Eq.trans ?_ (((chartPush D' W hW n).val.app (op _)).hom.map_smul _ _).symm
  refine Eq.trans ?_ (congrArg (_ • ·)
    (chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x).symm)
  refine (congrArg _ (((thetaChart g E hqc E' hqc' hE D U hU W hW h n).val.app (op V)).hom.map_smul
    r x)).trans ?_
  exact PresheafOfModules.map_smul _ _ _ _

variable (U : X.Opens) (hU : IsAffineOpen U) (n : ℤ)

/-- The glued comparison over the inverse image of `U` is additive. -/
public theorem thetaGlue_add (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (x y : (D.algebra.piece n).val.obj (op V)) :
    thetaGlue g E hqc E' hqc' hE D D' U hU n V hV (x + y) =
      thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x +
        thetaGlue g E hqc E' hqc' hE D D' U hU n V hV y := by
  refine (eq_thetaGlue g E hqc E' hqc' hE D D' U hU n V hV _ _ fun i => ?_).symm
  rw [map_add, resLE_thetaGlue, resLE_thetaGlue]
  exact (thetaLoc_add g E hqc E' hqc' hE D D' U hU n V i.1.1 i.1.2 i.2 x y).symm

/-- The glued comparison over the inverse image of `U` is linear, functions acting on the target
through `b^♯`. -/
public theorem thetaGlue_smul (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (r : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.obj.obj (op V))
    (x : (D.algebra.piece n).val.obj (op V)) :
    thetaGlue g E hqc E' hqc' hE D D' U hU n V hV (r • x) =
      (show (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme.ringCatSheaf.obj.obj
          (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V)) from
        ((bundleBaseChange g E hqc E' hqc' hE).app V).hom r) •
        thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x := by
  refine (eq_thetaGlue g E hqc E' hqc' hE D D' U hU n V hV _ _ fun i => ?_).symm
  refine ((D'.algebra.piece n).val.resLE inf_le_left).map_smulₛₗ _ _ |>.trans ?_
  refine Eq.trans ?_ (thetaLoc_smul g E hqc E' hqc' hE D D' U hU i.1.1 i.1.2 i.2 n V r x).symm
  exact congrArg (_ • ·) (resLE_thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x i)

/-- The glued comparison over the inverse image of `U` commutes with restriction. -/
public theorem thetaGlue_resLE {V₁ V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens}
    (hV₁ : V₁ ≤ V) (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    thetaGlue g E hqc E' hqc' hE D D' U hU n V₁ (hV₁.trans hV)
        ((D.algebra.piece n).val.resLE hV₁ x) =
      (D'.algebra.piece n).val.resLE
        (show bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V₁ ≤ bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V
          from fun _ hz => hV₁ hz)
        (thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x) := by
  refine (eq_thetaGlue g E hqc E' hqc' hE D D' U hU n V₁ (hV₁.trans hV) _ _ fun i => ?_).symm
  refine ((D'.algebra.piece n).val.resLE_resLE _ _ _).trans ?_
  refine Eq.trans ?_ (thetaLoc_resLE g E hqc E' hqc' hE D D' U hU n V i.1.1 i.1.2 i.2 hV₁ x).symm
  refine Eq.trans ?_ (congrArg ((D'.algebra.piece n).val.resLE _)
    (resLE_thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x i))
  exact ((D'.algebra.piece n).val.resLE_resLE _ _ _).symm

omit hU in
/-- The glued comparison does not depend on the affine open below, for nested affine opens. -/
public theorem thetaGlue_eq_of_le {U₁ U₃ : X.Opens} (hU₁ : IsAffineOpen U₁) (hU₃ : IsAffineOpen U₃)
    (h31 : U₃ ≤ U₁) (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U₃)
    (x : (D.algebra.piece n).val.obj (op V)) :
    thetaGlue g E hqc E' hqc' hE D D' U₁ hU₁ n V (fun _ hz => h31 (hV hz)) x =
      thetaGlue g E hqc E' hqc' hE D D' U₃ hU₃ n V hV x := by
  refine eq_thetaGlue g E hqc E' hqc' hE D D' U₃ hU₃ n V hV x _ fun i => ?_
  refine (resLE_thetaGlue g E hqc E' hqc' hE D D' U₁ hU₁ n V (fun _ hz => h31 (hV hz)) x
    ⟨i.1, fun _ hz => h31 (i.2 hz)⟩).trans ?_
  refine Eq.trans ?_ (thetaLoc_res g E hqc E' hqc' hE D D' hU₁ hU₃ h31 i.1.2 i.1.2 le_rfl
    (fun _ hz => h31 (i.2 hz)) i.2 n V hV x)
  exact ((D'.algebra.piece n).val.congr_map_apply (Subsingleton.elim _ (𝟙 _)) _).trans
    congr($((D'.algebra.piece n).val.presheaf.map_id _) _) |>.symm

/-- Every point of an open set lies in an affine open contained in it. -/
private theorem exists_affineOpen_mem_le (Y : Scheme.{u}) {U : Y.Opens} {y : Y} (hy : y ∈ U) :
    ∃ W : Y.affineOpens, y ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  exact ⟨⟨W, hW⟩, hyW, hWU⟩

omit hU in
/-- **The glued comparison does not depend on the affine open below.** -/
public theorem thetaGlue_eq {U₁ U₂ : X.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV₁ : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U₁)
    (hV₂ : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U₂)
    (x : (D.algebra.piece n).val.obj (op V)) :
    thetaGlue g E hqc E' hqc' hE D D' U₁ hU₁ n V hV₁ x =
      thetaGlue g E hqc E' hqc' hE D D' U₂ hU₂ n V hV₂ x := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (D'.algebra.piece n).isSheaf
    (fun k : {U₃ : X.affineOpens // U₃.1 ≤ U₁ ⊓ U₂} => bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
      (V ⊓ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ k.1.1))
    (fun _ _ hz => hz.1) ?_ fun k => ?_
  · intro p hp
    obtain ⟨W, hpW, hWU⟩ := exists_affineOpen_mem_le X (U := U₁ ⊓ U₂) ⟨hV₁ hp, hV₂ hp⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWU⟩, hp, hpW⟩
  · have hk : V ⊓ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ k.1.1 ≤
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ k.1.1 := inf_le_right
    refine (thetaGlue_resLE g E hqc E' hqc' hE D D' U₁ hU₁ n inf_le_left hV₁ x).symm.trans ?_
    refine (thetaGlue_eq_of_le g E hqc E' hqc' hE D D' n hU₁ k.1.2 (k.2.trans inf_le_left) _ hk
      _).trans ?_
    refine Eq.trans ?_ (thetaGlue_resLE g E hqc E' hqc' hE D D' U₂ hU₂ n inf_le_left hV₂ x)
    exact (thetaGlue_eq_of_le g E hqc E' hqc' hE D D' n hU₂ k.1.2 (k.2.trans inf_le_right) _ hk
      _).symm

/-- The glued comparison over the inverse image of an affine open, as a local map of presheaves
of modules. -/
public def thetaLocalHom (U : X.affineOpens) :
    TopCat.Sheaf.LocalModuleHom (D.algebra.piece n).val
      ((Scheme.Modules.pushforward (bundleBaseChange g E hqc E' hqc' hE)).obj
        (D'.algebra.piece n)).val
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U.1) where
  app V hV := ModuleCat.ofHom (X := (D.algebra.piece n).val.obj (op V))
    (Y := ((Scheme.Modules.pushforward (bundleBaseChange g E hqc E' hqc' hE)).obj
      (D'.algebra.piece n)).val.obj (op V)) (LinearMap.mk
    (AddHom.mk (thetaGlue g E hqc E' hqc' hE D D' U.1 U.2 n V hV)
      (thetaGlue_add g E hqc E' hqc' hE D D' U.1 U.2 n V hV))
    (thetaGlue_smul g E hqc E' hqc' hE D D' U.1 U.2 n V hV))
  naturality hV hWV x := thetaGlue_resLE g E hqc E' hqc' hE D D' U.1 U.2 n hWV hV x

omit [SheafOfModules.IsQuasicoherent E] in
/-- The inverse images of the affine opens of the base cover the projective bundle. -/
public theorem iSup_preimage_affineOpens :
    ⨆ U : X.affineOpens, (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U.1 = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  obtain ⟨W, hpW, -⟩ := exists_affineOpen_mem_le X (U := ⊤) trivial
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨W, hpW⟩

/-- **The comparison of the twists along the base change of a projective bundle**:
`θ♭ : 𝒪_{𝐏(E)}(n) ⟶ b_* 𝒪_{𝐏(E')}(n)`, over the inverse image of every affine open of the base
the glued local comparison. -/
public def thetaFlat :
    D.algebra.piece n ⟶
      (Scheme.Modules.pushforward (bundleBaseChange g E hqc E' hqc' hE)).obj (D'.algebra.piece n) :=
  ⟨TopCat.Sheaf.LocalModuleHom.gluedHom (iSup_preimage_affineOpens E hqc)
    ((Scheme.Modules.pushforward (bundleBaseChange g E hqc E' hqc' hE)).obj
      (D'.algebra.piece n)).isSheaf
    (thetaLocalHom g E hqc E' hqc' hE D D' n)
    (fun i j V hVi hVj => ModuleCat.hom_ext (LinearMap.ext fun x =>
      thetaGlue_eq g E hqc E' hqc' hE D D' n i.2 j.2 V hVi hVj x))⟩

/-- Over the inverse image of an affine open, `θ♭` is the glued local comparison. -/
public theorem thetaFlat_app (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (thetaFlat g E hqc E' hqc' hE D D' n).val.app (op V) x =
      thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x :=
  congrArg (fun φ => φ.hom x) (TopCat.Sheaf.LocalModuleHom.gluedHom_app
    (iSup_preimage_affineOpens E hqc) _ (thetaLocalHom g E hqc E' hqc' hE D D' n) _ ⟨U, hU⟩ V hV)

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
