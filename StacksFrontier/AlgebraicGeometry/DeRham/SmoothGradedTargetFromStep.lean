module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothPulledBackFormsToTarget
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepTargetQuotient
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamFormsToRelative
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The summands of the step of the filtration, read in the target complex of Section 0FMK

For `f : X ⟶ Y` over a base `S`, a cut `k` and `n = k + 1 + j`, the `(k, j + 1)` summand of the
wedge map cutting out the `k`-th step of Section 50.12's filtration of `Ω^•_{X/S}` goes out of
`f^{-1}Ω^k_{Y/S} ⊗_{(f∘g)^{-1}𝒪_S} Ω^{j+1}_{X/S}`. **This file reads that source in the degree-`n`
term of the target complex** `f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`:

`x ⊗ ω  ↦  θ(x) ⊗ q(ω)`,

`θ` the comparison `Stacks.DeRhamSmooth.pulledBackFormsToTarget` of the two inverse images of
`Ω^k_{Y/S}` and `q : Ω^{j+1}_{X/S} ⟶ Ω^{j+1}_{X/Y}` the canonical surjection
(`AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom`), the change of rings from
`(f∘g)^{-1}𝒪_S` to `f^{-1}𝒪_Y` being the lax comparison of the tensor product with restriction
of scalars.

This is the morphism `E_j` of the route to the two squares of Section 0FMK: what is needed of it
is that it carries the
differential `1 ⊗ d_{X/S}` to the differential of the target complex up to the sign `(-1)^k`, and
that read into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` it is the summand followed by the projection.

## Main definitions

* `Stacks.DeRhamSmooth.stepSummandToGradedTarget`: the morphism `E_j`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap)

universe u

namespace Stacks.CategoryTheory

/-- **The differential of an extended complex, read through `HomologicalComplex.extendXIso`, is the
differential of the complex**, at generic objects. -/
theorem extendXIso_inv_comp_extend_d_comp_hom {C : Type*} [_root_.CategoryTheory.Category C]
    [Limits.HasZeroObject C] [Limits.HasZeroMorphisms C] {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extendXIso e hi).inv ≫ (K.extend e).d i' j' ≫ (K.extendXIso e hj).hom = K.d i j := by
  rw [HomologicalComplex.extend_d_eq K e hi hj]
  simp

/-- **Conjugating by two isomorphisms ending in transports**, at generic objects:
`(a ≪≫ eqToIso h₁).inv ≫ D ≫ (b ≪≫ eqToIso h₂).hom` equals
`eqToHom h₁.symm ≫ (a.inv ≫ D ≫ b.hom) ≫ eqToHom h₂`. -/
theorem isoTrans_eqToIso_inv_comp_comp_hom {C : Type*} [_root_.CategoryTheory.Category C]
    {P Q Q' R R' R'' : C} (a : P ≅ Q) (h₁ : Q = Q') (D : P ⟶ R) (b : R ≅ R') (h₂ : R' = R'') :
    (a ≪≫ eqToIso h₁).inv ≫ D ≫ (b ≪≫ eqToIso h₂).hom =
      eqToHom h₁.symm ≫ (a.inv ≫ D ≫ b.hom) ≫ eqToHom h₂ := by
  simp

/-- **A summand of a tensor product, read through a lax comparison, carries the differential of
the second factor to a differential up to a sign**, at generic binders. `F` is a tensor product,
`G` a second one and `R` a restriction of scalars with lax comparisons `lax₁`, `lax₂`, `lax₃`
natural in the second variable (`hnat₁`, `hnat₂`); the composite
`(θ ⊗ 1) ≫ (1 ⊗ a) ≫ lax ≫ R(1 ⊗ q) ≫ i` carries `1 ⊗ dS` to `dT` up to the sign `s` (written
as the composite with `s • 𝟙`, so that it lives in the target's category of morphisms), granted
that `q` intertwines `dS` and `Df` (`key`) and `i` intertwines `s • R(1 ⊗ Df)` and `dT` (`hd`). -/
theorem tensorSummand_comp_d_of_lax {C D : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Category D] [Preadditive C] (F : C ⥤ C ⥤ C) (G : D ⥤ D) (R : D ⥤ C)
    {P P' N₁ N₂ T₁ T₂ : C} {U₁ U₂ V₁ V₂ : D}
    (θ : P ⟶ P') (dS : N₁ ⟶ N₂) (a₁ : N₁ ⟶ R.obj U₁) (a₂ : N₂ ⟶ R.obj U₂)
    (lax₁ : (F.obj P').obj (R.obj U₁) ⟶ R.obj (G.obj U₁))
    (lax₂ : (F.obj P').obj (R.obj U₂) ⟶ R.obj (G.obj U₂))
    (lax₃ : (F.obj P').obj (R.obj V₂) ⟶ R.obj (G.obj V₂))
    (q₁ : U₁ ⟶ V₁) (q₂ : U₂ ⟶ V₂) (Df : V₁ ⟶ V₂)
    (i₁ : R.obj (G.obj V₁) ⟶ T₁) (i₂ : R.obj (G.obj V₂) ⟶ T₂) (dT : T₁ ⟶ T₂) (s : ℤ)
    (hnat₁ : (F.obj P').map (R.map (q₁ ≫ Df)) ≫ lax₃ = lax₁ ≫ R.map (G.map (q₁ ≫ Df)))
    (hnat₂ : (F.obj P').map (R.map q₂) ≫ lax₃ = lax₂ ≫ R.map (G.map q₂))
    (key : a₁ ≫ R.map (q₁ ≫ Df) = dS ≫ a₂ ≫ R.map q₂)
    (hd : i₁ ≫ dT = (s • R.map (G.map Df)) ≫ i₂) :
    ((F.map θ).app N₁ ≫ (F.obj P').map a₁ ≫ lax₁ ≫ R.map (G.map q₁) ≫ i₁) ≫ dT =
      (F.obj P).map dS ≫ ((F.map θ).app N₂ ≫ (F.obj P').map a₂ ≫ lax₂ ≫
        R.map (G.map q₂) ≫ i₂) ≫ (s • 𝟙 T₂) := by
  have e₁ : lax₁ ≫ R.map (G.map q₁) ≫ R.map (G.map Df) = (F.obj P').map (R.map (q₁ ≫
      Df)) ≫ lax₃ := by
    rw [hnat₁, Functor.map_comp, Functor.map_comp]
  have e₂ : (F.obj P').map a₁ ≫ (F.obj P').map (R.map (q₁ ≫ Df)) =
      (F.obj P').map dS ≫ (F.obj P').map a₂ ≫ (F.obj P').map (R.map q₂) := by
    rw [← Functor.map_comp, key, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, hd, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id]
  congr 1
  rw [reassoc_of% e₁, reassoc_of% e₂, reassoc_of% hnat₂, NatTrans.naturality_assoc]

end Stacks.CategoryTheory

namespace Stacks.SheafOfModules.TensorRestrictScalars

variable {Y : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})
  (ρ : A ⟶ B)

/-- **The lax comparison is natural in the second module variable**: the case `φ = 𝟙` of
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_naturality`. -/
theorem laxComparison_naturality_right (F : SheafOfModules.{u} (Tensor.ringSheaf B))
    {G G' : SheafOfModules.{u} (Tensor.ringSheaf B)} (ψ : G ⟶ G') :
    ((Tensor.sheafTensor.{u, u, u, u, u} A).obj ((restrictScalarsSheaf A B ρ).obj F)).map
          ((restrictScalarsSheaf A B ρ).map ψ) ≫
        laxComparison A B ρ F G' =
      laxComparison A B ρ F G ≫
        (restrictScalarsSheaf A B ρ).map
          (((Tensor.sheafTensor.{u, u, u, u, u} B).obj F).map ψ) := by
  have h := laxComparison_naturality A B ρ (𝟙 F) ψ
  simp only [Functor.uncurry_obj_map] at h
  simpa using h

end Stacks.SheafOfModules.TensorRestrictScalars

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **`q : Ω^m_{X/S} ⟶ Ω^m_{X/Y}`, read over `f^{-1}𝒪_Y`**: the degree-`m` component of the
canonical homomorphism of exterior algebras
`AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom`, restricted to `f^{-1}𝒪_Y`. -/
def formsToRelativeCochain (m : ℕ) :
    (pushforward (toInverseImageBase f)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((m : ℕ) : ℤ)) ⟶
      (pushforward (toInverseImageBase f)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((m : ℕ) : ℤ)) :=
  (pushforward (toInverseImageBase f)).map
    ((AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom f g).app ((m : ℕ) : ℤ))

/-- **The `(k, j + 1)` summand's source read in the degree-`n` term of the target complex of
Section 0FMK**, `n = k + 1 + j`:

`f^{-1}Ω^k_{Y/S} ⊗_{(f∘g)^{-1}𝒪_S} Ω^{j+1}_{X/S} ⟶ (f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{j+1}_{X/Y})|`,

`x ⊗ ω ↦ θ(x) ⊗ q(ω)`: `θ ⊗ 1`, the triangle of restrictions of scalars on the second factor,
the lax comparison of the tensor product with the restriction of scalars along
`(f∘g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, `1 ⊗ q`, and the inverse of the degreewise comparison
`Stacks.DeRhamSmooth.gradedTargetXIso`. -/
def stepSummandToGradedTarget (k j : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((pulledBackDeRhamComplex f g).X k)).obj
        ((pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ⟶
      (gradedTargetComplex f g k).X ((k + 1 + j : ℕ) : ℤ) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        (pulledBackFormsToTarget f g k)).app _ ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
        ((coefficientRestriction f g).obj (pulledBackTargetForms f g k))).map
      ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
      (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
      (pulledBackTargetForms f g k)
      ((pushforward (toInverseImageBase f)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
    (coefficientRestriction f g).map
      ((pulledBackTargetFormsTensor f g k).map (formsToRelativeCochain f g (j + 1))) ≫
    (gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega)).inv

/-- **The de Rham differential of `f`, read through `Stacks.DeRhamSmooth.deRhamCochainXIso`, is the
differential of the `ℕ`-indexed complex up to the transports of its terms**: the extension by
zero contributes `HomologicalComplex.extend_d_eq` and nothing else. -/
theorem deRhamCochainXIso_inv_comp_d_comp_hom (m : ℕ) :
    (deRhamCochainXIso f m).inv ≫ (deRhamCochainComplex f).d ((m : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) ≫
        (deRhamCochainXIso f (m + 1)).hom =
      eqToHom (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f m).symm ≫
        (AlgebraicGeometry.Scheme.Hom.deRhamComplex f).d m (m + 1) ≫
          eqToHom (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f (m + 1)) := by
  refine Eq.trans (Stacks.CategoryTheory.isoTrans_eqToIso_inv_comp_comp_hom _ _ _ _ _) ?_
  exact congrArg (fun t => eqToHom (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f m).symm ≫ t ≫
      eqToHom (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f (m + 1)))
    (Stacks.CategoryTheory.extendXIso_inv_comp_extend_d_comp_hom _ _ rfl rfl)

/-- **The inverse of the triangle of restrictions of scalars acts trivially on sections**, up to
the heterogeneous equality its two spellings require: the inverse statement of
`Stacks.DeRhamSmooth.coefficientRestrictionToInverseImageBaseIso_hom_app_val_app_heq`. -/
theorem coefficientRestrictionToInverseImageBaseIso_inv_app_val_app_heq
    (M : Modules X.toRingedSpace) (W : (Opens X.carrier)ᵒᵖ)
    (y : ((pushforward (toInverseImageBase (f ≫ g))).obj M).val.obj W) :
    HEq ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app M).val.app W).hom y) y := by
  have h := coefficientRestrictionToInverseImageBaseIso_hom_app_val_app_heq f g M W
    ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app M).val.app W).hom y)
  have e : ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app M ≫
      (coefficientRestrictionToInverseImageBaseIso f g).hom.app M).val.app W).hom y) = y := by
    rw [Iso.inv_hom_id_app]
    rfl
  exact h.symm.trans (heq_of_eq e)

/-- The inverse of the triangle of restrictions of scalars followed by a restricted morphism acts
on a section as the morphism does, up to heterogeneous equality. -/
theorem coefficientRestrictionToInverseImageBaseIso_inv_app_comp_map_val_app_heq
    (M : Modules X.toRingedSpace) {N : Modules (inverseImageBase f)}
    (ψ : (pushforward (toInverseImageBase f)).obj M ⟶ N) (W : (Opens X.carrier)ᵒᵖ)
    (y : ((pushforward (toInverseImageBase (f ≫ g))).obj M).val.obj W) :
    HEq ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app M ≫
      (coefficientRestriction f g).map ψ).val.app W).hom y) ((ψ.val.app W).hom y) := by
  have h := coefficientRestrictionToInverseImageBaseIso_inv_app_val_app_heq f g M W y
  change HEq ((ψ.val.app W).hom
    ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app M).val.app W).hom y)) _
  generalize ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app M).val.app W).hom y) = z
    at h ⊢
  obtain rfl := eq_of_heq h
  exact HEq.rfl

/-- A transport between equal sheaves of modules over an arbitrary sheaf of rings is the identity
on a local section, up to the heterogeneous equality the two spellings require. -/
theorem sheafOfModules_eqToHom_val_app_heq {C : Type*} [_root_.CategoryTheory.Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.{u} R}
    (h : A = B) (V : Cᵒᵖ) (s : A.val.obj V) : HEq (((eqToHom h).val.app V).hom s) s := by
  subst h
  rfl

/-- **`q : Ω^m_{X/S} ⟶ Ω^m_{X/Y}` commutes with the de Rham differentials, read over
`(f∘g)^{-1}𝒪_S`**: the de Rham differential of `f ≫ g` followed by `q` (through the triangle of
restrictions of scalars) is `q` followed by the de Rham differential of `f` read through
`Stacks.DeRhamSmooth.deRhamCochainXIso`. On sections this is
`AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_comm_d`; the transports act trivially. -/
theorem formsToRelativeCochain_comm_d (m : ℕ) :
    (coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((m : ℕ) : ℤ)) ≫
      (coefficientRestriction f g).map (formsToRelativeCochain f g m ≫
        (deRhamCochainXIso f m).inv ≫ (deRhamCochainComplex f).d ((m : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) ≫
          (deRhamCochainXIso f (m + 1)).hom) =
    (AlgebraicGeometry.Scheme.Hom.deRhamComplex (f ≫ g)).d m (m + 1) ≫
      (coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((m + 1 : ℕ) : ℤ)) ≫
      (coefficientRestriction f g).map (formsToRelativeCochain f g (m + 1)) := by
  ext W ω
  have h1 := coefficientRestrictionToInverseImageBaseIso_inv_app_comp_map_val_app_heq f g
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((m : ℕ) : ℤ))
    (formsToRelativeCochain f g m ≫
        (deRhamCochainXIso f m).inv ≫ (deRhamCochainComplex f).d ((m : ℕ) : ℤ) ((m + 1 : ℕ) : ℤ) ≫
          (deRhamCochainXIso f (m + 1)).hom) W ω
  have h2 := coefficientRestrictionToInverseImageBaseIso_inv_app_comp_map_val_app_heq f g
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((m + 1 : ℕ) : ℤ))
    (formsToRelativeCochain f g (m + 1)) W
    ((((AlgebraicGeometry.Scheme.Hom.deRhamComplex (f ≫ g)).d m (m + 1)).val.app W).hom ω)
  refine eq_of_heq (h1.trans (HEq.trans ?_ h2.symm))
  have e := congrArg (fun t => ((formsToRelativeCochain f g m ≫ t).val.app W).hom ω)
    (deRhamCochainXIso_inv_comp_d_comp_hom f m)
  refine (heq_of_eq e).trans ?_
  clear e h1 h2
  change HEq (((eqToHom (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f (m + 1))).val.app W).hom
    ((((AlgebraicGeometry.Scheme.Hom.deRhamComplex f).d m (m + 1)).val.app W).hom
      (((eqToHom (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f m).symm).val.app W).hom
        (((formsToRelativeCochain f g m).val.app W).hom ω)))) _
  refine (sheafOfModules_eqToHom_val_app_heq _ W _).trans ?_
  have h3 := sheafOfModules_eqToHom_val_app_heq (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f
      m).symm
    W (((formsToRelativeCochain f g m).val.app W).hom ω)
  exact (heq_of_eq (congrArg
    (((AlgebraicGeometry.Scheme.Hom.deRhamComplex f).d m (m + 1)).val.app W).hom
      (eq_of_heq h3))).trans
    (heq_of_eq (AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_comm_d f g m W ω))

/-- **The de Rham differential `d : Ω^m_{X/S} ⟶ Ω^{m+1}_{X/S}` of a morphism of schemes
`h : X ⟶ S`, read over `h^{-1}𝒪_S`** as a morphism between the direct images to
`(X, h^{-1}𝒪_S)`: the differential of `AlgebraicGeometry.Scheme.Hom.deRhamComplex`, with its
source and target spelled as `Stacks.DeRhamDirectImage.toInverseImageBase` direct images. -/
def formsDifferential {Z T : Scheme.{u}} (h : Z ⟶ T) (m : ℕ) :
    (pushforward (toInverseImageBase h)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms h ((m : ℕ) : ℤ)) ⟶
      (pushforward (toInverseImageBase h)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms h ((m + 1 : ℕ) : ℤ)) :=
  (AlgebraicGeometry.Scheme.Hom.deRhamComplex h).d m (m + 1)

/-- The restriction of scalars of the lax comparison's codomain, re-read along the
coefficient-ring change: a definitional identity, isolated so that it is checked once. -/
theorem laxComparison_comp_coefficientRestriction_map_eq (k : ℕ)
    {M N : Modules (inverseImageBase f)} (ψ : M ⟶ N) :
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
        g.toLRSHom.toShHom) (pulledBackTargetForms f g k) M ≫
        (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map ψ) =
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
          g.toLRSHom.toShHom) (pulledBackTargetForms f g k) M ≫
        (Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
            g.toLRSHom.toShHom)).map (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (inverseImageBase f).sheaf).obj (pulledBackTargetForms f g k)).map ψ) := rfl

/-- The tensor product with a restricted module of a restricted morphism, re-read along the
coefficient-ring change: a definitional identity, isolated so that it is checked once. -/
theorem sheafTensor_map_coefficientRestriction_map_eq (k : ℕ)
    {M N : Modules (inverseImageBase f)} (ψ : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
        k))).map
        ((coefficientRestriction f g).map ψ) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).obj
          ((Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
          g.toLRSHom.toShHom)).obj (pulledBackTargetForms f g k))).map
        ((Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
            g.toLRSHom.toShHom)).map ψ) := rfl

/-- **The lax comparison into `(f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} -)|` is natural in
`f^{-1}𝒪_Y`-linear maps**, in the spelling of `Stacks.DeRhamDirectImage.coefficientRestriction`:
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_naturality_right`, with the
restriction of scalars of sheaves of commutative rings re-read as the restriction along the
coefficient-ring change (definitionally, one side at a time). -/
theorem laxComparison_pulledBackTargetForms_naturality (k : ℕ)
    {M N : Modules (inverseImageBase f)} (ψ : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
        k))).map
        ((coefficientRestriction f g).map ψ) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
          g.toLRSHom.toShHom) (pulledBackTargetForms f g k) N =
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
        g.toLRSHom.toShHom) (pulledBackTargetForms f g k) M ≫
      (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map ψ) :=
  ((congrArg (· ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
      CommRingCat.{u} (f ≫
      g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
      g.toLRSHom.toShHom) (pulledBackTargetForms f g k) N)
    (sheafTensor_map_coefficientRestriction_map_eq f g k ψ)).trans
    (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_naturality_right
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf) (inverseImageBase
        f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) _ ψ)).trans
    (laxComparison_comp_coefficientRestriction_map_eq f g k ψ).symm

/-- **(E_j) The step summand's source, read in the target complex, carries `1 ⊗ d_{X/S}` to the
differential of the target complex up to the sign `(-1)^k`**:

`E_j ≫ d_T = (1 ⊗ d_{X/S}) ≫ E_{j+1} ≫ (-1)^k`,

the sign written as a multiple of the identity of the target so that the equation lives in one
category of morphisms.

The differential of the target complex is `(-1)^k (1 ⊗ d_{X/Y})` through
`Stacks.DeRhamSmooth.gradedTargetXIso` (`Stacks.DeRhamSmooth.gradedTargetXIso_inv_comp_d`), the
lax comparison is natural in `f^{-1}𝒪_Y`-linear maps of the second variable, and
`q ∘ d_{X/S} = d_{X/Y} ∘ q` (`Stacks.DeRhamSmooth.formsToRelativeCochain_comm_d`). -/
theorem stepSummandToGradedTarget_comp_d (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫
        (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
            ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f ≫ g) (j + 1)) ≫
        stepSummandToGradedTarget f g k (j + 1) ≫
          ((-1 : ℤ) ^ k • 𝟙 ((gradedTargetComplex f g k).X ((k + 1 + (j + 1) : ℕ) : ℤ))) := by
  have hd := gradedTargetXIso_inv_comp_d f g k (j + 1) (k + 1 + j) (k + 1 + (j + 1))
    (by omega) (by omega)
  have key := formsToRelativeCochain_comm_d f g (j + 1)
  have n₁ := laxComparison_pulledBackTargetForms_naturality f g k
    (formsToRelativeCochain f g (j + 1) ≫ ((deRhamCochainXIso f (j + 1)).inv ≫
        (deRhamCochainComplex f).d ((j + 1 : ℕ) : ℤ) ((j + 1 + 1 : ℕ) : ℤ) ≫
          (deRhamCochainXIso f (j + 1 + 1)).hom))
  have n₂ := laxComparison_pulledBackTargetForms_naturality f g k
    (formsToRelativeCochain f g (j + 1 + 1))
  have h := Stacks.CategoryTheory.tensorSummand_comp_d_of_lax
    (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)))
    (D := Modules (inverseImageBase f))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))
    (pulledBackTargetFormsTensor f g k) (coefficientRestriction f g)
    (pulledBackFormsToTarget f g k) _ _ _ _ _ _ _ _ _ _ _ _ _ n₁ n₂ key (by exact hd)
  exact h

end Stacks.DeRhamSmooth

end
