module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
public import StacksFrontier.CategoryTheory.Sites.Modules.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom out of a finitely presented module commutes with filtered colimits

Let `(C, O)` be a ringed site, let `F` be an `O`-module of finite presentation and let
`G = colim_λ G_λ` be a filtered colimit of `O`-modules. Then the canonical map

`colim_λ Hom_O(F, G_λ) ⟶ Hom_O(F, colim_λ G_λ)`

is an isomorphism, that is, the functor `Hom_O(F, -)` preserves filtered colimits. The site has
objects and morphisms in `Type u`, the structure sheaf is `CommRingCat.{u}`-valued and the
modules are `SheafOfModules.{u}`.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomNatLeft`: precomposition in the first variable,
  as a natural transformation between the internal Hom functors in the second variable.
* `Stacks.SheafOfModules.InternalHom.freeInternalHomNatIso`: internal Hom out of a finite free
  module is the finite direct sum functor, as a natural isomorphism.
* `Stacks.SheafOfModules.InternalHom.internalHomOverNatIso`: restricting `Hom_O(F, -)` to a
  localized site is internal Hom out of the restriction of `F`, as a natural isomorphism of
  functors in the target.

## Main results

* `Stacks.SheafOfModules.InternalHom.isIso_map_colimitPost`: a functor preserving the relevant
  colimits carries the comparison morphism of a colimit to an isomorphism.
* `Stacks.SheafOfModules.InternalHom.isIso_colimitPost_of_isKernel`: a functor exhibited
  pointwise as the kernel of a map between colimit-preserving functors preserves those
  colimits.
* `Stacks.SheafOfModules.InternalHom.isIso_colimitPost_of_presentation`: the case of a module
  with a global finite presentation.
* `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesFilteredColimits`:
  internal Hom out of a module of finite presentation preserves filtered colimits.

## References

* [Stacks Project, Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

/-! ### Two categorical steps -/

section Comparison

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

/-- A functor that preserves the colimit of `D ⋙ H` and whose composite with `H` preserves the
colimit of `D` carries the comparison morphism `colim (D ⋙ H) ⟶ H (colim D)` to an
isomorphism. -/
theorem isIso_map_colimitPost {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {B' : Type u₃} [Category.{v₃} B'] {K : Type u₄} [Category.{v₄} K]
    (D : K ⥤ A) (H : A ⥤ B) (ρ : B ⥤ B')
    [HasColimit D] [HasColimit (D ⋙ H)] [HasColimit ((D ⋙ H) ⋙ ρ)]
    [PreservesColimit (D ⋙ H) ρ] [PreservesColimit D (H ⋙ ρ)] :
    IsIso (ρ.map (colimit.post D H)) := by
  have h := colimit.post_post D H ρ
  have h₂ : IsIso (colimit.post D (H ⋙ ρ)) := inferInstance
  exact (isIso_comp_left_iff (colimit.post (D ⋙ H) ρ) _).1 (h ▸ h₂)

variable {M : Type u₁} [Category.{v₁} M] [Preadditive M]
variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K M]

omit [Preadditive M] in
/-- The comparison morphisms of two functors `H₀ ⟶ H₁` at a diagram `D` form a commuting square
with the natural transformation between them. -/
theorem colimitPost_naturality (D : K ⥤ M) {H₀ H₁ : M ⥤ M} (β : H₀ ⟶ H₁) :
    (colim : (K ⥤ M) ⥤ M).map (Functor.whiskerLeft D β) ≫ colimit.post D H₁ =
      colimit.post D H₀ ≫ β.app (colimit D) := by
  apply colimit.hom_ext
  intro k
  rw [← Category.assoc, ← Category.assoc]
  show (colimit.ι (D ⋙ H₀) k ≫ colimMap (Functor.whiskerLeft D β)) ≫ colimit.post D H₁ = _
  rw [ι_colimMap, colimit.ι_post, Category.assoc, colimit.ι_post]
  exact (β.naturality (colimit.ι D k)).symm

/-- A functor exhibited pointwise as the kernel of a map between two functors that preserve
`K`-colimits preserves the `K`-colimit of `D`, provided `K`-colimits in `M` are left exact. -/
theorem isIso_colimitPost_of_isKernel [Balanced M]
    [Functor.PreservesZeroMorphisms (colim : (K ⥤ M) ⥤ M)]
    (D : K ⥤ M) {H₀ H₁ H₂ : M ⥤ M} (β : H₀ ⟶ H₁) (α : H₁ ⟶ H₂)
    (hw : ∀ G, β.app G ≫ α.app G = 0)
    (hker : ∀ G, IsLimit (KernelFork.ofι (β.app G) (hw G)))
    [PreservesLimit (parallelPair (Functor.whiskerLeft D α) 0) (colim : (K ⥤ M) ⥤ M)]
    [PreservesColimitsOfShape K H₁] [PreservesColimitsOfShape K H₂] :
    IsIso (colimit.post D H₀) := by
  have hwW : Functor.whiskerLeft D β ≫ Functor.whiskerLeft D α = 0 := by
    ext k
    exact hw (D.obj k)
  have L : IsLimit (KernelFork.ofι (Functor.whiskerLeft D β) hwW) :=
    evaluationJointlyReflectsLimits _ (fun k =>
      (isLimitMapConeForkEquiv' ((CategoryTheory.evaluation K M).obj k) hwW).symm (hker (D.obj k)))
  have L' := isLimitForkMapOfIsLimit' (colim : (K ⥤ M) ⥤ M) hwW L
  have s₁ := colimitPost_naturality D β
  have s₂ := colimitPost_naturality D α
  have hmβ : Mono (β.app (colimit D)) := mono_of_isLimit_fork (hker (colimit D))
  have hmc : Mono ((colim : (K ⥤ M) ⥤ M).map (Functor.whiskerLeft D β)) :=
    mono_of_isLimit_fork L'
  have hi₁ : IsIso (colimit.post D H₁) := inferInstance
  have hi₂ : IsIso (colimit.post D H₂) := inferInstance
  have hcond : (β.app (colimit D) ≫ inv (colimit.post D H₁)) ≫
      (colim : (K ⥤ M) ⥤ M).map (Functor.whiskerLeft D α) = 0 := by
    have h : inv (colimit.post D H₁) ≫
        (colim : (K ⥤ M) ⥤ M).map (Functor.whiskerLeft D α) =
        α.app (colimit D) ≫ inv (colimit.post D H₂) := by
      rw [IsIso.eq_comp_inv, Category.assoc, s₂, IsIso.inv_hom_id_assoc]
    rw [Category.assoc, h, ← Category.assoc, hw (colimit D), zero_comp]
  obtain ⟨ψ, hψ⟩ := KernelFork.IsLimit.lift' L' _ hcond
  rw [Fork.ι_ofι] at hψ
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_mono ((colim : (K ⥤ M) ⥤ M).map (Functor.whiskerLeft D β)),
      Category.assoc, hψ, Category.id_comp, ← Category.assoc, ← s₁, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  · rw [← cancel_mono (β.app (colimit D)), Category.assoc, s₁.symm, Category.id_comp,
      ← Category.assoc, hψ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Comparison

/-! ### Precomposition in the first variable, as a natural transformation -/

section NatLeft

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u})

/-- Precomposition by `f : F ⟶ F'` in the first variable of the internal Hom sheaf, as a
natural transformation `Hom_O(F', -) ⟶ Hom_O(F, -)`. -/
@[sga "4 IV 12.2" "Bifunctoriality"]
noncomputable def internalHomNatLeft
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F ⟶ F') :
    internalHomSecondFunctor.{u, u, u, u} J O F' ⟶
      internalHomSecondFunctor.{u, u, u, u} J O F where
  app G := ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft O.obj f.val⟩
  naturality _ _ _ := by ext; rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition by an identity is the identity. -/
theorem internalHomNatLeft_id
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    internalHomNatLeft J O (𝟙 F) = 𝟙 _ := by
  ext; rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition by a composite is the composite of the precompositions, in the opposite
order. -/
theorem internalHomNatLeft_comp
    {F F' F'' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F ⟶ F') (g : F' ⟶ F'') :
    internalHomNatLeft J O (f ≫ g) = internalHomNatLeft J O g ≫ internalHomNatLeft J O f := by
  ext; rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition is additive in the morphism. -/
theorem internalHomNatLeft_add
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f g : F ⟶ F') :
    internalHomNatLeft J O (f + g) = internalHomNatLeft J O f + internalHomNatLeft J O g := by
  ext G : 2
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro V
  have hrestr : (_root_.restrFun O.obj V.unop).map (f + g).val =
      (_root_.restrFun O.obj V.unop).map f.val +
        (_root_.restrFun O.obj V.unop).map g.val := by
    ext; rfl
  ext a
  exact (congrArg (fun φ => φ ≫ a) hrestr).trans (Preadditive.add_comp _ _ _ _ _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition by a zero morphism is zero. -/
theorem internalHomNatLeft_zero
    (F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    internalHomNatLeft J O (0 : F ⟶ F') = 0 := by
  simpa using internalHomNatLeft_add J O (0 : F ⟶ F') 0

/-- Precomposition, at a fixed target, as an additive map on morphisms of the first variable. -/
noncomputable def internalHomNatLeftAppAddHom
    (F F' G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (F ⟶ F') →+ ((internalHomSecondFunctor.{u, u, u, u} J O F').obj G ⟶
      (internalHomSecondFunctor.{u, u, u, u} J O F).obj G) where
  toFun f := (internalHomNatLeft J O f).app G
  map_zero' := by rw [internalHomNatLeft_zero]; rfl
  map_add' f g := by rw [internalHomNatLeft_add]; rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition takes a finite sum of morphisms to the sum of the precompositions. -/
theorem internalHomNatLeft_app_sum
    {F F' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    {ι : Type*} (s : Finset ι) (c : ι → (F ⟶ F'))
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    ∑ i ∈ s, (internalHomNatLeft J O (c i)).app G =
      (internalHomNatLeft J O (∑ i ∈ s, c i)).app G :=
  (map_sum (internalHomNatLeftAppAddHom J O F F' G) c s).symm

end NatLeft

/-! ### The case of a global finite presentation -/

section SmallSite

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- A site whose objects and morphisms lie in the module universe is essentially small
there. -/
local instance essentiallySmallSite_filteredColimits : EssentiallySmall.{u} C :=
  essentiallySmallSelf.{u, u, u} C

/-- Abelian presheaves on a site essentially small in the module universe are sheafifiable. -/
local instance hasSheafifyAbelian_filteredColimits : HasSheafify J AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u, u, u} J

/-- On a site essentially small in the module universe the maps inverted by sheafification of
abelian presheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveAbelian_filteredColimits :
    J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u} J

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u})

open Stacks.AlgebraicGeometry.InternalHomLocalKernel

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor

/-- Internal Hom out of the unit sheaf of modules is the identity functor. -/
noncomputable def unitInternalHomNatIso :
    internalHomSecondFunctor.{u, u, u, u} J O
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ≅ 𝟭 _ :=
  eqToIso (congrArg (internalHomSecondFunctor.{u, u, u, u} J O)
      (_root_.SheafOfModules.tensorUnit_sheafTensor O).symm) ≪≫
    unitSheafInternalHomNatIso O

variable (I : Type u) [Finite I]

/-- A finite coproduct of copies of the unit sheaf of modules is a biproduct. -/
local instance hasBiproduct_unit :
    HasBiproduct (fun _ : I =>
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :=
  HasBiproduct.of_hasProduct _

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A finite free module is the coproduct of copies of the unit sheaf of modules. -/
theorem free_eq_sigma :
    (_root_.SheafOfModules.free I :
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) =
      ∐ fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) :=
  rfl

/-- The `i`-th projection of `O^{⊕I}` for a finite index type, read through the identification
of the coproduct with the biproduct. -/
noncomputable def freeInternalHomProj (i : I) :
    (∐ fun _ : I =>
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ⟶
      _root_.SheafOfModules.unit _ :=
  (biproduct.isoCoproduct (fun _ : I => _root_.SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).inv ≫ biproduct.π _ i

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- An inclusion followed by a projection of `O^{⊕I}` is the corresponding matrix entry of the
biproduct. -/
theorem ι_comp_freeInternalHomProj (i j : I) :
    Sigma.ι (fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) j ≫
        freeInternalHomProj J O I i =
      biproduct.ι (fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) j ≫
        biproduct.π _ i := by
  have h : Sigma.ι (fun _ : I =>
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) j ≫
      (biproduct.isoCoproduct _).inv =
      biproduct.ι (fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) j := by
    simp
  rw [freeInternalHomProj, ← Category.assoc, h]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The biproduct identity for `O^{⊕I}`: the projections and inclusions sum to the identity. -/
theorem sum_freeInternalHomProj_comp_ι [Fintype I] :
    ∑ i : I, freeInternalHomProj J O I i ≫
        Sigma.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i =
      𝟙 (∐ fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) := by
  have hι (i : I) :
      biproduct.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i ≫
        (biproduct.isoCoproduct _).hom =
      Sigma.ι (fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i := by
    simp
  have h (i : I) : freeInternalHomProj J O I i ≫
      Sigma.ι (fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i =
      (biproduct.isoCoproduct _).inv ≫
        (biproduct.π (fun _ : I =>
            _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i ≫
          biproduct.ι (fun _ : I =>
            _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i) ≫
          (biproduct.isoCoproduct _).hom := by
    conv_lhs => rw [← hι i]
    rw [freeInternalHomProj]
    simp only [Category.assoc]
  have htot : ∑ i : I,
      biproduct.π (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i ≫
        biproduct.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i =
      𝟙 (⨁ fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :=
    IsBilimit.total (biproduct.isBilimit _)
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    htot, Category.id_comp, Iso.inv_hom_id]

/-- The `i`-th inclusion `𝟭 ⟶ Hom_O(O^{⊕I}, -)`: precomposition by the `i`-th projection of
`O^{⊕I}`, read through `Hom_O(O, -) ≅ 𝟭`. -/
noncomputable def freeInternalHomInj (i : I) :
    𝟭 (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ⟶
      internalHomSecondFunctor.{u, u, u, u} J O
        (∐ fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :=
  (unitInternalHomNatIso J O).inv ≫ internalHomNatLeft J O (freeInternalHomProj J O I i)

/-- The `i`-th evaluation `Hom_O(O^{⊕I}, -) ⟶ 𝟭`: precomposition by the `i`-th inclusion of
`O^{⊕I}`, read through `Hom_O(O, -) ≅ 𝟭`. -/
noncomputable def freeInternalHomEval (i : I) :
    internalHomSecondFunctor.{u, u, u, u} J O
        (∐ fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ⟶
      𝟭 (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :=
  internalHomNatLeft J O (Sigma.ι (fun _ : I =>
    _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) i) ≫
      (unitInternalHomNatIso J O).hom

/-- `Hom_O(O^{⊕I}, G)`, with the evaluations and inclusions above, as a bicone on the family of
`I` copies of `G`. -/
noncomputable def freeInternalHomBicone
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    Limits.Bicone (fun _ : I => G) where
  pt := (internalHomSecondFunctor.{u, u, u, u} J O
    (∐ fun _ : I =>
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).obj G
  π i := (freeInternalHomEval J O I i).app G
  ι i := (freeInternalHomInj J O I i).app G
  ι_π := by
    classical
    intro j j'
    have hmid : (internalHomNatLeft J O (freeInternalHomProj J O I j)).app G ≫
        (internalHomNatLeft J O (Sigma.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
            j')).app G =
        (internalHomNatLeft J O (Sigma.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) j' ≫
            freeInternalHomProj J O I j)).app G := by
      rw [internalHomNatLeft_comp]; rfl
    change ((unitInternalHomNatIso J O).inv.app G ≫
        (internalHomNatLeft J O (freeInternalHomProj J O I j)).app G) ≫
      ((internalHomNatLeft J O _).app G ≫ (unitInternalHomNatIso J O).hom.app G) = _
    rw [Category.assoc,
      ← Category.assoc ((internalHomNatLeft J O (freeInternalHomProj J O I j)).app G), hmid,
      ι_comp_freeInternalHomProj]
    by_cases h : j = j'
    · subst h
      rw [biproduct.ι_π_self, internalHomNatLeft_id]
      simp
    · rw [biproduct.ι_π_ne _ (Ne.symm h), internalHomNatLeft_zero]
      simp [h]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The bicone of `Hom_O(O^{⊕I}, G)` satisfies the biproduct identity. -/
theorem freeInternalHomBicone_total [Fintype I]
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    ∑ i : I, (freeInternalHomBicone J O I G).π i ≫ (freeInternalHomBicone J O I G).ι i =
      𝟙 (freeInternalHomBicone J O I G).pt := by
  have h (i : I) :
      (freeInternalHomBicone J O I G).π i ≫ (freeInternalHomBicone J O I G).ι i =
      (internalHomNatLeft J O (freeInternalHomProj J O I i ≫
        Sigma.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
            i)).app G := by
    show ((internalHomNatLeft J O _).app G ≫ (unitInternalHomNatIso J O).hom.app G) ≫
      ((unitInternalHomNatIso J O).inv.app G ≫ (internalHomNatLeft J O _).app G) = _
    rw [Category.assoc, ← Category.assoc ((unitInternalHomNatIso J O).hom.app G),
      Iso.hom_inv_id_app, Category.id_comp, internalHomNatLeft_comp]
    rfl
  have key : ∑ i : I, (internalHomNatLeft J O (freeInternalHomProj J O I i ≫
        Sigma.ι (fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
            i)).app G =
      𝟙 ((internalHomSecondFunctor.{u, u, u, u} J O
        (∐ fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).obj
          G) := by
    rw [internalHomNatLeft_app_sum, sum_freeInternalHomProj_comp_ι, internalHomNatLeft_id]
    rfl
  exact (Finset.sum_congr rfl (fun i _ => h i)).trans key

/-- `∐_{i ∈ I} G ≅ Hom_O(O^{⊕I}, G)` for a finite index type. -/
noncomputable def freeInternalHomIso
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (Functor.const (Discrete I) ⋙ colim :
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
          SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)).obj G ≅
      (internalHomSecondFunctor.{u, u, u, u} J O
        (∐ fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))).obj
          G :=
  letI := Fintype.ofFinite I
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((Functor.const (Discrete I)).obj G))
    (isBilimitOfTotal _ (freeInternalHomBicone_total J O I G)).isColimit

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- On the `i`-th inclusion, the isomorphism `∐_{i ∈ I} G ≅ Hom_O(O^{⊕I}, G)` is the `i`-th
inclusion of the bicone. -/
theorem ι_freeInternalHomIso_hom
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
    (i : Discrete I) :
    colimit.ι ((Functor.const (Discrete I)).obj G) i ≫ (freeInternalHomIso J O I G).hom =
      (freeInternalHomInj J O I i.as).app G :=
  colimit.ι_desc _ _

/-- Internal Hom out of a finite free module is the finite direct sum functor. -/
@[ega "0 5.4.2" "more general"]
noncomputable def freeInternalHomNatIso :
    (Functor.const (Discrete I) ⋙ colim :
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
          SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ≅
      internalHomSecondFunctor.{u, u, u, u} J O
        (∐ fun _ : I =>
          _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :=
  NatIso.ofComponents (freeInternalHomIso J O I) (by
    intro G G' g
    apply colimit.hom_ext
    intro i
    have hmap : (Functor.const (Discrete I) ⋙ colim :
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
          SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)).map g =
        colimMap ((Functor.const (Discrete I)).map g) := rfl
    rw [← Category.assoc, ← Category.assoc, hmap, ι_colimMap, Category.assoc,
      ι_freeInternalHomIso_hom, ι_freeInternalHomIso_hom]
    exact (freeInternalHomInj J O I i.as).naturality g)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Internal Hom out of a finite free module commutes with every colimit. -/
theorem preservesColimits_internalHomSecondFunctor_free (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K (internalHomSecondFunctor.{u, u, u, u} J O
      (∐ fun _ : I =>
        _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))) :=
  have hadj : (Functor.const (Discrete I) ⋙ colim :
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ⊣
      (Functor.const (Discrete I) ⋙ lim) :=
    Adjunction.comp constLimAdj colimConstAdj
  have : PreservesColimitsOfSize.{u, u} (Functor.const (Discrete I) ⋙ colim :
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) ⥤
        SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :=
    hadj.leftAdjoint_preservesColimits
  preservesColimitsOfShape_of_natIso (freeInternalHomNatIso J O I)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- If `F` admits a finite presentation then the canonical map
`colim_λ Hom_O(F, G_λ) ⟶ Hom_O(F, colim_λ G_λ)` is an isomorphism for every filtered
diagram. -/
theorem isIso_colimitPost_of_presentation
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (P : F.Presentation) (hP : P.IsFinite)
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    IsIso (colimit.post D (internalHomSecondFunctor.{u, u, u, u} J O F)) := by
  have _ := hP
  have _ : Fintype P.generators.I := Fintype.ofFinite _
  have _ : Fintype P.relations.I := Fintype.ofFinite _
  set b := P.generators.π with hb
  set a := P.relations.π ≫ kernel.ι P.generators.π with ha
  have hab : a ≫ b = 0 := by rw [ha, hb]; simp
  have hw (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
      (internalHomNatLeft J O b).app G ≫ (internalHomNatLeft J O a).app G = 0 := by
    rw [← NatTrans.comp_app, ← internalHomNatLeft_comp, hab, internalHomNatLeft_zero]
    rfl
  have hS : (ShortComplex.mk a b hab).Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have h : kernel.lift b a hab = P.relations.π := by
      apply (cancel_mono (kernel.ι b)).1
      rw [kernel.lift_ι, ha]
    rw [h]
    infer_instance
  have hker (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
      IsLimit (KernelFork.ofι ((internalHomNatLeft J O b).app G) (hw G)) := by
    have _ := sheafInternalHomMapLeft_mono_of_epi J O (G := G) b
    have hex := sheafInternalHomMapLeft_exact_of_exact_epi J O (ShortComplex.mk a b hab) G hS
    exact hex.choose_spec.fIsKernel
  have hfree (n : Type u) [Finite n] : PreservesColimitsOfShape K
      (internalHomSecondFunctor.{u, u, u, u} J O (_root_.SheafOfModules.free n)) := by
    rw [free_eq_sigma]
    exact preservesColimits_internalHomSecondFunctor_free J O n K
  have _ := hfree P.generators.I
  have _ := hfree P.relations.I
  exact isIso_colimitPost_of_isKernel D (internalHomNatLeft J O b)
    (internalHomNatLeft J O a) hw hker

/-! ### Restriction to a localized site -/

variable (X : RingedSite.{u, u, u})

/-- Restricting the internal Hom sheaf `Hom_O(F, -)` to the localized site over `U` gives the
internal Hom sheaf `Hom_{O|_U}(F|_U, -)` of the restrictions, naturally in the target. -/
noncomputable def internalHomOverNatIso (U : X.C)
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    internalHomSecondFunctor.{u, u, u, u} X.J X.O F ⋙
        _root_.SheafOfModules.overFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) U ≅
      _root_.SheafOfModules.overFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) U ⋙
        internalHomSecondFunctor.{u, u, u, u} (X.J.over U) (X.O.over U) (F.over U) :=
  NatIso.ofComponents (fun G => sheafInternalHomOverIso X U F G) (by intros; ext; rfl)

/-- On a ringed site, internal Hom out of a module of finite presentation commutes with filtered
colimits: the canonical map `colim_λ Hom_O(F, G_λ) ⟶ Hom_O(F, colim_λ G_λ)` is an isomorphism
for every filtered diagram `λ ↦ G_λ`. -/
@[stacks 0GMZ]
theorem internalHomSecondFunctor_preservesFilteredColimits
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    [F.IsFinitePresentation]
    (K : Type u) [Category.{u} K] [IsFiltered K] :
    PreservesColimitsOfShape K (internalHomSecondFunctor.{u, u, u, u} X.J X.O F) := by
  obtain ⟨ι, U, hU, hP⟩ :=
    (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations F).1
      ‹F.IsFinitePresentation›
  refine ⟨fun {D} ↦ ?_⟩
  have hiso : IsIso (colimit.post D (internalHomSecondFunctor.{u, u, u, u} X.J X.O F)) := by
    refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hU _ (fun i => ?_)
    obtain ⟨P, hPfin⟩ := hP i
    have hρ : PreservesColimitsOfSize.{u, u}
        (_root_.SheafOfModules.overFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i)) :=
      Stacks.SheafOfModules.preservesColimits_overFunctor_of_small _ (U i)
    have hsl : IsIso (colimit.post (D ⋙ _root_.SheafOfModules.overFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i))
        (internalHomSecondFunctor.{u, u, u, u} (X.J.over (U i)) (X.O.over (U i))
          (F.over (U i)))) :=
      isIso_colimitPost_of_presentation (X.J.over (U i)) (X.O.over (U i)) P hPfin _
    have _ : PreservesColimit (D ⋙ _root_.SheafOfModules.overFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i))
        (internalHomSecondFunctor.{u, u, u, u} (X.J.over (U i)) (X.O.over (U i))
          (F.over (U i))) :=
      preservesColimit_of_isIso_post _ _
    have _ : PreservesColimit D
        (_root_.SheafOfModules.overFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i)) :=
      hρ.preservesColimitsOfShape.preservesColimit
    have hcomp : PreservesColimit D
        (_root_.SheafOfModules.overFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i) ⋙
          internalHomSecondFunctor.{u, u, u, u} (X.J.over (U i)) (X.O.over (U i))
            (F.over (U i))) :=
      comp_preservesColimit _ _
    have _ : PreservesColimit D
        (internalHomSecondFunctor.{u, u, u, u} X.J X.O F ⋙
          _root_.SheafOfModules.overFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i)) :=
      (preservesColimit_iff_of_natIso D (internalHomOverNatIso X (U i) F)).2 hcomp
    exact isIso_map_colimitPost D (internalHomSecondFunctor.{u, u, u, u} X.J X.O F)
      (_root_.SheafOfModules.overFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) (U i))
  exact preservesColimit_of_isIso_post _ _

end SmallSite

end Stacks.SheafOfModules.InternalHom

end
