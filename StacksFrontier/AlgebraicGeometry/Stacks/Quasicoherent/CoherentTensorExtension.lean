module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentPointPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidalComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentFilteredColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctorExtension
public import StacksFrontier.CategoryTheory.KanExtension.ExtendBraided
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Fiber

/-!
# Extending a right exact tensor functor `Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` to `QCoh(𝒪_𝒳)`

Let `𝒳` be a Noetherian algebraic stack and `R` a ring. The first step of the proof of Stacks
0GRR applies Stacks 0GRJ to a right exact tensor functor `F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R`: it extends
to a right exact tensor functor `G : QCoh(𝒪_𝒳) ⥤ Mod_R` commuting with all colimits, in
particular with direct sums, together with a monoidal identification of the restriction of `G`
to `Coh(𝒪_𝒳)` with `F`. The target here is `Mod_R`, not the quasi-coherent modules on an
algebraic stack over the same base, so the argument is the one of Stacks 0GRJ
(`AlgebraicGeometry.Stack.existsUnique_tensorExtension_coherent`) with the target replaced: the
categorical extension `CategoryTheory.ObjectProperty.existsUnique_tensorExtension` (Stacks 0FWY)
at `D := ModuleCat R`, applied with the inputs on `𝒳` that Stacks 0GRJ uses: coherent modules are
categorically compact in `QCoh(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.coherentQuasicoherent_le_isFinitelyPresentable`) and every
quasi-coherent module is a filtered colimit of coherent ones (Stacks 0GRF,
`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`, in the form
`AlgebraicGeometry.Stack.ind_coherentQuasicoherent`).

Two monoidal structures on `QCoh(𝒪_𝒳)` are in the library
(`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidalComparison`): the
localized one (I) of `AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules`, in which
the base proves the closure and colimit properties of `Coh(𝒪_𝒳)` used by the extension, and the
strict one (II) of `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal`, of which
`Coh(𝒪_𝒳)` (`AlgebraicGeometry.Stack.isMonoidal_coherentModules`) is a full monoidal
subcategory. The extension is carried out for (I) and transported to (II) along the braided
monoidal comparison. The comparison of the two full subcategories of coherent modules is
`AlgebraicGeometry.Stack.AlgebraicStacks.coherentQuasicoherentEquivalence`, an isomorphism of
categories whose functor is braided monoidal.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.coherentLocalizedInclusion`: the inclusion of
  `Coh(𝒪_𝒳)` into `QCoh(𝒪_𝒳)` with the localized structure (I), with its braided monoidal
  structure `AlgebraicGeometry.Stack.AlgebraicStacks.coherentLocalizedInclusionBraided`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.coherentQuasicoherentEquivalence`: `Coh(𝒪_𝒳)` is the
  full subcategory `AlgebraicGeometry.Stack.coherentQuasicoherent` of `QCoh(𝒪_𝒳)`; its functor is
  braided monoidal (`coherentQuasicoherentEquivalenceBraided`) when that full subcategory is
  monoidal for (I).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_localizedTensorExtension`: the extension, for
  the localized structure (I) on `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_coherentTensorExtension`: **the `Mod_R`-valued
  form of Stacks 0GRJ**, for the strict structure (II): a right exact tensor functor
  `F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` extends to a right exact tensor functor `QCoh(𝒪_𝒳) ⥤ Mod_R`
  commuting with all colimits.

## References

* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
* [Stacks Project, Tag 0FWY](https://stacks.math.columbia.edu/tag/0FWY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.LaxMonoidal

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w w'

namespace CategoryTheory.ObjectProperty

variable {C : Type*} {D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  (P : ObjectProperty D) [P.IsMonoidal] (F : C ⥤ D) (h : ∀ X, P (F.obj X)) [F.Monoidal]

/-- The identification `P.lift F h ⋙ P.ι ≅ F`, for a monoidal functor `F` lifted to a full
monoidal subcategory and followed by the inclusion, is a monoidal natural isomorphism. -/
instance isMonoidal_liftCompιIso_hom : NatTrans.IsMonoidal (P.liftCompιIso F h).hom where
  unit := by
    rw [Functor.LaxMonoidal.comp_ε, ι_ε, Category.id_comp]
    exact Category.comp_id _
  tensor X Y := by
    rw [Functor.LaxMonoidal.comp_μ, ι_μ]
    change (𝟙 _ ≫ μ F X Y) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ F X Y
    rw [Category.id_comp, Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

section Strict

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided coherentAmbientSymmetric
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
  coherentQuasicoherentInclusionBraided

/-- The inclusion `Coh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`, with `QCoh(𝒪_𝒳)` written as
`AlgebraicGeometry.FibredSite.quasicoherentModules`: the inclusion followed by the comparison of
the two monoidal structures on `QCoh(𝒪_𝒳)`, which is the identity. -/
abbrev coherentLocalizedInclusion :
    Coh.{u, u, w} B S hS 𝒳 ⥤ FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids :=
  coherentQuasicoherentInclusion B S hS 𝒳 ⋙ (quasicoherentModulesComparison B S hS 𝒳).functor

/-- **The inclusion of `Coh(𝒪_𝒳)` into `QCoh(𝒪_𝒳)` with the localized monoidal structure is
braided monoidal**: it is the composite of the inclusion into `QCoh(𝒪_𝒳)` with the strict
structure (II), `AlgebraicGeometry.Stack.coherentQuasicoherentInclusionBraided`, with the
comparison `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonBraided`. -/
@[instance_reducible]
def coherentLocalizedInclusionBraided :
    @Functor.Braided _ _ _ _ _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (coherentLocalizedInclusion B S hS 𝒳) :=
  @Functor.Braided.instComp _ _ _ _ _ _ (_) (_) _ _ (_) (_) _ _
    (coherentQuasicoherentInclusionBraided B S hS 𝒳)
    (quasicoherentModulesComparisonBraided B S hS 𝒳)

end Strict

/-- **`Coh(𝒪_𝒳)` is the full subcategory of coherent quasi-coherent modules**: the isomorphism of
categories between `AlgebraicGeometry.Stack.Coh`, a full subcategory of `Mod(𝒪_𝒳)`, and the full
subcategory `AlgebraicGeometry.Stack.coherentQuasicoherent` of `QCoh(𝒪_𝒳)`. Both functors are the
identity on underlying modules. -/
def coherentQuasicoherentEquivalence :
    Coh.{u, u, w} B S hS 𝒳 ≌ (coherentQuasicoherent B S hS 𝒳).FullSubcategory where
  functor := (coherentQuasicoherent B S hS 𝒳).lift (coherentLocalizedInclusion B S hS 𝒳)
    fun M ↦ M.2
  inverse :=
    { obj M := ⟨M.obj.obj, M.2⟩
      map f := ObjectProperty.homMk f.hom.hom }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

section Localized

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided coherentAmbientSymmetric
  FibredSite.monoidalCategoryQuasicoherentModules FibredSite.braidedCategoryQuasicoherentModules
  coherentLocalizedInclusionBraided

set_option backward.isDefEq.respectTransparency false in
/-- The functor of `AlgebraicGeometry.Stack.AlgebraicStacks.coherentQuasicoherentEquivalence` is
braided monoidal, for the full monoidal subcategory structure on the coherent quasi-coherent
modules induced by the localized structure (I): it is the lift of the braided monoidal functor
`AlgebraicGeometry.Stack.AlgebraicStacks.coherentLocalizedInclusion`. -/
@[instance_reducible]
def coherentQuasicoherentEquivalenceBraided [(coherentQuasicoherent B S hS 𝒳).IsMonoidal] :
    (coherentQuasicoherentEquivalence B S hS 𝒳).functor.Braided :=
  { ObjectProperty.liftMonoidal _ (coherentLocalizedInclusion B S hS 𝒳) (fun M ↦ M.2),
    ObjectProperty.liftLaxBraided _ _ _ with }

/-- The functor of `AlgebraicGeometry.Stack.AlgebraicStacks.coherentQuasicoherentEquivalence` is
additive. -/
instance coherentQuasicoherentEquivalence_functor_additive :
    (coherentQuasicoherentEquivalence B S hS 𝒳).functor.Additive where
  map_add := rfl

variable {B S hS 𝒳} {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- **The extension of a right exact tensor functor `Coh(𝒪_𝒳) ⥤ Mod_R`, for the localized
monoidal structure on `QCoh(𝒪_𝒳)`.** Let `𝒳` be a Noetherian algebraic stack. An additive braided
monoidal functor `F : Coh(𝒪_𝒳) ⥤ Mod_R` preserving finite colimits is, by a monoidal isomorphism
`e`, the restriction to `Coh(𝒪_𝒳)` of an additive braided monoidal functor `QCoh(𝒪_𝒳) ⥤ Mod_R`
preserving finite colimits and all small colimits, `QCoh(𝒪_𝒳)` carrying the localized structure
`AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules`. -/
theorem exists_localizedTensorExtension (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (F : Coh.{u, u, w} B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.Additive] [F.Braided]
    [PreservesFiniteColimits F] :
    ∃ (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ⥤ ModuleCat.{u} R) (_ : G.Braided)
      (e : coherentLocalizedInclusion B S hS 𝒳 ⋙ G ≅ F),
      G.Additive ∧ PreservesFiniteColimits G ∧ PreservesColimitsOfSize.{u, u} G ∧
        NatTrans.IsMonoidal e.hom := by
  have := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have := hasZeroObject_quasicoherentModules B S hS 𝒳
  have : HasFiniteColimits (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := hasFiniteColimits_of_hasColimitsOfSize _
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_pair B S hS 𝒳 h𝒳.2.2
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_empty B S hS 𝒳 h𝒳.2.2
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_parallelPair B S hS 𝒳 h𝒳.2.2
  have := fun M ↦ preservesColimitsOfSize_quasicoherentTensorLeft B S hS 𝒳 M
  have := fun M ↦ preservesColimitsOfSize_quasicoherentTensorRight B S hS 𝒳 M
  let := coherentQuasicoherentEquivalenceBraided B S hS 𝒳
  obtain ⟨G, hG, e, h₁, h₂, h₃, he⟩ :=
    ObjectProperty.exists_braided_extension_of_equivalence (coherentQuasicoherent B S hS 𝒳)
      (coherentQuasicoherent_le_isFinitelyPresentable B S hS 𝒳 h𝒳)
      (ind_coherentQuasicoherent B S hS 𝒳 h𝒳) (coherentQuasicoherentEquivalence B S hS 𝒳) F
  let i : coherentLocalizedInclusion B S hS 𝒳 ≅
      (coherentQuasicoherentEquivalence B S hS 𝒳).functor ⋙ (coherentQuasicoherent B S hS 𝒳).ι :=
    (ObjectProperty.liftCompιIso _ _ _).symm
  have i₀ : NatTrans.IsMonoidal i.hom :=
    @Iso.instIsMonoidalInvFunctor _ _ (_) _ _ (_) _ _ (_) (_) _
      (@ObjectProperty.isMonoidal_liftCompιIso_hom _ _ _ _ (_) (_) _ (_) _ _ (_))
  refine ⟨G, hG, Functor.isoWhiskerRight i G ≪≫ Functor.associator _ _ _ ≪≫ e, h₁, h₂, h₃, ?_⟩
  exact inferInstanceAs (NatTrans.IsMonoidal
    (Functor.whiskerRight i.hom G ≫ (Functor.associator _ _ _).hom ≫ e.hom))

end Localized

section Strict

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided coherentAmbientSymmetric
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
  coherentQuasicoherentInclusionBraided

variable {B S hS 𝒳} {R : Type u} [CommRing R]

/-- **The `Mod_R`-valued form of Stacks 0GRJ** (the first step of the proof of Stacks 0GRR). Let
`𝒳` be a Noetherian algebraic stack and `R` a ring. Every right exact tensor functor
`F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` — additive, braided monoidal and preserving finite colimits — extends
to a right exact tensor functor `G : QCoh(𝒪_𝒳) ⥤ Mod_R` commuting with all small colimits, in
particular with direct sums: there is a monoidal isomorphism `e` between the restriction of `G`
to `Coh(𝒪_𝒳)` and `F` followed by the inclusion `Mod^{fg}_R ⥤ Mod_R`. The monoidal structures are
the tensor products of `𝒪_𝒳`-modules (Tag 01CA) and of `R`-modules. -/
theorem exists_coherentTensorExtension (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (F : Coh.{u, u, w} B S hS 𝒳 ⥤ FGModuleCat.{u} R) [F.Additive] [F.Braided]
    [PreservesFiniteColimits F] :
    ∃ (G : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) (_ : G.Additive) (_ : G.Braided)
      (_ : PreservesFiniteColimits G) (_ : PreservesColimitsOfSize.{u, u} G)
      (e : coherentQuasicoherentInclusion B S hS 𝒳 ⋙ G ≅ F ⋙ (ModuleCat.isFG.{u} R).ι),
      NatTrans.IsMonoidal e.hom := by
  have : PreservesFiniteColimits (ModuleCat.isFG.{u} R).ι :=
    inferInstanceAs (PreservesFiniteColimits (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)))
  have : (ModuleCat.isFG.{u} R).ι.Additive :=
    inferInstanceAs (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive
  have : PreservesFiniteColimits (F ⋙ (ModuleCat.isFG.{u} R).ι) :=
    comp_preservesFiniteColimits _ _
  obtain ⟨G, hG, e, h₁, h₂, h₃, he⟩ :=
    exists_localizedTensorExtension h𝒳 (F ⋙ (ModuleCat.isFG.{u} R).ι)
  refine ⟨(quasicoherentModulesComparison B S hS 𝒳).functor ⋙ G, h₁,
    comparisonFunctorCompBraided B S hS 𝒳 G hG, h₂, h₃,
    (Functor.associator _ _ _).symm ≪≫ e, ?_⟩
  exact @NatTrans.IsMonoidal.comp _ _ (_) _ _ (_) _ _ _ (Functor.associator _ _ _).inv (_) (_) (_)
    e.hom (@Iso.instIsMonoidalInvFunctor _ _ (_) _ _ (_) _ _ (_) (_) (Functor.associator _ _ _)
      (@NatTrans.IsMonoidal.instHomFunctorAssociator _ _ (_) _ _ (_) _ _ (_) _ _ (_) _ _ _
        (_) (_) (_))) he

end Strict

end AlgebraicGeometry.Stack.AlgebraicStacks
