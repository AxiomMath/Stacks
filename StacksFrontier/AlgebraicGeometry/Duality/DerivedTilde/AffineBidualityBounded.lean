module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineBidualitySlice
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionReduction
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.Homology.DerivedCategory.HomFromSingleProjectiveDetection
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ModelBiduality
public import StacksFrontier.RingTheory.Ext.DerivedFiniteness

/-!
# Biduality for a bounded complex with coherent cohomology on an affine scheme

Let `R` be a Noetherian ring, `ω` a dualizing complex for `R` and `L` a bounded object of `D(R)`
with finite cohomology. On `X = Spec R` the biduality morphism of [Stacks, Tag 0A89]

`L̃ ⟶ R𝓗om(R𝓗om(L̃, ω̃), ω̃)`

is an isomorphism.

No identification of the comparison of [Stacks, Tag 0A6H] (3)(a) with evaluation morphisms is
used. Both sides lie in `D_QCoh(𝒪_X)`, which `~` identifies with `D(R)` ([Stacks, Tag 06Z0]), and
there the shifts of `R` detect isomorphisms; so it suffices that postcomposition with the
biduality morphism is bijective on morphisms out of `R̃[-j]`. Postcomposition with the biduality
morphism is the duality functor on morphisms, up to a bijection
(`CategoryTheory.BidualityTransfer.bijective_comp_iff_bijective`), and the duality functor on
morphisms between pseudo-coherent objects is read off over the ring through the comparison of
[Stacks, Tag 0A6H] (3)(a) by its naturality alone. Over the ring it is bijective by canonical
biduality [stacks 0A7C] (`Dualizing.bijective_derivedHom_map_of_finiteCohomology`).

## Main results

* `Stacks.SheafOfModules.bijective_comp_derivedBiduality_iff`: on a ringed space, postcomposition
  with the biduality morphism is bijective exactly when the duality functor on morphisms is.
* `Stacks.Duality.isIso_derivedBiduality_derivedTilde_of_bounded`: the biduality morphism of
  `ω̃`, `L̃` on `Spec R` is an isomorphism.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace Stacks.SheafOfModules

section RingedSpace

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Evaluation is dinatural in the internal-hom variable.** For `g : Z ⟶ L`, the morphism
`R𝓗om(L, K) ⟶ R𝓗om(Z, K)` induced by `g`, tensored with `Z` and followed by evaluation, is
`R𝓗om(L, K) ⊗ g` followed by evaluation. -/
theorem derivedSheafHomCounit_dinatural (K : DerivedCategory (StructureSheafModules Rc))
    {Z L : DerivedCategory (StructureSheafModules Rc)} (g : Z ⟶ L) :
    ((derivedTensor Rc).map (((derivedSheafHom Rc).map g.op).app K)).app Z ≫
        derivedSheafHomCounit Rc Z K =
      ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj K)).map g ≫
        derivedSheafHomCounit Rc L K := by
  rw [derivedTensor_map_app_comp_derivedSheafHomCounit Rc (((derivedSheafHom Rc).obj (op L)).obj K)
      Z K (((derivedSheafHom Rc).map g.op).app K),
    derivedSheafHomCounit_whiskerLeft_eq Rc K g]

/-- **The biduality morphism is natural** in its argument: for `g : L ⟶ L'`,
`g ≫ β_{L'} = β_L ≫ R𝓗om(R𝓗om(g, K), K)`. -/
theorem derivedBiduality_naturality (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)} (g : L ⟶ L') :
    g ≫ derivedBiduality Rc K L' = derivedBiduality Rc K L ≫
      ((derivedSheafHom Rc).map (((derivedSheafHom Rc).map g.op).app K).op).app K :=
  CategoryTheory.BidualityTransfer.comp_biduality_eq (derivedTensor Rc)
    (derivedTensorBraiding Rc) (fun f B => derivedTensorBraiding_naturality_left Rc f B)
    (fun A _ _ f => derivedTensorBraiding_naturality_right Rc A f) g
    (derivedSheafHomCounit Rc L K) (derivedSheafHomCounit Rc L' K)
    (derivedSheafHomCounit Rc _ K) (derivedSheafHomCounit Rc _ K)
    (fun W => (tensorHomBijective_derivedSheafHomCounit' Rc _ K W).1)
    (derivedBiduality Rc K L) (derivedBiduality_spec Rc K L)
    (derivedBiduality Rc K L') (derivedBiduality_spec Rc K L')
    _ (derivedSheafHomCounit_dinatural Rc K g) _ (derivedSheafHomCounit_dinatural Rc K _)

/-- **Postcomposition with the biduality morphism is the duality functor on morphisms**, up to a
bijection: `g ↦ g ≫ β_L` on `Hom(Z, L)` is bijective exactly when `g ↦ R𝓗om(g, K)`,
`Hom(Z, L) ⟶ Hom(R𝓗om(L, K), R𝓗om(Z, K))`, is. -/
theorem bijective_comp_derivedBiduality_iff (K L Z : DerivedCategory (StructureSheafModules Rc)) :
    Function.Bijective (fun g : Z ⟶ L => g ≫ derivedBiduality Rc K L) ↔
      Function.Bijective (fun g : Z ⟶ L => ((derivedSheafHom Rc).map g.op).app K) :=
  CategoryTheory.BidualityTransfer.bijective_comp_iff_bijective (derivedTensor Rc)
    (derivedTensorBraiding Rc) (fun f B => derivedTensorBraiding_naturality_left Rc f B)
    (derivedSheafHomCounit Rc L K) (derivedSheafHomCounit Rc Z K)
    (fun W => tensorHomBijective_derivedSheafHomCounit' Rc Z K W)
    (derivedSheafHomCounit Rc _ K)
    (fun W => tensorHomBijective_derivedSheafHomCounit' Rc _ K W)
    (derivedBiduality Rc K L) (derivedBiduality_spec Rc K L)
    (fun g => ((derivedSheafHom Rc).map g.op).app K)
    (fun g => derivedSheafHomCounit_dinatural Rc K g)

end RingedSpace

end Stacks.SheafOfModules

namespace Stacks.Duality

open Stacks.SheafOfModules

variable (R : CommRingCat.{u}) [IsNoetherianRing R]
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-- Postcomposition with the forward map of an isomorphism is bijective. -/
private theorem bijective_comp_hom {C : Type*} [Category C] {X Y Y' : C} (e : Y ≅ Y') :
    Function.Bijective (fun y : X ⟶ Y => y ≫ e.hom) :=
  ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun y => ⟨y ≫ e.inv, by simp⟩⟩

/-- Precomposition with the forward map of an isomorphism is bijective. -/
private theorem bijective_hom_comp {C : Type*} [Category C] {X X' Y : C} (e : X ≅ X') :
    Function.Bijective (fun y : X' ⟶ Y => e.hom ≫ y) :=
  ⟨fun _ _ h => (cancel_epi e.hom).1 h, fun y => ⟨e.inv ≫ y, by simp⟩⟩

omit [IsNoetherianRing R]
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)] in
/-- A nonzero module receives a nonzero morphism from the ring. -/
theorem exists_hom_ring_ne_zero (F : ModuleCat.{u} R) (hF : ¬ IsZero F) :
    ∃ ψ : ModuleCat.of R R ⟶ F, ψ ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x : F, x ≠ 0 := by
    by_contra! hs
    exact hF (@ModuleCat.isZero_of_subsingleton _ _ F ⟨fun a b => by rw [hs a, hs b]⟩)
  refine ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton R F x), fun h => hx ?_⟩
  simpa using congrArg (fun φ => φ.hom (1 : R)) h

omit [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)] in
/-- The ring, placed in one degree, is pseudo-coherent and bounded below. -/
theorem isPseudoCoherent_singleFunctor_ring (j : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) j).obj (ModuleCat.of R R)) := by
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    _ 0 (R : Type u)).2.1).2 ⟨⟨j, fun i hi => DerivedCategory.isZero_of_isLE _ j i hi⟩, fun k => ?_⟩
  by_cases hk : k = j
  · subst hk
    have : Module.Finite R ((𝟭 (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
      inferInstanceAs (Module.Finite R R)
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) k).app
        (ModuleCat.of R R)).symm.toLinearEquiv
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) k).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) j).obj (ModuleCat.of R R))) := by
      rcases lt_or_gt_of_ne hk with h | h
      · exact DerivedCategory.isZero_of_isGE _ j k h
      · exact DerivedCategory.isZero_of_isLE _ j k h
    exact Module.Finite.of_surjective (0 : R →ₗ[R] _) fun y =>
      ⟨0, (ModuleCat.subsingleton_of_isZero hz).elim _ _⟩

omit [IsNoetherianRing R]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)] in
/-- **The duality functor on morphisms between associated complexes is read over the ring.** For
`W`, `L` pseudo-coherent and `ω` bounded below, if `g ↦ RHom_R(g, ω)` is bijective on
`Hom(W, L)` then `g ↦ R𝓗om(g, ω̃)` is bijective on `Hom(W̃, L̃)`: the two agree through the
comparison of [Stacks, Tag 0A6H] (3)(a), by its naturality in the first variable. -/
theorem bijective_derivedSheafHom_map_derivedTilde (ω L W : DerivedCategory (ModuleCat.{u} R))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherent L)
    (hW : StacksDraft.PseudoCoherence.IsPseudoCoherent W)
    (hω : (DerivedCategory.TStructure.t).plus ω)
    (hbij : Function.Bijective (fun g : W ⟶ L =>
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))).hom.map
        (show (op L, ω) ⟶ (op W, ω) from (g.op, 𝟙 ω)))) :
    Function.Bijective (fun g : (tilde.functor R).mapDerivedCategory.obj W ⟶
        (tilde.functor R).mapDerivedCategory.obj L =>
      ((derivedSheafHom (Spec R).sheaf).map g.op).app
        ((tilde.functor R).mapDerivedCategory.obj ω)) := by
  let hff := StandardModel.mapDerivedCategoryFullyFaithful R
  let θL := affinePseudoCoherentDerivedSheafHomIso R L ω hL hω
  let θW := affinePseudoCoherentDerivedSheafHomIso R W ω hW hω
  rw [← Function.Bijective.of_comp_iff _ (hff.map_bijective W L)]
  have hfun : ((fun g : (tilde.functor R).mapDerivedCategory.obj W ⟶
        (tilde.functor R).mapDerivedCategory.obj L =>
      ((derivedSheafHom (Spec R).sheaf).map g.op).app
        ((tilde.functor R).mapDerivedCategory.obj ω)) ∘
        fun g : W ⟶ L => (tilde.functor R).mapDerivedCategory.map g) =
      (fun y => (θL.hom ≫ y) ≫ θW.inv) ∘ (fun h => (tilde.functor R).mapDerivedCategory.map h) ∘
        (fun g : W ⟶ L =>
          (StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))).hom.map
            (show (op L, ω) ⟶ (op W, ω) from (g.op, 𝟙 ω))) :=
    funext fun g =>
      (Iso.eq_comp_inv _).2 (affinePseudoCoherentDerivedSheafHomIso_natural_left R hL hW hω g)
  rw [hfun]
  refine Function.Bijective.comp ?_ ((hff.map_bijective _ _).comp hbij)
  exact (bijective_comp_hom θW.symm).comp (bijective_hom_comp θL)

/-- **Biduality for a bounded complex with finite cohomology on an affine scheme.** For `R`
Noetherian, `ω` a dualizing complex for `R` and `L` a bounded object of `D(R)` with finite
cohomology, the biduality morphism `L̃ ⟶ R𝓗om(R𝓗om(L̃, ω̃), ω̃)` on `Spec R` is an isomorphism. -/
theorem isIso_derivedBiduality_derivedTilde_of_bounded
    (ω L : DerivedCategory (ModuleCat.{u} R)) (hω : Dualizing.IsDualizingComplex ω)
    (m m' : ℤ) (hLge : L.IsGE m) (hLle : L.IsLE m')
    (hL : ∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L)) :
    IsIso (derivedBiduality (Spec R).sheaf ((tilde.functor R).mapDerivedCategory.obj ω)
      ((tilde.functor R).mapDerivedCategory.obj L)) := by
  let d₀ := StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))
  let tl := (tilde.functor R).mapDerivedCategory
  let hff := StandardModel.mapDerivedCategoryFullyFaithful R
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  have hωge : ω.IsGE a := by
    obtain ⟨I, _, -, -, ⟨e⟩⟩ := hamp
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hωplus : (DerivedCategory.TStructure.t).plus ω := ⟨a, hωge⟩
  have pc_of : ∀ (Y : DerivedCategory (ModuleCat.{u} R)) (n : ℤ), Y.IsLE n →
      (∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj Y)) →
      StacksDraft.PseudoCoherence.IsPseudoCoherent Y := fun Y n hY hYf =>
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      Y 0 (R : Type u)).2.1).2 ⟨⟨n, fun i hi => DerivedCategory.isZero_of_isLE Y n i hi⟩, hYf⟩
  let θ := fun (Y : DerivedCategory (ModuleCat.{u} R))
      (hY : StacksDraft.PseudoCoherence.IsPseudoCoherent Y) =>
    affinePseudoCoherentDerivedSheafHomIso R Y ω hY hωplus
  let P₁ := d₀.hom.obj (op L, ω)
  have hP₁le : P₁.IsLE (b - m) :=
    StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude d₀ L ω m a b hLge hamp
  have hP₁fin : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj P₁) := fun i =>
    StacksDraft.DerivedHom.finite_homology_derivedHom d₀ L ω m' a hLle hωge hL
      hω.finiteCohomology i
  have hLpc := pc_of L m' hLle hL
  have hP₁pc := pc_of P₁ (b - m) hP₁le hP₁fin
  let K := tl.obj ω
  let E : ((derivedSheafHom (Spec R).sheaf).obj
        (op (((derivedSheafHom (Spec R).sheaf).obj (op (tl.obj L))).obj K))).obj K ≅
      tl.obj (d₀.hom.obj (op P₁, ω)) :=
    ((derivedSheafHom (Spec R).sheaf).mapIso (θ L hLpc).op).symm.app K ≪≫ θ P₁ hP₁pc
  let β := derivedBiduality (Spec R).sheaf K (tl.obj L)
  let f' : L ⟶ d₀.hom.obj (op P₁, ω) := hff.preimage (β ≫ E.hom)
  have hf' : tl.map f' = β ≫ E.hom := hff.map_preimage _
  have hEiso : IsIso E.hom := ⟨⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩⟩
  suffices IsIso f' by
    have : IsIso (β ≫ E.hom) := hf' ▸ Functor.map_isIso tl f'
    exact IsIso.of_isIso_comp_right β E.hom
  refine DerivedCategory.isIso_of_bijective_comp_singleFunctor_projective (ModuleCat.of R R)
    (exists_hom_ring_ne_zero R) f' fun j => ?_
  let W := (DerivedCategory.singleFunctor (ModuleCat.{u} R) j).obj (ModuleCat.of R R)
  have hWpc := isPseudoCoherent_singleFunctor_ring R j
  have hD := bijective_derivedSheafHom_map_derivedTilde R ω L W hLpc hWpc hωplus
    (Dualizing.bijective_derivedHom_map_of_finiteCohomology ω L W hω hL)
  have hβ := (bijective_comp_derivedBiduality_iff (Spec R).sheaf K (tl.obj L) (tl.obj W)).2 hD
  rw [← Function.Bijective.of_comp_iff' (hff.map_bijective W (d₀.hom.obj (op P₁, ω)))]
  have hfun : (fun b : W ⟶ d₀.hom.obj (op P₁, ω) => tl.map b) ∘ (fun a : W ⟶ L => a ≫ f') =
      (fun y => y ≫ E.hom) ∘ (fun g : tl.obj W ⟶ tl.obj L => g ≫ β) ∘ (fun a => tl.map a) := by
    funext a
    exact ((tl.map_comp a f').trans (congrArg (tl.map a ≫ ·) hf')).trans
      (Category.assoc _ _ _).symm
  rw [hfun]
  exact (bijective_comp_hom E).comp (hβ.comp (hff.map_bijective _ _))

end Stacks.Duality
