module

public import StacksFrontier.CategoryTheory.Monoidal.BidualityTransfer
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
public import StacksFrontier.RingTheory.Dualizing.BidualitySameUniverse

/-!
# Canonical biduality for the model-level derived tensor–Hom adjunction

Let `A` be a Noetherian ring and `ω` a dualizing complex for `A` ([stacks 0A7B]). For the
model-level adjunction `StacksDraft.DerivedHom.derivedHomAdjunction` over `A` itself — the one the
comparison of [Stacks, Tag 0A6H] (3)(a) is stated against — the canonical biduality morphism
`K ⟶ RHom_A(RHom_A(K, ω), ω)` is an isomorphism for every `K` with finite cohomology. This is the
biduality of [stacks 0A7C], read at that adjunction: the biduality criterion
`Dualizing.isIso_bidualityMor` applies to it directly, its homothety hypothesis being
`Dualizing.isIso_derivedHomothety_of_isDualizingComplex` and its evaluation hypothesis
`StacksDraft.DerivedHom.isIso_internalCurryMor_of_truncLE_pseudoCoherent`.

Consequently `RHom_A(-, ω)` is bijective on morphisms into an object with finite cohomology:
`g ↦ RHom_A(g, ω)`, `Hom(X, K) ⟶ Hom(RHom_A(K, ω), RHom_A(X, ω))`, is a bijection for every `X`.

## Main results

* `Dualizing.isIso_bidualityMor_of_isDualizingComplex` (in `BidualitySameUniverse`): canonical
  biduality at the model-level adjunction.
* `Dualizing.bijective_derivedHom_map_of_finiteCohomology`: the bijection on morphisms.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Dualizing

open StacksDraft.DerivedHom

universe u

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The model-level derived homothety of a dualizing complex identifies `RHom_A(ω, ω)` with the
tensor unit, so tensoring it with a module in degree zero returns that module: its Tor amplitude
is `[0, 0]`. -/
theorem torAmplitude_derivedHomSelf_model (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsDualizingComplex ω) :
    let D := derivedHomAdjunction (R := A)
    ∃ a b : ℤ, ∀ (N : ModuleCat.{u} A) (i : ℤ), i ∉ Set.Icc a b →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (D.tensor.obj (D.hom.obj (Opposite.op ω, ω),
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) := by
  intro D
  refine ⟨0, 0, fun N i hi => ?_⟩
  have hi' : i ≠ 0 := fun h => hi (by simp [h])
  have hh := isIso_derivedHomothety_of_isDualizingComplex D ω hω
  let e := asIso (derivedHomothety D.toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex A))) D.tensorUnitLeft ω)
  have hten : D.tensor.obj (D.hom.obj (Opposite.op ω, ω),
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N :=
    D.tensor.mapIso (Iso.prod e.symm (Iso.refl _)) ≪≫
      D.tensorUnitLeft ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)
  refine Limits.IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso hten)
  rcases lt_or_gt_of_ne hi' with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 i h
  · exact DerivedCategory.isZero_of_isLE _ 0 i h

/-- **`RHom_A(-, ω)` is bijective on morphisms into an object with finite cohomology.** For `ω` a
dualizing complex and `K` with finite cohomology, `g ↦ RHom_A(g, ω)` is a bijection
`Hom(X, K) ≃ Hom(RHom_A(K, ω), RHom_A(X, ω))` for every `X`: postcomposition with the invertible
biduality morphism of `K` is this map, up to the bijection exchanging the two variables. -/
theorem bijective_derivedHom_map_of_finiteCohomology (ω K X : DerivedCategory (ModuleCat.{u} A))
    (hω : IsDualizingComplex ω)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    Function.Bijective (fun g : X ⟶ K =>
      (derivedHomAdjunction (R := A)).hom.map
        (show (Opposite.op K, ω) ⟶ (Opposite.op X, ω) from (g.op, 𝟙 ω))) := by
  let d := (derivedHomAdjunction (R := A)).toDerivedHomAdjunction
  have hβ := isIso_bidualityMor_of_isDualizingComplex ω K hω hK
  let T : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) := Functor.curry.obj d.tensor
  have hbij : ∀ (L M W : DerivedCategory (ModuleCat.{u} A)),
      Function.Bijective (fun g : W ⟶ d.hom.obj (Opposite.op L, M) =>
        (T.map g).app L ≫ d.evaluation L M) := fun L M W => by
    convert (d.homEquiv W L M).bijective using 1
    funext g
    change d.tensor.map (g, 𝟙 L) ≫ d.evaluation L M = d.homEquiv W L M g
    rw [DerivedHomAdjunction.evaluation, ← d.homEquiv_naturality_left, Category.comp_id]
  have hspec : (T.map (bidualityMor d ω K)).app (d.hom.obj (Opposite.op K, ω)) ≫
      d.evaluation (d.hom.obj (Opposite.op K, ω)) ω =
        (d.tensorSwap K (d.hom.obj (Opposite.op K, ω))).hom ≫ d.evaluation K ω := by
    change d.tensor.map (show (K, d.hom.obj (Opposite.op K, ω)) ⟶
        (d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, ω)), ω),
          d.hom.obj (Opposite.op K, ω)) from (bidualityMor d ω K, 𝟙 _)) ≫ _ = _
    rw [DerivedHomAdjunction.evaluation, ← d.homEquiv_naturality_left, Category.comp_id,
      bidualityMor, AddEquiv.apply_symm_apply]
  refine (CategoryTheory.BidualityTransfer.bijective_comp_iff_bijective T
    d.tensorSwap
    (fun {Y Y'} f B => by
      change d.tensor.map (show (Y, B) ⟶ (Y', B) from (f, 𝟙 B)) ≫ _ =
        _ ≫ d.tensor.map (show (B, Y) ⟶ (B, Y') from (𝟙 B, f))
      exact d.tensorSwap_naturality f (𝟙 B))
    (d.evaluation K ω) (d.evaluation X ω) (hbij X ω)
    (d.evaluation (d.hom.obj (Opposite.op K, ω)) ω) (hbij _ ω)
    (bidualityMor d ω K) hspec
    (fun g => d.hom.map (show (Opposite.op K, ω) ⟶ (Opposite.op X, ω) from (g.op, 𝟙 ω)))
    (fun g => d.evaluation_naturality_left g)).1 ?_
  exact ⟨fun _ _ => (cancel_mono _).1,
    fun y => ⟨y ≫ inv (bidualityMor d ω K), by simp⟩⟩

end Dualizing
