module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.EtaleNeighbourhoodConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput

/-!
# Inverse images of locally constant sheaves of finite type, along any morphism

Let `u : U' ⟶ U` be a morphism of schemes and `H` a locally constant sheaf of finite type of
`ℤ/N`-modules on `U_étale` ([Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)). Then
`u⁻¹ H` is locally constant of finite type on `U'_étale`: a covering `{Vᵢ ⟶ U}` on which `H`
is constant with finitely generated values `Eᵢ` pulls back, over any étale `W ⟶ U'`, to the
covering `{Vᵢ ×_U W ⟶ W}`, and the restriction of `u⁻¹ H` to `Vᵢ ×_U W` is the inverse image of
the constant sheaf `Eᵢ` on `Vᵢ`, which is constant
(`Stacks.EtaleCohomology.etaleModuleInverseImageConstantIso`).

`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_etaleModuleInverseImage` is the case of a
finite étale morphism of connected schemes with coefficients `ℤ/ℓ`, proved through a big étale
site; here the morphism is arbitrary and the coefficients are `ℤ/N`, for instance the
inclusion of a geometric fibre.

## Main results

* `Stacks.EtaleCohomology.lccModules_etaleModuleInverseImage`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe (see
-- `Stacks.EtaleCohomology.lccModules`).
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **The inverse image of a locally constant sheaf of finite type is locally constant of finite
type**, along any morphism of schemes `u : U' ⟶ U`. -/
theorem lccModules_etaleModuleInverseImage (N : ℕ) {U U' : Scheme.{u}} (u' : U' ⟶ U)
    (H : EtaleModules.{u, 0} (ZMod N) U) (hH : lccModules U N H) :
    lccModules U' N ((etaleModuleInverseImage.{u, 0} (ZMod N) u').obj H) := by
  intro W'
  obtain ⟨I, V, f, hcov, htriv⟩ := hH (Scheme.Etale.mk (𝟙 U))
  have hsurj := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).1 hcov
  have hw : ∀ i, (V i).hom = (f i).left := fun i =>
    (MorphismProperty.Over.w (f i)).symm.trans (Category.comp_id _)
  let P : I → U'.Etale := fun i =>
    Scheme.Etale.mk (pullback.snd (V i).hom (W'.hom ≫ u') ≫ W'.hom)
  let p : ∀ i, P i ⟶ W' := fun i =>
    MorphismProperty.Over.homMk (pullback.snd (V i).hom (W'.hom ≫ u')) rfl
  refine ⟨I, P, p, ?_, fun i => ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : (W'.hom ≫ u').base x ∈ ⋃ i, Set.range (f i).left.base := by
      rw [hsurj]; trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    show x ∈ Set.range (pullback.snd (V i).hom (W'.hom ≫ u')).base
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, by rwa [hw]⟩
  · obtain ⟨E, hE, ⟨c⟩⟩ := htriv i
    refine ⟨E, hE, ⟨?_⟩⟩
    let Φ := etaleOverSheafEquivalence (P i) (ModuleCat.{u + 1} (ZMod N))
    refine Φ.fullyFaithfulFunctor.preimageIso ?_
    let cV : (etaleModuleInverseImage.{u, 0} (ZMod N) (V i).hom).obj H ≅
        (constantSheaf (smallEtaleTopology (V i).left) (ModuleCat.{u + 1} (ZMod N))).obj E :=
      (etaleModuleInverseImageIsoOverRestriction (ZMod N) (V i)).app H ≪≫
        (etaleOverRestrictionIso (V i) _).symm.app H ≪≫
        (etaleOverSheafEquivalence (V i) _).functor.mapIso c.symm ≪≫
        (etaleOverSheafEquivalenceConstantIso (V i) _).app E
    have hsq : (P i).hom ≫ u' = pullback.fst (V i).hom (W'.hom ≫ u') ≫ (V i).hom := by
      show (pullback.snd (V i).hom (W'.hom ≫ u') ≫ W'.hom) ≫ u' = _
      rw [Category.assoc, ← pullback.condition]
    exact (etaleOverSheafEquivalenceConstantIso (P i) _).app E ≪≫
      ((etaleModuleInverseImageConstantIso (ZMod N)
        (pullback.fst (V i).hom (W'.hom ≫ u'))).app E).symm ≪≫
      (etaleModuleInverseImage.{u, 0} (ZMod N)
        (pullback.fst (V i).hom (W'.hom ≫ u'))).mapIso cV.symm ≪≫
      ((etaleModuleInverseImageCompIso.{u, 0} (ZMod N) (pullback.fst (V i).hom (W'.hom ≫ u'))
        (V i).hom).app H).symm ≪≫
      eqToIso (congrArg (fun m => (etaleModuleInverseImage.{u, 0} (ZMod N) m).obj H) hsq.symm) ≪≫
      (etaleModuleInverseImageCompIso.{u, 0} (ZMod N) (P i).hom u').app H ≪≫
      (etaleModuleInverseImageIsoOverRestriction (ZMod N) (P i)).app _ ≪≫
      (etaleOverRestrictionIso (P i) _).symm.app _

end Stacks.EtaleCohomology

end
