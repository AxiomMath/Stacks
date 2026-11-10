module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.LocalRingPropertyList
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.ProperOverDvr
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedPurelyInseparable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric reducedness of fibres along a specialization

Let `f : X ⟶ Y` be a flat morphism of schemes which is locally of finite presentation, and let
`x' ⤳ x` be a specialization of points of `X`. If the fibre of `f` through `x` is geometrically
reduced over the residue field of its point of `Y`, then the fibre of `f` through `x'` is
geometrically reduced at `x'`. This is the half of [EGA IV₃, 12.1.1 (vi)] saying that the
points of `X` at which the fibre is geometrically reduced form a set stable under
generalization, for the points generalizing a point whose whole fibre is geometrically reduced.

The proof is by Noetherian approximation and a discrete valuation ring. Locally `f` is the base
change of a flat morphism of finite type over a base of finite type over `ℤ` (Stacks 05FE), and
both geometric reducedness of a fibre (Stacks 0576) and geometric reducedness of a fibre at a
point (Stacks 0384) can be read on such a model. Over a locally Noetherian base the
specialization is realized by a morphism from the spectrum of a discrete valuation ring `R`
whose generic residue field is any prescribed finitely generated extension of `κ(x')`
(Stacks 054F). The base change of `f` to `Spec R` is flat, so a uniformizer is a nonzerodivisor
in its local rings, and its special fibre is a base change of the geometrically reduced fibre
through `x`; Krull's intersection theorem then makes its local rings along the special fibre
reduced, hence also those at their generalizations. Reading this on the open generic fibre, and
pulling back along faithfully flat local homomorphisms, gives reducedness of the local rings of
the fibre through `x'` above `x'` after every finite purely inseparable extension of the residue
field, which is geometric reducedness at `x'` by Stacks 035Y, or by Stacks 020I over a perfect
field.

## Main results

* `AlgebraicGeometry.isGeometricallyReducedAt_fiber_of_specializes`: the statement above.
* `AlgebraicGeometry.isGeometricallyReducedAt_iff_of_etale`: geometric reducedness of a scheme
  over a field at a point is unchanged along an étale morphism.
* `AlgebraicGeometry.isGeometricallyReducedAt_fiber_iff_of_etale`: geometric reducedness of the
  fibres of a morphism at a point is étale local on the source.
* `AlgebraicGeometry.isGeometricallyReducedAt_fiber_iff_of_isPullback`: geometric reducedness
  of the fibres of a morphism at a point is unchanged under base change.
* `AlgebraicGeometry.isReduced_stalk_iff_of_etale`: reducedness of a local ring is unchanged
  along an étale morphism.

## References

* [Stacks Project, Tag 0384](https://stacks.math.columbia.edu/tag/0384)
* [Stacks Project, Tag 035Y](https://stacks.math.columbia.edu/tag/035Y)
* [Stacks Project, Tag 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks Project, Tag 05FE](https://stacks.math.columbia.edu/tag/05FE)
* [Stacks Project, Tag 0C0D](https://stacks.math.columbia.edu/tag/0C0D)
* [EGA IV₃, 12.1.1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Étale invariance -/

/-- Reducedness of the local ring is unchanged along an étale morphism of schemes. -/
theorem isReduced_stalk_iff_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    _root_.IsReduced (Y.presheaf.stalk (f x)) ↔ _root_.IsReduced (X.presheaf.stalk x) :=
  GermOfScheme.isEtaleLocal_isReduced_stalk (MorphismOfGerms.ofSchemeHomOfEq f x (f x) rfl)
    (MorphismOfGerms.isEtale_ofSchemeHomOfEq f x (f x) rfl inferInstance)

/-- The map of pullbacks along `g` induced by `h : X ⟶ Y` is a pullback square over `h`. -/
private theorem isPullback_pullback_map_comp {X Y B T : Scheme.{u}} (h : X ⟶ Y) (fY : Y ⟶ B)
    (g : T ⟶ B) :
    IsPullback (pullback.map (h ≫ fY) g fY g h (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.fst (h ≫ fY) g) (pullback.fst fY g) h := by
  refine IsPullback.of_right (h₁₂ := pullback.snd fY g) (h₂₂ := fY) ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback fY g).flip
  convert (IsPullback.of_hasPullback (h ≫ fY) g).flip using 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **Geometric reducedness at a point is étale local.** Let `h : X ⟶ Y` be an étale morphism of
schemes over a field `k`. Then `Y` is geometrically reduced at `h x` exactly when `X` is
geometrically reduced at `x`.

After a field extension `k'/k` the base change of `h` is étale, every point of `Y_{k'}` above
`h x` lifts to a point of `X_{k'}` above `x`, and reducedness of local rings is unchanged along
an étale morphism. -/
theorem isGeometricallyReducedAt_iff_of_etale {k : Type u} [Field k] {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} (h : X ⟶ Y) [Etale h]
    (hw : h ≫ fY = fX) (x : X) :
    IsGeometricallyReducedAt fY (h x) ↔ IsGeometricallyReducedAt fX x := by
  subst hw
  have key : ∀ (k' : Type u) [Field k'] [Algebra k k'],
      let g : Spec (.of k') ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
      ∃ m : pullback (h ≫ fY) g ⟶ pullback fY g, Etale m ∧
        IsPullback m (pullback.fst (h ≫ fY) g) (pullback.fst fY g) h := by
    intro k' _ _ g
    exact ⟨_, MorphismProperty.of_isPullback (isPullback_pullback_map_comp h fY g).flip
      ‹Etale h›, isPullback_pullback_map_comp h fY g⟩
  constructor
  · intro hY k' _ _ g x' hx'
    obtain ⟨m, hm, hsq⟩ := key k'
    have hmx : pullback.fst fY _ (m x') = h x := by
      rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply, hx']
    exact (isReduced_stalk_iff_of_etale m x').mp (hY k' (m x') hmx)
  · intro hX k' _ _ g y' hy'
    obtain ⟨m, hm, hsq⟩ := key k'
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback y' x hy'
    set x' := hsq.isoPullback.inv z with hx'
    have hmx : m x' = y' := by
      rw [hx', ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
    have hfx : pullback.fst (h ≫ fY) _ x' = x := by
      rw [hx', ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
    rw [← hmx]
    exact (isReduced_stalk_iff_of_etale m x').mpr (hX k' x' hfx)

/-! ### Base change of the fibres -/

/-- Geometric reducedness at a point is unchanged by the base change along a field extension,
Stacks 0384. -/
private theorem isGeometricallyReducedAt_iff_of_isPullback_spec {k k' : Type u} [Field k]
    [Field k'] [Algebra k k'] {Z Z' : Scheme.{u}} {F : Z ⟶ Spec (.of k)}
    {F' : Z' ⟶ Spec (.of k')} {T : Z' ⟶ Z}
    (hp : IsPullback T F' F (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (z' : Z') :
    IsGeometricallyReducedAt F' z' ↔ IsGeometricallyReducedAt F (T z') :=
  ((isGeometricallyReducedAt_iff_of_etale hp.isoPullback.hom hp.isoPullback_hom_snd z').symm.trans
    (isGeometricallyReducedAt_iff_baseChange_fieldExtension k k' F (T z')
      (hp.isoPullback.hom z') (by
        rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst])).symm)

/-- **Pointwise geometric reducedness of fibres under base change.** In a cartesian square
exhibiting `f' : X' ⟶ Y'` as the base change of `f : X ⟶ Y` along `g : Y' ⟶ Y`, the fibre of
`f'` over `y'` is geometrically reduced at a point `z'` exactly when the fibre of `f` over
`g y'` is geometrically reduced at the point `z` under it: the first fibre is the base change
of the second along the extension of residue fields, and pointwise geometric reducedness is
insensitive to a field extension, Stacks 0384. -/
@[ega "IV 4.6.10" "more general", ega "IV 6.7.8" "more general"]
theorem isGeometricallyReducedAt_fiber_iff_of_isPullback {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X} {g : Y' ⟶ Y} (h : IsPullback i f' f g)
    (y' : Y') (z' : f'.fiber y') (z : f.fiber (g y'))
    (hz : f.fiberι (g y') z = i (f'.fiberι y' z')) :
    IsGeometricallyReducedAt (f'.fiberToSpecResidueField y') z' ↔
      IsGeometricallyReducedAt (f.fiberToSpecResidueField (g y')) z := by
  let _ : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  have hp := isPullback_fiberToSpecResidueField_of_isPullback h y'
  have hc : pullback.map _ _ _ _ i (Spec.map (g.residueFieldMap y')) g h.w.symm (by simp) ≫
      f.fiberι (g y') = f'.fiberι y' ≫ i := pullback.lift_fst _ _ _
  have hTz : pullback.map _ _ _ _ i (Spec.map (g.residueFieldMap y')) g h.w.symm (by simp) z' =
      z :=
    (f.fiberι (g y')).isEmbedding.injective ((congrArg (fun t => t z') hc).trans hz.symm)
  rw [← hTz]
  exact isGeometricallyReducedAt_iff_of_isPullback_spec (k := Y.residueField (g y'))
    (k' := Y'.residueField y') hp z'

/-- **Geometric reducedness of the fibres at a point is étale local on the source.** For an
étale morphism `e : U ⟶ X` over `Y`, the fibre of `U ⟶ Y` over `y` is geometrically reduced at
a point exactly when the fibre of `X ⟶ Y` over `y` is geometrically reduced at its image. -/
theorem isGeometricallyReducedAt_fiber_iff_of_etale {U X Y : Scheme.{u}}
    {f : X ⟶ Y} {fU : U ⟶ Y} (e : U ⟶ X) [Etale e] (he : e ≫ f = fU) (y : Y)
    (z : fU.fiber y) (z₀ : f.fiber y) (hz : f.fiberι y z₀ = e (fU.fiberι y z)) :
    IsGeometricallyReducedAt (fU.fiberToSpecResidueField y) z ↔
      IsGeometricallyReducedAt (f.fiberToSpecResidueField y) z₀ := by
  subst he
  let m : (e ≫ f).fiber y ⟶ f.fiber y :=
    pullback.map _ (Y.fromSpecResidueField y) f (Y.fromSpecResidueField y) e (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hsq : IsPullback m ((e ≫ f).fiberι y) (f.fiberι y) e :=
    isPullback_pullback_map_comp e f (Y.fromSpecResidueField y)
  have hm₂ : m ≫ f.fiberToSpecResidueField y = (e ≫ f).fiberToSpecResidueField y :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have : Etale m := MorphismProperty.of_isPullback (P := @Etale) hsq.flip inferInstance
  have hmz : m z = z₀ := by
    apply (f.fiberι y).isEmbedding.injective
    rw [hz, ← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
  rw [← hmz]
  exact (isGeometricallyReducedAt_iff_of_etale m hm₂ z).symm

/-! ### The Noetherian case -/

/-- A flat morphism reflects reducedness of local rings. -/
private theorem isReduced_stalk_of_flat {X Y : Scheme.{u}} (p : X ⟶ Y) [Flat p] (x : X)
    (hx : _root_.IsReduced (X.presheaf.stalk x)) :
    _root_.IsReduced (Y.presheaf.stalk (p x)) := by
  algebraize [(p.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap p x) (p.toLRSHom.prop x)
  exact isReduced_of_injective (p.stalkMap x).hom
    ‹RingHom.FaithfullyFlat (p.stalkMap x).hom›.injective

/-- **The discrete valuation ring argument.** Let `f : X ⟶ Y` be flat and locally of finite
type with `Y` locally Noetherian, let `x' ⤳ x` be a strict specialization in `X` and suppose
the fibre of `f` through `x` is geometrically reduced. For a finitely generated extension `L`
of `κ(x')`, the `L`-point of `X ×_Y Spec L` induced by `x'` has a reduced local ring.

By Stacks 054F there is a discrete valuation ring `R` and a morphism `Spec R ⟶ X` sending the
generic point to `x'` and the closed point to `x`, with fraction field `L`. The base change
`Z = X ×_Y Spec R` is flat over `R`, its special fibre is a base change of the fibre through
`x` and so reduced, hence its local rings along the special fibre are reduced, and so are
those at their generalizations. The section of `Z` induced by `Spec R ⟶ X` meets the generic
fibre, which is open in `Z`, at the point in question. -/
private theorem isReduced_stalk_pullback_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {x x' : X} (hxx' : x' ⤳ x)
    (hne : x ≠ x') (hx : GeometricallyReduced (f.fiberToSpecResidueField (f x)))
    (L : Type u) [Field L] [Algebra (X.residueField x') L]
    [Algebra.EssFiniteType (X.residueField x') L] :
    let a : Spec (.of L) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') L)) ≫
        X.fromSpecResidueField x'
    ∀ p : Spec (.of L), _root_.IsReduced ((pullback f (a ≫ f)).presheaf.stalk
      (pullback.lift a (𝟙 _) (by simp) p)) := by
  intro a p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨R, _, _, _, r, hη, hs, e, he⟩ :=
    exists_dvr_morphism_of_specializes_with_residueField_equiv X hxx' hne L
  -- the generic point of `Spec R`, as an open immersion from `Spec L`
  have hj₀ : IsOpenImmersion
      ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))) := by
    rw [genericPoint_eq_bot_of_affine (CommRingCat.of R)]
    exact isOpenImmersion_fromSpecResidueField_genericPoint R
  let j : Spec (.of L) ⟶ Spec (.of R) :=
    Spec.map e.toCommRingCatIso.hom ≫
      (Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))
  have : IsOpenImmersion j := inferInstance
  have hring : (X.residueFieldCongr hη.symm).hom ≫ r.residueFieldMap (genericPoint _) ≫
      e.toCommRingCatIso.hom = CommRingCat.ofHom (algebraMap (X.residueField x') L) := by
    ext t
    exact he t
  have hja : j ≫ r = a := by
    have h₁ : (Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))) ≫ r =
        Spec.map (r.residueFieldMap (genericPoint _)) ≫
          Spec.map (X.residueFieldCongr hη.symm).hom ≫ X.fromSpecResidueField x' := by
      rw [Scheme.residueFieldCongr_fromSpecResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [j, a, Category.assoc, h₁]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← hring]
  -- the base change to `Spec R` and its section
  let ρ := r ≫ f
  let hZ := pullback.snd f ρ
  have : Flat hZ := inferInstance
  have : LocallyOfFiniteType hZ := inferInstance
  have : IsLocallyNoetherian (pullback f ρ) := LocallyOfFiniteType.isLocallyNoetherian hZ
  let σ : Spec (.of R) ⟶ pullback f ρ := pullback.lift r (𝟙 _) (by simp [ρ])
  have hσ : σ ≫ hZ = 𝟙 _ := pullback.lift_snd _ _ _
  -- the special fibre is reduced
  have hspecial : GeometricallyReduced
      (hZ.fiberToSpecResidueField (IsLocalRing.closedPoint (CommRingCat.of R))) := by
    have hset := geometricallyReduced_fiber_set_eq_preimage_of_isPullback f hZ
      (pullback.fst f ρ) ρ (IsPullback.of_hasPullback f ρ)
    have hmem : IsLocalRing.closedPoint (CommRingCat.of R) ∈ ρ ⁻¹'
        {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
      change GeometricallyReduced (f.fiberToSpecResidueField ((r ≫ f) _))
      rw [show (r ≫ f) (IsLocalRing.closedPoint (CommRingCat.of R)) = f x from congrArg f hs]
      exact hx
    rwa [← hset] at hmem
  have : IsReduced (hZ.fiber (IsLocalRing.closedPoint (CommRingCat.of R))) :=
    isReduced_fiber_of_geometricallyReduced_fiberToSpecResidueField hZ _ hspecial
  have hσs : hZ (σ (IsLocalRing.closedPoint (CommRingCat.of R))) =
      IsLocalRing.closedPoint (CommRingCat.of R) := by
    change (σ ≫ hZ) (IsLocalRing.closedPoint (CommRingCat.of R)) = _
    rw [hσ]
    rfl
  have hredS := isReduced_stalk_of_flat_of_isReduced_closedFiber hZ _ hσs
  have hgen : σ (genericPoint (Spec (.of R))) ⤳ σ (IsLocalRing.closedPoint (CommRingCat.of R)) :=
    (genericPoint_specializes _).map σ.continuous
  have hredη := isReduced_stalk_of_specializes_of_isReduced hgen hredS
  -- the generic fibre is an open subscheme of `Z`
  have hcongr : a ≫ f = j ≫ ρ := by rw [← hja]; rfl
  let ψ : pullback f (a ≫ f) ⟶ pullback f ρ :=
    (pullback.congrHom rfl hcongr).hom ≫ (pullbackLeftPullbackSndIso f ρ j).inv ≫
      pullback.fst (pullback.snd f ρ) j
  have : IsOpenImmersion ψ := inferInstance
  have hψ₁ : ψ ≫ pullback.fst f ρ = pullback.fst f (a ≫ f) := by
    simp only [ψ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
    exact pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
  have hψ₂ : ψ ≫ pullback.snd f ρ = pullback.snd f (a ≫ f) ≫ j := by
    simp only [ψ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]
    rw [← Category.assoc]
    congr 1
    exact pullback.lift_snd _ _ _ |>.trans (Category.comp_id _)
  have hψ : pullback.lift a (𝟙 _) (by simp) ≫ ψ = j ≫ σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψ₁, pullback.lift_fst, Category.assoc,
        show σ ≫ pullback.fst f ρ = r from pullback.lift_fst _ _ _, hja]
    · rw [Category.assoc, hψ₂, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        Category.assoc, show σ ≫ pullback.snd f ρ = 𝟙 _ from pullback.lift_snd _ _ _,
        Category.comp_id]
  have hpt : ψ (pullback.lift a (𝟙 _) (by simp) p) = σ (genericPoint (Spec (.of R))) := by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
    congr 1
    simp only [j, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  rw [← hpt] at hredη
  exact (isReduced_stalk_iff_of_etale ψ _).mp hredη

/-- **Reading the discrete valuation ring argument on the fibre.** For an extension `L` of
`κ(x')`, the scheme `X ×_Y Spec L` is a flat base change of the fibre of `f` through `x'`, and
its `L`-point induced by `x'` maps to that point of the fibre. -/
private theorem exists_flat_to_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x' : X)
    (L : Type u) [Field L] [Algebra (X.residueField x') L] :
    let a : Spec (.of L) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') L)) ≫
        X.fromSpecResidueField x'
    let b : Spec (.of L) ⟶ Spec (Y.residueField (f x')) :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') L)) ≫
        Spec.map (f.residueFieldMap x')
    ∃ Φ : pullback f (a ≫ f) ⟶ f.fiber (f x'),
      IsPullback Φ (pullback.snd f (a ≫ f)) (f.fiberToSpecResidueField (f x')) b ∧
        ∀ p : Spec (.of L), Φ (pullback.lift a (𝟙 _) (by simp) p) = f.asFiber x' := by
  intro a b
  have hb : b ≫ Y.fromSpecResidueField (f x') = a ≫ f := by
    simp only [b, a, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let Φ : pullback f (a ≫ f) ⟶ f.fiber (f x') :=
    pullback.lift (pullback.fst f (a ≫ f)) (pullback.snd f (a ≫ f) ≫ b)
      (by rw [Category.assoc (pullback.snd _ _) b, hb]; exact pullback.condition)
  have hΦ₁ : Φ ≫ f.fiberι (f x') = pullback.fst f (a ≫ f) := pullback.lift_fst _ _ _
  have hΦ₂ : Φ ≫ f.fiberToSpecResidueField (f x') = pullback.snd f (a ≫ f) ≫ b :=
    pullback.lift_snd _ _ _
  refine ⟨Φ, ?_, fun p => ?_⟩
  · refine IsPullback.of_right (h₁₂ := f.fiberι (f x')) (h₂₂ := Y.fromSpecResidueField (f x'))
      ?_ hΦ₂ (IsPullback.of_hasPullback f (Y.fromSpecResidueField (f x')))
    rw [hΦ₁, hb]
    exact IsPullback.of_hasPullback f (a ≫ f)
  · apply (f.fiberι (f x')).isEmbedding.injective
    rw [f.fiberι_asFiber, ← Scheme.Hom.comp_apply, hΦ₁, ← Scheme.Hom.comp_apply,
      pullback.lift_fst]
    simp only [a, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

/-- **The Noetherian case.** Let `f : X ⟶ Y` be flat and locally of finite type over a locally
Noetherian base, and let `x' ⤳ x` be a specialization in `X` such that the fibre through `x`
is geometrically reduced. Then the fibre through `x'` is geometrically reduced at `x'`.

If both points lie in one fibre there is nothing to do. Otherwise, by Stacks 035Y, or by
Stacks 020I over a perfect field, it suffices that the local rings of the fibre through `x'`
above `x'` are reduced after every finite purely inseparable extension; each of them receives
a faithfully flat local homomorphism from a local ring to which the discrete valuation ring
argument applies. -/
private theorem isGeometricallyReducedAt_asFiber_of_specializes_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    {x x' : X} (hxx' : x' ⤳ x) (hx : GeometricallyReduced (f.fiberToSpecResidueField (f x))) :
    IsGeometricallyReducedAt (f.fiberToSpecResidueField (f x')) (f.asFiber x') := by
  by_cases hfx : f x' = f x
  · rw [← hfx] at hx
    exact (geometricallyReduced_iff_forall_isGeometricallyReducedAt _).mp hx _
  have hne : x ≠ x' := fun h => hfx (by rw [h])
  -- the local rings above `x'` after an extension `L` of `κ(x')` are reduced
  have key : ∀ (L : Type u) [Field L] [Algebra (X.residueField x') L]
      [Algebra.EssFiniteType (X.residueField x') L],
      let a : Spec (.of L) ⟶ X :=
        Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') L)) ≫
          X.fromSpecResidueField x'
      ∃ Φ : pullback f (a ≫ f) ⟶ f.fiber (f x'),
        IsPullback Φ (pullback.snd f (a ≫ f)) (f.fiberToSpecResidueField (f x'))
          (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') L)) ≫
            Spec.map (f.residueFieldMap x')) ∧
        ∃ q, Φ q = f.asFiber x' ∧ _root_.IsReduced ((pullback f (a ≫ f)).presheaf.stalk q) := by
    intro L _ _ _ a
    obtain ⟨Φ, hΦ, hΦp⟩ := exists_flat_to_fiber f x' L
    exact ⟨Φ, hΦ, _, hΦp (IsLocalRing.closedPoint L),
      isReduced_stalk_pullback_of_specializes f hxx' hne hx L (IsLocalRing.closedPoint L)⟩
  let _ : Algebra (Y.residueField (f x')) (X.residueField x') :=
    (f.residueFieldMap x').hom.toAlgebra
  by_cases hp : ringChar (Y.residueField (f x')) = 0
  · -- characteristic zero: the residue field is perfect
    have : CharZero (Y.residueField (f x')) := (CharP.ringChar_zero_iff_CharZero _).mp hp
    obtain ⟨Φ, hΦ, q, hΦq, hred⟩ := key (X.residueField x')
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x')
        (X.residueField x'))) ≫ Spec.map (f.residueFieldMap x')) := by
      have := flat_specMap_algebraMap (X.residueField x') (X.residueField x')
      have : Flat (Spec.map (f.residueFieldMap x')) :=
        flat_specMap_algebraMap (Y.residueField (f x')) (X.residueField x')
      infer_instance
    have : Flat Φ := MorphismProperty.of_isPullback hΦ.flip inferInstance
    have := isReduced_stalk_of_flat Φ q hred
    rw [hΦq] at this
    exact isGeometricallyReducedAt_of_isReduced (k := Y.residueField (f x')) _ _
  · -- positive characteristic: finite purely inseparable extensions suffice
    have : CharP (Y.residueField (f x')) (ringChar (Y.residueField (f x'))) := ringChar.charP _
    refine ((isGeometricallyReducedAt_tfae (k := Y.residueField (f x')) _ hp
      (f.fiberToSpecResidueField (f x')) (f.asFiber x')).out 1 2).mpr ?_
    intro k' _ _ _ _ g w hw
    -- a field containing both `κ(x')` and `k'`
    let C := X.residueField x' ⊗[Y.residueField (f x')] k'
    obtain ⟨m, hm⟩ := Ideal.exists_maximal C
    let L := C ⧸ m
    let : Field L := Ideal.Quotient.field m
    have : Module.Finite (X.residueField x') C := inferInstance
    have : Module.Finite (X.residueField x') L :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ (X.residueField x') m).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.EssFiniteType (X.residueField x') L := inferInstance
    let φ' : k' →+* L := (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom
    have hcompat : f.residueFieldMap x' ≫ CommRingCat.ofHom (algebraMap (X.residueField x') L) =
        CommRingCat.ofHom (algebraMap (Y.residueField (f x')) k') ≫ CommRingCat.ofHom φ' := by
      ext c
      change Ideal.Quotient.mk m ((algebraMap (Y.residueField (f x')) (X.residueField x') c) ⊗ₜ
          (1 : k')) =
        Ideal.Quotient.mk m ((1 : X.residueField x') ⊗ₜ (algebraMap (Y.residueField (f x')) k' c))
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    obtain ⟨Φ, hΦ, q, hΦq, hred⟩ := key L
    have hb : Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x') L)) ≫
        Spec.map (f.residueFieldMap x') = Spec.map (CommRingCat.ofHom φ') ≫ g := by
      simp only [g, ← Spec.map_comp]
      exact congrArg Spec.map hcompat
    let Ψ : pullback f _ ⟶ pullback (f.fiberToSpecResidueField (f x')) g :=
      pullback.lift Φ (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ'))
        (by rw [hΦ.w, hb]; simp only [Category.assoc])
    have hΨ : IsPullback Ψ (pullback.snd _ _) (pullback.snd _ g)
        (Spec.map (CommRingCat.ofHom φ')) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst _ g)
        (h₂₂ := g) ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback (f.fiberToSpecResidueField (f x')) g)
      rw [show Ψ ≫ pullback.fst _ g = Φ from pullback.lift_fst _ _ _, ← hb]
      exact hΦ
    have : Flat (Spec.map (CommRingCat.ofHom φ')) := by
      let : Algebra k' L := φ'.toAlgebra
      exact flat_specMap_algebraMap k' L
    have : Flat Ψ := MorphismProperty.of_isPullback hΨ.flip inferInstance
    have hredw := isReduced_stalk_of_flat Ψ q hred
    have : UniversallyInjective g :=
      universallyInjective_specMap_of_isPurelyInseparable (Y.residueField (f x')) k'
    have : UniversallyInjective (pullback.fst (f.fiberToSpecResidueField (f x')) g) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ g).flip ‹UniversallyInjective g›
    have hΨq : Ψ q = w := by
      apply (pullback.fst (f.fiberToSpecResidueField (f x')) g).injective
      rw [hw, ← Scheme.Hom.comp_apply, show Ψ ≫ pullback.fst _ g = Φ from
        pullback.lift_fst _ _ _, hΦq]
    rwa [hΨq] at hredw

/-- The Noetherian case, for an arbitrary point of the fibre. -/
private theorem isGeometricallyReducedAt_fiber_of_specializes_of_isLocallyNoetherian
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    {y : Y} (z : f.fiber y) {x : X} (hzx : f.fiberι y z ⤳ x)
    (hx : GeometricallyReduced (f.fiberToSpecResidueField (f x))) :
    IsGeometricallyReducedAt (f.fiberToSpecResidueField y) z := by
  obtain ⟨⟨x', hx'⟩, rfl⟩ := (f.fiberHomeo y).symm.surjective z
  obtain rfl : f x' = y := hx'
  rw [Scheme.Hom.fiberι_fiberHomeo_symm] at hzx
  exact isGeometricallyReducedAt_asFiber_of_specializes_of_isLocallyNoetherian f hzx hx

/-- The affine case of `AlgebraicGeometry.isGeometricallyReducedAt_fiber_of_specializes`.

By Stacks 05FE `f` is the base change of a flat morphism of finite type over a base of finite
type over `ℤ`, and both the hypothesis, by Stacks 0576, and the conclusion, by Stacks 0384,
can be read on that model. There the specialization is realized by a discrete valuation ring,
Stacks 054F: over it the local rings along the special fibre are reduced, by flatness and
Krull's intersection theorem, hence so are those at their generalizations, which include the
point in question after any finite extension of the residue field. -/
private theorem isGeometricallyReducedAt_fiber_of_specializes_of_isAffine {X Y : Scheme.{u}}
    [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] {y : Y} (z : f.fiber y)
    {x : X} (hzx : f.fiberι y z ⤳ x)
    (hx : GeometricallyReduced (f.fiberToSpecResidueField (f x))) :
    IsGeometricallyReducedAt (f.fiberToSpecResidueField y) z := by
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨m⟩ := exists_flat_finiteTypeAffineModel f hfp
  have : Flat m.f₀ := m.property
  have : LocallyOfFiniteType m.f₀ := m.locallyOfFiniteType
  have : IsLocallyNoetherian m.S₀ := by
    -- the base of the model is of finite type over `ℤ`
    let _ : IsAffine m.S₀ := m.base_affine
    let _ : LocallyOfFiniteType (terminal.from m.S₀) := m.base_locallyOfFiniteType
    let e : Spec (.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
      specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
    let g : m.S₀ ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from m.S₀ ≫ e.inv
    let _ : LocallyOfFiniteType g := by dsimp [g]; infer_instance
    let _ : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm
    exact LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : m.f₀.fiber (m.toBase y),
      m.f₀.fiberι _ z₀ = m.toSource (f.fiberι y z) := by
    refine ⟨(m.f₀.fiberHomeo _).symm ⟨m.toSource (f.fiberι y z), ?_⟩, by simp⟩
    have hfz : f (f.fiberι y z) = y := (f.range_fiberι y).le ⟨z, rfl⟩
    change m.f₀ (m.toSource _) = m.toBase y
    rw [← Scheme.Hom.comp_apply, m.isPullback.w, Scheme.Hom.comp_apply, hfz]
  refine (isGeometricallyReducedAt_fiber_iff_of_isPullback m.isPullback y z z₀ hz₀).mpr ?_
  have hx₀ : GeometricallyReduced (m.f₀.fiberToSpecResidueField (m.f₀ (m.toSource x))) := by
    have hset := geometricallyReduced_fiber_set_eq_preimage_of_isPullback m.f₀ f m.toSource
      m.toBase m.isPullback
    have hmem : f x ∈ {y' : Y | GeometricallyReduced (f.fiberToSpecResidueField y')} := hx
    rw [hset] at hmem
    have he : m.f₀ (m.toSource x) = m.toBase (f x) := by
      rw [← Scheme.Hom.comp_apply, m.isPullback.w, Scheme.Hom.comp_apply]
    rw [he]
    exact hmem
  refine isGeometricallyReducedAt_fiber_of_specializes_of_isLocallyNoetherian m.f₀ z₀ ?_ hx₀
  rw [hz₀]
  exact hzx.map m.toSource.continuous

/-- Geometric reducedness of a fibre passes to an open subscheme of the source. -/
private theorem geometricallyReduced_fiber_of_isOpenImmersion {U X Y : Scheme.{u}}
    {f : X ⟶ Y} {fU : U ⟶ Y} (e : U ⟶ X) [IsOpenImmersion e] (he : e ≫ f = fU) (y : Y)
    (h : GeometricallyReduced (f.fiberToSpecResidueField y)) :
    GeometricallyReduced (fU.fiberToSpecResidueField y) := by
  rw [geometricallyReduced_iff_forall_isGeometricallyReducedAt] at h ⊢
  intro z
  have hfz : f (e (fU.fiberι y z)) = y := by
    rw [← Scheme.Hom.comp_apply, he]
    exact (fU.range_fiberι y).le ⟨z, rfl⟩
  exact (isGeometricallyReducedAt_fiber_iff_of_etale e he y z
    ((f.fiberHomeo y).symm ⟨e (fU.fiberι y z), hfz⟩) (by simp)).mpr (h _)

/-- **Geometric reducedness of the fibres propagates to generalizations.** Let `f : X ⟶ Y` be
flat and locally of finite presentation, let `z` be a point of the fibre of `f` over `y`, and
suppose its image in `X` specializes to a point `x` such that the fibre of `f` through `x` is
geometrically reduced. Then the fibre over `y` is geometrically reduced at `z`.

This is the generalization half of [EGA IV₃, 12.1.1 (vi)]: the set of points of `X` at which
the fibre of a flat morphism locally of finite presentation is geometrically reduced is stable
under generalization, given geometric reducedness along the whole fibre through `x`. The
statement is local around `x` on both `X` and `Y`, which reduces it to the case of an affine
open neighbourhood of `x` mapping to an affine open neighbourhood of its image: the fibres of the
restriction over that open of `Y` are the base changes of those of `f` along an isomorphism of
residue fields, and the fibres of the further restriction to the open of `X` are open in them. -/
@[ega "IV 12.1.1.3" "(vii), special case"]
theorem isGeometricallyReducedAt_fiber_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] {y : Y}
    (z : f.fiber y) {x : X} (hzx : f.fiberι y z ⤳ x)
    (hx : GeometricallyReduced (f.fiberToSpecResidueField (f x))) :
    IsGeometricallyReducedAt (f.fiberToSpecResidueField y) z := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) trivial
  obtain ⟨U, hU, hxU, hUV'⟩ := exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := x) hxV
  have hUV : U ≤ f ⁻¹ᵁ V := hUV'
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  set w := f.fiberι y z with hw
  have hwy : f w = y := (f.range_fiberι y).le ⟨z, rfl⟩
  have hwU : w ∈ U := hzx.mem_open U.2 hxU
  have hyV : y ∈ V := hwy ▸ hUV hwU
  let g := f.resLE V U hUV
  let e : U.toScheme ⟶ (f ⁻¹ᵁ V).toScheme := X.homOfLE hUV
  have he : e ≫ f ∣_ V = g := rfl
  let yV : V.toScheme := ⟨y, hyV⟩
  -- the three points of the fibres lying under `z`
  let z₁ : (f ∣_ V).fiber yV := ((f ∣_ V).fiberHomeo yV).symm
    ⟨⟨w, hUV hwU⟩, Subtype.ext ((morphismRestrict_base_coe f V _).trans hwy)⟩
  let zU : g.fiber yV := (g.fiberHomeo yV).symm ⟨⟨w, hwU⟩, Subtype.ext <| by
    change ((f ∣_ V) (X.homOfLE hUV ⟨w, hwU⟩)).1 = y
    rw [morphismRestrict_base_coe]
    exact (congrArg f (Scheme.homOfLE_apply hUV ⟨w, hwU⟩)).trans hwy⟩
  have hz₁ : f.fiberι (V.ι yV) z = (f ⁻¹ᵁ V).ι ((f ∣_ V).fiberι yV z₁) := by
    change f.fiberι y z = _
    simp [z₁, hw]
  have hzU : (f ∣_ V).fiberι yV z₁ = e (g.fiberι yV zU) := by
    apply Subtype.ext
    simp only [z₁, zU, e, Scheme.Hom.fiberι_fiberHomeo_symm]
    exact (Scheme.homOfLE_apply hUV ⟨w, hwU⟩).symm
  refine ((isGeometricallyReducedAt_fiber_iff_of_isPullback
    (isPullback_morphismRestrict f V).flip yV z₁ z hz₁).mp ?_)
  refine (isGeometricallyReducedAt_fiber_iff_of_etale (f := f ∣_ V) (fU := g) e he
    yV zU z₁ hzU).mp ?_
  -- the affine case
  let u : U.toScheme := ⟨x, hxU⟩
  have hu : g.fiberι yV zU ⤳ u := by
    have h₁ : g.fiberι yV zU = ⟨w, hwU⟩ := Scheme.Hom.fiberι_fiberHomeo_symm _ _ _
    rw [h₁]
    exact (subtype_specializes_iff _ _).mpr hzx
  refine isGeometricallyReducedAt_fiber_of_specializes_of_isAffine g zU hu ?_
  -- the hypothesis on the restriction
  let vV : V.toScheme := ⟨f x, hxV⟩
  have hgu : g u = vV := Subtype.ext <| by
    change ((f ∣_ V) (X.homOfLE hUV u)).1 = f x
    rw [morphismRestrict_base_coe]
    exact congrArg f (Scheme.homOfLE_apply hUV u)
  rw [hgu]
  refine geometricallyReduced_fiber_of_isOpenImmersion (f := f ∣_ V) (fU := g) e he vV ?_
  have hset := geometricallyReduced_fiber_set_eq_preimage_of_isPullback f (f ∣_ V)
    (f ⁻¹ᵁ V).ι V.ι (isPullback_morphismRestrict f V).flip
  have hmem : vV ∈ V.ι ⁻¹' {y' : Y | GeometricallyReduced (f.fiberToSpecResidueField y')} := hx
  rwa [← hset] at hmem

end AlgebraicGeometry

end
