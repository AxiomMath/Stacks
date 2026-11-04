module

public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedPurelyInseparable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric reducedness after a field extension

Geometric reducedness at a point of a scheme over a field can be checked after extending the
base field and choosing a point above it. Consequently, geometric reducedness of the whole
scheme is preserved and reflected by every field extension.

## Main results

* `AlgebraicGeometry.isGeometricallyReducedAt_iff_baseChange_fieldExtension` gives the pointwise
  equivalence.
* `AlgebraicGeometry.geometricallyReduced_iff_baseChange_fieldExtension` gives the corresponding
  global equivalence.

## Implementation notes

A scheme over `k` is represented by a morphism `f : X ⟶ Spec k`. Its base change along
`k → k'` is the pullback of `f` along the induced morphism `Spec k' ⟶ Spec k`. A point of
the pullback lies over `x` when its image under the first pullback projection is `x`. The
comparison between base changing twice and base changing once along a composite is
`AlgebraicGeometry.iteratedBaseChangeIso`.

The three directions of the pointwise equivalence are carried by separate lemmas: descent of
geometric reducedness along the base change, and the two cases of the converse according as the
ground field has characteristic zero, where it is perfect, or positive characteristic, where the
criterion of Tag 035Y applies.

## References

* [Stacks Project, Tag 0384](https://stacks.math.columbia.edu/tag/0384)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The morphism of spectra induced by a field extension is flat. -/
private lemma flat_specMap_algebraMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
  infer_instance

/-- A flat morphism reflects reducedness of local rings, at any point over a given point. -/
private lemma isReduced_stalk_of_flat {X Y : Scheme.{u}} (p : X ⟶ Y)
    [Flat p] (x : X) (y : Y) (hxy : p x = y) [_root_.IsReduced (X.presheaf.stalk x)] :
    _root_.IsReduced (Y.presheaf.stalk y) := by
  subst hxy
  algebraize [(p.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap p x) (p.toLRSHom.prop x)
  exact isReduced_of_injective (p.stalkMap x).hom
    ‹RingHom.FaithfullyFlat (p.stalkMap x).hom›.injective

/-- Geometric reducedness at a point implies reducedness of the local ring there. -/
private lemma isReduced_stalk_of_isGeometricallyReducedAt
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (h : IsGeometricallyReducedAt f x) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  let g : Spec (.of k) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k))
  obtain ⟨z, rfl⟩ := (pullback.fst f g).surjective x
  have := flat_specMap_algebraMap k k
  have : _root_.IsReduced ((pullback f g).presheaf.stalk z) := h k z rfl
  exact isReduced_stalk_of_flat (pullback.fst f g) z _ rfl

/-- Geometric reducedness at a point descends to any point above it in a base change along a
field extension. -/
private lemma isGeometricallyReducedAt_baseChange_of_isGeometricallyReducedAt
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme))
    (hx' : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyReducedAt f x) :
    IsGeometricallyReducedAt
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) x' := by
  let φ : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  simp only [IsGeometricallyReducedAt]
  intro K _ _ z hz
  let : Algebra k K := RingHom.toAlgebra ((algebraMap k' K).comp (algebraMap k k'))
  let : IsScalarTower k k' K := .of_algebraMap_eq' rfl
  let χ : Spec (.of K) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' K))
  let μ : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hcomp : χ ≫ φ = μ := specMap_algebraMap_comp k k' K
  let e := iteratedBaseChangeIso f φ χ μ hcomp
  have : _root_.IsReduced ((pullback f μ).presheaf.stalk (e.hom z)) := by
    apply h K (e.hom z)
    rw [← hx', ← hz]
    exact congrArg (fun g ↦ g.base.hom z) (iteratedBaseChangeIso_fst f φ χ μ hcomp)
  have hzred' : _root_.IsReduced
      ((pullback (pullback.snd f φ) χ).presheaf.stalk (e.inv (e.hom z))) :=
    isReduced_of_injective (e.inv.stalkMap (e.hom z)).hom
      (asIso <| e.inv.stalkMap (e.hom z)).commRingCatIsoToRingEquiv.injective
  have hepoint : e.inv (e.hom z) = z := by
    show (e.hom ≫ e.inv) z = z
    rw [e.hom_inv_id]
    rfl
  rw [hepoint] at hzred'
  exact hzred'

/-- Over a perfect field, geometric reducedness at a point of a base change descends to the
point below it. -/
private lemma isGeometricallyReducedAt_of_baseChange_of_perfectField
    (k k' : Type u) [Field k] [PerfectField k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme))
    (hx' : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyReducedAt
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) x') :
    IsGeometricallyReducedAt f x := by
  let φ : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have : _root_.IsReduced ((pullback f φ).presheaf.stalk x') :=
    isReduced_stalk_of_isGeometricallyReducedAt k' (pullback.snd f φ) x' h
  have := flat_specMap_algebraMap k k'
  have : _root_.IsReduced (X.presheaf.stalk x) :=
    isReduced_stalk_of_flat (pullback.fst f φ) x' x hx'
  exact isGeometricallyReducedAt_of_isReduced f x

/-- Given a common extension `M` of two extensions `k'` and `K` of `k`, the base change of `f`
along `k → k' → M` carries a flat morphism to the base change along `k → K`, compatible with
the projections down to the original scheme. -/
private lemma exists_flat_morphism_of_common_extension
    (k k' K M : Type u) [Field k] [Field k'] [Field K] [Field M]
    [Algebra k k'] [Algebra k K] [Algebra k M] [Algebra k' M] [Algebra K M]
    [IsScalarTower k k' M] [IsScalarTower k K M]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    ∃ r : (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
            (Spec.map (CommRingCat.ofHom (algebraMap k' M))) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      Flat r ∧
        r ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
              (Spec.map (CommRingCat.ofHom (algebraMap k' M))) ≫
            pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
  let φ : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let ψ : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let χ' : Spec (.of M) ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' M))
  let χK : Spec (.of M) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K M))
  let μ : Spec (.of M) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k M))
  have hcomp' : χ' ≫ φ = μ := specMap_algebraMap_comp k k' M
  have hcompK : χK ≫ ψ = μ := specMap_algebraMap_comp k K M
  refine ⟨iteratedBaseChangeComparison f φ ψ χ' χK μ hcomp' hcompK, ?_,
    iteratedBaseChangeComparison_fst f φ ψ χ' χK μ hcomp' hcompK⟩
  dsimp [iteratedBaseChangeComparison]
  infer_instance

/-- In positive characteristic, geometric reducedness at a point of a base change descends to
the point below it, by the purely inseparable criterion of Tag 035Y. -/
private lemma isGeometricallyReducedAt_of_baseChange_of_charP
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (p : ℕ) [CharP k p] (hp : p ≠ 0)
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme))
    (hx' : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyReducedAt
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) x') :
    IsGeometricallyReducedAt f x := by
  let φ : Spec (.of k') ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k k'))
  apply ((isGeometricallyReducedAt_tfae p hp f x).out 2 1).mp
  intro K _ _ _ _ _ y hy
  let ψ : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : UniversallyInjective ψ :=
    universallyInjective_specMap_of_isPurelyInseparable k K
  have : UniversallyInjective (pullback.fst f ψ) :=
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f ψ).flip
      (show UniversallyInjective ψ from inferInstance)
  obtain ⟨M, _, _, _, _, hk'M, hKM⟩ := exists_common_extension k k' K
  let : IsScalarTower k k' M := hk'M
  let : IsScalarTower k K M := hKM
  obtain ⟨r, hrflat, hrdiag⟩ := exists_flat_morphism_of_common_extension k k' K M f
  obtain ⟨z, hz⟩ :=
    (pullback.fst (pullback.snd f φ)
      (Spec.map (CommRingCat.ofHom (algebraMap k' M)))).surjective x'
  have hrx : (pullback.fst f ψ) (r z) = x := by
    calc
      (pullback.fst f ψ) (r z) = (r ≫ pullback.fst f ψ) z := rfl
      _ = ((pullback.fst (pullback.snd f φ)
            (Spec.map (CommRingCat.ofHom (algebraMap k' M)))) ≫
          pullback.fst f φ) z :=
        congrArg (fun g ↦ g.base.hom z) hrdiag
      _ = x := by rw [Scheme.Hom.comp_apply, hz, hx']
  have hry : r z = y := (pullback.fst f ψ).injective (hrx.trans hy.symm)
  have : Flat r := hrflat
  have : _root_.IsReduced
      ((pullback (pullback.snd f φ)
        (Spec.map (CommRingCat.ofHom (algebraMap k' M)))).presheaf.stalk z) := h M z hz
  exact isReduced_stalk_of_flat r z y hry

/-- **Stacks Project, Tag 0384, pointwise statement.** Geometric reducedness at a point is
preserved and reflected after extending the base field and choosing a point above it. -/
@[stacks 0384 "pointwise equivalence", ega "IV 4.6.10"]
public theorem isGeometricallyReducedAt_iff_baseChange_fieldExtension
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme))
    (hx' : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) x' = x) :
    IsGeometricallyReducedAt f x ↔
      IsGeometricallyReducedAt
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) x' := by
  refine ⟨isGeometricallyReducedAt_baseChange_of_isGeometricallyReducedAt k k' f x x' hx',
    fun h ↦ ?_⟩
  by_cases hp : ringChar k = 0
  · have : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hp
    exact isGeometricallyReducedAt_of_baseChange_of_perfectField k k' f x x' hx' h
  · have : CharP k (ringChar k) := ringChar.charP k
    exact isGeometricallyReducedAt_of_baseChange_of_charP k k' (ringChar k) hp f x x' hx' h

/-- **Stacks Project, Tag 0384, global statement.** A scheme over a field is geometrically
reduced if and only if its base change along a field extension is geometrically reduced. -/
@[stacks 0384 "global equivalence"]
public theorem geometricallyReduced_iff_baseChange_fieldExtension
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    GeometricallyReduced f ↔
      GeometricallyReduced
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  rw [geometricallyReduced_iff_forall_isGeometricallyReducedAt,
    geometricallyReduced_iff_forall_isGeometricallyReducedAt]
  refine ⟨fun h x' ↦ (isGeometricallyReducedAt_iff_baseChange_fieldExtension k k' f _ x' rfl).mp
    (h _), fun h x ↦ ?_⟩
  obtain ⟨x', hx'⟩ :=
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).surjective x
  exact (isGeometricallyReducedAt_iff_baseChange_fieldExtension k k' f x x' hx').mpr (h x')

end AlgebraicGeometry
