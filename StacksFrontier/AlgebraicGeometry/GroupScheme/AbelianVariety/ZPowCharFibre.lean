module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LowerSemicontinuity
public import StacksFrontier.FieldTheory.KaehlerDifferential.CartierEquality
public import StacksFrontier.FieldTheory.PBasis
public import StacksFrontier.RingTheory.FormallySmooth.FieldCotangent
public import StacksFrontier.RingTheory.Kaehler.PerfectField
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Points in the fibre of multiplication by the characteristic on an abelian variety

For an abelian variety `A` of dimension `g` over a field `k` of characteristic `p > 0`, the fibre
of multiplication by `p` over the identity has at most `p ^ g` distinct points
([Stacks, Tag 0C0Y](https://stacks.math.columbia.edu/tag/0C0Y)). The argument is carried out
granted the theorem of the cube for `A`, `Stacks.Groupoids.HasTheoremOfTheCube A`, which is the
one input of Tag 0BFG (`isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube`) on which
it rests, and that input is then discharged by `Stacks.Groupoids.hasTheoremOfTheCube`.

## Main results

* `Stacks.Groupoids.cardinalMk_fiber_multiplication_by_char_le_of_hasTheoremOfTheCube`: the fibre
  of `[p]` over the identity has at most `p ^ dim A` points, granted the theorem of the cube.
* `Stacks.Groupoids.cardinalMk_fiber_multiplication_by_char_le`: the fibre of `[p]` over the
  identity has at most `p ^ dim A` points.

## The proof

* `[p]` is finite locally free of rank `p ^ (2g)` (Tag 0BFG), hence finite, flat and surjective.
* `[p]` kills derivations of the function field. A `k`-derivation `D` of `K = k(A)` is a
  `K[ε]`-point of `A` lifting the generic point. In the commutative group `A(K[ε])` the points
  with a given reduction form a torsor under a `K`-vector space, on which `p`-th powers act as
  multiplication by `p = 0`, so the `p`-th power of that point is the constant lift of its
  reduction. Read through the endomorphism `φ` of `K` induced by `[p]`, this says
  `D (φ y) = 0` for all `y`, i.e. `φ` kills `Ω_{K/k}`.
* `Ω_{K/k}` has dimension `g` over `K`, as `K` is formally smooth over `k`, so `K` has a `p`-basis
  of `g` elements; `φ(K)` lies in the compositum `k K^p`, and comparing `[K : φ(K)] = p ^ (2g)`
  with `[K : k K^p] = p ^ g` bounds the separable degree `[K : φ(K)]_s` by `p ^ g`.
* The number of points of a fibre of the finite flat morphism `[p]` is at most the number of
  geometric connected components of its fibres, which is lower semicontinuous (Tag 0BUI) and so
  maximal at the generic point, where it is that separable degree.

## Implementation notes

The multiplication map is the `p`-th power of the identity endomorphism of the group object.
The fibre is represented by the pullback along its identity section, and its distinct points
are counted by the cardinality of the underlying scheme.

## References

* [Stacks Project, Tag 0C0Y](https://stacks.math.columbia.edu/tag/0C0Y)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0BUI](https://stacks.math.columbia.edu/tag/0BUI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Stacks.Groupoids

universe u v w

private theorem dual_joint_ext {K : Type u} [Field K] {X : Scheme.{u}}
    (f g : Spec (.of (DoubleDualNumber K)) ⟶ X)
    (h₁ : firstDualNumberInclusion K ≫ f = firstDualNumberInclusion K ≫ g)
    (h₂ : secondDualNumberInclusion K ≫ f = secondDualNumberInclusion K ≫ g) : f = g := by
  let R := CommRingCat.of (DoubleDualNumber K)
  let S := CommRingCat.of (DualNumber K)
  let q₁ : R ⟶ S := CommRingCat.ofHom (firstDualNumberProjection K).toRingHom
  let q₂ : R ⟶ S := CommRingCat.ofHom (secondDualNumberProjection K).toRingHom
  let : IsLocalRing (DoubleDualNumber K) := {
    isUnit_or_isUnit_of_add_one := by
      intro a b h
      rw [add_comm, ← eq_sub_iff_add_eq] at h
      rcases eq_or_ne (TrivSqZeroExt.fst a) 0 with ha | ha <;>
        simp [TrivSqZeroExt.isUnit_iff_isUnit_fst, h, ha] }
  have : IsLocalHom q₁.hom := IsLocalHom.of_surjective _ (fun z => by
    refine ⟨(TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (z.snd, 0) : DoubleDualNumber K), ?_⟩
    change firstDualNumberProjection K _ = z
    ext <;> simp [firstDualNumberProjection])
  have hx : f (IsLocalRing.closedPoint R) = g (IsLocalRing.closedPoint R) := by
    have h := congrArg (fun a : Spec S ⟶ X => a (IsLocalRing.closedPoint S)) h₁
    change f (Spec.map q₁ _) = g (Spec.map q₁ _) at h
    simpa only [Spec_closedPoint] using h
  let a := Scheme.stalkClosedPointTo f
  let b := (X.presheaf.stalkCongr (Inseparable.of_eq hx)).hom ≫ Scheme.stalkClosedPointTo g
  have ha : Spec.map a ≫ X.fromSpecStalk (f (IsLocalRing.closedPoint R)) = f :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk f
  have hb : Spec.map b ≫ X.fromSpecStalk (f (IsLocalRing.closedPoint R)) = g := by
    dsimp [b]
    rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom]
    refine (congrArg (Spec.map (Scheme.stalkClosedPointTo g) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk _)).trans ?_
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  have he (q : R ⟶ S) (h : Spec.map q ≫ f = Spec.map q ≫ g) : a ≫ q = b ≫ q := by
    apply Spec.map_inj.mp
    apply (cancel_mono (X.fromSpecStalk (f (IsLocalRing.closedPoint R)))).mp
    simpa only [Spec.map_comp, Category.assoc, ha, hb] using h
  have hq₁ := he q₁ h₁
  have hq₂ := he q₂ h₂
  have hab : a = b := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    have hfirst : firstDualNumberProjection K (a t) = firstDualNumberProjection K (b t) :=
      congrArg (fun h => h.hom t) hq₁
    have hsecond : secondDualNumberProjection K (a t) = secondDualNumberProjection K (b t) :=
      congrArg (fun h => h.hom t) hq₂
    apply TrivSqZeroExt.ext
    · simpa [firstDualNumberProjection] using congrArg TrivSqZeroExt.fst hfirst
    · apply Prod.ext
      · simpa [firstDualNumberProjection] using congrArg TrivSqZeroExt.snd hfirst
      · simpa [secondDualNumberProjection] using congrArg TrivSqZeroExt.snd hsecond
  rw [← ha, ← hb, hab]

private noncomputable def specPoint {K : Type u} [CommRing K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) (R : Type u) [CommRing R] [Algebra K R] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)) ≫ s)

private noncomputable def specPointMap {K : Type u} [CommRing K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) {R T : Type u} [CommRing R] [CommRing T]
    [Algebra K R] [Algebra K T] (f : R →ₐ[K] T) :
    specPoint s T ⟶ specPoint s R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    dsimp [specPoint]
    rw [← Spec.map_comp_assoc]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext f.commutes))

private theorem specPointMap_comp {K : Type u} [CommRing K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) {R T U : Type u} [CommRing R] [CommRing T] [CommRing U]
    [Algebra K R] [Algebra K T] [Algebra K U] (f : R →ₐ[K] T) (g : T →ₐ[K] U) :
    specPointMap s g ≫ specPointMap s f = specPointMap s (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

private theorem specPointMap_id {K : Type u} [CommRing K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) (R : Type u) [CommRing R] [Algebra K R] :
    specPointMap s (AlgHom.id K R) = 𝟙 (specPoint s R) := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

private theorem scale_zero {K : Type u} [CommRing K] :
    scaleDualNumber K 0 = (TrivSqZeroExt.inlAlgHom K K K).comp
      (TrivSqZeroExt.fstHom K K K) := by
  ext <;> simp [scaleDualNumber, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]

private theorem scale_one {K : Type u} [CommRing K] :
    scaleDualNumber K 1 = AlgHom.id K (DualNumber K) := by
  simp [scaleDualNumber, TrivSqZeroExt.map_id]

private theorem dual_kernel_scale_add {K : Type u} [Field K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) (G : Over S) [GrpObj G]
    (a : specPoint s (DualNumber K) ⟶ G)
    (ha : specPointMap s (TrivSqZeroExt.fstHom K K K) ≫ a = 1) (r t : K) :
    specPointMap s (scaleDualNumber K (r + t)) ≫ a =
      (specPointMap s (scaleDualNumber K r) ≫ a) *
      (specPointMap s (scaleDualNumber K t) ≫ a) := by
  let i₁ := TrivSqZeroExt.map (LinearMap.inl K K K)
  let i₂ := TrivSqZeroExt.map (LinearMap.inr K K K)
  let d := TrivSqZeroExt.map ((LinearMap.inl K K K) + (LinearMap.inr K K K))
  have h₁₁ : (firstDualNumberProjection K).comp i₁ = AlgHom.id K _ := by
    ext <;> simp [i₁, firstDualNumberProjection, TrivSqZeroExt.fst_map,
        TrivSqZeroExt.snd_map]
  have h₁₂ : (firstDualNumberProjection K).comp i₂ = scaleDualNumber K 0 := by
    ext <;> simp [i₂, firstDualNumberProjection, scaleDualNumber, TrivSqZeroExt.fst_map,
        TrivSqZeroExt.snd_map]
  have h₂₁ : (secondDualNumberProjection K).comp i₁ = scaleDualNumber K 0 := by
    ext <;> simp [i₁, secondDualNumberProjection, scaleDualNumber, TrivSqZeroExt.fst_map,
        TrivSqZeroExt.snd_map]
  have h₂₂ : (secondDualNumberProjection K).comp i₂ = AlgHom.id K _ := by
    ext <;> simp [i₂, secondDualNumberProjection, TrivSqZeroExt.fst_map,
        TrivSqZeroExt.snd_map]
  have h₁d : (firstDualNumberProjection K).comp d = AlgHom.id K _ := by
    ext <;> simp [d, firstDualNumberProjection, TrivSqZeroExt.fst_map,
        TrivSqZeroExt.snd_map]
  have h₂d : (secondDualNumberProjection K).comp d = AlgHom.id K _ := by
    ext <;> simp [d, secondDualNumberProjection, TrivSqZeroExt.fst_map,
        TrivSqZeroExt.snd_map]
  have hz : specPointMap s (scaleDualNumber K 0) ≫ a = 1 := by
    rw [scale_zero, ← specPointMap_comp, Category.assoc, ha, MonObj.comp_one]
  have hd : specPointMap s d ≫ a =
      (specPointMap s i₁ ≫ a) * (specPointMap s i₂ ≫ a) := by
    apply Over.OverMorphism.ext
    apply dual_joint_ext
    · change (specPointMap s (firstDualNumberProjection K) ≫ _).left =
        (specPointMap s (firstDualNumberProjection K) ≫ _).left
      congr 1
      simp only [MonObj.comp_mul, ← Category.assoc, specPointMap_comp,
        h₁d, h₁₁, h₁₂, specPointMap_id, Category.id_comp, hz, mul_one]
    · change (specPointMap s (secondDualNumberProjection K) ≫ _).left =
        (specPointMap s (secondDualNumberProjection K) ≫ _).left
      congr 1
      simp only [MonObj.comp_mul, ← Category.assoc, specPointMap_comp,
        h₂d, h₂₁, h₂₂, specPointMap_id, Category.id_comp, hz, one_mul]
  let q := TrivSqZeroExt.map (r • LinearMap.fst K K K + t • LinearMap.snd K K K)
  have hqd : q.comp d = scaleDualNumber K (r + t) := by
    ext <;> simp [q, d, scaleDualNumber, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]
  have hq₁ : q.comp i₁ = scaleDualNumber K r := by
    ext <;> simp [q, i₁, scaleDualNumber, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]
  have hq₂ : q.comp i₂ = scaleDualNumber K t := by
    ext <;> simp [q, i₂, scaleDualNumber, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]
  have h := congrArg (fun b => specPointMap s q ≫ b) hd
  simpa only [MonObj.comp_mul, ← Category.assoc, specPointMap_comp, hqd, hq₁, hq₂] using h

private theorem dual_kernel_pow {K : Type u} [Field K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) (G : Over S) [GrpObj G]
    (a : specPoint s (DualNumber K) ⟶ G)
    (ha : specPointMap s (TrivSqZeroExt.fstHom K K K) ≫ a = 1) (n : ℕ) :
    a ^ n = specPointMap s (scaleDualNumber K (n : K)) ≫ a := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, scale_zero, ← specPointMap_comp, Category.assoc, ha,
      MonObj.comp_one, pow_zero]
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, dual_kernel_scale_add s G a ha, scale_one,
      specPointMap_id, Category.id_comp]

private theorem dual_kernel_pow_char {K : Type u} [Field K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) (G : Over S) [GrpObj G]
    (a : specPoint s (DualNumber K) ⟶ G)
    (ha : specPointMap s (TrivSqZeroExt.fstHom K K K) ≫ a = 1)
    (p : ℕ) [CharP K p] : a ^ p = 1 := by
  rw [dual_kernel_pow s G a ha, CharP.cast_eq_zero, scale_zero,
    ← specPointMap_comp, Category.assoc, ha, MonObj.comp_one]

private theorem dual_pow_char {K : Type u} [Field K] {S : Scheme.{u}}
    (s : Spec (.of K) ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (a : specPoint s (DualNumber K) ⟶ G) (p : ℕ) [CharP K p] :
    a ^ p = specPointMap s (scaleDualNumber K 0) ≫ a ^ p := by
  let z := specPointMap s (scaleDualNumber K 0)
  let b := z ≫ a
  have hb : specPointMap s (TrivSqZeroExt.fstHom K K K) ≫ b =
      specPointMap s (TrivSqZeroExt.fstHom K K K) ≫ a := by
    dsimp [b, z]
    rw [← Category.assoc, specPointMap_comp]
    congr 2
    ext
    simp [scaleDualNumber]
  have h : specPointMap s (TrivSqZeroExt.fstHom K K K) ≫ (a / b) = 1 := by
    simp [div_eq_mul_inv, MonObj.comp_mul, GrpObj.comp_inv, hb]
  have hp := dual_kernel_pow_char s G (a / b) h p
  rw [div_pow, div_eq_one] at hp
  simpa [b, MonObj.comp_pow] using hp

private def derivationDualHom {k K : Type u} [Field k] [Field K] [Algebra k K]
    (D : Derivation k K K) : K →ₐ[k] DualNumber K where
  toFun x := ⟨x, D x⟩
  map_one' := TrivSqZeroExt.ext rfl D.map_one_eq_zero
  map_mul' x y := by
    refine TrivSqZeroExt.ext rfl ?_
    change D (x * y) = x * D y + D x * y
    simp [mul_comm]
  map_zero' := TrivSqZeroExt.ext rfl D.map_zero
  map_add' x y := TrivSqZeroExt.ext rfl (D.map_add x y)
  commutes' x := TrivSqZeroExt.ext rfl (D.map_algebraMap x)

private theorem fromSpecResidueField_comp_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    X.fromSpecResidueField x ≫ f =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x) := by
  apply (cancel_mono (Spec (.of k)).toSpecΓ).mp
  rw [Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ_assoc]
  rw [← SpecMap_ΓSpecIso_hom]
  simp only [← Spec.map_comp, Iso.hom_inv_id_assoc]
  rfl

section Translation

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type w} [Category.{v} C] [CartesianMonoidalCategory C]
private def translationIso (G : C) [GrpObj G] (a : 𝟙_ C ⟶ G) : G ≅ G where
  hom := (toUnit G ≫ a) * 𝟙 G
  inv := (toUnit G ≫ a⁻¹) * 𝟙 G
  hom_inv_id := by simp [MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by simp [MonObj.comp_mul, GrpObj.comp_inv]

private noncomputable def fiberTranslationIso (G H : C) [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] (a : 𝟙_ C ⟶ G)
    [HasPullback η[H] f] [HasPullback (a ≫ f) f] :
    pullback η[H] f ≅ pullback (a ≫ f) f where
  hom := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (translationIso G a).hom) (by
      simp only [translationIso, MonObj.comp_mul, Category.assoc, MonObj.mul_comp,
        Category.comp_id]
      rw [← pullback.condition]
      simp only [← Category.assoc]
      rw [toUnit_unique (pullback.snd η[H] f ≫ toUnit G) (pullback.fst η[H] f)]
      simp [Category.assoc, MonObj.one_eq_one])
  inv := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (translationIso G a).inv) (by
      simp only [translationIso, MonObj.comp_mul, Category.assoc, MonObj.mul_comp,
        Category.comp_id, GrpObj.inv_comp]
      rw [← pullback.condition]
      simp only [← Category.assoc]
      rw [toUnit_unique (pullback.snd (a ≫ f) f ≫ toUnit G)
        (pullback.fst (a ≫ f) f)]
      simp [MonObj.one_eq_one, GrpObj.comp_inv, Category.assoc])
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp [Category.assoc]

end Translation

open MonoidalCategory in
@[sga "3 VIB 1.2" "partial"]
private noncomputable def schemeFiberTranslationIso {S : Scheme.{u}}
    (G H : Over S) [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] (a : 𝟙_ (Over S) ⟶ G) :
    pullback (η[H]).left f.left ≅ pullback (a ≫ f).left f.left :=
  (PreservesPullback.iso (Over.forget S) η[H] f).symm ≪≫
    (Over.forget S).mapIso (fiberTranslationIso G H f a) ≪≫
      PreservesPullback.iso (Over.forget S) (a ≫ f) f

open MonoidalCategory in
private theorem cardinalMk_fiber_translation {S : Scheme.{u}}
    (G H : Over S) [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] (a : 𝟙_ (Over S) ⟶ G) :
    Cardinal.mk (pullback (η[H]).left f.left : Scheme.{u}) =
      Cardinal.mk (pullback (a ≫ f).left f.left : Scheme.{u}) :=
  Cardinal.mk_congr (Scheme.homeoOfIso (schemeFiberTranslationIso G H f a)).toEquiv

open MonoidalCategory in
private theorem cardinalMk_fiber_zpow_id_translation
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    Cardinal.mk (pullback (η[A]).left (((𝟙 A : A ⟶ A) ^ d).left) : Scheme.{u}) =
      Cardinal.mk (pullback (a ^ d).left (((𝟙 A : A ⟶ A) ^ d).left) : Scheme.{u}) := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have : IsMonHom ((𝟙 A : A ⟶ A) ^ d) := by
    simpa only [Grp.Hom.hom_hom_zpow, Grp.id_hom_hom] using
      (inferInstance : IsMonHom (((𝟙 (Grp.mk A)) ^ d).hom.hom))
  simpa [GrpObj.comp_zpow] using
    cardinalMk_fiber_translation A A ((𝟙 A : A ⟶ A) ^ d) a


section RationalPoints

open MonoidalCategory CartesianMonoidalCategory

private noncomputable def homPullbackUnitEquiv
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (U G H : C) [MonObj H] (f : G ⟶ H) [HasPullback η[H] f] :
    (U ⟶ pullback η[H] f) ≃ {a : U ⟶ G // a ≫ f = 1} where
  toFun b := ⟨b ≫ pullback.snd _ _, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    simp [MonObj.one_eq_one]⟩
  invFun a := pullback.lift (toUnit U) a.1 (by
    simpa [MonObj.one_eq_one] using a.2.symm)
  left_inv b := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst]
      exact toUnit_unique _ _
    · simp
  right_inv a := by
    apply Subtype.ext
    simp

private noncomputable def pointEquivOfIsFinite
    {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k)))
    [IsFinite A.hom] : (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃ A.left := by
  have : IsLocallyArtinian A.left := IsLocallyArtinian.of_locallyQuasiFinite A.hom
  let e : (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃
      {p : Spec (.of k) ⟶ A.left // p ≫ A.hom = 𝟙 _} := {
    toFun a := ⟨a.left, a.w⟩
    invFun p := Over.homMk p.1 p.2
    left_inv a := by ext; rfl
    right_inv p := rfl }
  exact e.trans ((pointEquivClosedPoint A.hom).trans {
    toFun := Subtype.val
    invFun := fun x => ⟨x, isClosed_discrete _⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl })

private theorem cardinalMk_fiber_unit_eq_cardinalMk_kernel
    {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [MonObj A]
    (f : A ⟶ A) [IsFinite f.left] :
    Cardinal.mk (pullback (η[A]).left f.left : Scheme.{u}) =
      Cardinal.mk {a : 𝟙_ (Over (Spec (.of k))) ⟶ A // a ≫ f = 1} := by
  let B := pullback η[A] f
  let e := PreservesPullback.iso (Over.forget (Spec (.of k))) η[A] f
  have hB : B.hom = e.hom ≫ pullback.fst (η[A]).left f.left := by
    calc
      B.hom = (pullback.fst η[A] f).left := by
        simpa using (Over.w (pullback.fst η[A] f)).symm
      _ = _ := (PreservesPullback.iso_hom_fst (Over.forget (Spec (.of k))) η[A] f).symm
  have : IsFinite B.hom := by rw [hB]; infer_instance
  calc
    Cardinal.mk (pullback (η[A]).left f.left : Scheme.{u}) = Cardinal.mk B.left :=
      Cardinal.mk_congr (Scheme.homeoOfIso e).symm.toEquiv
    _ = Cardinal.mk (𝟙_ (Over (Spec (.of k))) ⟶ B) :=
      Cardinal.mk_congr (pointEquivOfIsFinite B).symm
    _ = _ := Cardinal.mk_congr (homPullbackUnitEquiv _ A A f)

/-- A finite locally free morphism is finite, flat and locally of finite presentation. -/
private theorem isFinite_flat_of_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r] :
    IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f :=
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r)

private theorem cardinalMk_fiber_zpow_id_eq_cardinalMk_pow_eq_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A)
    (d : ℤ) (hd : d ≠ 0) :
    Cardinal.mk (pullback (η[A]).left (((𝟙 A : A ⟶ A) ^ d).left) : Scheme.{u}) =
      Cardinal.mk {a : 𝟙_ (Over (Spec (.of k))) ⟶ A // a ^ d = 1} := by
  have := isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube A hcube d hd
  have := (isFinite_flat_of_isFiniteLocallyFreeOfRank
    (((𝟙 A : A ⟶ A) ^ d).left) (d.natAbs ^ (2 * abelianVarietyDimension A))).1
  simpa only [GrpObj.comp_zpow, Category.comp_id] using
    cardinalMk_fiber_unit_eq_cardinalMk_kernel A ((𝟙 A : A ⟶ A) ^ d)

end RationalPoints

private theorem surjective_of_isFinite_flat
    {X Y : Scheme.{u}} [Nonempty X] [PreconnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    Surjective f := by
  have hr : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hr.eq_univ (Set.range_nonempty f))⟩

theorem surjective_zpow_id_of_ne_zero
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) :
    Surjective (((𝟙 A : A ⟶ A) ^ d).left) := by
  have := isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube A hcube d hd
  obtain ⟨hfin, hflat, hfp⟩ := isFinite_flat_of_isFiniteLocallyFreeOfRank
    (((𝟙 A : A ⟶ A) ^ d).left) (d.natAbs ^ (2 * abelianVarietyDimension A))
  exact surjective_of_isFinite_flat _
private theorem Γevaluation_residueFieldCongr (X : Scheme.{u}) {x y : X} (h : x = y) :
    X.Γevaluation x ≫ (X.residueFieldCongr h).hom = X.Γevaluation y := by
  subst y
  simp

private theorem Γevaluation_genericPoint_residueFieldMap (X : Scheme.{u}) [IrreducibleSpace X]
    (f : X ⟶ X) [IsDominant f] :
    X.Γevaluation (genericPoint X) ≫
        (X.residueFieldCongr (map_genericPoint_of_isDominant f).symm).hom ≫
          f.residueFieldMap (genericPoint X) =
      f.appTop ≫ X.Γevaluation (genericPoint X) := by
  rw [← Category.assoc, Γevaluation_residueFieldCongr, Scheme.Γevaluation_naturality]

private noncomputable def genericResidueFieldEnd
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IrreducibleSpace A.left]
    (f : A ⟶ A) [IsDominant f.left] :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    A.left.residueField (genericPoint A.left) →ₐ[k]
      A.left.residueField (genericPoint A.left) := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  let r : A.left.residueField (genericPoint A.left) ⟶
      A.left.residueField (genericPoint A.left) :=
    (A.left.residueFieldCongr (map_genericPoint_of_isDominant f.left).symm).hom ≫
      f.left.residueFieldMap (genericPoint A.left)
  have hr : A.left.Γevaluation (genericPoint A.left) ≫ r =
      f.left.appTop ≫ A.left.Γevaluation (genericPoint A.left) := by
    exact Γevaluation_genericPoint_residueFieldMap A.left f.left
  have hcomm : ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)) ≫ r =
      (Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left) := by
    simp only [Category.assoc]
    rw [hr, ← Category.assoc A.hom.appTop, ← Scheme.Hom.comp_appTop, Over.w]
  exact { r.hom with commutes' := fun a => congrArg (fun b => b a) hcomm }

private theorem genericResidueFieldEnd_spec
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IrreducibleSpace A.left]
    (f : A ⟶ A) [IsDominant f.left] :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    Spec.map (CommRingCat.ofHom (genericResidueFieldEnd A f).toRingHom) ≫
        A.left.fromSpecResidueField (genericPoint A.left) =
      A.left.fromSpecResidueField (genericPoint A.left) ≫ f.left := by
  dsimp only [genericResidueFieldEnd]
  simp only [CommRingCat.ofHom_hom]
  rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f.left _

private theorem genericResidueFieldEnd_zpow_derivation_eq_zero
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (p : ℕ) [CharP k p] (hp : 0 < p) :
    letI : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
      surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast hp.ne')
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    ∀ D : Derivation k (A.left.residueField (genericPoint A.left))
        (A.left.residueField (genericPoint A.left)), ∀ y,
      D (genericResidueFieldEnd A ((𝟙 A : A ⟶ A) ^ (p : ℤ)) y) = 0 := by
  let : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
    surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast hp.ne')
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  intro D y
  let K : Type u := A.left.residueField (genericPoint A.left)
  let c : Spec (.of K) ⟶ A.left := A.left.fromSpecResidueField (genericPoint A.left)
  let s : Spec (.of K) ⟶ Spec (.of k) := c ≫ A.hom
  let d := derivationDualHom D
  have hs : s = Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
    fromSpecResidueField_comp_eq A.hom _
  have hw : (Spec.map (CommRingCat.ofHom d.toRingHom) ≫ c) ≫ A.hom =
      (specPoint s (DualNumber K)).hom := by
    change (Spec.map (CommRingCat.ofHom d.toRingHom) ≫ c) ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ s
    rw [Category.assoc]
    change Spec.map (CommRingCat.ofHom d.toRingHom) ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ s
    rw [hs, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact d.commutes t
  let a : specPoint s (DualNumber K) ⟶ A :=
    Over.homMk (Spec.map (CommRingCat.ofHom d.toRingHom) ≫ c) hw
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have : CharP K p := charP_of_injective_algebraMap' k p
  have h := congrArg Over.Hom.left (dual_pow_char s A a p)
  let f := ((𝟙 A : A ⟶ A) ^ (p : ℤ))
  have hpow : a ^ p = a ≫ f := by
    simp [f, zpow_natCast, MonObj.comp_pow]
  rw [hpow] at h
  change (Spec.map (CommRingCat.ofHom d.toRingHom) ≫ c) ≫ f.left =
    Spec.map (CommRingCat.ofHom (scaleDualNumber K 0).toRingHom) ≫
      ((Spec.map (CommRingCat.ofHom d.toRingHom) ≫ c) ≫ f.left) at h
  have hc : c ≫ f.left =
      Spec.map (CommRingCat.ofHom (genericResidueFieldEnd A f).toRingHom) ≫ c :=
    (genericResidueFieldEnd_spec A f).symm
  simp only [Category.assoc, hc] at h
  simp only [← Category.assoc] at h
  have hh := (cancel_mono c).mp h
  simp only [← Spec.map_comp] at hh
  have he := congrArg (fun g => (g.hom y).snd) (Spec.map_inj.mp hh)
  change D (genericResidueFieldEnd A f y) =
    (scaleDualNumber K 0 (d (genericResidueFieldEnd A f y))).snd at he
  simpa [scaleDualNumber, f, zpow_natCast] using he

private theorem genericResidueFieldEnd_zpow_differential_eq_zero
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (p : ℕ) [CharP k p] (hp : 0 < p) :
    letI : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
      surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast hp.ne')
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    ∀ y, KaehlerDifferential.D k _
      (genericResidueFieldEnd A ((𝟙 A : A ⟶ A) ^ (p : ℤ)) y) = 0 := by
  let : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
    surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast hp.ne')
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  intro y
  apply (Module.forall_dual_apply_eq_zero_iff (A.left.residueField (genericPoint A.left)) _).mp
  intro l
  exact genericResidueFieldEnd_zpow_derivation_eq_zero A hcube p hp
    (l.compDer (KaehlerDifferential.D k _)) y

private theorem genericResidueFieldEnd_apply_Γevaluation
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IrreducibleSpace A.left]
    (f : A ⟶ A) [IsDominant f.left] (s : Γ(A.left, ⊤)) :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    genericResidueFieldEnd A f (A.left.Γevaluation (genericPoint A.left) s) =
      A.left.Γevaluation (genericPoint A.left) (f.left.appTop s) := by
  exact congrArg (fun b => b s) (Γevaluation_genericPoint_residueFieldMap A.left f.left)

private theorem abelianVarietyDimension_eq_trdeg
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] :
    let : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    abelianVarietyDimension A =
      Cardinal.toNat (Algebra.trdeg k (A.left.residueField (genericPoint A.left))) := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  have h := AlgebraicGeometry.topologicalKrullDim_eq_trdeg_residueField
    k A.left A.hom (genericPoint A.left) (genericPoint_spec A.left)
  simp only [abelianVarietyDimension, h, WithBot.unbotD_coe,
    Cardinal.toNat_toENat]

private theorem finSepDegree_le_of_inseparable_subextension
    {K E P : Type*} [Field K] [Field E] [Field P]
    [Algebra E P] [Algebra P K] [Algebra E K] [IsScalarTower E P K]
    [Algebra.IsAlgebraic E P]
    [FiniteDimensional E P] [FiniteDimensional E K] [FiniteDimensional P K]
    (p g : ℕ)
    (hPK : IsPurelyInseparable P K) (hp : 0 < p)
    (hdegree : Module.finrank E K = p ^ (2 * g))
    (hPdegree : Module.finrank P K = p ^ g) :
    Field.finSepDegree E K ≤ p ^ g := by
  have hTower := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic E P K
  have hPInsep : Field.finInsepDegree P K = p ^ g := by
    rw [hPK.finInsepDegree_eq, hPdegree]
  have hEInsep : p ^ g ≤ Field.finInsepDegree E K := by
    have hpos : 0 < Field.finInsepDegree E P :=
      Nat.pos_of_ne_zero (NeZero.ne (Field.finInsepDegree E P))
    rw [← hPInsep, ← hTower]
    exact Nat.le_mul_of_pos_left _ hpos
  have hsep := Field.finSepDegree_mul_finInsepDegree E K
  rw [hdegree] at hsep
  have hprod : Field.finSepDegree E K * (p ^ g) ≤ (p ^ g) * (p ^ g) := by
    calc
      Field.finSepDegree E K * (p ^ g) ≤
          Field.finSepDegree E K * Field.finInsepDegree E K :=
        Nat.mul_le_mul_left _ hEInsep
      _ = p ^ (2 * g) := hsep
      _ = (p ^ g) * (p ^ g) := by rw [← pow_add]; congr 1; omega
  exact Nat.le_of_mul_le_mul_right hprod (Nat.pow_pos hp)

private noncomputable def boundedExpFinEquiv (g p : ℕ) :
    BoundedExp (Fin g) p ≃ (Fin g → Fin p) := by
  let e₁ : BoundedExp (Fin g) p ≃
      {f : Fin g → ℕ // ∀ i, f i < p} :=
    Equiv.subtypeEquiv Finsupp.equivFunOnFinite (by
      intro f
      simp [Finsupp.equivFunOnFinite])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun _ => (Fin.equivSubtype (n := p)).symm))

private theorem pBasis_finrank_of_fin_index
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p g : ℕ) (x : Fin g → K) (hx : PBasis k x p) :
    Module.finrank (compositumFrobenius k K p) K = p ^ g := by
  classical
  let : Fintype (BoundedExp (Fin g) p) :=
    Fintype.ofEquiv _ (boundedExpFinEquiv g p).symm
  calc
    Module.finrank (compositumFrobenius k K p) K =
        Fintype.card (BoundedExp (Fin g) p) := Module.finrank_eq_card_basis hx.basis
    _ = Fintype.card (Fin g → Fin p) := Fintype.card_congr (boundedExpFinEquiv g p)
    _ = p ^ g := by simp [Fintype.card_pi]

private theorem mem_compositumFrobenius_of_D_eq_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (y : K)
    (hy : KaehlerDifferential.D k K y = 0) : y ∈ compositumFrobenius k K p := by
  classical
  by_contra hnot
  have he : PIndependent k (Subtype.val : (∅ : Set K) → K) p :=
    (pIndependent_iff_linearIndependent_differentials _ p).mpr (linearIndependent_empty_type)
  have hn : y ∉ Submodule.span (compositumFrobenius k K p)
      (Set.range (monomialFamily (Subtype.val : (∅ : Set K) → K) p)) := by
    intro h
    apply hnot
    clear hy hnot
    induction h using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨E, rfl⟩ := hz
      have hE : E.val = 0 := Subsingleton.elim _ _
      simp [monomialFamily, hE, monomialPow]
    | zero => exact Subfield.zero_mem _
    | add z w _ _ hz hw => exact Subfield.add_mem _ hz hw
    | smul r z _ hz => exact Subfield.mul_mem _ r.property hz
  have hi := (pIndependent_iff_linearIndependent_differentials _ p).mp
    (insert_pIndependent_of_not_mem_span p ∅ he hn)
  have hnz := LinearIndependent.ne_zero (R := K)
    (v := fun i : ↥(insert y (∅ : Set K)) => KaehlerDifferential.D k K i.val)
    ⟨y, by simp⟩ hi
  change KaehlerDifferential.D k K y ≠ 0 at hnz
  exact hnz hy

private theorem functionField_separableDegree_le_of_pBasis
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p g : ℕ) [Fact p.Prime] [CharP k p] [CharP K p]
    (hp : 0 < p) (x : Fin g → K) (hx : PBasis k x p)
    (f : K →ₐ[k] K)
    (hzero : ∀ y, KaehlerDifferential.D k K (f y) = 0)
    (hdegree : Module.finrank f.fieldRange K = p ^ (2 * g)) :
    Field.finSepDegree f.fieldRange K ≤ p ^ g := by
  classical
  let P₀ := compositumFrobenius k K p
  have hcontains : ∀ a : k, algebraMap k K a ∈ P₀ :=
    fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let P : IntermediateField k K := P₀.toIntermediateField hcontains
  have hEP : f.fieldRange ≤ P := by
    rintro y ⟨z, rfl⟩
    exact mem_compositumFrobenius_of_D_eq_zero p (f z) (hzero z)
  have hPsub : P.toSubfield = compositumFrobenius k K p := rfl
  have hPdegree : Module.finrank P K = p ^ g := by
    change Module.finrank P.toSubfield K = p ^ g
    rw [hPsub]
    exact pBasis_finrank_of_fin_index p g x hx
  have hPure : IsPurelyInseparable P K := by
    rw [isPurelyInseparable_iff_pow_mem (F := P) p]
    intro y
    refine ⟨1, ?_⟩
    rw [pow_one]
    change y ^ p ∈ Set.range (algebraMap P K)
    have hy : y ^ p ∈ P₀ := Subfield.subset_closure (Or.inr ⟨y, rfl⟩)
    have hyP : y ^ p ∈ P := hy
    exact ⟨⟨y ^ p, hyP⟩, rfl⟩
  let : Algebra P K := P.toAlgebra
  let : Algebra f.fieldRange P := (IntermediateField.inclusion hEP).toRingHom.toAlgebra
  let : IsScalarTower f.fieldRange P K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hPfin : FiniteDimensional P K :=
    FiniteDimensional.of_finrank_pos (hPdegree ▸ Nat.pow_pos hp)
  have hEfin : FiniteDimensional f.fieldRange K :=
    FiniteDimensional.of_finrank_pos (hdegree ▸ Nat.pow_pos hp)
  have : FiniteDimensional f.fieldRange P := FiniteDimensional.left f.fieldRange P K
  have : Algebra.IsAlgebraic f.fieldRange P := Algebra.IsAlgebraic.of_finite _ _
  exact finSepDegree_le_of_inseparable_subextension p g hPure hp hdegree hPdegree

private theorem exists_pBasis_fin
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional K Ω[K⁄k]] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ x : Fin (Module.finrank K Ω[K⁄k]) → K, PBasis k x p := by
  classical
  obtain ⟨S, hS⟩ := exists_pBasis (k := k) (K := K) p
  have hD := (pBasis_iff_basis_differentials (k := k) (Subtype.val : S → K) p).mp hS
  let b : Module.Basis S K Ω[K⁄k] := Module.Basis.mk hD.1 hD.2
  let : Fintype S :=
    (b.finite_index_of_rank_lt_aleph0 (Module.rank_lt_aleph0 K Ω[K⁄k])).fintype
  let e : S ≃ Fin (Module.finrank K Ω[K⁄k]) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let x : Fin (Module.finrank K Ω[K⁄k]) → K := fun i => e.symm i
  refine ⟨x, (pBasis_iff_basis_differentials (k := k) x p).mpr ⟨?_, ?_⟩⟩
  · exact hD.1.comp e.symm e.symm.injective
  · have hr : Set.range (fun i => KaehlerDifferential.D k K (x i)) =
        Set.range (fun s : S => KaehlerDifferential.D k K s) :=
      by
        change Set.range ((fun s : S => KaehlerDifferential.D k K (s : K)) ∘ e.symm) = _
        rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    rw [hr]
    exact hD.2


private theorem finSepDegree_le_pow_finrank_differentials_of_zero_differential
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional K Ω[K⁄k]] (p : ℕ) [Fact p.Prime]
    [CharP k p] [CharP K p]
    (f : K →ₐ[k] K) (hzero : ∀ y, KaehlerDifferential.D k K (f y) = 0)
    (hdegree : Module.finrank f.fieldRange K = p ^ (2 * Module.finrank K Ω[K⁄k])) :
    Field.finSepDegree f.fieldRange K ≤ p ^ Module.finrank K Ω[K⁄k] := by
  obtain ⟨x, hx⟩ := exists_pBasis_fin (k := k) (K := K) p
  exact functionField_separableDegree_le_of_pBasis p (Module.finrank K Ω[K⁄k])
    (Nat.Prime.pos Fact.out) x hx f hzero hdegree

private theorem multiplication_by_characteristic_isFiniteLocallyFreeOfRank
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (p : ℕ) [CharP k p] (hp : 0 < p) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left)
      (p ^ (2 * abelianVarietyDimension A)) := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  simpa [Int.natAbs_natCast] using
    (isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube A hcube (p : ℤ) hpz)

/-- The stalk of `Spec k` at a point is a quotient of `k`, compatible with the residue field map. -/
private theorem exists_surjective_stalk_comp_eq_algebraMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    ∃ b : k →+* (Spec (.of k)).presheaf.stalk (f x), Function.Surjective b ∧
      (f.stalkMap x ≫ X.residue x).hom.comp b = algebraMap k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let S : Scheme := Spec (.of k)
  let y : S := f x
  refine ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ S.presheaf.germ ⊤ y trivial).hom, ?_, ?_⟩
  · intro r
    obtain ⟨U, hyU, s, rfl⟩ := S.presheaf.exists_germ_eq r
    have hU : U = ⊤ := by
      apply top_unique
      intro z _
      simpa [Subsingleton.elim z y] using hyU
    subst U
    refine ⟨(Scheme.ΓSpecIso (.of k)).hom.hom s, ?_⟩
    change (S.presheaf.germ ⊤ y trivial).hom
      ((Scheme.ΓSpecIso (.of k)).inv.hom ((Scheme.ΓSpecIso (.of k)).hom.hom s)) = _
    simp
    rfl
  · change ((Scheme.ΓSpecIso (.of k)).inv ≫
      S.presheaf.germ ⊤ y trivial ≫ f.stalkMap x ≫ X.residue x).hom = _
    rw [← Scheme.residue_residueFieldMap]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ S.Γevaluation y ≫
      f.residueFieldMap x).hom = _
    rw [Scheme.Γevaluation_naturality]
    rfl

private theorem residueField_essFiniteType
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.EssFiniteType k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  obtain ⟨b, hb, hcomp⟩ := exists_surjective_stalk_comp_eq_algebraMap f x
  let g := (f.stalkMap x ≫ X.residue x).hom
  have hg : g.EssFiniteType := RingHom.EssFiniteType.comp
    (LocallyOfFiniteType.stalkMap f x)
    (RingHom.FiniteType.of_surjective _ (X.residue_surjective x)).essFiniteType
  have hc := RingHom.EssFiniteType.comp
    (RingHom.FiniteType.of_surjective b hb).essFiniteType hg
  rw [hcomp] at hc
  exact RingHom.essFiniteType_algebraMap.mp hc

private theorem genericResidueField_formallySmooth
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f] :
    letI : Algebra k (X.residueField (genericPoint X)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.Γevaluation (genericPoint X)).hom.toAlgebra
    Algebra.FormallySmooth k (X.residueField (genericPoint X)) := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  obtain ⟨b, hb, hcomp⟩ := exists_surjective_stalk_comp_eq_algebraMap f (genericPoint X)
  let x := genericPoint X
  have hbs : b.FormallySmooth := .of_bijective ⟨b.injective, hb⟩
  have hfs : (f.stalkMap x).hom.FormallySmooth := by
    apply Scheme.Hom.mem_smoothLocus.mp
    rw [f.smoothLocus_eq_top]
    trivial
  have hrs : (X.residue x).hom.FormallySmooth :=
    .of_bijective ⟨(X.residue x).hom.injective, X.residue_surjective x⟩
  exact RingHom.formallySmooth_algebraMap.mp (hcomp ▸ (hbs.comp hfs).comp hrs)

private theorem finrank_differentials_eq_trdeg_of_formallySmooth
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] [Algebra.FormallySmooth k K] :
    Module.finrank K Ω[K⁄k] = Cardinal.toNat (Algebra.trdeg k K) := by
  have : Subsingleton (Algebra.H1Cotangent k K) :=
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent k K).mp inferInstance
  have h := (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K).2.2
  have hH : Module.finrank K (Algebra.H1Cotangent k K) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hH, Nat.cast_zero, sub_zero] at h
  exact_mod_cast h.symm

private theorem abelianVarietyDimension_eq_finrank_differentials
    {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    abelianVarietyDimension A =
      Module.finrank (A.left.residueField (genericPoint A.left))
        Ω[A.left.residueField (genericPoint A.left)⁄k] := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  have : Algebra.EssFiniteType k (A.left.residueField (genericPoint A.left)) :=
    residueField_essFiniteType A.hom (genericPoint A.left)
  have : Smooth A.hom := by
    have hft : LocallyOfFiniteType A.hom := inferInstance
    have hred : GeometricallyReduced A.hom := inferInstance
    obtain ⟨X, f, rfl⟩ := Over.mk_surjective A
    have : LocallyOfFiniteType f := by simpa only [Over.mk_hom] using hft
    have : GeometricallyReduced f := by simpa only [Over.mk_hom] using hred
    exact smooth_of_grpObj f
  have : Algebra.FormallySmooth k (A.left.residueField (genericPoint A.left)) :=
    genericResidueField_formallySmooth A.hom
  exact (abelianVarietyDimension_eq_trdeg A).trans
    (finrank_differentials_eq_trdeg_of_formallySmooth (k := k)).symm

private theorem exists_generic_pBasis
    {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    ∃ x : Fin (abelianVarietyDimension A) →
      A.left.residueField (genericPoint A.left), PBasis k x p := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  have : Algebra.EssFiniteType k (A.left.residueField (genericPoint A.left)) :=
    residueField_essFiniteType A.hom (genericPoint A.left)
  have : CharP (A.left.residueField (genericPoint A.left)) p :=
    charP_of_injective_algebraMap' k p
  have := (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k
    (A.left.residueField (genericPoint A.left))).1
  rw [abelianVarietyDimension_eq_finrank_differentials A]
  exact exists_pBasis_fin p


private theorem finSepDegree_genericResidueFieldEnd_le_of_zero_differential
    {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (p : ℕ) [Fact p.Prime] [CharP k p] (f : A ⟶ A) [IsDominant f.left] :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    let φ := genericResidueFieldEnd A f
    (∀ y, KaehlerDifferential.D k _ (φ y) = 0) →
      Module.finrank φ.fieldRange (A.left.residueField (genericPoint A.left)) =
        p ^ (2 * abelianVarietyDimension A) →
      Field.finSepDegree φ.fieldRange (A.left.residueField (genericPoint A.left)) ≤
        p ^ abelianVarietyDimension A := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  have : CharP (A.left.residueField (genericPoint A.left)) p :=
    charP_of_injective_algebraMap' k p
  dsimp only
  intro hzero hdegree
  obtain ⟨x, hx⟩ := exists_generic_pBasis A p
  exact functionField_separableDegree_le_of_pBasis p (abelianVarietyDimension A)
    (Nat.Prime.pos Fact.out) x hx (genericResidueFieldEnd A f) hzero hdegree

open TopologicalSpace in
private theorem rank_stalk_of_isFiniteLocallyFreeOfRank (X : Scheme.{u}) (F : X.Modules) (r : ℕ)
    [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.rank (X.presheaf.stalk x) (F.presheaf.stalk x) = r ∧
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  classical
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨q, hq, hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  have hcover := (Opens.coversTop_iff X q.X).mp q.coversTop
  obtain ⟨i, hi⟩ := hcover.exists_mem x
  let U := q.X i
  have hπ : IsIso (q.generators i).π := hq.isIso i
  let e : SheafOfModules.free (q.generators i).I ≅ F.over U := asIso (q.generators i).π
  let E := U.sheafOfModulesEquivOver X.ringCatSheaf
  let eFree := SheafOfModules.mapFreeIso E.functor (q.generators i).I
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)
  let t : LocallyFreeRank.Trivialization X
      (LocallyFreeRank.toRingSheaf X X.sheaf) F U := ⟨(q.generators i).I, by
    exact (eFree ≪≫ E.functor.mapIso e ≪≫
      (show E.functor.obj (F.over U) ≅
        LocallyFreeRank.restrictMod X U
          (LocallyFreeRank.toRingSheaf X X.sheaf) F from Iso.refl _)).symm⟩
  obtain ⟨et⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X X.sheaf F x hi t
  let ei := (hr i).some
  let eFin := et.trans (Finsupp.domLCongr ei)
  change F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    (Fin r →₀ X.presheaf.stalk x) at eFin
  have hfree : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Module.Free.of_equiv eFin.symm
  refine ⟨?_, hfree⟩
  have he : Module.rank (X.presheaf.stalk x) (F.presheaf.stalk x) =
      Module.rank (X.presheaf.stalk x) (Fin r →₀ X.presheaf.stalk x) := eFin.rank_eq
  rw [he]
  simp

open TopologicalSpace in
private theorem preimage_genericPoint_of_locallyQuasiFinite
    {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Y) [LocallyQuasiFinite f] :
    f ⁻¹' {f (genericPoint X)} = {genericPoint X} := by
  have : DiscreteTopology (f ⁻¹' {f (genericPoint X)}) :=
    (f.fiberHomeo (f (genericPoint X))).discreteTopology
  ext x
  constructor
  · intro hx
    have hs : (⟨genericPoint X, rfl⟩ : f ⁻¹' {f (genericPoint X)}) ⤳ ⟨x, hx⟩ :=
      (subtype_specializes_iff _ _).mpr ((genericPoint_spec X).specializes trivial)
    exact (congrArg Subtype.val (specializes_iff_eq.mp hs)).symm
  · rintro rfl
    rfl

open TopologicalSpace in
private noncomputable def unitStalkLinearEquiv {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) :
    (ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{u})).presheaf x)) ≃ₗ[ToType (R.stalk x)]
      (ToType (R.stalk x)) := by
  set pIso : (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk (PresheafOfModules.unit
        (R ⋙ forget₂ _ RingCat.{u})).presheaf x :=
    preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ R) with hpIso
  set addE : (ToType (TopCat.Presheaf.stalk (PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{u})).presheaf x)) ≃+
      ToType (R.stalk x) := pIso.symm.addCommGroupIsoToAddEquiv
  have key : ∀ (U : Opens X) (hxU : x ∈ U)
      (s : ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf.obj
        (Opposite.op U))),
      addE ((ConcreteCategory.hom (TopCat.Presheaf.germ
          (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf U x hxU)) s) =
        (ConcreteCategory.hom (R.germ U x hxU)) s := by
    intro U hxU s
    have h := ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ R)
      (Opposite.op ⟨U, hxU⟩)
    rw [← hpIso] at h
    have h2 := ConcreteCategory.congr_hom h s
    change (ConcreteCategory.hom pIso.inv)
        ((ConcreteCategory.hom (colimit.ι (((OpenNhds.inclusion x).op ⋙ R) ⋙
          (forget₂ CommRingCat.{u} RingCat.{u} ⋙
            forget₂ RingCat.{u} AddCommGrpCat.{u}))
            (Opposite.op ⟨U, hxU⟩))) s) =
        (ConcreteCategory.hom ((forget₂ CommRingCat.{u} RingCat.{u} ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u}).map
            (colimit.ι ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)))) s
    exact h2
  refine { addE with toFun := addE, map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf m
  obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  set W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀ =
      (ConcreteCategory.hom (R.germ W x hxW))
        ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf U x hxU)) m₀ =
      (ConcreteCategory.hom (TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf W x hxW))
        ((ConcreteCategory.hom ((PresheafOfModules.unit
          (R ⋙ forget₂ _ RingCat.{u})).presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  rw [hr, hm]
  set rr : ToType (R.obj (Opposite.op W)) :=
    (ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀
  set mm : ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf.obj
      (Opposite.op W)) :=
    (ConcreteCategory.hom ((PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{u})).presheaf.map (homOfLE (inf_le_left)).op)) m₀
  rw [← PresheafOfModules.germ_smul
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})) x W hxW rr mm]
  refine (key W hxW _).trans ?_
  rw [key W hxW mm]
  exact map_mul (R.germ W x hxW).hom rr mm

private theorem rank_stalkMap_of_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r]
    (x : X) (hfiber : f ⁻¹' {f x} = {x}) :
    letI := (f.stalkMap x).hom.toAlgebra
    Module.rank (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) = r := by
  let := (f.stalkMap x).hom.toAlgebra
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let G : Y.Modules := (Scheme.Modules.pushforward f).obj F
  let : F.IsQuasicoherent := by
    let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅ F :=
      coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ F)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module (Y.presheaf.stalk (f x)) (G.presheaf.stalk (f x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val (f x)
  obtain ⟨e⟩ :=
    AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber
      f x hfiber F
  let e' : F.presheaf.stalk x ≃ₗ[Y.presheaf.stalk (f x)] G.presheaf.stalk (f x) :=
    LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
  let e₀ := unitStalkLinearEquiv X.presheaf x
  let e₁ : F.presheaf.stalk x ≃ₗ[Y.presheaf.stalk (f x)] X.presheaf.stalk x :=
    { e₀.toAddEquiv with
      map_smul' := fun a b => e₀.map_smul ((f.stalkMap x).hom a) b }
  exact (e₁.symm.trans e').rank_eq.trans
    (rank_stalk_of_isFiniteLocallyFreeOfRank Y G r (f x)).1


private theorem residueDegree_eq_of_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r]
    (x : X) (hfiber : f ⁻¹' {f x} = {x})
    (hX : IsField (X.presheaf.stalk x))
    (hY : IsField (Y.presheaf.stalk (f x))) :
    f.residueDegree x = r := by
  let : Field (X.presheaf.stalk x) := hX.toField
  let : Field (Y.presheaf.stalk (f x)) := hY.toField
  let := (f.stalkMap x).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let eX : X.presheaf.stalk x ≃+* X.residueField x :=
    RingEquiv.ofBijective (X.residue x).hom
      ⟨(X.residue x).hom.injective, X.residue_surjective x⟩
  let eY : Y.presheaf.stalk (f x) ≃+* Y.residueField (f x) :=
    RingEquiv.ofBijective (Y.residue (f x)).hom
      ⟨(Y.residue (f x)).hom.injective, Y.residue_surjective (f x)⟩
  have he := Algebra.finrank_eq_of_equiv_equiv eY eX
    (congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x))
  exact he.symm.trans (by
    simpa [Module.finrank] using
      congrArg Cardinal.toNat (rank_stalkMap_of_isFiniteLocallyFreeOfRank f r x hfiber))

private theorem residueDegree_genericPoint_eq_of_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r] :
    f.residueDegree (genericPoint X) = r := by
  apply residueDegree_eq_of_isFiniteLocallyFreeOfRank f r (genericPoint X)
    (preimage_genericPoint_of_locallyQuasiFinite f)
  · exact Field.toIsField _
  · rw [map_genericPoint_of_isDominant f]
    exact Field.toIsField _


private theorem residueFieldCongr_symm_hom_apply (X : Scheme.{u})
    {x y : X} (h : x = y) (a : X.residueField x) :
    (X.residueFieldCongr h.symm).hom ((X.residueFieldCongr h).hom a) = a := by
  subst y
  rfl

private theorem genericResidueFieldEnd_residueFieldCongr
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IrreducibleSpace A.left]
    (f : A ⟶ A) [IsDominant f.left] (a : A.left.residueField (f.left (genericPoint A.left))) :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    genericResidueFieldEnd A f
        ((A.left.residueFieldCongr (map_genericPoint_of_isDominant f.left)).hom a) =
      f.left.residueFieldMap (genericPoint A.left) a := by
  change f.left.residueFieldMap (genericPoint A.left)
    ((A.left.residueFieldCongr (map_genericPoint_of_isDominant f.left).symm).hom
      ((A.left.residueFieldCongr (map_genericPoint_of_isDominant f.left)).hom a)) = _
  rw [residueFieldCongr_symm_hom_apply]

private theorem finrank_genericResidueFieldEnd_eq_residueDegree
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IrreducibleSpace A.left]
    (f : A ⟶ A) [IsDominant f.left] :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    Module.finrank (genericResidueFieldEnd A f).fieldRange
      (A.left.residueField (genericPoint A.left)) =
        f.left.residueDegree (genericPoint A.left) := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  let φ := genericResidueFieldEnd A f
  let h := map_genericPoint_of_isDominant f.left
  let e₀ := A.left.residueFieldCongr h
  let e₁ : A.left.residueField (f.left (genericPoint A.left)) ≃+*
      A.left.residueField (genericPoint A.left) :=
    RingEquiv.ofBijective e₀.hom.hom (ConcreteCategory.bijective_of_isIso e₀.hom)
  let e := e₁.trans φ.equivFieldRange.toRingEquiv
  let := (f.left.residueFieldMap (genericPoint A.left)).hom.toAlgebra
  apply (Algebra.finrank_eq_of_equiv_equiv e
    (RingEquiv.refl (A.left.residueField (genericPoint A.left))) ?_).symm
  ext a
  exact genericResidueFieldEnd_residueFieldCongr A f a

private theorem finrank_genericResidueFieldEnd_zpow_id
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) :
    letI : Surjective (((𝟙 A : A ⟶ A) ^ d).left) :=
      surjective_zpow_id_of_ne_zero A hcube d hd
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    Module.finrank (genericResidueFieldEnd A ((𝟙 A : A ⟶ A) ^ d)).fieldRange
      (A.left.residueField (genericPoint A.left)) =
        d.natAbs ^ (2 * abelianVarietyDimension A) := by
  let : Surjective (((𝟙 A : A ⟶ A) ^ d).left) :=
    surjective_zpow_id_of_ne_zero A hcube d hd
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  have := isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube A hcube d hd
  have := (isFinite_flat_of_isFiniteLocallyFreeOfRank
    (((𝟙 A : A ⟶ A) ^ d).left) (d.natAbs ^ (2 * abelianVarietyDimension A))).1
  rw [finrank_genericResidueFieldEnd_eq_residueDegree]
  exact residueDegree_genericPoint_eq_of_isFiniteLocallyFreeOfRank _ _


private theorem finSepDegree_multiplication_by_char_le_of_zero_differential
    {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
      surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    let φ := genericResidueFieldEnd A ((𝟙 A : A ⟶ A) ^ (p : ℤ))
    (∀ y, KaehlerDifferential.D k _ (φ y) = 0) →
      Field.finSepDegree φ.fieldRange (A.left.residueField (genericPoint A.left)) ≤
        p ^ abelianVarietyDimension A := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero Fact.out)
  let : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
    surjective_zpow_id_of_ne_zero A hcube p hp
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  dsimp only
  intro hzero
  apply finSepDegree_genericResidueFieldEnd_le_of_zero_differential A p _ hzero
  simpa only [Int.natAbs_natCast] using finrank_genericResidueFieldEnd_zpow_id A hcube p hp


private theorem enatCard_le_of_surjective {α β : Type u} {f : α → β}
    (hf : Function.Surjective f) : ENat.card β ≤ ENat.card α :=
  Cardinal.toENat.monotone' (Cardinal.mk_le_of_surjective hf)

private theorem enatCard_connectedComponents_eq (X : Type u) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : ENat.card (_root_.ConnectedComponents X) = ENat.card X := by
  apply ENat.card_congr
  exact (Equiv.ofBijective (ConnectedComponents.mk : X → ConnectedComponents X)
    ⟨fun x y h => by simpa using ConnectedComponents.coe_eq_coe'.mp h,
      ConnectedComponents.surjective_coe⟩).symm

private theorem enatCard_fiber_le_numGeometricConnectedComponents
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y) :
    ENat.card (f.fiber y) ≤ AlgebraicGeometry.numGeometricConnectedComponents f y := by
  let K := SeparableClosure (Y.residueField y)
  let g : Spec (.of K) ⟶ Spec (Y.residueField y) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  have : Surjective g := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have : IsFinite (f.fiberToSpecResidueField y) := by
    exact inferInstanceAs (IsFinite (pullback.snd f (Y.fromSpecResidueField y)))
  have : IsLocallyArtinian (pullback (f.fiberToSpecResidueField y) g) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd (f.fiberToSpecResidueField y) g)
  change ENat.card (f.fiber y) ≤
    ENat.card (_root_.ConnectedComponents (pullback (f.fiberToSpecResidueField y) g : Scheme.{u}))
  rw [enatCard_connectedComponents_eq]
  exact enatCard_le_of_surjective (pullback.fst (f.fiberToSpecResidueField y) g).surjective

open TopologicalSpace in
private theorem lowerSemicontinuous_le_genericPoint
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X] [QuasiSober X]
    {β : Type v} [LinearOrder β] {f : X → β}
    (hf : LowerSemicontinuous f) (x : X) : f x ≤ f (genericPoint X) := by
  by_contra h
  have hx : x ∈ f ⁻¹' Set.Ioi (f (genericPoint X)) := lt_of_not_ge h
  have hgen := ((genericPoint_spec X).mem_open_set_iff
    (hf.isOpen_preimage (f (genericPoint X)))).mpr ⟨x, trivial, hx⟩
  exact (lt_irrefl (f (genericPoint X))) hgen

private theorem enatCard_fiber_le_numGeometricConnectedComponents_genericPoint
    {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (y : Y) :
    ENat.card (f.fiber y) ≤
      AlgebraicGeometry.numGeometricConnectedComponents f (genericPoint Y) :=
  (enatCard_fiber_le_numGeometricConnectedComponents f y).trans
    (lowerSemicontinuous_le_genericPoint
      (AlgebraicGeometry.lowerSemicontinuous_numGeometricConnectedComponents f) y)


private theorem enatCard_pullback_le_numGeometricConnectedComponents_genericPoint
    {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    {k : Type u} [Field k] (g : Spec (.of k) ⟶ Y) :
    ENat.card (pullback f g : Scheme.{u}) ≤
      AlgebraicGeometry.numGeometricConnectedComponents f (genericPoint Y) := by
  let r := pullback.snd f g
  let y := IsLocalRing.closedPoint k
  let e : {x : (pullback f g : Scheme.{u}) // r x = y} ≃
      (pullback f g : Scheme.{u}) := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, Subsingleton.elim _ _⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have he : ENat.card (pullback f g : Scheme.{u}) = ENat.card (r.fiber y) :=
    ENat.card_congr ((r.fiberHomeo y).toEquiv.trans e).symm
  have hbase := congrFun
    (AlgebraicGeometry.numGeometricConnectedComponents_eq_of_isPullback
      f r (pullback.fst f g) g (IsPullback.of_hasPullback f g)) y
  rw [he]
  apply (enatCard_fiber_le_numGeometricConnectedComponents r y).trans
  rw [hbase]
  exact lowerSemicontinuous_le_genericPoint
    (AlgebraicGeometry.lowerSemicontinuous_numGeometricConnectedComponents f) (g y)

private noncomputable def pullbackPointEquiv
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    {a : Y ⟶ pullback f g // a ≫ pullback.snd f g = 𝟙 Y} ≃
      {a : Y ⟶ X // a ≫ f = g} where
  toFun a := ⟨a.1 ≫ pullback.fst f g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, a.2, Category.id_comp]⟩
  invFun a := ⟨pullback.lift a.1 (𝟙 Y) (by simpa using a.2), pullback.lift_snd _ _ _⟩
  left_inv a := by
    apply Subtype.ext
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, a.2]
  right_inv a := by apply Subtype.ext; exact pullback.lift_fst _ _ _

private noncomputable def specPointEquivAlgHom
    (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] :
    {a : Spec (.of M) ⟶ Spec (.of L) //
      a ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K M))} ≃ (L →ₐ[K] M) where
  toFun a := {
    (Spec.homEquiv a.1).hom with
    commutes' := by
      intro r
      have h : CommRingCat.ofHom (algebraMap K L) ≫ Spec.homEquiv a.1 =
          CommRingCat.ofHom (algebraMap K M) := by
        apply Spec.map_injective
        simpa using a.2
      exact congrArg (fun b : CommRingCat.of K ⟶ CommRingCat.of M => b r) h }
  invFun a := ⟨Spec.map (CommRingCat.ofHom a.toRingHom), by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact a.commutes r⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by
    ext r
    change (Spec.preimage (Spec.map (CommRingCat.ofHom a.toRingHom))).hom r = a r
    rw [Spec.preimage_map]
    rfl

private theorem enatCard_pullback_spec_eq_finSepDegree
    (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Module.Finite K L] [IsAlgClosed M] :
    ENat.card (pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K M))) : Scheme.{u}) =
        (Field.finSepDegree K L : ℕ∞) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K M))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr (by
    change (algebraMap K L).Finite
    exact (RingHom.finite_algebraMap).mpr inferInstance)
  let B := Over.mk (pullback.snd f g)
  have : IsFinite B.hom := inferInstanceAs (IsFinite (pullback.snd f g))
  let e₀ : (MonoidalCategory.tensorUnit (Over (Spec (.of M))) ⟶ B) ≃
      {a : Spec (.of M) ⟶ pullback f g // a ≫ pullback.snd f g = 𝟙 _} := {
    toFun a := ⟨a.left, a.w⟩
    invFun a := Over.homMk a.1 a.2
    left_inv a := by ext; rfl
    right_inv a := rfl }
  let e := (pointEquivOfIsFinite B).symm.trans
    (e₀.trans ((pullbackPointEquiv f g).trans (specPointEquivAlgHom K L M)))
  change ENat.card B.left = _
  rw [ENat.card_congr e, ENat.card_eq_coe_natCard,
    ← Field.finSepDegree_eq_of_isAlgClosed K L M]

/-- If the fibre of `f` through `x` is `{x}`, the map from `Spec κ(x)` to the fibre is
surjective. -/
private theorem surjective_asFiberHom_of_fiber_eq_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (hx : f ⁻¹' {f x} = {x}) :
    Surjective (f.asFiberHom x) := by
  constructor
  intro z
  refine ⟨(show Spec (X.residueField x) from IsLocalRing.closedPoint (X.residueField x)), ?_⟩
  apply (f.fiberι _).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, f.asFiberHom_fiberι, Scheme.fromSpecResidueField_apply]
  have hz : f.fiberι _ z ∈ f ⁻¹' {f x} := (f.fiberHomeo (f x) z).property
  rw [hx] at hz
  exact hz.symm

private theorem numGeometricConnectedComponents_le_finSepDegree
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hx : f ⁻¹' {f x} = {x})
    (hfin : (f.residueFieldMap x).hom.Finite) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    AlgebraicGeometry.numGeometricConnectedComponents f (f x) ≤
      (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℕ∞) := by
  let K := Y.residueField (f x)
  let L := X.residueField x
  let : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite K L := hfin
  let M := AlgebraicClosure K
  let q := Spec.map (f.residueFieldMap x)
  let g := Spec.map (CommRingCat.ofHom (algebraMap K M))
  let r := f.fiberToSpecResidueField (f x)
  have : IsFinite q := (IsFinite.SpecMap_iff _).mpr hfin
  have : IsFinite r :=
    inferInstanceAs (IsFinite (pullback.snd f (Y.fromSpecResidueField (f x))))
  have := surjective_asFiberHom_of_fiber_eq_singleton f x hx
  let t := pullback.map q g r g (f.asFiberHom x) (𝟙 _) (𝟙 _)
    (by simp [q, r])
    (by simp)
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : Surjective t := MorphismProperty.pullbackMap
    (P := @AlgebraicGeometry.Surjective.{u}) ‹Surjective (f.asFiberHom x)›
    (inferInstance : Surjective (𝟙 _))
    (f.asFiberHom_fiberToSpecResidueField x).symm (by simp)
  have : IsLocallyArtinian (pullback r g) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd r g)
  rw [← AlgebraicGeometry.enatCard_connectedComponents_fiberBaseChange f (f x) M]
  change ENat.card (_root_.ConnectedComponents (pullback r g : Scheme.{u})) ≤ _
  rw [enatCard_connectedComponents_eq]
  exact (enatCard_le_of_surjective t.surjective).trans_eq
    (enatCard_pullback_spec_eq_finSepDegree K L M)

private noncomputable def algHomEquivOfBaseRingEquiv
    {F E K M : Type*} [Field F] [Field E] [Field K] [Field M]
    [Algebra F K] [Algebra E K] [Algebra F M] [Algebra E M]
    (e : F ≃+* E)
    (hK : ∀ a, algebraMap F K a = algebraMap E K (e a))
    (hM : ∀ a, algebraMap F M a = algebraMap E M (e a)) :
    (K →ₐ[F] M) ≃ (K →ₐ[E] M) where
  toFun f := {
    f.toRingHom with
    commutes' := by
      intro a
      obtain ⟨b, rfl⟩ := e.surjective a
      change f (algebraMap E K (e b)) = _
      rw [← hK, f.commutes, hM] }
  invFun f := {
    f.toRingHom with
    commutes' := by
      intro a
      change f (algebraMap F K a) = _
      rw [hK, f.commutes, ← hM] }
  left_inv _ := rfl
  right_inv _ := rfl

private theorem finSepDegree_eq_of_baseRingEquiv
    {F E K : Type u} [Field F] [Field E] [Field K]
    [Algebra F K] [Algebra E K] [Module.Finite F K] [Module.Finite E K]
    (e : F ≃+* E) (hK : ∀ a, algebraMap F K a = algebraMap E K (e a)) :
    Field.finSepDegree F K = Field.finSepDegree E K := by
  let M := AlgebraicClosure E
  let : Algebra F M := ((algebraMap E M).comp e.toRingHom).toAlgebra
  rw [Field.finSepDegree_eq_of_isAlgClosed F K M,
    Field.finSepDegree_eq_of_isAlgClosed E K M]
  exact Nat.card_congr (algHomEquivOfBaseRingEquiv e hK (fun _ => rfl))

private theorem finSepDegree_genericResidueFieldEnd_eq
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IrreducibleSpace A.left]
    (f : A ⟶ A) [IsDominant f.left]
    (hfin : (f.left.residueFieldMap (genericPoint A.left)).hom.Finite) :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    letI := (f.left.residueFieldMap (genericPoint A.left)).hom.toAlgebra
    Field.finSepDegree (genericResidueFieldEnd A f).fieldRange
      (A.left.residueField (genericPoint A.left)) =
        Field.finSepDegree (A.left.residueField (f.left (genericPoint A.left)))
          (A.left.residueField (genericPoint A.left)) := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  let φ := genericResidueFieldEnd A f
  let h := map_genericPoint_of_isDominant f.left
  let e₀ := A.left.residueFieldCongr h
  let e₁ : A.left.residueField (f.left (genericPoint A.left)) ≃+*
      A.left.residueField (genericPoint A.left) :=
    RingEquiv.ofBijective e₀.hom.hom (ConcreteCategory.bijective_of_isIso e₀.hom)
  let e := e₁.trans φ.equivFieldRange.toRingEquiv
  let := (f.left.residueFieldMap (genericPoint A.left)).hom.toAlgebra
  have : Module.Finite (A.left.residueField (f.left (genericPoint A.left)))
      (A.left.residueField (genericPoint A.left)) := hfin
  have he : ∀ a, algebraMap (A.left.residueField (f.left (genericPoint A.left)))
      (A.left.residueField (genericPoint A.left)) a =
        algebraMap φ.fieldRange (A.left.residueField (genericPoint A.left)) (e a) := by
    intro a
    exact (genericResidueFieldEnd_residueFieldCongr A f a).symm
  have : Module.Finite φ.fieldRange (A.left.residueField (genericPoint A.left)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [finrank_genericResidueFieldEnd_eq_residueDegree]
      exact Module.finrank_pos)
  exact (finSepDegree_eq_of_baseRingEquiv e he).symm

private theorem numGeometricConnectedComponents_genericPoint_le_finSepDegree
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [IsIntegral A.left]
    (f : A ⟶ A) [IsDominant f.left] [IsFinite f.left]
    (r : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f.left r] (hr : 0 < r) :
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    AlgebraicGeometry.numGeometricConnectedComponents f.left (genericPoint A.left) ≤
      (Field.finSepDegree (genericResidueFieldEnd A f).fieldRange
        (A.left.residueField (genericPoint A.left)) : ℕ∞) := by
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  have hfin : (f.left.residueFieldMap (genericPoint A.left)).hom.Finite := by
    let := (f.left.residueFieldMap (genericPoint A.left)).hom.toAlgebra
    apply FiniteDimensional.of_finrank_pos
    change 0 < f.left.residueDegree (genericPoint A.left)
    rw [residueDegree_genericPoint_eq_of_isFiniteLocallyFreeOfRank f.left r]
    exact hr
  have hb := numGeometricConnectedComponents_le_finSepDegree f.left
    (genericPoint A.left) (preimage_genericPoint_of_locallyQuasiFinite f.left) hfin
  let := (f.left.residueFieldMap (genericPoint A.left)).hom.toAlgebra
  dsimp only at hb
  rw [← finSepDegree_genericResidueFieldEnd_eq A f hfin] at hb
  simpa only [map_genericPoint_of_isDominant] using hb

private theorem numGeometricConnectedComponents_multiplication_by_char_le_of_zero_differential
    {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A)
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
      surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))
    letI : Algebra k (A.left.residueField (genericPoint A.left)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
        A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
    let φ := genericResidueFieldEnd A ((𝟙 A : A ⟶ A) ^ (p : ℤ))
    (∀ y, KaehlerDifferential.D k _ (φ y) = 0) →
      AlgebraicGeometry.numGeometricConnectedComponents
        (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) (genericPoint A.left) ≤
          ((p ^ abelianVarietyDimension A : ℕ) : ℕ∞) := by
  have hp : 0 < p := (Nat.Prime.pos Fact.out)
  let : Surjective (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) :=
    surjective_zpow_id_of_ne_zero A hcube p (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))
  let : Algebra k (A.left.residueField (genericPoint A.left)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
      A.left.Γevaluation (genericPoint A.left)).hom.toAlgebra
  dsimp only
  intro hzero
  have := multiplication_by_characteristic_isFiniteLocallyFreeOfRank A hcube p hp
  obtain ⟨hfin, hflat, hfp⟩ := isFinite_flat_of_isFiniteLocallyFreeOfRank
    (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) (p ^ (2 * abelianVarietyDimension A))
  apply (numGeometricConnectedComponents_genericPoint_le_finSepDegree A
    ((𝟙 A : A ⟶ A) ^ (p : ℤ))
    (p ^ (2 * abelianVarietyDimension A)) (Nat.pow_pos hp)).trans
  exact_mod_cast finSepDegree_multiplication_by_char_le_of_zero_differential A hcube p hzero

/-- **The fibre of multiplication by the characteristic over the identity of an abelian variety
has at most `p ^ dim A` distinct points**, granted the theorem of the cube for `A`. This is the
statement of [Stacks, Tag 0C0Y] with that one input. -/
theorem cardinalMk_fiber_multiplication_by_char_le_of_hasTheoremOfTheCube
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (p : ℕ) [CharP k p] (hp : 0 < p) :
    Cardinal.mk
      (pullback (η[A]).left (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) : Scheme.{u}) ≤
      p ^ abelianVarietyDimension A := by
  have := multiplication_by_characteristic_isFiniteLocallyFreeOfRank A hcube p hp
  obtain ⟨hfin, hflat, hfp⟩ := isFinite_flat_of_isFiniteLocallyFreeOfRank
    (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) (p ^ (2 * abelianVarietyDimension A))
  have hc := enatCard_pullback_le_numGeometricConnectedComponents_genericPoint
    (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) (η[A]).left
  have he := ENat.card_congr (Scheme.homeoOfIso
    (pullbackSymmetry (η[A]).left (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left))).toEquiv
  have hgeneric :
      AlgebraicGeometry.numGeometricConnectedComponents
        (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) (genericPoint A.left) ≤
          ((p ^ abelianVarietyDimension A : ℕ) : ℕ∞) := by
    have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp)⟩
    exact numGeometricConnectedComponents_multiplication_by_char_le_of_zero_differential A hcube p
      (genericResidueFieldEnd_zpow_differential_eq_zero A hcube p hp)
  have hbound := he.trans_le (hc.trans hgeneric)
  simpa only [Nat.cast_pow] using Cardinal.toENat_le_natCast.mp hbound

/-- Let `k` be a field of characteristic `p > 0` and `A` an abelian variety of dimension `g` over
`k`. The fibre of `[p] : A → A` over the identity has at most `p ^ g` distinct points. The fibre is
the pullback of `[p]` along the identity section, and its points are counted by the cardinality of
its underlying space. -/
@[stacks 0C0Y]
theorem cardinalMk_fiber_multiplication_by_char_le {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] (p : ℕ)
    [CharP k p] (hp : 0 < p) :
    Cardinal.mk
      (pullback (η[A]).left (((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) : Scheme.{u}) ≤
      p ^ abelianVarietyDimension A :=
  cardinalMk_fiber_multiplication_by_char_le_of_hasTheoremOfTheCube A (hasTheoremOfTheCube k A)
    p hp

end Stacks.Groupoids

end
