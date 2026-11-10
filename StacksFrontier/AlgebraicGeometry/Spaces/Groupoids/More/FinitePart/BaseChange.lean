module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness

/-!
# Base change of a finite open subspace

A pair `(a, Z)` of Stacks 04PC over a scheme `T` restricts along a morphism `h : T' ⟶ T` of
schemes of the site: the new morphism to the target is `h ≫ a`, and the new open subspace is
the preimage of `Z` under the canonical morphism `T' ×_Y X ⟶ T ×_Y X`. Both the open-subspace
condition and the finiteness of the projection are preserved, because that canonical morphism
is cartesian over `h` and the preimage of a subfunctor is cartesian over the subfunctor.

This operation is functorial, which is what makes the finite part of a morphism a presheaf.

## Main definitions

* `AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange`: the relation saying that one pair
  is obtained from another by base change along a given morphism.
* `AlgebraicGeometry.Space.baseChangeAmbientMap`: the canonical morphism of ambient fibre
  products induced by a morphism of the bases.
* `AlgebraicGeometry.Space.restrictFinitePair`: the base change of a pair of Stacks 04PC.

## Main results

* `AlgebraicGeometry.Space.isPullback_baseChangeAmbientMap`: the canonical morphism of ambient
  fibre products is cartesian over the morphism of the bases.
* `AlgebraicGeometry.Space.restrictFinitePair_isBaseChange`: the restricted pair is a base
  change of the original one.
* `AlgebraicGeometry.Space.restrictFinitePair_id` and
  `AlgebraicGeometry.Space.restrictFinitePair_comp`: restriction is functorial.

## Implementation notes

The relation `FiniteOpenSubspace.IsBaseChange` records the equality of the morphisms to the
target together with a morphism between the two open subspaces which makes a cartesian square
over the morphism of the bases and commutes with the two morphisms to `X`. It is a property of
the two pairs, not extra data: the comparison morphism is determined by its two composites
because the inclusion of an open subspace is a monomorphism.

Functoriality is an equality of structures whose second component is a subfunctor of a
pullback, and the two pullbacks are equal rather than merely isomorphic — the two morphisms to
the target are equal, not just isomorphic. The transport of the subfunctor along that equality
is therefore an `eqToHom`, handled by `pullback_congrHom_hom_eqToHom`, after which the two
subfunctors are literally the same.

The name `IsBaseChange` is nested inside `FiniteOpenSubspace` because the mathematics is a
relation between two such pairs, and because the root `IsBaseChange` is Mathlib's
base-change property of a module map.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FiniteOpenSubspace

/-- The pair `q` over `T'` is obtained from the pair `p` over `T` by base change along
`h : T' ⟶ T`: the morphisms to the target agree after composing with `h`, and the open
subspace of `q` is cartesian over that of `p` along `h`, compatibly with the two morphisms
to `X`. -/
def IsBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f (schemeSpace T))
    (q : FiniteOpenSubspace B S hS f (schemeSpace T')) : Prop :=
  (q.toBase.hom = yoneda.map h ≫ p.toBase.hom) ∧
    ∃ j : q.subspace.toFunctor ⟶ p.subspace.toFunctor,
      (IsPullback
        (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom)
        j (yoneda.map h)
        (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom)) ∧
      (j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
        q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)

end FiniteOpenSubspace

/-- The canonical morphism from the ambient fibre product after changing the base from `T` to
`T'` to the original ambient fibre product: `h` on the base component and the identity on
the `X` component. -/
noncomputable def baseChangeAmbientMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} {T T' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) :
    pullback (h ≫ a).hom f.hom ⟶ pullback a.hom f.hom :=
  pullback.map (h ≫ a).hom f.hom a.hom f.hom h.hom (𝟙 _) (𝟙 _) (by simp) (by simp)

private lemma baseChangeAmbientMap_fst (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} {T T' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) :
    baseChangeAmbientMap B S hS f a h ≫ pullback.fst a.hom f.hom =
      pullback.fst (h ≫ a).hom f.hom ≫ h.hom := by
  dsimp [baseChangeAmbientMap]
  rw [pullback.lift_fst]

private lemma baseChangeAmbientMap_snd (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} {T T' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) :
    baseChangeAmbientMap B S hS f a h ≫ pullback.snd a.hom f.hom =
      pullback.snd (h ≫ a).hom f.hom := by
  dsimp [baseChangeAmbientMap]
  rw [pullback.lift_snd, Category.comp_id]

/-- The canonical morphism of ambient fibre products is cartesian over the morphism of the
bases: changing the base of `T ×_Y X` from `T` to `T'` is the same as taking its fibre product
with `T'` over `T`. -/
theorem isPullback_baseChangeAmbientMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} {T T' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) :
    IsPullback (baseChangeAmbientMap B S hS f a h)
      (pullback.fst (h ≫ a).hom f.hom) (pullback.fst a.hom f.hom) h.hom := by
  refine IsPullback.of_right ?_ (baseChangeAmbientMap_fst B S hS f a h)
    (IsPullback.of_hasPullback a.hom f.hom).flip
  rw [baseChangeAmbientMap_snd]
  exact (IsPullback.of_hasPullback (h ≫ a).hom f.hom).flip

/-- Two fibre products over the same morphism with equal first legs are equal. -/
private lemma pullback_eq_of_left_eq {C : Type*} [Category C] {X Y Z : C} {f f' : X ⟶ Z}
    {g : Y ⟶ Z} [HasPullback f g] [HasPullback f' g] (h : f = f') :
    pullback f g = pullback f' g := by
  cases h
  rfl

/-- The comparison isomorphism of two fibre products with equal first legs is the transport
along the equality of the two fibre products. -/
private lemma pullback_congrHom_hom_eqToHom {C : Type*} [Category C] {X Y Z : C}
    {f f' : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [HasPullback f' g] (h : f = f') :
    (pullback.congrHom h (rfl : g = g)).hom = eqToHom (pullback_eq_of_left_eq h) := by
  cases h
  simp [pullback.congrHom, pullback.map]

/-- Precomposing with a transport along an equality of presheaves does not change the preimage
of a subfunctor, up to that equality. -/
private lemma preimage_eqToHom_comp_heq {D : Type*} [Category D] {F G H : D ⥤ Type u}
    (e : F = G) (f : G ⟶ H) (Z : Subfunctor H) :
    HEq (Z.preimage (eqToHom e ≫ f)) (Z.preimage f) := by
  cases e
  simp

/-- The canonical morphisms of ambient fibre products compose along a composite of base
morphisms, up to the comparison of the two fibre products over `k ≫ h ≫ a` and `m ≫ a`. -/
private theorem congrHom_hom_comp_baseChangeAmbientMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} {T T' T'' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) (k : T'' ⟶ T') (m : T'' ⟶ T) (hm : m = k ≫ h)
    (he : (k ≫ h ≫ a).hom = (m ≫ a).hom) :
    (pullback.congrHom he (rfl : f.hom = f.hom)).hom ≫ baseChangeAmbientMap B S hS f a m =
      baseChangeAmbientMap B S hS f (h ≫ a) k ≫ baseChangeAmbientMap B S hS f a h := by
  subst hm
  apply pullback.hom_ext <;> simp [baseChangeAmbientMap, pullback.congrHom]

/-- The canonical morphism of ambient fibre products along an identity is the comparison of the
two fibre products. -/
private theorem baseChangeAmbientMap_eq_congrHom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} {T : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (a : T ⟶ Y) (h : T ⟶ T) (hh : h = 𝟙 T) (he : (h ≫ a).hom = a.hom) :
    baseChangeAmbientMap B S hS f a h = (pullback.congrHom he (rfl : f.hom = f.hom)).hom := by
  subst hh
  apply pullback.hom_ext <;> simp [baseChangeAmbientMap, pullback.congrHom]

/-- The base change of a pair of Stacks 04PC along `h : T' ⟶ T`: its open subspace is the
preimage of the given one under the canonical morphism of ambient fibre products, which is
simultaneously the base change of the open subspace and of its finite projection. -/
noncomputable def restrictFinitePair (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f (schemeSpace T)) :
    FiniteOpenSubspace B S hS f (schemeSpace T') := by
  let qbase := schemeSpaceMap h ≫ p.toBase
  let κ := baseChangeAmbientMap B S hS f p.toBase (schemeSpaceMap h)
  let Z := p.subspace.preimage κ
  have hOld : IsAlgebraicSpace B S hS (pullback p.toBase.hom f.hom) :=
    isAlgebraicSpace_pullback B S hS p.toBase.hom f.hom
      (schemeSpace T).property X.property Y.property
  have hNew : IsAlgebraicSpace B S hS (pullback qbase.hom f.hom) :=
    isAlgebraicSpace_pullback B S hS qbase.hom f.hom
      (schemeSpace T').property X.property Y.property
  have hZ := isOpenSubspace_preimage B S hS κ p.subspace hOld hNew p.isOpen
  exact ⟨qbase, Z, hZ, isFinite_of_isPullback B S hS
    ((Subfunctor.isPullback_preimage κ p.subspace).paste_vert
      (isPullback_baseChangeAmbientMap B S hS f p.toBase (schemeSpaceMap h)))
    p.finite_projection⟩

/-- The restricted pair really is a base change of the original one. -/
theorem restrictFinitePair_isBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f (schemeSpace T)) :
    FiniteOpenSubspace.IsBaseChange B S hS f h p (restrictFinitePair B S hS f h p) := by
  let qbase := schemeSpaceMap h ≫ p.toBase
  let κ := baseChangeAmbientMap B S hS f p.toBase (schemeSpaceMap h)
  dsimp [restrictFinitePair]
  change (qbase.hom = yoneda.map h ≫ p.toBase.hom) ∧ _
  refine ⟨rfl, p.subspace.fromPreimage κ, ?_, ?_⟩
  · simpa [qbase, κ, restrictFinitePair, schemeSpaceMap, schemeSpace] using
      ((Subfunctor.isPullback_preimage κ p.subspace).paste_vert
        (isPullback_baseChangeAmbientMap B S hS f p.toBase (schemeSpaceMap h))).flip
  · rw [← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc,
      baseChangeAmbientMap_snd]

/-- Restriction along the identity is the identity. -/
theorem restrictFinitePair_id (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : BigFppfOver B S hS}
    (p : FiniteOpenSubspace B S hS f (schemeSpace T)) :
    restrictFinitePair B S hS f (𝟙 T) p = p := by
  have hsm : schemeSpaceMap (𝟙 T) = 𝟙 (schemeSpace T) := by
    apply ObjectProperty.hom_ext _
    simp [schemeSpaceMap, schemeSpace]
  rcases p with ⟨toBase, subspace, isOpen, finite_projection⟩
  have hbase : schemeSpaceMap (𝟙 T) ≫ toBase = toBase := by simp [hsm]
  have hq : (schemeSpaceMap (𝟙 T)).hom ≫ toBase.hom = toBase.hom := congrArg (·.hom) hbase
  unfold restrictFinitePair
  rw [FiniteOpenSubspace.mk.injEq]
  refine ⟨hbase, ?_⟩
  have hpb := pullback_eq_of_left_eq (g := f.hom) hq
  have hκ : baseChangeAmbientMap B S hS f toBase (schemeSpaceMap (𝟙 T)) =
      eqToHom hpb := by
    rw [baseChangeAmbientMap_eq_congrHom B S hS f toBase _ hsm hq,
      pullback_congrHom_hom_eqToHom]
  apply heq_of_eq
  rw [hκ]
  cases hpb.symm
  apply Subfunctor.ext
  funext U
  ext x
  rfl

/-- Restriction is compatible with composition. -/
theorem restrictFinitePair_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T T' T'' : BigFppfOver B S hS}
    (h : T' ⟶ T) (k : T'' ⟶ T')
    (p : FiniteOpenSubspace B S hS f (schemeSpace T)) :
    restrictFinitePair B S hS f k (restrictFinitePair B S hS f h p) =
      restrictFinitePair B S hS f (k ≫ h) p := by
  have hsm : schemeSpaceMap (k ≫ h) = schemeSpaceMap k ≫ schemeSpaceMap h :=
    ObjectProperty.hom_ext _ (yoneda.map_comp k h)
  have hbase : schemeSpaceMap k ≫ (schemeSpaceMap h ≫ p.toBase) =
      schemeSpaceMap (k ≫ h) ≫ p.toBase := by
    rw [hsm, Category.assoc]
  unfold restrictFinitePair
  rw [FiniteOpenSubspace.mk.injEq]
  refine ⟨hbase, ?_⟩
  have hbaseHom := congrArg (fun t => t.hom) hbase
  have hpb := pullback_eq_of_left_eq
    (f := (schemeSpaceMap k ≫ (schemeSpaceMap h ≫ p.toBase)).hom)
    (f' := (schemeSpaceMap (k ≫ h) ≫ p.toBase).hom) (g := f.hom) hbaseHom
  dsimp only [restrictFinitePair]
  let κ₁ := baseChangeAmbientMap B S hS f p.toBase (schemeSpaceMap h)
  let κ₂ := baseChangeAmbientMap B S hS f (schemeSpaceMap h ≫ p.toBase)
    (schemeSpaceMap k)
  let κ₃ := baseChangeAmbientMap B S hS f p.toBase (schemeSpaceMap (k ≫ h))
  have hcomp : eqToHom hpb ≫ κ₃ = κ₂ ≫ κ₁ := by
    rw [← pullback_congrHom_hom_eqToHom hbaseHom]
    exact congrHom_hom_comp_baseChangeAmbientMap B S hS f _ _ _ _ hsm hbaseHom
  refine (heq_of_eq ?_).trans (preimage_eqToHom_comp_heq hpb κ₃ p.subspace)
  rw [hcomp, Subfunctor.preimage_comp]

end AlgebraicGeometry.Space

end
