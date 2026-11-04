module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.CountableOpens
public import StacksCore.Tactic.StacksAttribute

/-!
# Countability of morphisms between schemes of finite type

Over a countable Noetherian ring there are only countably many morphisms over the base between
any two schemes of finite type. A morphism is reconstructed from its restrictions to a finite
affine cover of the source, and each such restriction is coded by an open of the chart together
with a morphism of open subschemes of affine schemes of finite type, of which there are countably
many.

## Main results

* `AlgebraicGeometry.countable_hom_of_finiteType`: the morphisms over the base between two
  schemes of finite type form a countable type.

## Implementation notes

Schemes over the base are represented as objects of the over category. Following Mathlib's
convention, finite type is expressed by the conjunction of the
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` typeclass
assumptions on each structure morphism.

## References

* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The restriction of a morphism over the base to the preimage of an open immersion `b` into the
target, along a morphism `a` into the source, as a morphism over the base into the source of
`b`. -/
noncomputable def chartRestriction {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {V W : Scheme.{u}} (a : V ⟶ X.left) (b : W ⟶ Y.left) [IsOpenImmersion b] :
    Σ U : V.Opens, (Over.mk (U.ι ≫ a ≫ X.hom) : Over S) ⟶ Over.mk (b ≫ Y.hom) :=
  ⟨(a ≫ f.left) ⁻¹ᵁ b.opensRange,
    Over.homMk (IsOpenImmersion.lift b (((a ≫ f.left) ⁻¹ᵁ b.opensRange).ι ≫ a ≫ f.left) (by
      rintro z ⟨x, rfl⟩
      exact x.property)) (by
      simp only [Over.mk_hom]
      rw [← Category.assoc (IsOpenImmersion.lift _ _ _), IsOpenImmersion.lift_fac]
      simp only [Category.assoc, f.w])⟩

/-- The morphism `(chartRestriction f a b).2` followed by `b` is the inclusion of the open
`(chartRestriction f a b).1` followed by `a ≫ f.left`. -/
private theorem chartRestriction_fac {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {V W : Scheme.{u}} (a : V ⟶ X.left) (b : W ⟶ Y.left) [IsOpenImmersion b] :
    (chartRestriction f a b).2.left ≫ b = (chartRestriction f a b).1.ι ≫ a ≫ f.left :=
  IsOpenImmersion.lift_fac b _ _

/-- A point `x` lies in the open `(chartRestriction f a b).1` if and only if its image under
`a ≫ f.left` lies in the range of `b`. -/
private theorem mem_chartRestriction_fst {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {V W : Scheme.{u}} (a : V ⟶ X.left) (b : W ⟶ Y.left) [IsOpenImmersion b] {x : V} :
    x ∈ (chartRestriction f a b).1 ↔ (a ≫ f.left) x ∈ b.opensRange :=
  Iff.rfl

/-- Given two affine schemes of finite type over a countable Noetherian ring, the morphisms over
the base from open subschemes of the first to the second, indexed by the open, form a countable
type. -/
private theorem countable_sigma_open_hom_of_affine_finiteType
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (S T : Over (Spec (.of R))) [IsAffine S.left] [IsAffine T.left]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    Countable (Σ U : S.left.Opens, (Over.mk (U.ι ≫ S.hom) : Over (Spec (.of R))) ⟶ T) := by
  have := countable_opens_of_affine_finiteType S
  have (U : S.left.Opens) : Countable ((Over.mk (U.ι ≫ S.hom) : Over (Spec (.of R))) ⟶ T) := by
    have := countable_open_hom_of_affine_finiteType S T U ⊤
    exact Countable.of_equiv _
      ((Iso.refl _).homCongr
        (Over.isoMk (f := Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom)) (Scheme.topIso T.left)))
  infer_instance

/-- Countability of the morphisms over the base, proved on a pair of finite affine covers: a
morphism is coded by, for each pair of charts, the open on which it is defined there together with
the induced morphism of open subschemes. -/
private theorem countable_hom_of_finiteType_aux
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X Y : Over (Spec (.of R)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Countable (X ⟶ Y) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let A := X.left.affineCover.finiteSubcover
  let B := Y.left.affineCover.finiteSubcover
  have (p : A.I₀ × B.I₀) : Countable (Σ U : (A.X p.1).Opens,
      (Over.mk (U.ι ≫ A.f p.1 ≫ X.hom) : Over (Spec (.of R))) ⟶ Over.mk (B.f p.2 ≫ Y.hom)) := by
    let S : Over (Spec (.of R)) := Over.mk (A.f p.1 ≫ X.hom)
    let T : Over (Spec (.of R)) := Over.mk (B.f p.2 ≫ Y.hom)
    have : LocallyOfFiniteType S.hom := by
      dsimp [S]
      infer_instance
    have : QuasiCompact S.hom := by
      dsimp [S]
      infer_instance
    have : LocallyOfFiniteType T.hom := by
      dsimp [T]
      infer_instance
    have : QuasiCompact T.hom := by
      dsimp [T]
      infer_instance
    have : IsAffine S.left := by
      dsimp [S, A]
      infer_instance
    have : IsAffine T.left := by
      dsimp [T, B]
      infer_instance
    exact countable_sigma_open_hom_of_affine_finiteType S T
  refine Function.Injective.countable
    (f := fun f : X ⟶ Y => fun p : A.I₀ × B.I₀ => chartRestriction f (A.f p.1) (B.f p.2))
    fun f g hfg => Over.OverMorphism.ext (A.hom_ext _ _ fun i => ?_)
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨j, y, hy⟩ := B.exists_eq ((A.f i ≫ f.left) x)
  have hp : chartRestriction f (A.f i) (B.f j) = chartRestriction g (A.f i) (B.f j) :=
    congrFun hfg (i, j)
  have hx : x ∈ (chartRestriction f (A.f i) (B.f j)).1 := by
    rw [mem_chartRestriction_fst, ← hy]
    exact ⟨y, rfl⟩
  refine ⟨_, hx, ?_⟩
  have hf := chartRestriction_fac f (A.f i) (B.f j)
  rw [hp] at hf ⊢
  simpa only [Category.assoc] using hf.symm.trans (chartRestriction_fac g (A.f i) (B.f j))

/-- Over a countable Noetherian ring, the morphisms over the base between two schemes of finite
type form a countable type. -/
@[stacks 0G0U "countable_hom"]
public theorem countable_hom_of_finiteType
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X Y : Over (Spec (.of R)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Countable (X ⟶ Y) := countable_hom_of_finiteType_aux X Y

end AlgebraicGeometry
