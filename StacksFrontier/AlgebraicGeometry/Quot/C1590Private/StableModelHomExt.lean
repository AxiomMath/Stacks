module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# Morphisms between stable models are unique

The uniqueness half of "unique up to unique isomorphism" in Stacks 0E8A. The source omits the
verification, with the hint that "the scheme theoretic image of `c₁` is `Y₁`". Here is that
argument.

Let `c : A → D` be a morphism of algebraic spaces with `𝒪_D ≅ c_*𝒪_A`, and let `u, v : D → T` be
two morphisms to an algebraic space `T`, separated over some `U`, which agree over `U` and after
composing with `c`. The locus where `u` and `v` agree is the base change of the diagonal of `T`
over `U`, so it is a closed subspace `Z ⊆ D`. The morphism `c` factors through `Z`, so the ideal of
`Z` is killed by `c♯ : 𝒪_D → c_*𝒪_A`, which is injective; the ideal is zero, so `D` itself factors
through `Z` (Stacks 03MB), that is `u = v`.

## Main results

* `AlgebraicGeometry.C1590Private.eq_of_comp_eq_of_isIso_structureSharp`: the general statement
  above.
* `AlgebraicGeometry.C1590Private.IsStableModel.hom_ext`: two morphisms of families between stable
  models of the same family, compatible with the base maps and the contractions, are equal.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private


section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms agreeing after a morphism with `𝒪_D ≅ c_*𝒪_A` agree.** Let `c : A ⟶ D` be a
morphism of algebraic spaces whose structure map `c♯ : 𝒪_D ⟶ c_*𝒪_A` is an isomorphism, and let
`u, v : D ⟶ T` be morphisms to an algebraic space separated over `U` by `t : T ⟶ U`. If
`u ≫ t = v ≫ t` and `c ≫ u = c ≫ v`, then `u = v`. -/
theorem eq_of_comp_eq_of_isIso_structureSharp {A D T U : AlgebraicSpaces B S hS} (c : A ⟶ D)
    (hc : IsIso (Space.structureSharp B S hS c)) {u v : D ⟶ T} (t : T ⟶ U)
    (ht : Space.IsSeparated B S hS t.hom) (hut : u ≫ t = v ≫ t) (hcu : c ≫ u = c ≫ v) : u = v := by
  let l : D.obj ⟶ pullback t.hom t.hom := pullback.lift u.hom v.hom (congrArg (·.hom) hut)
  let p : pullback l (pullback.diagonal t.hom) ⟶ D.obj := pullback.fst _ _
  have hp : Space.IsClosedImmersion B S hS p :=
    (Space.isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback l (pullback.diagonal t.hom)).flip ht
  have hE : IsAlgebraicSpace B S hS (pullback l (pullback.diagonal t.hom)) :=
    isAlgebraicSpace_pullback B S hS l _ D.2 T.2
      (isAlgebraicSpace_pullback B S hS t.hom t.hom T.2 T.2 U.2)
  let Z : Space.ClosedSubspaces B S hS D.obj :=
    ⟨Subfunctor.range p, Space.isClosedSubspace_range_of_isClosedImmersion B S hS p hE hp⟩
  have hlf : l ≫ pullback.fst t.hom t.hom = u.hom := pullback.lift_fst _ _ _
  have hls : l ≫ pullback.snd t.hom t.hom = v.hom := pullback.lift_snd _ _ _
  -- the two morphisms agree on the closed subspace
  have hpuv : p ≫ u.hom = p ≫ v.hom := by
    rw [← hlf, ← hls, ← Category.assoc, ← Category.assoc,
      pullback.condition (f := l) (g := pullback.diagonal t.hom), Category.assoc, Category.assoc,
      pullback.diagonal_fst, pullback.diagonal_snd]
  -- the morphism `c` factors through the closed subspace
  have hcl : c.hom ≫ l = (c.hom ≫ u.hom) ≫ pullback.diagonal t.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, hlf]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, hls]
      exact (congrArg (·.hom) hcu).symm
  let c' : A.obj ⟶ pullback l (pullback.diagonal t.hom) := pullback.lift c.hom _ hcl
  let g : A ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk (c' ≫ Subfunctor.toRange p)
  have hg : g ≫ ObjectProperty.homMk Z.1.ι = c := by
    apply ObjectProperty.hom_ext
    change (c' ≫ Subfunctor.toRange p) ≫ (Subfunctor.range p).ι = c.hom
    rw [Category.assoc, Subfunctor.toRange_ι]
    exact pullback.lift_fst _ _ _
  -- its ideal is killed by `c♯`, hence zero, hence killed by `𝟙♯`
  have hle := Space.definingIdealSheaf_le_kernelIdealSheaf_of_comp_eq B S hS c Z g hg
  have hle' : Space.definingIdealSheaf B S hS D Z ≤ Space.kernelIdealSheaf B S hS (𝟙 D) := by
    intro U s hs
    let s' : ToType ((Space.structureRingSheaf B S hS D).obj.obj U) := s
    have hs' : s' ∈ RingHom.ker ((Space.structureSharp B S hS c).hom.app U).hom := hle U hs
    have h0 : s' = 0 :=
      (ConcreteCategory.bijective_of_isIso ((Space.structureSharp B S hS c).hom.app U)).1
        ((RingHom.mem_ker.mp hs').trans (map_zero _).symm)
    change s' ∈ RingHom.ker ((Space.structureSharp B S hS (𝟙 D)).hom.app U).hom
    rw [h0]
    exact (RingHom.ker ((Space.structureSharp B S hS (𝟙 D)).hom.app U).hom).zero_mem
  obtain ⟨g', hg'⟩ :=
    (Space.exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf B S hS D Z (𝟙 D)).2 hle'
  have hg'h : g'.hom ≫ (Subfunctor.range p).ι = 𝟙 D.obj := congrArg (·.hom) hg'
  have hι : (Subfunctor.range p).ι ≫ u.hom = (Subfunctor.range p).ι ≫ v.hom := by
    rw [← cancel_epi (Subfunctor.toRange p), ← Category.assoc, Subfunctor.toRange_ι,
      ← Category.assoc, Subfunctor.toRange_ι, hpuv]
  apply ObjectProperty.hom_ext
  rw [← Category.id_comp u.hom, ← hg'h, Category.assoc, hι, ← Category.assoc, hg'h,
    Category.id_comp]

end General

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The structure map `𝒪_Y ⟶ c_*𝒪_X` of a stable model is an isomorphism: condition (1) of
Stacks 0E8A at the identity of the base. -/
theorem IsStableModel.isIso_structureSharp {g : ℕ} {X Y : CurveFamily B hZ}
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (h : IsStableModel B hZ g b c) :
    IsIso (Space.structureSharp B integerBase hZ c) := by
  have h1 : schemeSpaceMap (𝟙 Y.base) = 𝟙 _ := (schemeSpaceFunctor B integerBase hZ).map_id _
  refine (h.universallyAcyclic (𝟙 Y.base) c (𝟙 _) (𝟙 _) Y.toBase ?_ ?_
    (by rw [Category.comp_id, Category.id_comp])).1 <;>
  · rw [h1]
    exact IsPullback.id_horiz _

/-- **Morphisms between stable models are unique** (the uniqueness in Stacks 0E8A). Two
morphisms of families `e, e' : Y₁ ⟶ Y₂` between stable models `c₁ : X ⟶ Y₁` and `c₂ : X ⟶ Y₂` of
the same family, both compatible with the base maps and with the contractions, are equal. -/
theorem IsStableModel.hom_ext {g : ℕ} {X Y₁ Y₂ : CurveFamily B hZ} {b₁ : X.base ⟶ Y₁.base}
    {c₁ : X.total ⟶ Y₁.total} {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total}
    (h₁ : IsStableModel B hZ g b₁ c₁) (_h₂ : IsStableModel B hZ g b₂ c₂) {e e' : Y₁ ⟶ Y₂}
    (he : b₁ ≫ e.baseMap = b₂) (hc : c₁ ≫ e.totalMap = c₂) (he' : b₁ ≫ e'.baseMap = b₂)
    (hc' : c₁ ≫ e'.totalMap = c₂) : e = e' := by
  have := h₁.isIso_base
  have hb : e.baseMap = e'.baseMap := (cancel_epi b₁).1 (he.trans he'.symm)
  exact CurveFamily.Hom.ext hb (eq_of_comp_eq_of_isIso_structureSharp c₁
    h₁.isIso_structureSharp Y₂.toBase Y₂.proper.1 (by rw [e.cartesian.w, e'.cartesian.w, hb])
    (hc.trans hc'.symm))

end AlgebraicGeometry.C1590Private

end
