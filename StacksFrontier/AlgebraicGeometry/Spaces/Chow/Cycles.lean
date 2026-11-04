module

public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IntegralClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# Cycles on a good algebraic space

In the situation of Stacks 0EDT, let `X/B` be good. A *cycle* on `X` is a formal sum
`α = ∑ n_Z [Z]` over the integral closed subspaces `Z ⊆ X`, with integer coefficients, subject
to the condition that the point sets of the subspaces occurring with a nonzero coefficient form
a locally finite collection of subsets of `|X|`. A cycle is a *`k`-cycle* when every subspace
occurring with a nonzero coefficient has δ-dimension `k`, and the `k`-cycles form an abelian
group `Z_k(X)` under coefficientwise addition.

The δ-dimension of an integral closed subspace `Z ⊆ X` is the value of `δ_{X/B}` at the generic
point of `|Z|`. It is read off inside `Z` itself: an integral algebraic space is irreducible and
decent, hence its point space is irreducible and quasi-sober, so it has a generic point with no
hypothesis on the ambient space, and the inclusion carries that point to a generic point of
`|Z|`.

## Main definitions

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.deltaValue`: the dimension function
  `δ_{X/B}` induced on a good algebraic space by the dimension function of the base.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.genericPoint`: the generic point of an
  integral closed subspace, as a point of that subspace.
* `AlgebraicGeometry.Space.deltaDimension`: **Stacks 0EDX**, the δ-dimension of an integral
  closed subspace of a good algebraic space.
* `AlgebraicGeometry.Space.cyclesOfDimension`, `AlgebraicGeometry.Space.CycleGroup`:
  **Stacks 0EDZ**, the group `Z_k(X)` of `k`-cycles on a good algebraic space.

## Main results

* `AlgebraicGeometry.Space.isGenericPoint_pointsMap_genericPoint`: the inclusion carries the
  generic point of an integral closed subspace to a generic point of its point set.
* `AlgebraicGeometry.Space.deltaDimension_eq_of_isGenericPoint`: the δ-dimension may be
  evaluated at any generic point of the point set.
* `AlgebraicGeometry.Space.inducedDimensionValue_comp_of_isLocallyQuasiFinite`: the induced
  dimension function of Stacks 0EDN is unchanged along a locally quasi-finite morphism; in
  particular along an immersion.
* `AlgebraicGeometry.Space.mem_cyclesOfDimension_iff`: the membership criterion for `Z_k(X)`.

## Implementation notes

Cycles are indexed by the integral closed subspaces themselves,
`AlgebraicGeometry.Space.IntegralClosedSubspace` of Stacks 0ENF, rather than by their generic
points. This is the shape of Stacks 0EDZ, and it is the shape of the existing
`AlgebraicGeometry.Space.WeilDivisor` of Stacks 0ENJ, whose point set abbreviation
`AlgebraicGeometry.Space.subspacePointSet` and whose local-finiteness clause are reused here.
Indexing by points would need the bijection of Stacks 0ENF between points and integral closed
subspaces, which is available only for a decent algebraic space; the formulation below needs no
decency hypothesis on `X`.

Local finiteness is tested, as in the source, on the point sets of exactly the subspaces with
nonzero coefficient; `AlgebraicGeometry.Space.cyclesOfDimension` is an `AddSubgroup` of the
coefficient families, so `Z_k(X)` inherits the group structure with no further work.

The δ-dimension needs no goodness hypothesis: `AlgebraicGeometry.Space.inducedDimensionValue`
is defined for an arbitrary morphism and an arbitrary function on the points of its target.
Goodness enters only where the value of the induced function has to be *computed*, through
`AlgebraicGeometry.Space.inducedDimensionValue_eq`, which is how
`AlgebraicGeometry.Space.inducedDimensionValue_comp_of_isLocallyQuasiFinite` is proved: the
relative transcendence degree is finite for a morphism locally of finite type, and Stacks 06RX
identifies it before and after a locally quasi-finite morphism.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 06RX](https://stacks.math.columbia.edu/tag/06RX)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0BDS](https://stacks.math.columbia.edu/tag/0BDS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The induced dimension function along a locally quasi-finite morphism -/

/-- **Stacks 06RX for the induced dimension function.** The function induced on `X` by a
function `δ` on `Z` through a morphism `X ⟶ Z` which factors as a locally quasi-finite morphism
`f : X ⟶ Y` followed by a morphism `g : Y ⟶ Z` locally of finite type agrees at `x` with the
function induced on `Y` through `g`, evaluated at the image of `x`.

The base contributions agree because the two points have the same image in `Z`, and the two
relative transcendence degrees agree by Stacks 06RX. -/
theorem inducedDimensionValue_comp_of_isLocallyQuasiFinite (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (δ : points B S hS Z → ℤ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocallyQuasiFinite B S hS f) (hg : IsLocallyOfFiniteType B S hS g)
    (x : points B S hS X) :
    inducedDimensionValue B S hS δ (f ≫ g) x =
      inducedDimensionValue B S hS δ g (pointsMap B S hS X f x) := by
  have hflft : IsLocallyOfFiniteType B S hS f := fun U V a b h ha hb hsq =>
    (hf U V a b h ha hb hsq).1
  obtain ⟨n, hn⟩ := exists_finite_transcendenceDegreeAt B S hS g hg (pointsMap B S hS X f x)
  have hcomp : HasTranscendenceDegreeAt B S hS (f ≫ g) x (n : ℕ∞) :=
    (hasTranscendenceDegreeAt_comp_of_isLocallyQuasiFinite B S hS hX hY hZ f g hf hg x
      (n : ℕ∞)).mpr hn
  rw [inducedDimensionValue_eq B S hS hY hZ δ g hg _ (n : ℕ∞) hn,
    inducedDimensionValue_eq B S hS hX hZ δ (f ≫ g)
      (isLocallyOfFiniteType_comp B S hS hX hY hZ f g hflft hg) x (n : ℕ∞) hcomp,
    pointsMap_comp]
  rfl

/-! ### The dimension function of a good algebraic space -/

/-- **Stacks 0EDT.** The dimension function `δ_{X/B}` induced on an algebraic space `X` with
structure morphism `sX : X ⟶ B` by the dimension function of the base: at `x` it is the value of
`δ` at the image of `x` plus the transcendence degree of `x` over that image. -/
noncomputable abbrev BaseSpaceDimensionSituation.deltaValue
    (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (x : points D.site D.base D.base_mem X) : ℤ :=
  inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sX x

/-- The dimension function of a good algebraic space does not change when the structure
morphism is factored through a locally quasi-finite morphism; in particular an immersion of
good algebraic spaces over the base does not change it. -/
theorem BaseSpaceDimensionSituation.deltaValue_comp_of_isLocallyQuasiFinite
    (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y) (f : X ⟶ Y) (sY : Y ⟶ D.space)
    (hf : IsLocallyQuasiFinite D.site D.base D.base_mem f)
    (hsY : IsLocallyOfFiniteType D.site D.base D.base_mem sY)
    (x : points D.site D.base D.base_mem X) :
    D.deltaValue (f ≫ sY) x =
      D.deltaValue sY (pointsMap D.site D.base D.base_mem X f x) :=
  inducedDimensionValue_comp_of_isLocallyQuasiFinite D.site D.base D.base_mem hX hY
    D.isAlgebraicSpace D.delta.toFun f sY hf hsY x

/-! ### The generic point of an integral closed subspace -/

section GenericPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The point space of an integral closed subspace is quasi-sober: an integral algebraic space
is decent, and the point space of a decent algebraic space is quasi-sober. -/
theorem IntegralClosedSubspace.quasiSober_points (Z : IntegralClosedSubspace B S hS X) :
    QuasiSober (points B S hS Z.subspace.toFunctor) :=
  quasiSober_points_of_isDecentSpace B S hS Z.isClosedSubspace.1 Z.isIntegralSpace.2.1

/-- The point space of an integral closed subspace is irreducible, this being part of
integrality. -/
theorem IntegralClosedSubspace.irreducibleSpace_points
    (Z : IntegralClosedSubspace B S hS X) :
    IrreducibleSpace (points B S hS Z.subspace.toFunctor) :=
  Z.isIntegralSpace.2.2

/-- The point space of an integral closed subspace is Kolmogorov: an integral algebraic space
is decent, and the point space of a decent algebraic space is Kolmogorov by Stacks 03K3. -/
theorem IntegralClosedSubspace.t0Space_points (Z : IntegralClosedSubspace B S hS X) :
    T0Space (points B S hS Z.subspace.toFunctor) :=
  t0Space_points_of_isDecentSpace B S hS Z.isClosedSubspace.1 Z.isIntegralSpace.2.1

/-- The *generic point* of an integral closed subspace `Z`, as a point of `Z`: the point space
of `Z` is irreducible and quasi-sober, so it has a generic point. -/
noncomputable def IntegralClosedSubspace.genericPoint (Z : IntegralClosedSubspace B S hS X) :
    points B S hS Z.subspace.toFunctor :=
  letI := Z.quasiSober_points B S hS
  letI := Z.irreducibleSpace_points B S hS
  _root_.genericPoint (points B S hS Z.subspace.toFunctor)

/-- The point space of an integral closed subspace is the closure of its generic point. -/
theorem IntegralClosedSubspace.closure_singleton_genericPoint
    (Z : IntegralClosedSubspace B S hS X) :
    closure ({Z.genericPoint B S hS} : Set (points B S hS Z.subspace.toFunctor)) = Set.univ :=
  let := Z.quasiSober_points B S hS
  let := Z.irreducibleSpace_points B S hS
  genericPoint_spec (points B S hS Z.subspace.toFunctor)

/-- The inclusion of an integral closed subspace is a closed embedding on points: it is an
embedding by Stacks 0ABJ, a closed immersion being an immersion, and its image is closed by
Stacks 04CD. -/
theorem IntegralClosedSubspace.isClosedEmbedding_pointsMap
    (hX : IsAlgebraicSpace B S hS X) (Z : IntegralClosedSubspace B S hS X) :
    Topology.IsClosedEmbedding
      (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι) :=
  ⟨isEmbedding_pointsMap_of_isImmersion B S hS hX Z.subspace.ι
      (isImmersion_of_isClosedImmersion B S hS Z.isClosedSubspace.2),
    isClosed_range_pointsMap_integralClosedSubspace B S hS hX Z⟩

/-- The image under the inclusion of the closure of a point of an integral closed subspace is
the closure of its image. -/
private theorem image_closure_singleton_pointsMap
    (hX : IsAlgebraicSpace B S hS X) (Z : IntegralClosedSubspace B S hS X)
    (y : points B S hS Z.subspace.toFunctor) :
    (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι) '' closure {y} =
      closure {pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι y} := by
  rw [← (Z.isClosedEmbedding_pointsMap B S hS hX).closure_image_eq, Set.image_singleton]

/-- The inclusion of an integral closed subspace carries its generic point to a generic point
of its set of points: the inclusion is a closed embedding on points, so it commutes with
closures. -/
theorem isGenericPoint_pointsMap_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) :
    IsGenericPoint
      (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS))
      (subspacePointSet B S hS X Z.subspace) := by
  have h := image_closure_singleton_pointsMap B S hS hX Z (Z.genericPoint B S hS)
  rw [Z.closure_singleton_genericPoint B S hS, Set.image_univ] at h
  exact h.symm

/-- A generic point of the set of points of an integral closed subspace is the image of the
generic point of that subspace.

Such a point lies in the subspace, so it is the image of a point `y`; the closure of `y` is
everything because the inclusion is a closed embedding and injective, and the point space of
the subspace is Kolmogorov, so `y` is the generic point. -/
theorem eq_pointsMap_genericPoint_of_isGenericPoint (hX : IsAlgebraicSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) (ξ : points B S hS X)
    (hξ : IsGenericPoint ξ (subspacePointSet B S hS X Z.subspace)) :
    ξ = pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS) := by
  have hemb := Z.isClosedEmbedding_pointsMap B S hS hX
  have hmem : ξ ∈ subspacePointSet B S hS X Z.subspace := hξ ▸ subset_closure rfl
  obtain ⟨y, rfl⟩ := hmem
  have hy : IsGenericPoint y (Set.univ : Set (points B S hS Z.subspace.toFunctor)) :=
    hemb.injective.image_injective <| by
      rw [image_closure_singleton_pointsMap B S hS hX Z y, Set.image_univ]
      exact hξ
  have : T0Space (points B S hS Z.subspace.toFunctor) := Z.t0Space_points B S hS
  exact congrArg _ (hy.eq (Z.closure_singleton_genericPoint B S hS))

end GenericPoint

/-! ### The δ-dimension of an integral closed subspace -/

/-- **Stacks 0EDX, for an integral closed subspace.** The *δ-dimension* of an integral closed
subspace `Z` of a good algebraic space `X/B` is the value of `δ_{X/B}` at the generic point of
`|Z|`. -/
@[stacks 0EDX "the δ-dimension of an integral closed subspace"]
noncomputable def deltaDimension (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  D.deltaValue sX
    (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem))

/-- The δ-dimension of an integral closed subspace may be evaluated at any generic point of its
set of points. -/
theorem deltaDimension_eq_of_isGenericPoint (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (ξ : points D.site D.base D.base_mem X)
    (hξ : IsGenericPoint ξ
      (subspacePointSet D.site D.base D.base_mem X Z.subspace)) :
    deltaDimension D sX Z = D.deltaValue sX ξ :=
  congrArg (D.deltaValue sX)
    (eq_pointsMap_genericPoint_of_isGenericPoint D.site D.base D.base_mem hX Z ξ hξ).symm

/-! ### Cycles of a fixed δ-dimension -/

section Cycles

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A point lies in the set tested for local finiteness at an integral closed subspace exactly
when the coefficient there is nonzero and the point lies in that subspace. -/
private theorem mem_ite_subspacePointSet_iff
    {α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ}
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    {p : points D.site D.base D.base_mem X} :
    p ∈ (if α Z = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else subspacePointSet D.site D.base D.base_mem X Z.subspace) ↔
      α Z ≠ 0 ∧ p ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  by_cases h : α Z = 0 <;> simp [h]

/-- **Stacks 0EDZ, parts (1) and (2).** The subgroup `Z_k(X)` of integer coefficient families
on the integral closed subspaces of a good algebraic space `X/B` which are *cycles* — the point
sets of the subspaces with nonzero coefficient form a locally finite collection of subsets of
`|X|` — and are *of δ-dimension `k`* — every subspace with nonzero coefficient has δ-dimension
`k`. -/
@[stacks 0EDZ "parts (1) and (2): cycles and k-cycles", ega "IV 21.6.1" "fixed δ-dimension k"]
noncomputable def cyclesOfDimension (sX : X ⟶ D.space) (k : ℤ) :
    AddSubgroup (IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) where
  carrier := {α | (LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if α Z = 0 then ∅ else subspacePointSet D.site D.base D.base_mem X Z.subspace) ∧
    ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α Z ≠ 0 →
      deltaDimension D sX Z = k}
  zero_mem' := ⟨fun _ => ⟨Set.univ, Filter.univ_mem, by simp⟩, by simp⟩
  add_mem' := by
    rintro α β ⟨hαfin, hαdim⟩ ⟨hβfin, hβdim⟩
    refine ⟨fun x => ?_, fun Z hZ => ?_⟩
    · obtain ⟨V, hV, hVα⟩ := hαfin x
      obtain ⟨W, hW, hWβ⟩ := hβfin x
      refine ⟨V ∩ W, Filter.inter_mem hV hW, (hVα.union hWβ).subset ?_⟩
      rintro Z ⟨p, hp, hpV, hpW⟩
      obtain ⟨hne, hpZ⟩ := (mem_ite_subspacePointSet_iff D (α := α + β)).1 hp
      by_cases hαZ : α Z = 0
      · have hβZ : β Z ≠ 0 := by simpa only [Pi.add_apply, hαZ, zero_add] using hne
        exact Or.inr ⟨p, (mem_ite_subspacePointSet_iff D).2 ⟨hβZ, hpZ⟩, hpW⟩
      · exact Or.inl ⟨p, (mem_ite_subspacePointSet_iff D).2 ⟨hαZ, hpZ⟩, hpV⟩
    · by_cases hαZ : α Z = 0
      · exact hβdim Z (by simpa only [Pi.add_apply, hαZ, zero_add] using hZ)
      · exact hαdim Z hαZ
  neg_mem' := by
    rintro α ⟨hfin, hdim⟩
    refine ⟨?_, fun Z hZ => hdim Z (neg_ne_zero.mp (by simpa only [Pi.neg_apply] using hZ))⟩
    change LocallyFinite _ at hfin ⊢
    simpa only [Pi.neg_apply, neg_eq_zero] using hfin

/-- A coefficient family is a `k`-cycle exactly when the point sets of the integral closed
subspaces with nonzero coefficient form a locally finite collection and each such subspace has
δ-dimension `k`. -/
@[simp]
theorem mem_cyclesOfDimension_iff (sX : X ⟶ D.space) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    α ∈ cyclesOfDimension D sX k ↔
      (LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
          if α Z = 0 then ∅ else subspacePointSet D.site D.base D.base_mem X Z.subspace) ∧
        ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α Z ≠ 0 →
          deltaDimension D sX Z = k :=
  Iff.rfl

/-- **Stacks 0EDZ, part (3).** The abelian group `Z_k(X)` of `k`-cycles on a good algebraic
space `X/B`. -/
@[stacks 0EDZ "part (3): the abelian group of k-cycles"]
noncomputable abbrev CycleGroup (sX : X ⟶ D.space) (k : ℤ) :=
  ↥(cyclesOfDimension D sX k)

end Cycles

end AlgebraicGeometry.Space

end
