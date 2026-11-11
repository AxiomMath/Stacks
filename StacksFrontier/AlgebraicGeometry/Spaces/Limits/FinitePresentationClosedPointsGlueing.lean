module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing

/-!
# Glueing algebraic spaces of finite presentation at finitely many closed points

Let `S` be a scheme and let `s₀, …, s_{n-1}` be pairwise distinct closed points of `S` whose
open complement `U = S ∖ {s₀, …, s_{n-1}}` has quasi-compact inclusion. With
`Sᵢ = Spec 𝒪_{S,sᵢ}` and `Uᵢ = Sᵢ ∖ {sᵢ}` there is a comparison functor
`FP_S ⥤ FP_U ×_{FP_{U₀} × ⋯ × FP_{U_{n-1}}} (FP_{S₀} × ⋯ × FP_{S_{n-1}})`,
where `FP_T` is the category of algebraic spaces of finite presentation over `T`. It takes an
algebraic space of finite presentation over `S` to its base change to `U`, the family of its
base changes to the `Sᵢ`, and the family of canonical identifications of the two further base
changes to the `Uᵢ`. Stacks 0E92 asserts that this functor is an equivalence.

The data the functor needs is that of a commuting square over the base for each point, and no
more; it is packaged as `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData`,
whose fields spell out the objects `U`, `Sᵢ`, `Uᵢ` of the big fppf site of `S` and the morphisms
between them. The `n`-fold `2`-fibre product is the iso-comma category of the two functors into
the product category `∀ i, FP_{Uᵢ}` assembled from the base changes, so the target is literally
the one the lemma names.

Essential surjectivity is reduced to the case `n = 1` — that is, to Stacks 0E90 — by induction
on `n`, following the argument of Stacks 0E92: the last point is split off by a single
application of Stacks 0E90 over the intermediate base `S ∖ {s₀, …, s_{n-2}}`, and the induction
hypothesis is applied to the remaining `n - 1` points with that intermediate base in place of
`U`. The tower of intermediate bases, together with the requirement that each of its steps be
essentially surjective, is
`AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.Solvable`.

Full faithfulness, the construction of the tower, and hence Stacks 0E92 itself, are in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedPointsGlueingEquivalence`,
as `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_comparisonFunctor_closedPoints`.

## Main definitions

* `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData`: the data of `n`
  commuting squares over a common base in the big fppf site of `S`, one for each point.
* `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.comparisonFunctor`:
  the comparison functor of Stacks 0E92, from the algebraic spaces of finite presentation over
  the base to the `n`-fold `2`-fibre product.
* `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.Peel`: the datum that
  splits the last point off, namely the intermediate base through which the open part and the
  last local part both factor.
* `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.Peel.tail`: the
  glueing data for the remaining points, over the intermediate base.
* `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.Solvable`: the tower
  of such splittings, each of whose binary comparison functors is essentially surjective.

## Main results

* `CategoryTheory.Over.pullbackSquareObjIso_comp_base` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_comp_base`: the comparison
  of a commuting square over `Z` is the comparison of the same square read over `M`, conjugated
  by the comparisons of the two factorisations through `M ⟶ Z`.
* `CategoryTheory.Over.pullbackSquareObjIso_comp_factor` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_comp_factor`: replacing the
  first leg of a commuting square by its composite with a factorisation of the first base
  morphism changes the comparison only by the comparisons of the factorisations.
* `AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData`'s
  `essSurj_comparisonFunctor`: the comparison functor is essentially surjective along a tower
  of splittings whose binary comparison functors are essentially surjective.

## Relation to Stacks 0E92

This file proves the comparison functor and the reduction of its essential surjectivity from
`n` to `n - 1` points. The tower `Solvable` is built, with Stacks 0E90 applied at each of its
intermediate bases (through
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_mono`), and full
faithfulness is proved by the same splitting, in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedPointsGlueingEquivalence`;
its `isEquivalence_comparisonFunctor_closedPoints` is Stacks 0E92.

## Implementation notes

The glueing data carries a morphism `overlapToOpen i : Uᵢ ⟶ U` for every point, rather than only
the morphism to the intermediate base of the step at which the point is split off: the functor
compares base changes to the single open part `U`, so that is the morphism it needs. The square
condition of the data is read over the base, and the square conditions of the tail of a
splitting are consequences of it, so only the square condition of the split-off point has to be
carried in `Peel`.

The comparison isomorphisms of the squares are the pinned ones of
`AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso`, and the two coherence
identities between them that the induction needs are proved by the recipe of the file carrying
Stacks 0E90: transport to the slice of presheaves along the fully faithful inclusion of the full
subcategory, and check the composites with the projections of the iterated pullback. The
associativity of the comparisons of factorisations, which the induction also needs, is
`AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeFactorIso_assoc`.

## References

* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E92](https://stacks.math.columbia.edu/tag/0E92)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **The comparison of a commuting square is compatible with a base change of its base.** Let a
square `nu ≫ um = nl ≫ lm` over `M` be composed with `m : M ⟶ Z`, giving a square
`nu ≫ v = nl ≫ lb` over `Z`. Then the comparison of the latter, followed by the comparison of
the factorisation `lm ≫ m = lb`, is the comparison of the factorisation `um ≫ m = v` followed by
the comparison of the former at the base change along `m`. -/
theorem pullbackSquareObjIso_comp_base {Z M U L N : C} {m : M ⟶ Z} {um : U ⟶ M} {v : U ⟶ Z}
    {lm : L ⟶ M} {lb : L ⟶ Z} {nu : N ⟶ U} {nl : N ⟶ L} (hum : um ≫ m = v) (hlm : lm ≫ m = lb)
    (w₂ : nu ≫ um = nl ≫ lm) (w₁ : nu ≫ v = nl ≫ lb) (A : Over Z) :
    (Over.pullback nu).map (pullbackFactorObjIso hum A).hom ≫
        (pullbackSquareObjIso w₂ ((Over.pullback m).obj A)).hom =
      (pullbackSquareObjIso w₁ A).hom ≫
        (Over.pullback nl).map (pullbackFactorObjIso hlm A).hom := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply (isPullback_pullback_snd_pullback_snd_pullback_of_comp (f := nl) (g := lm) (k := m)
    rfl rfl A).hom_ext
  · simp
  · simp

/-- **The comparison of a commuting square is compatible with a factorisation of its first base
morphism.** Replacing the first leg `nu` of a square `nu ≫ v = nl ≫ lb` by its composite with a
factorisation `um ≫ m = v` gives a square over the same base, and the two comparisons agree up
to the comparisons of the two factorisations of `nu ≫ v`. -/
theorem pullbackSquareObjIso_comp_factor {Z M U L N : C} {m : M ⟶ Z} {v : U ⟶ Z} {lb : L ⟶ Z}
    {nu : N ⟶ U} {nl : N ⟶ L} {nm : N ⟶ M} {nz : N ⟶ Z} (w₁ : nu ≫ v = nl ≫ lb)
    (w₂ : nm ≫ m = nl ≫ lb) (h₁ : nu ≫ v = nz) (h₂ : nm ≫ m = nz) (A : Over Z) :
    (pullbackFactorObjIso h₂ A).hom ≫ (pullbackSquareObjIso w₂ A).hom =
      (pullbackFactorObjIso h₁ A).hom ≫ (pullbackSquareObjIso w₁ A).hom := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply (isPullback_pullback_snd_pullback (u := lb) (q := nl) A).hom_ext
  · simp
  · simp

end CategoryTheory.Over

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two coherence identities between the pinned comparison isomorphisms -/

/-- **The comparison of a commuting square is compatible with a base change of its base**, read
in the categories of algebraic spaces of finite presentation. -/
theorem baseChangeSquareIso_comp_base {Z M U L N : BigFppfOver B S hS} {m : M ⟶ Z} {um : U ⟶ M}
    {v : U ⟶ Z} {lm : L ⟶ M} {lb : L ⟶ Z} {nu : N ⟶ U} {nl : N ⟶ L} (hum : um ≫ m = v)
    (hlm : lm ≫ m = lb) (w₂ : nu ≫ um = nl ≫ lm) (w₁ : nu ≫ v = nl ≫ lb)
    (A : FinitePresentationSpacesOver B S hS Z) :
    (baseChange B S hS nu).map ((baseChangeFactorIso B S hS hum).hom.app A) ≫
        (baseChangeSquareIso B S hS w₂).hom.app ((baseChange B S hS m).obj A) =
      (baseChangeSquareIso B S hS w₁).hom.app A ≫
        (baseChange B S hS nl).map ((baseChangeFactorIso B S hS hlm).hom.app A) := by
  refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS N)).map_injective ?_
  simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left, ι_map_baseChange_map,
    baseChangeFactorIso_hom_app_left, Over.pullbackSquareIso_hom_app]
  exact Over.pullbackSquareObjIso_comp_base (by rw [← Functor.map_comp, hum])
    (by rw [← Functor.map_comp, hlm]) (by rw [← Functor.map_comp, ← Functor.map_comp, w₂])
    (by rw [← Functor.map_comp, ← Functor.map_comp, w₁]) A.obj

/-- **The comparison of a commuting square is compatible with a factorisation of its first base
morphism**, read in the categories of algebraic spaces of finite presentation. -/
theorem baseChangeSquareIso_comp_factor {Z M U L N : BigFppfOver B S hS} {m : M ⟶ Z}
    {v : U ⟶ Z} {lb : L ⟶ Z} {nu : N ⟶ U} {nl : N ⟶ L} {nm : N ⟶ M} {nz : N ⟶ Z}
    (w₁ : nu ≫ v = nl ≫ lb) (w₂ : nm ≫ m = nl ≫ lb) (h₁ : nu ≫ v = nz) (h₂ : nm ≫ m = nz)
    (A : FinitePresentationSpacesOver B S hS Z) :
    (baseChangeFactorIso B S hS h₂).hom.app A ≫ (baseChangeSquareIso B S hS w₂).hom.app A =
      (baseChangeFactorIso B S hS h₁).hom.app A ≫
        (baseChangeSquareIso B S hS w₁).hom.app A := by
  refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS N)).map_injective ?_
  simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left,
    baseChangeFactorIso_hom_app_left, Over.pullbackSquareIso_hom_app]
  exact Over.pullbackSquareObjIso_comp_factor
    (by rw [← Functor.map_comp, ← Functor.map_comp, w₁])
    (by rw [← Functor.map_comp, ← Functor.map_comp, w₂])
    (by rw [← Functor.map_comp, h₁]) (by rw [← Functor.map_comp, h₂]) A.obj

/-! ### The square condition at a point, transported along a splitting -/

/-- Base change along an isomorphism of the big fppf site of `S` is essentially surjective. -/
private theorem essSurj_baseChange_of_isIso {X Y : BigFppfOver B S hS} (j : X ⟶ Y) [IsIso j] :
    (baseChange B S hS j).EssSurj := by
  constructor
  intro T
  refine ⟨(baseChange B S hS (inv j)).obj T, ⟨?_⟩⟩
  exact ((baseChangeFactorIso B S hS (IsIso.hom_inv_id j)).app T).symm ≪≫
    (baseChangeId B S hS X).app T

/-- **The square condition at the split-off point.** If a comparison `ψ` over the overlap
satisfies the square condition of the square over the intermediate base `M` for the object `Y'`
there, then it satisfies the square condition of the square over `Z` for an object `Y` whose
base change to `M` is identified with `Y'`. -/
private theorem squareCondition_of_base {Z M U L N : BigFppfOver B S hS} {m : M ⟶ Z}
    {um : U ⟶ M} {v : U ⟶ Z} {lm : L ⟶ M} {lb : L ⟶ Z} {nu : N ⟶ U} {nl : N ⟶ L}
    (hum : um ≫ m = v) (hlm : lm ≫ m = lb) (w₂ : nu ≫ um = nl ≫ lm) (w₁ : nu ≫ v = nl ≫ lb)
    {Y : FinitePresentationSpacesOver B S hS Z} {Y' : FinitePresentationSpacesOver B S hS M}
    {A : FinitePresentationSpacesOver B S hS U} {Bl : FinitePresentationSpacesOver B S hS L}
    (c : (baseChange B S hS m).obj Y ≅ Y') (a' : (baseChange B S hS um).obj Y' ≅ A)
    (e : (baseChange B S hS lm).obj Y' ≅ Bl)
    (ψ : (baseChange B S hS nu).obj A ⟶ (baseChange B S hS nl).obj Bl)
    (hψ : (baseChange B S hS nu).map a'.hom ≫ ψ =
      (baseChangeSquareIso B S hS w₂).hom.app Y' ≫ (baseChange B S hS nl).map e.hom) :
    (baseChange B S hS nu).map ((baseChangeFactorIso B S hS hum).hom.app Y ≫
        (baseChange B S hS um).map c.hom ≫ a'.hom) ≫ ψ =
      (baseChangeSquareIso B S hS w₁).hom.app Y ≫ (baseChange B S hS nl).map
        ((baseChangeFactorIso B S hS hlm).hom.app Y ≫ (baseChange B S hS lm).map c.hom ≫
          e.hom) := by
  have hnat := (baseChangeSquareIso B S hS w₂).hom.naturality c.hom
  simp only [Functor.comp_map] at hnat
  simp only [Functor.map_comp, Category.assoc]
  rw [hψ, reassoc_of% hnat, ← Category.assoc,
    baseChangeSquareIso_comp_base B S hS hum hlm w₂ w₁ Y]
  simp only [Category.assoc, ← Functor.map_comp]

/-- **The square condition at a point that is not split off.** If a comparison `ψ` over the
overlap satisfies the square condition of the square whose first leg factors through the
intermediate base `M`, then it satisfies the square condition of the original square. -/
private theorem squareCondition_of_factor {Z M U L N : BigFppfOver B S hS} {m : M ⟶ Z}
    {um : U ⟶ M} {v : U ⟶ Z} {lb : L ⟶ Z} {nu : N ⟶ U} {nl : N ⟶ L} {nm : N ⟶ M}
    (hum : um ≫ m = v) (hnm : nu ≫ um = nm) (w₁ : nu ≫ v = nl ≫ lb) (w₂ : nm ≫ m = nl ≫ lb)
    {Y : FinitePresentationSpacesOver B S hS Z} {Y' : FinitePresentationSpacesOver B S hS M}
    {A : FinitePresentationSpacesOver B S hS U} {Bl : FinitePresentationSpacesOver B S hS L}
    (c : (baseChange B S hS m).obj Y ≅ Y') (a' : (baseChange B S hS um).obj Y' ≅ A)
    (b : (baseChange B S hS lb).obj Y ≅ Bl)
    (ψ : (baseChange B S hS nu).obj A ⟶ (baseChange B S hS nl).obj Bl)
    (hψ : (baseChange B S hS nm).map c.hom ≫ (baseChangeFactorIso B S hS hnm).hom.app Y' ≫
        (baseChange B S hS nu).map a'.hom ≫ ψ =
      (baseChangeSquareIso B S hS w₂).hom.app Y ≫ (baseChange B S hS nl).map b.hom) :
    (baseChange B S hS nu).map ((baseChangeFactorIso B S hS hum).hom.app Y ≫
        (baseChange B S hS um).map c.hom ≫ a'.hom) ≫ ψ =
      (baseChangeSquareIso B S hS w₁).hom.app Y ≫ (baseChange B S hS nl).map b.hom := by
  have h₂ : nm ≫ m = nu ≫ v := by rw [← hnm, Category.assoc, hum]
  have hassoc := baseChangeFactorIso_assoc B S hS hnm hum (rfl : nu ≫ v = nu ≫ v) h₂ Y
  have hnat := (baseChangeFactorIso B S hS hnm).hom.naturality c.hom
  simp only [Functor.comp_map] at hnat
  refine (Iso.cancel_iso_hom_left
    ((baseChangeFactorIso B S hS (rfl : nu ≫ v = nu ≫ v)).app Y) _ _).mp ?_
  simp only [Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hassoc, ← reassoc_of% hnat, hψ,
    reassoc_of% (baseChangeSquareIso_comp_factor B S hS w₁ w₂ (rfl : nu ≫ v = nu ≫ v) h₂ Y)]

/-! ### The glueing data at finitely many points -/

/-- The data of `n` commuting squares over a common base in the big fppf site of `S`: an open
part `U`, and for each of `n` points a local part `Sᵢ` over the base and an overlap `Uᵢ` over
both `U` and `Sᵢ`, such that the two composites to the base agree. In the situation of
Stacks 0E92 the base is `S`, the open part is `S ∖ {s₀, …, s_{n-1}}`, the `i`th local part is
`Spec 𝒪_{S,sᵢ}` and the `i`th overlap is its puncture. -/
structure ClosedPointsGlueingData (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (n : ℕ) where
  /-- The base, over which everything lies. -/
  base : BigFppfOver B S hS
  /-- The open part, the complement of all the points. -/
  openPart : BigFppfOver B S hS
  /-- The local part at the `i`th point. -/
  localPart : Fin n → BigFppfOver B S hS
  /-- The overlap at the `i`th point, the puncture of the local part. -/
  overlapPart : Fin n → BigFppfOver B S hS
  /-- The structure morphism of the open part. -/
  openToBase : openPart ⟶ base
  /-- The structure morphism of the `i`th local part. -/
  localToBase (i : Fin n) : localPart i ⟶ base
  /-- The `i`th overlap lies over the open part. -/
  overlapToOpen (i : Fin n) : overlapPart i ⟶ openPart
  /-- The `i`th overlap lies over the `i`th local part. -/
  overlapToLocal (i : Fin n) : overlapPart i ⟶ localPart i
  /-- The two composites from the `i`th overlap to the base agree. -/
  w (i : Fin n) : overlapToOpen i ≫ openToBase = overlapToLocal i ≫ localToBase i

namespace ClosedPointsGlueingData

variable {B S hS} {n : ℕ} (D : ClosedPointsGlueingData B S hS n)

/-- The functor from the algebraic spaces of finite presentation over the open part to the
product of those over the overlaps, assembled from the base changes along the morphisms
`Uᵢ ⟶ U`. This is the first of the two functors whose iso-comma category is the `n`-fold
`2`-fibre product of Stacks 0E92. -/
noncomputable abbrev openToOverlaps :
    FinitePresentationSpacesOver B S hS D.openPart ⥤
      ∀ i, FinitePresentationSpacesOver B S hS (D.overlapPart i) :=
  Functor.pi' fun i ↦ baseChange B S hS (D.overlapToOpen i)

/-- The functor from the product of the algebraic spaces of finite presentation over the local
parts to the product of those over the overlaps, assembled from the base changes along the
morphisms `Uᵢ ⟶ Sᵢ`. This is the second of the two functors whose iso-comma category is the
`n`-fold `2`-fibre product of Stacks 0E92. -/
noncomputable abbrev localsToOverlaps :
    (∀ i, FinitePresentationSpacesOver B S hS (D.localPart i)) ⥤
      ∀ i, FinitePresentationSpacesOver B S hS (D.overlapPart i) :=
  Functor.pi fun i ↦ baseChange B S hS (D.overlapToLocal i)

/-- The first functor of the `2`-fibre product acts on morphisms coordinatewise, by base change
along the morphism from the overlap to the open part. -/
@[simp]
theorem openToOverlaps_map {A A' : FinitePresentationSpacesOver B S hS D.openPart} (f : A ⟶ A') :
    D.openToOverlaps.map f = fun i ↦ (baseChange B S hS (D.overlapToOpen i)).map f :=
  rfl

/-- The second functor of the `2`-fibre product acts on morphisms coordinatewise, by base change
along the morphism from the overlap to the local part. -/
@[simp]
theorem localsToOverlaps_map {A A' : ∀ i, FinitePresentationSpacesOver B S hS (D.localPart i)}
    (f : A ⟶ A') :
    D.localsToOverlaps.map f = fun i ↦ (baseChange B S hS (D.overlapToLocal i)).map (f i) :=
  rfl

/-- **The comparison functor of Stacks 0E92.** It takes an algebraic space of finite
presentation over the base to its base change to the open part, the family of its base changes
to the local parts, and the family of the canonical identifications of the two further base
changes to the overlaps. -/
noncomputable def comparisonFunctor :
    FinitePresentationSpacesOver B S hS D.base ⥤ IsoComma D.openToOverlaps D.localsToOverlaps :=
  IsoComma.lift _ _ (baseChange B S hS D.openToBase)
    (Functor.pi' fun i ↦ baseChange B S hS (D.localToBase i))
    (NatIso.pi' fun i ↦ baseChangeSquareIso B S hS (D.w i))

/-- The comparison morphism of the image of an object under the comparison functor is, in each
coordinate, the comparison isomorphism of the square at that point. -/
@[simp]
theorem comparisonFunctor_obj_hom (A : FinitePresentationSpacesOver B S hS D.base) :
    (D.comparisonFunctor.obj A).obj.hom =
      fun i ↦ (baseChangeSquareIso B S hS (D.w i)).hom.app A :=
  rfl

/-- The first projection of the comparison functor is base change along the structure morphism
of the open part. -/
theorem comparisonFunctor_comp_fst :
    D.comparisonFunctor ⋙ IsoComma.fst D.openToOverlaps D.localsToOverlaps =
      baseChange B S hS D.openToBase :=
  rfl

/-- The second projection of the comparison functor is the family of the base changes along the
structure morphisms of the local parts. -/
theorem comparisonFunctor_comp_snd :
    D.comparisonFunctor ⋙ IsoComma.snd D.openToOverlaps D.localsToOverlaps =
      Functor.pi' fun i ↦ baseChange B S hS (D.localToBase i) :=
  rfl

/-- The square condition of a morphism out of the image of the comparison functor, read in each
coordinate: this is the commuting square of the morphism of the `2`-fibre product. -/
theorem comparisonFunctor_hom_w {Y : FinitePresentationSpacesOver B S hS D.base}
    {T : IsoComma D.openToOverlaps D.localsToOverlaps} (f : D.comparisonFunctor.obj Y ⟶ T)
    (i : Fin n) :
    (baseChange B S hS (D.overlapToOpen i)).map f.hom.left ≫ T.obj.hom i =
      (baseChangeSquareIso B S hS (D.w i)).hom.app Y ≫
        (baseChange B S hS (D.overlapToLocal i)).map (f.hom.right i) :=
  congrFun f.hom.w i

/-- An object of the `n`-fold `2`-fibre product lies in the essential image of the comparison
functor as soon as some algebraic space of finite presentation over the base has base changes
isomorphic to its components, compatibly with the comparisons over the overlaps. -/
theorem comparisonFunctor_essImage_of_iso {Y : FinitePresentationSpacesOver B S hS D.base}
    {T : IsoComma D.openToOverlaps D.localsToOverlaps}
    (α : (baseChange B S hS D.openToBase).obj Y ≅ T.obj.left)
    (β : ∀ i, (baseChange B S hS (D.localToBase i)).obj Y ≅ T.obj.right i)
    (hw : ∀ i, (baseChange B S hS (D.overlapToOpen i)).map α.hom ≫ T.obj.hom i =
      (baseChangeSquareIso B S hS (D.w i)).hom.app Y ≫
        (baseChange B S hS (D.overlapToLocal i)).map (β i).hom) :
    D.comparisonFunctor.essImage T := by
  refine ⟨Y, ⟨ObjectProperty.isoMk _ (Comma.isoMk α (Pi.isoMk β) ?_)⟩⟩
  apply CategoryTheory.Pi.ext
  intro i
  exact hw i

/-! ### Splitting off the last point -/

/-- A splitting of the glueing data at the last of its points: an intermediate base `M` through
which both the open part and the last local part factor, in such a way that the square at the
last point is a square over `M`. In the situation of Stacks 0E92 the intermediate base is
`S ∖ {s₀, …, s_{n-1}}`, so that the square at the last point `s_n` is the one to which
Stacks 0E90 applies over that base. -/
structure Peel {n : ℕ} (D : ClosedPointsGlueingData B S hS (n + 1)) where
  /-- The intermediate base. -/
  mid : BigFppfOver B S hS
  /-- The structure morphism of the intermediate base. -/
  midToBase : mid ⟶ D.base
  /-- The open part lies over the intermediate base. -/
  openToMid : D.openPart ⟶ mid
  /-- The factorisation of the structure morphism of the open part. -/
  openToMid_comp : openToMid ≫ midToBase = D.openToBase
  /-- The last local part lies over the intermediate base. -/
  lastToMid : D.localPart (Fin.last n) ⟶ mid
  /-- The factorisation of the structure morphism of the last local part. -/
  lastToMid_comp : lastToMid ≫ midToBase = D.localToBase (Fin.last n)
  /-- The square at the last point, read over the intermediate base. -/
  last_w : D.overlapToOpen (Fin.last n) ≫ openToMid =
    D.overlapToLocal (Fin.last n) ≫ lastToMid

namespace Peel

variable {D : ClosedPointsGlueingData B S hS (n + 1)} (p : D.Peel)

/-- The glueing data for the remaining points, over the intermediate base: the open part is the
intermediate base, and the overlaps lie over it through the open part. -/
def tail : ClosedPointsGlueingData B S hS n where
  base := D.base
  openPart := p.mid
  localPart i := D.localPart i.castSucc
  overlapPart i := D.overlapPart i.castSucc
  openToBase := p.midToBase
  localToBase i := D.localToBase i.castSucc
  overlapToOpen i := D.overlapToOpen i.castSucc ≫ p.openToMid
  overlapToLocal i := D.overlapToLocal i.castSucc
  w i := by rw [Category.assoc, p.openToMid_comp]; exact D.w i.castSucc

/-- The comparison functor of Stacks 0E90 at the split-off point: the binary comparison functor
attached to the square at the last point, read over the intermediate base. -/
noncomputable abbrev lastFunctor :
    FinitePresentationSpacesOver B S hS p.mid ⥤
      IsoComma (baseChange B S hS (D.overlapToOpen (Fin.last n)))
        (baseChange B S hS (D.overlapToLocal (Fin.last n))) :=
  glueingFunctor B S hS p.last_w

end Peel

/-- A tower of splittings of the glueing data whose binary comparison functors are all
essentially surjective. For no points this says that the open part is the base; for `n + 1`
points it says that the last point can be split off by a square whose comparison functor — the
functor of Stacks 0E90 — is essentially surjective, and that the remaining `n` points again
admit such a tower. -/
def Solvable : ∀ (n : ℕ), ClosedPointsGlueingData B S hS n → Prop
  | 0, D => IsIso D.openToBase
  | n + 1, D => ∃ p : D.Peel, p.lastFunctor.EssSurj ∧ Solvable n p.tail

/-! ### Essential surjectivity by induction on the number of points -/

/-- **The induction step of the essential surjectivity of Stacks 0E92.** Splitting off the last
point by a comparison functor of Stacks 0E90 which is essentially surjective, and knowing the
comparison functor of the remaining points to be essentially surjective, the comparison functor
of all the points is essentially surjective. -/
private theorem essSurj_comparisonFunctor_peel {n : ℕ}
    {D : ClosedPointsGlueingData B S hS (n + 1)} (p : D.Peel) (hlast : p.lastFunctor.EssSurj)
    (htail : p.tail.comparisonFunctor.EssSurj) : D.comparisonFunctor.EssSurj := by
  constructor
  intro T
  have hTi : ∀ i, IsIso (T.obj.hom i) := (isIso_pi_iff _).mp T.property
  -- the last point, by the comparison functor of Stacks 0E90 over the intermediate base
  obtain ⟨Y', ⟨Ξ⟩⟩ := hlast.mem_essImage
    (⟨⟨T.obj.left, T.obj.right (Fin.last n), T.obj.hom (Fin.last n)⟩, hTi _⟩ :
      IsoComma (baseChange B S hS (D.overlapToOpen (Fin.last n)))
        (baseChange B S hS (D.overlapToLocal (Fin.last n))))
  set a' : (baseChange B S hS p.openToMid).obj Y' ≅ T.obj.left :=
    (IsoComma.fst _ _).mapIso Ξ with ha'
  set e : (baseChange B S hS p.lastToMid).obj Y' ≅ T.obj.right (Fin.last n) :=
    (IsoComma.snd _ _).mapIso Ξ with he
  have hS1 : (baseChange B S hS (D.overlapToOpen (Fin.last n))).map a'.hom ≫
      T.obj.hom (Fin.last n) =
        (baseChangeSquareIso B S hS p.last_w).hom.app Y' ≫
          (baseChange B S hS (D.overlapToLocal (Fin.last n))).map e.hom := Ξ.hom.hom.w
  -- the glueing datum for the remaining points, over the intermediate base
  set E : p.tail.openToOverlaps.obj Y' ≅
      p.tail.localsToOverlaps.obj fun j ↦ T.obj.right j.castSucc :=
    Pi.isoMk fun j ↦ (baseChangeFactorIso B S hS
        (rfl : D.overlapToOpen j.castSucc ≫ p.openToMid =
          D.overlapToOpen j.castSucc ≫ p.openToMid)).app Y' ≪≫
      (baseChange B S hS (D.overlapToOpen j.castSucc)).mapIso a' ≪≫
        @asIso _ _ _ _ (T.obj.hom j.castSucc) (hTi j.castSucc) with hE
  -- the remaining points, by the induction hypothesis
  obtain ⟨Y, ⟨Θ⟩⟩ := htail.mem_essImage
    (⟨⟨Y', fun j ↦ T.obj.right j.castSucc, E.hom⟩, E.isIso_hom⟩ :
      IsoComma p.tail.openToOverlaps p.tail.localsToOverlaps)
  set c : (baseChange B S hS p.midToBase).obj Y ≅ Y' := (IsoComma.fst _ _).mapIso Θ with hc
  set b : ∀ j : Fin n, (baseChange B S hS (D.localToBase j.castSucc)).obj Y ≅
      T.obj.right j.castSucc := fun j ↦ Pi.isoApp ((IsoComma.snd _ _).mapIso Θ) j with hb
  have hS2 : ∀ j : Fin n,
      (baseChange B S hS (D.overlapToOpen j.castSucc ≫ p.openToMid)).map c.hom ≫ E.hom j =
        (baseChangeSquareIso B S hS (p.tail.w j)).hom.app Y ≫
          (baseChange B S hS (D.overlapToLocal j.castSucc)).map (b j).hom :=
    fun j ↦ comparisonFunctor_hom_w p.tail Θ.hom j
  -- the object over the base, and its comparisons
  set bb : ∀ i : Fin (n + 1), (baseChange B S hS (D.localToBase i)).obj Y ≅ T.obj.right i :=
    fun i ↦ Fin.lastCases ((baseChangeFactorIso B S hS p.lastToMid_comp).app Y ≪≫
      (baseChange B S hS p.lastToMid).mapIso c ≪≫ e) b i with hbb
  have key : ∀ i : Fin (n + 1),
      (baseChange B S hS (D.overlapToOpen i)).map
          ((baseChangeFactorIso B S hS p.openToMid_comp).hom.app Y ≫
            (baseChange B S hS p.openToMid).map c.hom ≫ a'.hom) ≫ T.obj.hom i =
        (baseChangeSquareIso B S hS (D.w i)).hom.app Y ≫
          (baseChange B S hS (D.overlapToLocal i)).map (bb i).hom := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [hbb]
      simp only [Fin.lastCases_last, Iso.trans_hom, Functor.mapIso_hom]
      exact squareCondition_of_base B S hS p.openToMid_comp p.lastToMid_comp p.last_w
        (D.w (Fin.last n)) c a' e (T.obj.hom (Fin.last n)) hS1
    | cast j =>
      rw [hbb]
      simp only [Fin.lastCases_castSucc]
      exact squareCondition_of_factor B S hS p.openToMid_comp rfl (D.w j.castSucc)
        (p.tail.w j) c a' (b j) (T.obj.hom j.castSucc) (hS2 j)
  exact comparisonFunctor_essImage_of_iso D
    ((baseChangeFactorIso B S hS p.openToMid_comp).app Y ≪≫
      (baseChange B S hS p.openToMid).mapIso c ≪≫ a') bb key

/-- **Essential surjectivity of the comparison functor along a tower of splittings.**
Every object of the `n`-fold `2`-fibre product — an algebraic space of finite presentation over
the open part, a family of such over the local parts, and a family of identifications over the
overlaps — is, up to isomorphism, the image of an algebraic space of finite presentation over
the base, as soon as the glueing data admits a tower of splittings whose binary comparison
functors are essentially surjective. The induction splits off the last point by one such
comparison functor and applies the induction hypothesis to the remaining points. This is the
essential surjectivity half of Stacks 0E92, which is
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_comparisonFunctor_closedPoints`
of `StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedPointsGlueingEquivalence`;
there the tower is constructed. -/
theorem essSurj_comparisonFunctor :
    ∀ (n : ℕ) (D : ClosedPointsGlueingData B S hS n), Solvable n D →
      D.comparisonFunctor.EssSurj := by
  intro n
  induction n with
  | zero =>
    intro D h
    have : IsIso D.openToBase := h
    have hes := essSurj_baseChange_of_isIso (B := B) (S := S) (hS := hS) D.openToBase
    constructor
    intro T
    obtain ⟨Y, ⟨a⟩⟩ := hes.mem_essImage T.obj.left
    exact comparisonFunctor_essImage_of_iso D a (fun i ↦ i.elim0) fun i ↦ i.elim0
  | succ n ih =>
    intro D h
    obtain ⟨p, hlast, htail⟩ := h
    exact essSurj_comparisonFunctor_peel p hlast (ih p.tail htail)

end ClosedPointsGlueingData

end AlgebraicGeometry.FinitePresentationSpacesOver

end
