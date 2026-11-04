module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Recognising an open immersion from an open cover of the source

A separated morphism of schemes that becomes an open immersion on each member of some open
cover of its source is an open immersion as soon as it is injective on the generic points of
the irreducible components.

The reduction is to injectivity of the morphism on points, after which Mathlib's
`AlgebraicGeometry.IsOpenImmersion.of_openCover_source` applies. Injectivity is proved by
showing that the relative diagonal is surjective: a point of the fibre product `X ×_Y X`
specialises from a generic point `η`, and `η` lies in one of the open pieces
`X_i ×_Y X_j`, where both projections are open immersions. So the two images of `η` in `X`
are again generic points, and they have the same image in `Y`; the hypothesis identifies
them, which puts `η`, and therefore the point we started from, in the closed image of the
diagonal.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_openCover_source_of_separated_of_genericPoints_injOn`:
  the criterion.

## Implementation notes

An open cover is `AlgebraicGeometry.Scheme.OpenCover` and injectivity on generic points is
`Set.InjOn` over Mathlib's `genericPoints`. The local hypothesis is imposed on every member
of the cover; injectivity of the original morphism is not assumed, it is derived.

## References

* [Stacks Project, Tag 09NG](https://stacks.math.columbia.edu/tag/09NG)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Every point of a scheme is a specialisation of a generic point of an irreducible
component. -/
public lemma exists_genericPoint_specializes {X : Scheme.{u}} (x : X) :
    ∃ η, η ∈ genericPoints X ∧ η ⤳ x := by
  obtain ⟨Z, hZ, hxZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (closure ({x} : Set X))
      isIrreducible_singleton.closure
  let η : genericPoints X := genericPoints.ofComponent ⟨Z, hZ⟩
  refine ⟨η, η.2, ?_⟩
  rw [specializes_iff_mem_closure, genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩]
  exact hxZ (subset_closure (Set.mem_singleton x))

/-- **A point of the source of an open immersion whose image is a generic point of an irreducible
component is itself a generic point of an irreducible component.** The closure of the point is the
preimage of the closure of its image, and the preimage of an irreducible component meeting the
open range is an irreducible component. -/
public lemma mem_genericPoints_of_isOpenImmersion_apply {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f] {x : A} (hx : f x ∈ genericPoints B) : x ∈ genericPoints A := by
  show closure ({x} : Set A) ∈ irreducibleComponents A
  rw [f.isOpenEmbedding.closure_eq_preimage_closure_image]
  simpa only [Set.image_singleton] using
    preimage_mem_irreducibleComponents hx f.isOpenEmbedding
      ⟨f x, subset_closure (Set.mem_singleton _), ⟨x, rfl⟩⟩

/-- An open immersion carries generic points to generic points. -/
public lemma genericPoints_map_of_openImmersion
    {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j]
    {a : A} (ha : a ∈ genericPoints A) : j a ∈ genericPoints B := by
  apply (mem_genericPoints_iff_forall_specializes_eq (j a)).2
  intro b hba
  obtain ⟨a', ha', rfl⟩ := j.isOpenEmbedding.generalizingMap hba
  simp [(mem_genericPoints_iff_forall_specializes_eq a).1 ha a' ha']

private lemma pullback_fst_diagonal_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X) :
    pullback.fst f f (pullback.diagonal f a) = a := by
  simp only [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
  simp

private lemma pullback_snd_diagonal_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X) :
    pullback.snd f f (pullback.diagonal f a) = a := by
  simp only [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
  simp

/-- A generic point of `X ×_Y X` in the range of an open immersion `m` whose composites with both
projections are open immersions has equal projections, if `f` is injective on generic points. -/
public lemma pullback_fst_eq_snd_of_mem_genericPoints {X Y W : Scheme.{u}} {f : X ⟶ Y}
    (hinj : Set.InjOn f (genericPoints X)) (m : W ⟶ pullback f f) [IsOpenImmersion m]
    [IsOpenImmersion (m ≫ pullback.fst f f)] [IsOpenImmersion (m ≫ pullback.snd f f)]
    {η : ↥(pullback f f)} (hmη : η ∈ Set.range m) (hη : η ∈ genericPoints ↥(pullback f f)) :
    pullback.fst f f η = pullback.snd f f η := by
  obtain ⟨q, rfl⟩ := hmη
  have hq := mem_genericPoints_of_isOpenImmersion_apply m hη
  refine hinj ?_ ?_ ?_
  · simpa only [Scheme.Hom.comp_apply] using
      genericPoints_map_of_openImmersion (m ≫ pullback.fst f f) hq
  · simpa only [Scheme.Hom.comp_apply] using
      genericPoints_map_of_openImmersion (m ≫ pullback.snd f f) hq
  · simpa using
      congrArg (fun k : pullback f f ⟶ Y => k (m q)) (pullback.condition (f := f) (g := f))

/-- A point `η` of `X ×_Y X` in the range of a map `m` whose composite with the first projection
is an open immersion lies on the diagonal as soon as `Δ(pr₁ η)` lies in the range of `m`. -/
public lemma mem_range_diagonal_of_diagonal_mem_range {X Y W : Scheme.{u}} {f : X ⟶ Y}
    (m : W ⟶ pullback f f) [IsOpenImmersion (m ≫ pullback.fst f f)] {η : ↥(pullback f f)}
    (hη : η ∈ Set.range m) (h : pullback.diagonal f (pullback.fst f f η) ∈ Set.range m) :
    η ∈ Set.range (pullback.diagonal f) := by
  obtain ⟨q, rfl⟩ := hη
  obtain ⟨q', hq'⟩ := h
  obtain rfl : q' = q := (m ≫ pullback.fst f f).isOpenEmbedding.injective <| by
    simp [Scheme.Hom.comp_apply, hq', pullback_fst_diagonal_apply]
  exact ⟨_, hq'.symm⟩

/-- If `f` is locally an open immersion on an open cover of the source and injective on generic
points, then every generic point of `X ×_Y X` lies on the diagonal. -/
public lemma mem_range_diagonal_of_mem_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : X.OpenCover) (h𝒰 : ∀ i, IsOpenImmersion (𝒰.f i ≫ f))
    (hinj : Set.InjOn f (genericPoints X)) {η : ↥(pullback f f)}
    (hη : η ∈ genericPoints ↥(pullback f f)) : η ∈ Set.range (pullback.diagonal f) := by
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f f
  obtain ⟨i, q, hqη⟩ := 𝒱.exists_eq η
  have hindex : 𝒱.I₀ = (𝒰.I₀ × 𝒰.I₀) := by simp [𝒱]
  let ij : 𝒰.I₀ × 𝒰.I₀ := hindex ▸ i
  have hQ : 𝒱.X i = pullback (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) := by
    simpa [𝒱, ij, hindex] using Scheme.Pullback.openCoverOfLeftRight_X 𝒰 𝒰 f f ij
  let eIso : 𝒱.X i ≅ pullback (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) := eqToIso hQ
  let e : 𝒱.X i ⟶ pullback (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) := eIso.hom
  have : IsOpenImmersion (𝒰.f ij.1 ≫ f) := h𝒰 ij.1
  have : IsOpenImmersion (𝒰.f ij.2 ≫ f) := h𝒰 ij.2
  have : IsOpenImmersion (𝒰.f ij.1) := 𝒰.map_prop ij.1
  have : IsOpenImmersion (𝒰.f ij.2) := 𝒰.map_prop ij.2
  let m : 𝒱.X i ⟶ pullback f f := 𝒱.f i
  have hVf : m = e ≫ pullback.map (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) f f
      (𝒰.f ij.1) (𝒰.f ij.2) (𝟙 Y) (by simp) (by simp) := by
    cases hQ
    rfl
  have : IsOpenImmersion m := 𝒱.map_prop i
  have hmq : m q = η := hqη
  let j₁ : 𝒱.X i ⟶ X := e ≫ (pullback.fst (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) ≫ 𝒰.f ij.1)
  let j₂ : 𝒱.X i ⟶ X := e ≫ (pullback.snd (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) ≫ 𝒰.f ij.2)
  have hmfst : m ≫ pullback.fst f f = j₁ := by
    simp only [j₁, hVf, Category.assoc, pullback.map, pullback.lift_fst]
  have hmsnd : m ≫ pullback.snd f f = j₂ := by
    simp only [j₂, hVf, Category.assoc, pullback.map, pullback.lift_snd]
  have : IsOpenImmersion (m ≫ pullback.fst f f) := hmfst ▸ inferInstance
  have : IsOpenImmersion (m ≫ pullback.snd f f) := hmsnd ▸ inferInstance
  have hmη : η ∈ Set.range m := ⟨q, hmq⟩
  have hηeq := pullback_fst_eq_snd_of_mem_genericPoints hinj m hmη hη
  have hj₁η : j₁ q = pullback.fst f f η := by simp only [← hmfst, Scheme.Hom.comp_apply, hmq]
  have hj₂η : j₂ q = pullback.snd f f η := by simp only [← hmsnd, Scheme.Hom.comp_apply, hmq]
  obtain ⟨p, hp⟩ : (pullback.diagonal f) (pullback.fst f f η) ∈ Set.range
      (pullback.map (𝒰.f ij.1 ≫ f) (𝒰.f ij.2 ≫ f) f f
        (𝒰.f ij.1) (𝒰.f ij.2) (𝟙 Y) (by simp) (by simp)) := by
    rw [Scheme.Pullback.range_map]
    simp only [Set.mem_inter_iff, Set.mem_preimage, pullback_fst_diagonal_apply,
      pullback_snd_diagonal_apply]
    exact ⟨⟨_, hj₁η⟩, hηeq ▸ ⟨_, hj₂η⟩⟩
  refine mem_range_diagonal_of_diagonal_mem_range m hmη ⟨eIso.inv p, ?_⟩
  rw [hVf]
  simp only [Scheme.Hom.comp_apply, e, eIso]
  exact hp

/-- A separated morphism that is locally an open immersion on an open cover of the source and
injective on generic points of irreducible components is injective. -/
public lemma injective_of_openCover_source_of_separated_of_genericPoints_injOn
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (𝒰 : X.OpenCover)
    (h𝒰 : ∀ i, IsOpenImmersion (𝒰.f i ≫ f)) (hinj : Set.InjOn f (genericPoints X)) :
    Function.Injective f := by
  intro x x' hxx'
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x x' hxx'
  obtain ⟨η, hη, hηz⟩ := exists_genericPoint_specializes z
  obtain ⟨w, rfl⟩ := (specializes_iff_forall_closed.mp hηz) _
    (pullback.diagonal f).isClosedEmbedding.isClosed_range
    (mem_range_diagonal_of_mem_genericPoints f 𝒰 h𝒰 hinj hη)
  exact ((pullback_fst_diagonal_apply f w).symm.trans hzfst).symm.trans
    ((pullback_snd_diagonal_apply f w).symm.trans hzsnd)

/-- **Stacks Project, Tag 09NG.** A separated morphism that is locally an open immersion on
the source and injective on generic points of irreducible components is an open immersion. -/
@[stacks 09NG]
public theorem isOpenImmersion_of_openCover_source_of_separated_of_genericPoints_injOn
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (𝒰 : X.OpenCover)
    (h𝒰 : ∀ i, IsOpenImmersion (𝒰.f i ≫ f))
    (hinj : Set.InjOn f (genericPoints X)) :
    IsOpenImmersion f :=
  IsOpenImmersion.of_openCover_source f 𝒰
    (injective_of_openCover_source_of_separated_of_genericPoints_injOn f 𝒰 h𝒰 hinj) h𝒰

end AlgebraicGeometry

end
