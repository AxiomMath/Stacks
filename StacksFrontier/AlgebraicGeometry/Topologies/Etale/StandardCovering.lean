module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# Standard étale coverings in a big étale site

A covering family of a big étale site is *standard* when it is finite and its target and all
of its sources are affine. Standard étale coverings are the covering families of the big
affine étale site, and this file proves the three closure properties that make them one: they
contain the singleton family of an isomorphism, they are closed under composition, and they
are stable under base change along a morphism between affine objects.

The base-change statement exhibits the fibre products and their projections explicitly,
together with pullback squares in the ambient category of schemes, so that no `HasPullback`
instance in the cutoff category is assumed.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.IsStandardEtaleCovering` — a chosen covering family of a big
  étale site which is finite and has affine target and sources.

## Main results

* `AlgebraicGeometry.BigEtaleSite.isStandardEtaleCovering_singleton` — the singleton family of
  an isomorphism with affine target is a standard étale covering.
* `AlgebraicGeometry.BigEtaleSite.isStandardEtaleCovering_comp` — standard étale coverings
  satisfy the composition axiom.
* `AlgebraicGeometry.BigEtaleSite.isStandardEtaleCovering_baseChange` — standard étale
  coverings are stable under base change between affine objects.

## Implementation notes

A covering family is a `CategoryTheory.Covering` of the site's cutoff category; its membership
in the site's chosen coverings supplies the étale and joint-surjectivity conditions, so only
finiteness and affineness are imposed here. This is equivalent to the usual description by a
finite affine cover, while retaining the actual objects and arrows of the cutoff category.

Since the cutoff category's inclusion into schemes is fully faithful and the cutoff is closed
under the relevant fibre products, a pullback square in schemes between objects of the cutoff
category is reflected; `inclusion_isPullback` is that transfer, and it is what lets the base
change of a covering be computed in schemes and then read back inside the site.

## References

* [Stacks Project, Tag 0219](https://stacks.math.columbia.edu/tag/0219)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSite

/-- A standard étale covering in a big étale site is a finite chosen étale covering
all of whose source schemes are affine. -/
public abbrev IsStandardEtaleCovering (B : AlgebraicGeometry.BigEtaleSite.{u})
    (𝒰 : Covering B.Scheme) : Prop :=
  B.IsCovering 𝒰 ∧ IsAffine (B.inclusion.obj 𝒰.1) ∧
    Finite 𝒰.2.I₀ ∧ ∀ i, IsAffine (B.inclusion.obj (𝒰.2.X i))

/-- A pullback square in the cutoff category of a big étale site remains a pullback square
after applying the canonical inclusion into all schemes. -/
public lemma inclusion_isPullback (B : AlgebraicGeometry.BigEtaleSite.{u})
    {P X Y Z : B.Scheme} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p₁ p₂ f g) :
    IsPullback (B.inclusion.map p₁) (B.inclusion.map p₂)
      (B.inclusion.map f) (B.inclusion.map g) := by
  let Q : B.Scheme := ⟨pullback (B.inclusion.map f) (B.inclusion.map g),
    Scheme.size_pullback_lt _ _ X.property Y.property⟩
  let q₁ : Q ⟶ X := ObjectProperty.homMk (pullback.fst (B.inclusion.map f) (B.inclusion.map g))
  let q₂ : Q ⟶ Y := ObjectProperty.homMk (pullback.snd (B.inclusion.map f) (B.inclusion.map g))
  have hq : q₁ ≫ f = q₂ ≫ g := by
    apply B.inclusion.map_injective
    simpa [q₁, q₂, Q] using
      (pullback.condition (f := B.inclusion.map f) (g := B.inclusion.map g))
  let e : Q ⟶ P := h.lift q₁ q₂ hq
  let d : P ⟶ Q := ObjectProperty.homMk
    (pullback.lift (B.inclusion.map p₁) (B.inclusion.map p₂)
      (by simpa using congrArg B.inclusion.map h.w))
  have he₁ : e ≫ p₁ = q₁ := h.lift_fst _ _ _
  have he₂ : e ≫ p₂ = q₂ := h.lift_snd _ _ _
  have hd₁ : B.inclusion.map d ≫ pullback.fst _ _ = B.inclusion.map p₁ := pullback.lift_fst _ _ _
  have hd₂ : B.inclusion.map d ≫ pullback.snd _ _ = B.inclusion.map p₂ := pullback.lift_snd _ _ _
  have hed : e ≫ d = 𝟙 Q := by
    apply B.inclusion.map_injective
    apply pullback.hom_ext
    · rw [Functor.map_comp, Category.assoc, hd₁]
      simpa [q₁, Q] using congrArg B.inclusion.map he₁
    · rw [Functor.map_comp, Category.assoc, hd₂]
      simpa [q₂, Q] using congrArg B.inclusion.map he₂
  have hde : d ≫ e = 𝟙 P := h.hom_ext
    (by rw [Category.assoc, he₁]; exact B.inclusion.map_injective hd₁)
    (by rw [Category.assoc, he₂]; exact B.inclusion.map_injective hd₂)
  let E : Q ≅ P := ⟨e, d, hed, hde⟩
  exact (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map g)).of_iso
    (B.inclusion.mapIso E) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa [E, q₁, Q] using (congrArg B.inclusion.map he₁).symm)
    (by simpa [E, q₂, Q] using (congrArg B.inclusion.map he₂).symm)
    (by simp) (by simp)

/-- An isomorphism with affine source, regarded as a singleton family, is a standard
étale covering. -/
public theorem isStandardEtaleCovering_singleton
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    {U V : B.Scheme} (f : V ⟶ U) [IsIso f]
    [IsAffine (B.inclusion.obj U)] :
    IsStandardEtaleCovering B
      ⟨U, PreZeroHypercover.singleton.{u + 1} f⟩ := by
  exact ⟨B.coverings_isSite.1 f, inferInstance, inferInstance, fun _ ↦
    @IsAffine.of_isIso _ _ (B.inclusion.map f) (Functor.map_isIso B.inclusion f) _⟩

/-- Composing a standard étale covering with standard étale coverings of all its
members again gives a standard étale covering. -/
public theorem isStandardEtaleCovering_comp (B : AlgebraicGeometry.BigEtaleSite.{u}) :
    CompositionCond (IsStandardEtaleCovering B) := by
  intro 𝒰 h𝒰 𝒱 h𝒱 h
  refine ⟨B.coverings_isSite.2.1 𝒰 h𝒰.1 𝒱 (fun i ↦ (h𝒱 i).1) h,
    h𝒰.2.1, ?_, ?_⟩
  · have := h𝒰.2.2.1
    have (i : 𝒰.2.I₀) := (h𝒱 i).2.2.1
    show Finite (Σ i, (𝒱 i).2.I₀)
    infer_instance
  · rintro ⟨i, j⟩
    exact (h𝒱 i).2.2.2 j

/-- The base change of a standard étale covering along a morphism between affine
objects is a standard étale covering. The displayed pullback squares specify the
base-changed family. -/
public theorem isStandardEtaleCovering_baseChange
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (𝒰 : Covering B.Scheme) (h𝒰 : IsStandardEtaleCovering B 𝒰)
    (V : B.Scheme) [IsAffine (B.inclusion.obj V)] (g : V ⟶ 𝒰.1) :
    ∃ (P : 𝒰.2.I₀ → B.Scheme) (π₁ : ∀ i, P i ⟶ 𝒰.2.X i)
      (π₂ : ∀ i, P i ⟶ V),
      (∀ i, IsPullback (B.inclusion.map (π₁ i)) (B.inclusion.map (π₂ i))
        (B.inclusion.map (𝒰.2.f i)) (B.inclusion.map g)) ∧
        IsStandardEtaleCovering B ⟨V, ⟨𝒰.2.I₀, P, π₂⟩⟩ := by
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.coverings_isSite.2.2 𝒰 h𝒰.1 V g
  refine ⟨P, π₁, π₂, fun i ↦ inclusion_isPullback B (hpb i),
    hcov, inferInstance, h𝒰.2.2.1, ?_⟩
  intro i
  have : IsAffine (B.inclusion.obj (𝒰.2.X i)) := h𝒰.2.2.2 i
  have : IsAffine (B.inclusion.obj 𝒰.1) := h𝒰.2.1
  have hp := inclusion_isPullback B (hpb i)
  exact @IsAffine.of_isIso _ _ hp.isoPullback.hom inferInstance inferInstance

end AlgebraicGeometry.BigEtaleSite
