module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard V coverings

A standard V covering of an affine scheme is a finite family of morphisms from affine
schemes such that every morphism to the base out of the spectrum of a valuation ring lifts
to some member of the family after passing to an extension of valuation rings.  Standard V
coverings are stable under base change and under composition, and the lifting condition can
equivalently be tested on the single morphism out of the disjoint union of the sources.

## Main definitions

* `AlgebraicGeometry.IsExtensionOfValuationRings`: a ring homomorphism between valuation
  rings is injective and local.
* `AlgebraicGeometry.IsStandardVCovering`: the predicate that a finite family of affine
  schemes over an affine base is a standard V covering.

## Main results

* `AlgebraicGeometry.isStandardVCovering_pullback`: stability under base change.
* `AlgebraicGeometry.IsStandardVCovering.comp`: stability under composition.
* `AlgebraicGeometry.isStandardVCovering_tfae`: equivalent forms of the lifting condition.

## Implementation notes

Finite families are indexed by an arbitrary type carrying a `Finite` instance.  An extension
of valuation rings is represented by its injective local ring homomorphism, and the
commutative diagram of the source is the equality of the two composites from the spectrum of
the extension ring to the base.

## References

* [Stacks Project, Tag 0ETB](https://stacks.math.columbia.edu/tag/0ETB)
* [Stacks Project, Tag 0ASG](https://stacks.math.columbia.edu/tag/0ASG)
* [Stacks Project, Tag 0ETE](https://stacks.math.columbia.edu/tag/0ETE)
* [Stacks Project, Tag 0ETF](https://stacks.math.columbia.edu/tag/0ETF)
* [Stacks Project, Tag 0ETG](https://stacks.math.columbia.edu/tag/0ETG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- An injective local homomorphism between valuation rings exhibits its target as an
extension of its source.  This is the map-based form of an extension of valuation rings
from [Stacks Project, Tag 0ASG]. -/
public abbrev IsExtensionOfValuationRings {V W : Type*} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing W] [IsDomain W] [ValuationRing W] (e : V →+* W) : Prop :=
  Function.Injective e ∧ IsLocalHom e

/-- A finite family of morphisms from affine schemes to an affine scheme is a **standard V
covering** if every morphism from the spectrum of a valuation ring lifts to one member
after an extension of valuation rings. -/
@[stacks 0ETB]
public def IsStandardVCovering {T : Scheme.{u}} [IsAffine T] {I : Type v} [Finite I]
    (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ T) : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (g : Spec (.of V) ⟶ T),
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W) (e : V →+* W),
      IsExtensionOfValuationRings e ∧
        ∃ (i : I) (h : Spec (.of W) ⟶ X i),
          Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f i

/-- The lifting-property characterization of a standard V covering. -/
public theorem isStandardVCovering_iff {T : Scheme.{u}} [IsAffine T] {I : Type v}
    [Finite I] (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ T) :
    IsStandardVCovering X f ↔
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] (g : Spec (.of V) ⟶ T),
        ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
          (e : V →+* W),
          IsExtensionOfValuationRings e ∧
            ∃ (i : I) (h : Spec (.of W) ⟶ X i),
              Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ f i :=
  Iff.rfl

/-- A standard V covering of an affine scheme remains a standard V covering after pullback
along a morphism from another affine scheme. -/
@[stacks 0ETE]
public lemma isStandardVCovering_pullback
    {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    {I : Type v} [Finite I] (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    (f : ∀ i, X i ⟶ T) (g : T' ⟶ T)
    (hf : IsStandardVCovering X f) :
    IsStandardVCovering (fun i ↦ pullback (f i) g)
      (fun i ↦ pullback.snd (f i) g) := by
  intro V _ _ _ g'
  obtain ⟨W, _, _, _, e, he, i, h, hh⟩ := hf V (g' ≫ g)
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, he, i,
    pullback.lift h (Spec.map (CommRingCat.ofHom e) ≫ g') (by simpa [Category.assoc] using hh.symm),
    by simp only [pullback.lift_snd]⟩

/-- Composing a standard V covering with a standard V covering of each member gives a
standard V covering. -/
@[stacks 0ETF]
public lemma IsStandardVCovering.comp
    {T : Scheme.{u}} [IsAffine T]
    {J : Type v} [Finite J] (X : J → Scheme.{u}) [∀ j, IsAffine (X j)]
    (f : ∀ j, X j ⟶ T) (hf : IsStandardVCovering X f)
    {I : J → Type w} [∀ j, Finite (I j)]
    (Y : ∀ j, I j → Scheme.{u}) [∀ j i, IsAffine (Y j i)]
    (g : ∀ j i, Y j i ⟶ X j)
    (hg : ∀ j, IsStandardVCovering (Y j) (g j)) :
    IsStandardVCovering (fun ji : Σ j, I j ↦ Y ji.1 ji.2)
      (fun ji ↦ g ji.1 ji.2 ≫ f ji.1) := by
  intro V _ _ _ g₀
  obtain ⟨W, _, _, _, e, he, j, h, hcomm⟩ := hf V g₀
  obtain ⟨Ω, _, _, _, e', he', i, k, hk⟩ := hg j W h
  have : IsLocalHom e := he.2
  have : IsLocalHom e' := he'.2
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, e'.comp e,
    ⟨he'.1.comp he.1, RingHom.isLocalHom_comp _ _⟩, ⟨j, i⟩, k, ?_⟩
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hcomm, ← Category.assoc, hk,
    Category.assoc]

private lemma exists_factor_sigma_of_localRing
    {I : Type v} [Finite I] (X : I → Scheme.{u})
    (W : Type u) [CommRing W] [IsLocalRing W] (h : Spec (.of W) ⟶ ∐ X) :
    ∃ (i : I) (h' : Spec (.of W) ⟶ X i), h' ≫ Sigma.ι X i = h := by
  obtain ⟨J, ⟨e⟩⟩ := Small.equiv_small.{u} (α := I)
  let Y : J → Scheme.{u} := X ∘ e.symm
  let φ := Sigma.reindex e.symm X
  let h₀ := h ≫ φ.inv
  let z : Σ j, Y j := (sigmaMk Y).symm (h₀ (IsLocalRing.closedPoint W))
  have hrange : Set.range h₀ ⊆ (Sigma.ι Y z.1).opensRange := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map h₀.continuous).mem_open
      (Sigma.ι Y z.1).opensRange.2 ⟨z.2, by simpa [h₀, z] using (sigmaMk_mk Y z.1 z.2).symm⟩
  let h' := IsOpenImmersion.lift (Sigma.ι Y z.1) h₀ hrange
  have hh' : h' ≫ Sigma.ι Y z.1 = h ≫ φ.inv := IsOpenImmersion.lift_fac _ _ _
  refine ⟨e.symm z.1, h', ?_⟩
  rw [← Sigma.ι_reindex_hom e.symm X z.1, ← Category.assoc, hh']
  simp [φ, Category.assoc]

/-- A finite family of affine schemes over an affine scheme is a standard V covering if and only
if it admits a refining standard V covering, if and only if the morphism from the disjoint union
of the family is a standard V covering. -/
@[stacks 0ETG]
public theorem isStandardVCovering_tfae {T : Scheme.{u}} [IsAffine T]
    {I : Type v} [Finite I] (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    (f : ∀ i, X i ⟶ T) :
    List.TFAE [
      IsStandardVCovering X f,
      ∃ (K : Type v) (_ : Finite K) (Y : K → Scheme.{u}) (_ : ∀ k, IsAffine (Y k))
          (g : ∀ k, Y k ⟶ T),
        IsStandardVCovering Y g ∧
          Nonempty
            (({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
              ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)),
      IsStandardVCovering
        (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f)] := by
  tfae_have 1 → 2 := fun hf ↦ ⟨I, inferInstance, X, inferInstance, f, hf, ⟨.id _⟩⟩
  tfae_have 2 → 1 := by
    rintro ⟨K, _, Y, _, g, hg, ⟨r⟩⟩ V _ _ _ a
    obtain ⟨W, _, _, _, e, he, k, h, hw⟩ := hg V a
    exact ⟨W, inferInstance, inferInstance, inferInstance, e, he, r.s₀ k,
      h ≫ r.h₀ k, by rw [Category.assoc, r.w₀, hw]⟩
  tfae_have 1 → 3 := by
    intro hf V _ _ _ g
    obtain ⟨W, _, _, _, e, he, i, h, hw⟩ := hf V g
    exact ⟨W, inferInstance, inferInstance, inferInstance, e, he, (),
      h ≫ Sigma.ι X i, by simpa [Category.assoc] using hw⟩
  tfae_have 3 → 1 := by
    intro hf V _ _ _ g
    obtain ⟨W, _, _, _, e, he, _, h, hw⟩ := hf V g
    obtain ⟨i, h', hh'⟩ := exists_factor_sigma_of_localRing X W h
    exact ⟨W, inferInstance, inferInstance, inferInstance, e, he, i, h',
      by simpa [← hh', Category.assoc] using hw⟩
  tfae_finish

end AlgebraicGeometry
