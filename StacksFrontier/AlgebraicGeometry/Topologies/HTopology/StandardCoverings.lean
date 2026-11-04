module

public import StacksFrontier.AlgebraicGeometry.Topologies.H.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.Refinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementBind
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard h coverings of an affine scheme

Over an affine scheme the affine-local condition defining a ph covering collapses to a
single refinement condition over the whole base, because every affine open of the base is
obtained from the base itself by a base change and the base itself is one of the affine opens
tested.  Consequently a standard h covering of an affine scheme — a finite family of
morphisms of finite presentation from affine schemes which is refined by a standard ph
covering — is exactly a finite family of morphisms of finite presentation from affine schemes
which is an h covering.

## Main results

* `AlgebraicGeometry.isPHCovering_iff_exists_standardPHCovering_refinement`: over an affine
  scheme a family is a ph covering exactly when it consists of morphisms locally of finite
  type and is refined by a standard ph covering of the base.
* `AlgebraicGeometry.isStandardHCovering_iff_isHCovering`: the characterization of standard h
  coverings as finite h coverings of affine schemes by affine schemes.
* `AlgebraicGeometry.IsStandardHCovering.isHCovering` and
  `AlgebraicGeometry.isStandardHCovering_of_isHCovering`: the two implications separately.
* `AlgebraicGeometry.IsStandardHCovering.reindex`: reindexing a standard h covering along an
  equivalence of index types gives a standard h covering.

## Implementation notes

The refining standard ph covering lives in the scheme universe, while the family itself is
indexed in an independent universe; this is the convention of
`AlgebraicGeometry.IsPHCovering` and `AlgebraicGeometry.IsStandardHCovering`.

Testing the base itself means testing the affine open `⊤`, whose associated scheme is only
isomorphic — not equal — to the base; the refinement obtained there is therefore pushed
forward along the inclusion of `⊤`, which is a proper surjection because
`AlgebraicGeometry.Scheme.topIso` makes it an isomorphism.  In the other direction the
refining covering is base changed along the inclusion of an affine open, where
`AlgebraicGeometry.StandardPHCovering.pullback` applies.

## References

* [Stacks Project, Tag 0DBG](https://stacks.math.columbia.edu/tag/0DBG)
* [Stacks Project, Tag 0EUY](https://stacks.math.columbia.edu/tag/0EUY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- Over an affine scheme `T`, a family of morphisms is a ph covering precisely when its
members are locally of finite type and some standard ph covering of `T` itself refines it.
This is the affine-base form of the definition of Stacks 0DBG, whose refinement condition is
imposed over every affine open of the target. -/
public theorem isPHCovering_iff_exists_standardPHCovering_refinement {T : Scheme.{u}}
    [IsAffine T] {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    IsPHCovering X f ↔ (∀ i, LocallyOfFiniteType (f i)) ∧
      ∃ 𝒰 : PreZeroHypercover.{u} T, StandardPHCovering 𝒰.f ∧
        Nonempty (𝒰.Hom ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T)) := by
  rw [isPHCovering_iff]
  refine and_congr_right' ⟨fun h ↦ ?_, fun h U hU ↦ ?_⟩
  · obtain ⟨𝒱, h𝒱, ⟨ψ⟩⟩ := h ⊤ (isAffineOpen_top T)
    have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
    have hiso : IsIso (⊤ : T.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    exact ⟨𝒱.pushforward (⊤ : T.Opens).ι,
      StandardPHCovering.comp h𝒱 inferInstance inferInstance,
      ⟨(ψ.pushforward (⊤ : T.Opens).ι).comp
        (PreZeroHypercover.pullback₂PushforwardHom (⊤ : T.Opens).ι _)⟩⟩
  · obtain ⟨𝒰, h𝒰, ⟨φ⟩⟩ := h
    have : IsAffine U.toScheme := hU
    exact ⟨𝒰.pullback₂ U.ι, StandardPHCovering.pullback h𝒰 U.ι, ⟨φ.pullback₂ U.ι⟩⟩

/-- A standard h covering of an affine scheme is exactly a finite family of morphisms of
finite presentation from affine schemes which is an h covering. -/
public theorem isStandardHCovering_iff_isHCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T) :
    IsStandardHCovering f ↔ Finite I ∧ (∀ i, IsAffine (X i)) ∧
      (∀ i, FinitePresentation (f i)) ∧ IsHCovering X f := by
  constructor
  · rintro ⟨hfin, haff, hfp, hrefine⟩
    refine ⟨hfin, haff, hfp, fun i ↦ (hfp i).1, ?_⟩
    refine (isPHCovering_iff_exists_standardPHCovering_refinement X f).2 ⟨fun i ↦ ?_, hrefine⟩
    have := (hfp i).1
    infer_instance
  · rintro ⟨hfin, haff, hfp, hh⟩
    exact ⟨hfin, haff, hfp,
      ((isPHCovering_iff_exists_standardPHCovering_refinement X f).1 hh.2).2⟩

/-- A standard h covering is an h covering. -/
public theorem IsStandardHCovering.isHCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (h : IsStandardHCovering f) :
    IsHCovering X f :=
  ((isStandardHCovering_iff_isHCovering f).1 h).2.2.2

/-- Reindexing a standard h covering along an equivalence of its index type gives a standard
h covering. -/
public theorem IsStandardHCovering.reindex {T : Scheme.{u}} [IsAffine T]
    {E : PreZeroHypercover.{v} T} (hE : IsStandardHCovering E.f) {ι : Type w}
    (e : ι ≃ E.I₀) : IsStandardHCovering (E.reindex e).f := by
  obtain ⟨hfin, haff, hfp, 𝒲, h𝒲, ⟨φ⟩⟩ := hE
  have : Finite E.I₀ := hfin
  exact ⟨Finite.of_equiv E.I₀ e.symm, fun i ↦ haff (e i), fun i ↦ hfp (e i), 𝒲, h𝒲,
    ⟨φ.comp (PreZeroHypercover.Hom.toReindex E e)⟩⟩

/-- A finite h covering of an affine scheme by affine schemes along morphisms of finite
presentation is a standard h covering. -/
public theorem isStandardHCovering_of_isHCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hfin : Finite I) (haff : ∀ i, IsAffine (X i))
    (hfp : ∀ i, FinitePresentation (f i)) (hh : IsHCovering X f) :
    IsStandardHCovering f :=
  (isStandardHCovering_iff_isHCovering f).2 ⟨hfin, haff, hfp, hh⟩

end AlgebraicGeometry
