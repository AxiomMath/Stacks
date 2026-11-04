module

public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksCore.Tactic.StacksAttribute

/-!
# Ph coverings

A family of morphisms of schemes is a ph covering when each member is locally of finite
type and, over every affine open of the target, the pullback of the family is refined by a
standard ph covering. Isomorphisms and proper surjections are ph coverings.

## Main definitions

* `AlgebraicGeometry.IsPHCovering`: the predicate that a family of morphisms of schemes is
  a ph covering.

## Main results

* `AlgebraicGeometry.isPHCovering_of_isIso`: a singleton family consisting of an
  isomorphism is a ph covering.
* `AlgebraicGeometry.surjective_proper_isPHCovering`: a proper surjection is a ph covering
  by itself.
* `AlgebraicGeometry.isPHCovering_pullback_of_forall_exists_isAffineOpen` and
  `AlgebraicGeometry.isPHCovering_pullback_of_isAffine`: a ph covering stays a ph covering
  under base change along a morphism each of whose affine opens maps into an affine open of
  the target, in particular along any morphism to an affine scheme.

## Implementation notes

The definition is affine-local on the target: the refinement is required over each affine
open `U` of `T`, where the family is pulled back along `U.ι` and compared with a standard
ph covering of `U` by a morphism of pre-zero-hypercovers. Singleton families are indexed
by `Unit`.

The two base change statements are the special cases of Stacks 0DBI part (3) that need no
refinement of a composite of two standard ph coverings, and neither is tagged with Stacks 0DBI.
Part (3) in general, and with it part (2), are `AlgebraicGeometry.isPHCovering_pullback` and
`AlgebraicGeometry.isPHCovering_bind` in
`StacksFrontier.AlgebraicGeometry.Topologies.Ph.CoveringsParts0DBI`, which collapse the two-step
covering with Stacks 0DBF part (2), `AlgebraicGeometry.exists_standardPHCovering_refinement_bind`.

## References

* [Stacks Project, Tag 0DBG](https://stacks.math.columbia.edu/tag/0DBG)
* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0DES](https://stacks.math.columbia.edu/tag/0DES)
-/
@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0DBG.** A family `{X i ⟶ T}` is a **ph covering** if every member is locally
of finite type and, over every affine open `U` of `T`, a standard ph covering of
`U.toScheme` refines the pullback of the family to `U`. -/
@[stacks 0DBG]
public noncomputable def IsPHCovering {T : Scheme.{u}}
    {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) : Prop :=
  (∀ i, LocallyOfFiniteType (f i)) ∧ ∀ (U : T.Opens) (hU : IsAffineOpen U),
    ∃ 𝒰 : PreZeroHypercover.{u} U.toScheme,
      @StandardPHCovering 𝒰.I₀ U.toScheme hU 𝒰.X 𝒰.f ∧
        Nonempty (𝒰.Hom
          (({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T).pullback₂ U.ι))

/-- The affine-local characterization of a ph covering. -/
public theorem isPHCovering_iff {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    IsPHCovering X f ↔ (∀ i, LocallyOfFiniteType (f i)) ∧
      ∀ (U : T.Opens) (hU : IsAffineOpen U), ∃ 𝒰 : PreZeroHypercover.{u} U.toScheme,
        @StandardPHCovering 𝒰.I₀ U.toScheme hU 𝒰.X 𝒰.f ∧
          Nonempty (𝒰.Hom
            (({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T).pullback₂ U.ι)) :=
  Iff.rfl

/-- A singleton family consisting of a proper surjection is a ph covering. -/
private theorem isPHCovering_singleton_of_surjective_of_isProper {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Surjective f] [IsProper f] :
    IsPHCovering (fun _ : Unit ↦ Y) (fun _ ↦ f) := by
  rw [isPHCovering_iff]
  refine ⟨fun _ ↦ inferInstance, ?_⟩
  intro U hU
  classical
  have : IsAffine U.toScheme := hU
  let P := Limits.pullback f U.ι
  let p : P ⟶ U.toScheme := Limits.pullback.snd f U.ι
  have : CompactSpace P := (quasiCompact_iff_compactSpace p).mp (by infer_instance)
  let A := P.affineCover.finiteSubcover
  let 𝒰 : PreZeroHypercover U.toScheme := ⟨A.I₀, A.X, fun i ↦ A.f i ≫ p⟩
  exact ⟨𝒰, StandardPHCovering.of_presentation 𝒰.f
    (hX := fun _ ↦ inferInstance) p A.f (by infer_instance) (by infer_instance)
    (fun _ ↦ inferInstance) A.iUnion_range (fun _ ↦ rfl),
    ⟨⟨fun _ ↦ (), fun i ↦ A.f i, fun _ ↦ rfl⟩⟩⟩

/-- **Stacks 0DBI.** A singleton isomorphism is a ph covering of schemes. -/
@[stacks 0DBI "isomorphisms"]
public theorem isPHCovering_of_isIso {T' T : Scheme.{u}} (f : T' ⟶ T) [IsIso f] :
    IsPHCovering (fun _ : Unit ↦ T') (fun _ ↦ f) :=
  isPHCovering_singleton_of_surjective_of_isProper f

/-- **Stacks 0DES.** A proper surjection of schemes is a ph covering. -/
@[stacks 0DES]
public theorem surjective_proper_isPHCovering {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Surjective f] [IsProper f] :
    IsPHCovering (fun _ : Unit ↦ Y) (fun _ ↦ f) :=
  isPHCovering_singleton_of_surjective_of_isProper f

/-- **The confined case of Stacks 0DBI part (3).** Let `{X i ⟶ T}` be a ph covering and let
`g : T' ⟶ T` be a morphism with the property that every affine open of `T'` is mapped by `g`
into some affine open of `T`. Then the base change `{X i ×_T T' ⟶ T'}` is a ph covering.

This is a special case of Stacks 0DBI part (3), `AlgebraicGeometry.isPHCovering_pullback`. -/
public theorem isPHCovering_pullback_of_forall_exists_isAffineOpen {T T' : Scheme.{u}}
    {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsPHCovering X f) (g : T' ⟶ T)
    (hg : ∀ U' : T'.Opens, IsAffineOpen U' →
      ∃ U : T.Opens, IsAffineOpen U ∧ Set.range (U'.ι ≫ g).base ⊆ (U : Set T)) :
    IsPHCovering (fun i ↦ Limits.pullback (f i) g)
      (fun i ↦ Limits.pullback.snd (f i) g) := by
  refine ⟨fun i ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (f i) g) (hf.1 i), fun U' hU' ↦ ?_⟩
  obtain ⟨U, hU, hsub⟩ := hg U' hU'
  have : IsAffine U.toScheme := hU
  have : IsAffine U'.toScheme := hU'
  have hr : Set.range (U'.ι ≫ g).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hsub
  let h : U'.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι (U'.ι ≫ g) hr
  have hfac : h ≫ U.ι = U'.ι ≫ g := IsOpenImmersion.lift_fac _ _ hr
  obtain ⟨𝒰, hstd, ⟨ρ⟩⟩ := hf.2 U hU
  have hρ : ∀ a, ∃ (i : I) (ψ : 𝒰.X a ⟶ Limits.pullback (f i) U.ι),
      ψ ≫ Limits.pullback.snd (f i) U.ι = 𝒰.f a :=
    fun a ↦ ⟨ρ.s₀ a, ρ.h₀ a, ρ.w₀ a⟩
  choose idx ψ hψ using hρ
  have key : ∀ a, ∃ φ : Limits.pullback (𝒰.f a) h ⟶
      Limits.pullback (Limits.pullback.snd (f (idx a)) g) U'.ι,
      φ ≫ Limits.pullback.snd (Limits.pullback.snd (f (idx a)) g) U'.ι =
        Limits.pullback.snd (𝒰.f a) h := by
    intro a
    have hc : Limits.pullback.fst (f (idx a)) U.ι ≫ f (idx a) =
        Limits.pullback.snd (f (idx a)) U.ι ≫ U.ι := Limits.pullback.condition
    have hc' : Limits.pullback.fst (𝒰.f a) h ≫ 𝒰.f a =
        Limits.pullback.snd (𝒰.f a) h ≫ h := Limits.pullback.condition
    have hq : (Limits.pullback.fst (𝒰.f a) h ≫ ψ a ≫
        Limits.pullback.fst (f (idx a)) U.ι) ≫ f (idx a) =
        (Limits.pullback.snd (𝒰.f a) h ≫ U'.ι) ≫ g := by
      simp only [Category.assoc, hc]
      rw [← Category.assoc (ψ a), hψ a, ← Category.assoc, hc', Category.assoc, hfac]
    exact ⟨Limits.pullback.lift (Limits.pullback.lift _ _ hq)
      (Limits.pullback.snd (𝒰.f a) h) (Limits.pullback.lift_snd _ _ hq),
      Limits.pullback.lift_snd _ _ _⟩
  choose φ hφ using key
  exact ⟨⟨𝒰.I₀, fun a ↦ Limits.pullback (𝒰.f a) h,
    fun a ↦ Limits.pullback.snd (𝒰.f a) h⟩, hstd.pullback h, ⟨⟨idx, φ, hφ⟩⟩⟩

/-- **Stacks 0DBI part (3) over an affine target.** The base change of a ph covering of an
affine scheme along an arbitrary morphism of schemes is a ph covering.

This is a special case of Stacks 0DBI part (3), `AlgebraicGeometry.isPHCovering_pullback`, which
makes no affineness assumption on the target. -/
public theorem isPHCovering_pullback_of_isAffine {T T' : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsPHCovering X f) (g : T' ⟶ T) :
    IsPHCovering (fun i ↦ Limits.pullback (f i) g)
      (fun i ↦ Limits.pullback.snd (f i) g) :=
  isPHCovering_pullback_of_forall_exists_isAffineOpen hf g fun _ _ ↦
    ⟨⊤, isAffineOpen_top T, by simp⟩

end AlgebraicGeometry
