module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting

/-!
# The infinitesimal lifting criterion for smoothness at a point, unconditionally

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `x` be a point of `X`. Then `f` is smooth at `x`
exactly when every lifting problem at `x` along a surjection of local rings with square-zero
kernel has a solution, and exactly when every lifting problem at `x` along a small extension has
a solution. This is Stacks 0APN.

## Main results

* `AlgebraicGeometry.Space.FormallySmooth.liftsAt`: a formally smooth morphism of algebraic
  spaces has the lifting property at every point against every class of square-zero surjections
  of local rings.
* `AlgebraicGeometry.Space.IsSmoothAt.liftsAt`: **Stacks 0APN, (1) implies (2) and (3).** A
  morphism smooth at a point has the lifting property at that point.
* `AlgebraicGeometry.Space.tfae_isSmoothAt_liftsAt`: **Stacks 0APN**, the equivalence of the
  three conditions.

## Implementation notes

The implication from smoothness at `x` uses the formal smoothness of a smooth morphism of
algebraic spaces, Stacks 04AM, which is `AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`
and carries no hypothesis beyond smoothness. Smoothness at `x` gives an open subspace containing
`x` on which `f` is smooth; a section over the spectrum of a local ring whose closed point lies
over `x` factors through that open subspace, because the closed point specializes from every
point; and the restricted lifting problem is solved by formal smoothness. The implications from
the square-zero condition to the small-extension condition and from the small-extension
condition to smoothness at `x` are `AlgebraicGeometry.Space.LiftsAt.mono` and
`AlgebraicGeometry.Space.isSmoothAt_of_liftsAt_isSmallExtension`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A formally smooth morphism of algebraic spaces has the lifting property at every point of
its source, against every class of square-zero surjections of local rings: the test spectra
are affine and the closed immersion between them is square-zero, so the lifting problem is one
of the lifting problems in the definition of formal smoothness. -/
theorem FormallySmooth.liftsAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (hformal : FormallySmooth f)
    (x : points B S hS X)
    (extension : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop)
    (hextension : ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
      extension φ → InfinitesimalLifting.IsSquareZeroSurjection φ) :
    LiftsAt B S hS f x extension := by
  intro R' R φ hφ T T' i e e' hi hRloc _p _ α β _ hcomm
  have := hRloc
  have hsq : InfinitesimalLifting.IsSquareZeroSurjection φ := hextension φ hφ
  have hsite : IsSquareZeroClosedImmersion B S hS i :=
    isSquareZeroClosedImmersion_of_specMap B S hS φ hsq.2.2.1 hsq.2.2.2 T T' i e e' hi
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := IsAffine.of_isIso e'.hom
  have hab : f.app (op T) (yonedaEquiv α) = Y.map i.op (yonedaEquiv β) := by
    calc
      f.app (op T) (yonedaEquiv α) = yonedaEquiv (α ≫ f) := (yonedaEquiv_comp α f).symm
      _ = yonedaEquiv (yoneda.map i ≫ β) := congrArg yonedaEquiv hcomm
      _ = Y.map i.op (yonedaEquiv β) := (yonedaEquiv_naturality β i).symm
  obtain ⟨z, hz⟩ := hformal T T' ‹_› ‹_› i hsite (yonedaEquiv α) (yonedaEquiv β) hab
  refine ⟨yonedaEquiv.symm z, ?_, ?_⟩
  · apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality (yonedaEquiv.symm z) i]
    simpa using hz.1
  · apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hz.2

/-- **Stacks 0APN, (1) implies (2) and (3).** A morphism of algebraic spaces over `S` which is
smooth at a point of its source has the lifting property at that point against every class of
square-zero surjections of local rings.

Smoothness at the point gives an open subspace of the source containing it on which the
morphism is smooth, hence formally smooth by Stacks 04AM
(`AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`); the spectrum of a local ring whose
closed point lies over the given point factors through that open subspace, because the closed
point specializes from every point, so the lifting problem is a lifting problem for the
restricted morphism. -/
@[stacks 0APN "condition (1) implies conditions (2) and (3)", sga "3 XI 1.5" "partial"]
theorem IsSmoothAt.liftsAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} {x : points B S hS X}
    (hsm : IsSmoothAt B S hS f x)
    (extension : ∀ ⦃R' R : CommRingCat.{u}⦄, (R' ⟶ R) → Prop)
    (hextension : ∀ ⦃R' R : CommRingCat.{u}⦄ (φ : R' ⟶ R),
      extension φ → InfinitesimalLifting.IsSquareZeroSurjection φ) :
    LiftsAt B S hS f x extension := by
  obtain ⟨U, hU, x', hx', hsmU⟩ := hsm
  have hformal : FormallySmooth (U.ι ≫ f) := formallySmooth_of_isSmooth' hU.1 hY hsmU
  intro R' R φ hφ T T' i e e' hi hRloc p hp α β hpx hcomm
  have := hRloc
  -- The closed point specializes from every point of `Spec R`, so the whole spectrum lands in
  -- the open set of points of `U`, and `α` factors through `U`.
  have hfactor : ∃ α' : yoneda.obj T ⟶ U.toFunctor, α' ≫ U.ι = α := by
    let W : Set (points B S hS X) := Set.range (pointsMap B S hS U.toFunctor U.ι)
    have hW : IsOpen W := by
      have h := (openSubspacesOrderIso B S hS X hX ⟨U, hU⟩).2
      rwa [openSubspacesOrderIso_apply B S hS X hX ⟨U, hU⟩] at h
    let D : Set (points B S hS (yoneda.obj T)) := pointsMap B S hS (yoneda.obj T) α ⁻¹' W
    have hD : IsOpen D := (continuous_pointsMap B S hS α).isOpen_preimage W hW
    obtain ⟨V, hV, hVspec⟩ := (isOpen_yoneda_iff_isSchemeOpen B S hS T D).mp hD
    have hclosed : schemePoint B S hS T p ∈ V := by
      refine (hVspec p).mp ?_
      change pointsMap B S hS (yoneda.obj T) α (p.class B S hS (yoneda.obj T)) ∈ W
      rw [hpx]
      exact ⟨x', hx'⟩
    have hspec : ∀ z : (BigFppfOver.toScheme B S hS).obj T,
        z ⤳ schemePoint B S hS T p := by
      intro z
      have h₀ := IsLocalRing.specializes_closedPoint (e.hom.base z)
      have h₁ := h₀.map (f := e.inv.base) e.inv.continuous
      have hz : e.inv.base (e.hom.base z) = z := by simp
      simpa [hz, hp] using h₁
    refine (factorsThrough_openSubspace_iff_points B S hS hX
      (isAlgebraicSpace_yoneda B S hS T) U hU α).2 ?_
    rintro _ ⟨y₀, rfl⟩
    induction y₀ using Quot.inductionOn with
    | h q => exact (hVspec q).mpr ((hspec _).mem_open hV hclosed)
  obtain ⟨αU, hαU⟩ := hfactor
  obtain ⟨γU, hγU⟩ := hformal.liftsAt B S hS
    (pointsMap B S hS (yoneda.obj T) αU (p.class B S hS (yoneda.obj T)))
    extension hextension φ hφ T T' i e e' hi p hp αU β rfl
    (by rwa [← Category.assoc, hαU])
  refine ⟨γU ≫ U.ι, ?_, ?_⟩
  · rw [← Category.assoc, hγU.1, hαU]
  · simpa only [Category.assoc] using hγU.2

/-- **Stacks 0APN.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, with `Y` locally Noetherian, and let `x` be a point of `X`. Then the
following are equivalent: `f` is smooth at `x`; every lifting problem at `x` along a surjection
of local rings with square-zero kernel has a solution; every lifting problem at `x` along a
small extension has a solution.

The implication from (1) to (2) is `AlgebraicGeometry.Space.IsSmoothAt.liftsAt`, from (2) to
(3) is `AlgebraicGeometry.Space.LiftsAt.mono` and from (3) to (1) is
`AlgebraicGeometry.Space.isSmoothAt_of_liftsAt_isSmallExtension`. -/
@[stacks 0APN, sga "3 XI 1.5" "partial"]
theorem tfae_isSmoothAt_liftsAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hFiniteType : IsLocallyOfFiniteType B S hS f) :
    [IsSmoothAt B S hS f x,
      LiftsAt B S hS f x fun ⦃_ _⦄ φ => InfinitesimalLifting.IsSquareZeroSurjection φ,
      LiftsAt B S hS f x fun ⦃_ _⦄ φ =>
        InfinitesimalLifting.IsSmallExtension φ].TFAE := by
  tfae_have 1 → 2 := fun hsm => hsm.liftsAt B S hS hX hY _ fun _ _ _ hφ => hφ
  tfae_have 2 → 3 := fun h =>
    LiftsAt.mono B S hS (fun _ _ φ hφ =>
      InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ) h
  tfae_have 3 → 1 := fun h =>
    isSmoothAt_of_liftsAt_isSmallExtension B S hS hX hY f x hNoeth hFiniteType h
  tfae_finish

end AlgebraicGeometry.Space

end
