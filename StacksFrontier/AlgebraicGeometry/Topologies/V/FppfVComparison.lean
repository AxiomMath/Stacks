module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfPhComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhComparison

/-!
# Flat V coverings are fppf coverings, and hence ph coverings

This file proves the last paragraph of the Stacks proof of 0ETR: once the members of a V
covering are known to be flat and locally of finite presentation, the covering is an fppf
covering, and therefore a ph covering.

The one fact needed for this is that the members of a V covering are jointly surjective.
It follows from the lifting property against spectra of valuation rings by taking the
valuation ring to be the residue field of the point one wants to hit: a field is a valuation
ring, so a standard V covering must lift `Spec κ(t) ⟶ T` through one of its members, and the
image of any point of the lift is `t`.

Combined with `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage`, this discharges the
*flat* case of the hypothesis
`AlgebraicGeometry.StandardVCoveringHasPHRefinement` that
`AlgebraicGeometry.isPHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement` carries,
modulo the weak form of Stacks 0CP0 isolated as
`AlgebraicGeometry.FppfHasFiniteDomination`. The rest of that hypothesis is the flattening
step — the reduction of an arbitrary standard V covering by finitely presented affines to a
flat one, which in the Stacks Project goes through a generic flatness stratification of the
base (Stacks 0H3Z) and the Raynaud-Gruson flattening theorem for an admissible blowup
(Stacks 0815, 080Y) — and that step is carried out in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`, so the predicate
holds in full. What this file contributes is the shorter route in the flat case.

## Main results

* `AlgebraicGeometry.IsStandardVCovering.exists_mem_range`: the members of a standard V
  covering are jointly surjective.
* `AlgebraicGeometry.IsVCovering.exists_mem_range`: the members of a V covering are jointly
  surjective.
* `AlgebraicGeometry.StandardPHCovering.comp_isIso`: standard ph coverings transport along an
  isomorphism of the base.
* `AlgebraicGeometry.mem_fppfPrecoverage_of_isVCovering`: a V covering whose members are flat
  and locally of finite presentation is an fppf covering.
* `AlgebraicGeometry.isPHCovering_of_isVCovering_of_flat` and
  `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_flat`: granted
  `AlgebraicGeometry.FppfHasFiniteDomination`, the flat case of Stacks 0ETR.
* `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flat`: granted the same, the flat
  case of `AlgebraicGeometry.StandardVCoveringHasPHRefinement`, in the shape that hypothesis
  itself has.

## Implementation notes

Joint surjectivity is *not* the content of a Stacks tag on its own. It is a strict
consequence of Stacks 0ETP, which says that a V covering is universally submersive, so
nothing here is tagged with 0ETP either. Likewise the flat case of Stacks 0ETR is not Stacks
0ETR, so `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_flat` carries no tag; 0ETR itself
is registered on `AlgebraicGeometry.isPHCovering_iff_isVCovering` in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`.

The valuation ring used for joint surjectivity is written
`IsLocalRing.ResidueField (T.presheaf.stalk t)` rather than `T.residueField t`. The two are
the same type, but `AlgebraicGeometry.Scheme.residueField` is a bundled `CommRingCat`, and
the `CommRing` instance found on its carrier is the bundled one, through which the `Field`
instance — and hence `IsDomain` and `ValuationRing` — is not found. Writing the unbundled
type makes all three instances resolve.

Points of a composite are read with `AlgebraicGeometry.Scheme.Hom.comp_apply` as a term,
chained with `Eq.trans`, rather than by `rw`: the two spellings of the application of a
composite are definitionally but not syntactically equal, so `rw` reports that it cannot find
a pattern which the goal visibly contains.

## References

* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0ETP](https://stacks.math.columbia.edu/tag/0ETP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- Equal composites of morphisms of schemes agree on points. -/
private theorem apply_apply_eq_of_comp_eq {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ W}
    {c : X ⟶ Z} {d : Z ⟶ W} (h : a ≫ b = c ≫ d) (x : X) : b (a x) = d (c x) :=
  (Scheme.Hom.comp_apply a b x).symm.trans
    ((congrArg (fun k : X ⟶ W => k x) h).trans (Scheme.Hom.comp_apply c d x))

/-- The members of a standard V covering are jointly surjective.

Given `t` in the base, the residue field `κ(t)` is a valuation ring, so the canonical morphism
`Spec κ(t) ⟶ T` lifts, after an extension of valuation rings `κ(t) ⊆ W`, to some member of the
family. The image of any point of `Spec W` under that lift is then a preimage of `t`. -/
theorem IsStandardVCovering.exists_mem_range {T : Scheme.{u}} [IsAffine T] {I : Type v}
    [Finite I] {X : I → Scheme.{u}} [∀ i, IsAffine (X i)] {f : ∀ i, X i ⟶ T}
    (hf : IsStandardVCovering X f) (t : T) : ∃ i, t ∈ Set.range (f i).base := by
  obtain ⟨W, _, _, _, e, _, i, h, hcomm⟩ :=
    hf (IsLocalRing.ResidueField (T.presheaf.stalk t)) (T.fromSpecResidueField t)
  refine ⟨i, h (IsLocalRing.closedPoint W), ?_⟩
  exact (apply_apply_eq_of_comp_eq hcomm.symm _).trans (Scheme.fromSpecResidueField_apply t _)

/-- The members of a V covering are jointly surjective.

An affine open `U` containing the given point carries a standard V covering refining the
pullback of the family to `U`; that covering hits the point by
`AlgebraicGeometry.IsStandardVCovering.exists_mem_range`, and the first projection of the
fibre product carries the witness back to a member of the original family. -/
theorem IsVCovering.exists_mem_range {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (hV : IsVCovering X f) (t : T) : ∃ i, t ∈ Set.range (f i).base := by
  obtain ⟨U, hU, htU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := T) (x := t) (U := ⊤) (Opens.mem_top t)
  obtain ⟨𝒰, hfinite, haffine, hstd, ⟨ρ⟩⟩ := hV U hU
  have : IsAffine U.toScheme := hU
  have : Finite 𝒰.I₀ := hfinite
  have : ∀ j, IsAffine (𝒰.X j) := haffine
  obtain ⟨j, p, hp⟩ := hstd.exists_mem_range (⟨t, htU⟩ : U.toScheme)
  refine ⟨ρ.s₀ j, pullback.fst (f (ρ.s₀ j)) U.ι (ρ.h₀ j p), ?_⟩
  have hsnd : pullback.snd (f (ρ.s₀ j)) U.ι (ρ.h₀ j p) = (⟨t, htU⟩ : U.toScheme) :=
    ((Scheme.Hom.comp_apply _ _ _).symm.trans
      (congrArg (fun k : 𝒰.X j ⟶ U.toScheme => k p) (ρ.w₀ j))).trans hp
  exact (apply_apply_eq_of_comp_eq pullback.condition (ρ.h₀ j p)).trans
    (congrArg (fun y : U.toScheme => U.ι y) hsnd)

/-- A standard ph covering stays one after composing every member with an isomorphism of the
base, presented by the same proper surjection composed with that isomorphism. -/
theorem StandardPHCovering.comp_isIso {ι : Type v} {T T' : Scheme.{u}} [IsAffine T]
    [IsAffine T'] {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : StandardPHCovering f)
    (e : T ⟶ T') [IsIso e] : StandardPHCovering fun i ↦ f i ≫ e := by
  obtain ⟨P, g, j, hg, hgsurj, hj, hcover, hcomp⟩ := hf.exists_presentation
  have : Finite ι := hf.finite
  have : IsProper g := hg
  have : Surjective g := hgsurj
  exact StandardPHCovering.of_presentation _ hf.isAffine (g ≫ e) j inferInstance inferInstance
    hj hcover fun i ↦ by rw [← Category.assoc, hcomp i]

/-- A standard V covering whose members are flat and locally of finite presentation is an
fppf covering: joint surjectivity is
`AlgebraicGeometry.IsStandardVCovering.exists_mem_range`. -/
theorem mem_fppfPrecoverage_of_isStandardVCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    [Finite I] (X : I → Scheme.{u}) [∀ i, IsAffine (X i)] (f : ∀ i, X i ⟶ T)
    (hflat : ∀ i, Flat (f i)) (hfp : ∀ i, LocallyOfFinitePresentation (f i))
    (hstd : IsStandardVCovering X f) :
    Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T :=
  (Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
    ⟨hstd.exists_mem_range, fun i ↦ ⟨hflat i, hfp i⟩⟩

/-- A V covering whose members are flat and locally of finite presentation is an fppf
covering: joint surjectivity is `AlgebraicGeometry.IsVCovering.exists_mem_range`. -/
theorem mem_fppfPrecoverage_of_isVCovering {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) (hflat : ∀ i, Flat (f i))
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) (hV : IsVCovering X f) :
    Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T :=
  (Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
    ⟨hV.exists_mem_range, fun i ↦ ⟨hflat i, hfp i⟩⟩

/-- **The flat case of Stacks 0ETR (2) ⟹ (1)**, granted
`AlgebraicGeometry.FppfHasFiniteDomination`: a V covering whose members are flat and locally
of finite presentation is a ph covering.

This is the last paragraph of the Stacks proof of 0ETR, which recognizes the flattened family
as an fppf covering and appeals to Stacks 0DBT. No tag is attached: this is the flat case, not
the general statement, which also needs the flattening step that
`AlgebraicGeometry.StandardVCoveringHasPHRefinement` isolates. The general statement is
`AlgebraicGeometry.isPHCovering_iff_isVCovering` in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`, and that is where
0ETR is registered. -/
theorem isPHCovering_of_isVCovering_of_flat (H : FppfHasFiniteDomination.{u, v})
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hflat : ∀ i, Flat (f i)) (hfp : ∀ i, LocallyOfFinitePresentation (f i))
    (hV : IsVCovering X f) : IsPHCovering X f :=
  isPHCovering_of_mem_fppfPrecoverage H X f
    (mem_fppfPrecoverage_of_isVCovering X f hflat hfp hV)

/-- **The flat case of Stacks 0ETR**, granted
`AlgebraicGeometry.FppfHasFiniteDomination`: for a family of flat morphisms locally of finite
presentation, the ph and V covering conditions agree. Unlike
`AlgebraicGeometry.isPHCovering_iff_isVCovering`, Stacks 0ETR, this needs no flattening
input. -/
theorem isPHCovering_iff_isVCovering_of_flat (H : FppfHasFiniteDomination.{u, v})
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hflat : ∀ i, Flat (f i)) (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  ⟨isVCovering_of_isPHCovering X f, isPHCovering_of_isVCovering_of_flat H X f hflat hfp⟩

/-- **The flat case of `AlgebraicGeometry.StandardVCoveringHasPHRefinement`**, granted
`AlgebraicGeometry.FppfHasFiniteDomination`: a standard V covering of an affine scheme whose
members are *flat* and locally of finite presentation is refined by a standard ph covering.

This is stated in exactly the shape of the hypothesis that
`AlgebraicGeometry.isPHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement` carries,
so it measures the distance from here to that predicate: only the reduction of the general case
to the flat one, i.e. the flattening. The proof reads
the refinement off `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` at the top open of
the affine base and transports it along `AlgebraicGeometry.Scheme.topIso`. -/
theorem standardVCoveringHasPHRefinement_of_flat (H : FppfHasFiniteDomination.{u, u})
    (U : Scheme.{u}) (hU : IsAffine U) (K : Type u) (hK : Finite K) (A : K → Scheme.{u})
    (hA : ∀ κ, IsAffine (A κ)) (a : ∀ κ, A κ ⟶ U) (hflat : ∀ κ, Flat (a κ))
    (hfp : ∀ κ, LocallyOfFinitePresentation (a κ))
    (hstd : @IsStandardVCovering U hU K hK A hA a) :
    ∃ 𝒱 : PreZeroHypercover.{u} U, @StandardPHCovering 𝒱.I₀ U hU 𝒱.X 𝒱.f ∧
      Nonempty (𝒱.Hom ({ I₀ := K, X := A, f := a } : PreZeroHypercover.{u} U)) := by
  have : IsAffine U := hU
  have : Finite K := hK
  have : ∀ κ, IsAffine (A κ) := hA
  have htop : IsAffine (⊤ : U.Opens).toScheme := isAffineOpen_top U
  obtain ⟨𝒲, hstdph, ⟨ρ⟩⟩ := (isPHCovering_of_mem_fppfPrecoverage H A a
    (mem_fppfPrecoverage_of_isStandardVCovering A a hflat hfp hstd)).2 ⊤ (isAffineOpen_top U)
  refine ⟨⟨𝒲.I₀, 𝒲.X, fun i ↦ 𝒲.f i ≫ U.topIso.hom⟩, hstdph.comp_isIso U.topIso.hom, ?_⟩
  refine ⟨⟨ρ.s₀, fun i ↦ ρ.h₀ i ≫ pullback.fst (a (ρ.s₀ i)) U.topIso.hom, fun i ↦ ?_⟩⟩
  have h₁ : ρ.h₀ i ≫ pullback.snd (a (ρ.s₀ i)) U.topIso.hom = 𝒲.f i := ρ.w₀ i
  have h₂ : pullback.fst (a (ρ.s₀ i)) U.topIso.hom ≫ a (ρ.s₀ i)
      = pullback.snd (a (ρ.s₀ i)) U.topIso.hom ≫ U.topIso.hom := pullback.condition
  exact (Category.assoc _ _ _).trans
    (((congrArg (fun k => ρ.h₀ i ≫ k) h₂).trans (Category.assoc _ _ _).symm).trans
      (congrArg (fun k => k ≫ U.topIso.hom) h₁))

end AlgebraicGeometry

end
