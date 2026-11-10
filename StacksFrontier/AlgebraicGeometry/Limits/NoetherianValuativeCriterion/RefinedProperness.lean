module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.GenericProperness
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeSeparatedness
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# A refined valuative criterion for properness over a locally Noetherian base

Let `f : X ⟶ S` and `h : U ⟶ X` be morphisms of finite type with `S` locally Noetherian, `f`
separated and `h(U)` dense in `X`. If every valuative diagram for `f` over a discrete valuation
ring whose generic arrow factors through `h` has a dotted arrow, then `f` is proper.

## Main results

* `AlgebraicGeometry.isProper_of_denseRange_of_exists_discreteLift`: **Stacks 0CM3**, the
  criterion, with no hypothesis beyond the tag's.
* `AlgebraicGeometry.isSeparated_of_denseRange_of_subsingleton_discreteLift`: **Stacks 0CM4**,
  the companion criterion for separatedness, where the dotted arrow is only assumed to be unique
  when it exists and `f` is only assumed locally of finite type, proved by a different route.
* `AlgebraicGeometry.isProper_of_denseRange_of_unique_discreteLift`: **Stacks 0CM5**, the
  criterion with a unique dotted arrow, which needs no separatedness assumption and no
  hypothesis beyond the tag's.

Each of the three has a counterpart — `isProper_of_exists_discreteLift_of_denseRange`,
`isSeparated_of_subsingleton_discreteLift_of_denseRange` and
`isProper_of_unique_discreteLift_of_denseRange` — carrying an extra hypothesis `h0208`, the
implication from condition (4) to condition (1) of Stacks 0208. Those are the earlier form of
this file's results, from a revision in which that implication was not available (see the
implementation notes); they are the ones that still carry the geometric argument, and they are
retained unchanged. They register no tag.

## Implementation notes

Density of `h(U)` is the topological density `DenseRange h` of the set-theoretic image, which is
the notion the source uses here and the one
`AlgebraicGeometry.universallyClosed_of_unique_lift_of_denseRange` uses for Stacks 0894.

The argument is the one of the source. Properness is Zariski-local at the target, so the base may
be taken quasi-compact; then `U` is quasi-compact and may be replaced by the coproduct of a finite
affine open covering, which changes neither the hypotheses nor the image; then `U` is affine, hence
quasi-affine, so it immerses into a relative projective space over `X`
(`AlgebraicGeometry.exists_immersion_projectiveSpace`), and the scheme-theoretic image `Z` of that
immersion contains `U` as a dense open subscheme and is proper over `X`, being a closed subscheme
of `ℙⁿ_X`. Since `Z ⟶ X` is closed with dense image it is surjective, so properness of `Z ⟶ S`
gives properness of `f`. Properness of `Z ⟶ S` is tested on the generic points of the irreducible
components of `Z`: those lie in `U` because `U` is a dense open of `Z`, so the hypothesis produces
a dotted arrow to `X`, properness of `Z ⟶ X` lifts it to `Z`, and separatedness of `Z ⟶ S` makes
it unique.

That last step is condition (4) of Stacks 0208 for `Z ⟶ S`, i.e.
`AlgebraicGeometry.GenericDiscreteValuativeCriterion`, and the implication from it to properness
is `AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion`.

The source's proof of that implication needs Chow's lemma over a Noetherian base. The
conditional statements of this file take the implication as the hypothesis `h0208` and carry the
geometric argument; `h0208` is discharged by `isProper_of_genericDiscreteValuativeCriterion'`, and
the tags sit on the resulting hypothesis-free statements. Nothing is assumed: each of
`@[stacks 0CM3]`, `@[stacks 0CM4]` and `@[stacks 0CM5]` sits unqualified on a theorem that asks
exactly the hypotheses of its tag. Stacks 0CM5 is proved through Stacks 0CM3.

Stacks 0CM4 needs none of this and is proved outright in
`AlgebraicGeometry.isSeparated_of_denseRange_of_subsingleton_discreteLift`, which does not go
through Stacks 0CM3. Instead it verifies the fourth condition of Stacks 0207,
`AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType`, whose hypotheses on `f` are exactly
the tag's and which quantifies only over the discrete valuation subrings of the residue field at
a generic point `η` of an irreducible component of `X`. Such an `η` is `h u` for some `u : U`,
because a quasi-compact dominant morphism hits every such point (Stacks 01RL,
`AlgebraicGeometry.isDominant_iff_genericPoints_subset_range`), and `κ(u)` is a finitely
generated extension of `κ(η)` because `h` is locally of finite type; so a discrete valuation
subring of `κ(η)` with fraction field `κ(η)` is dominated by a discrete valuation ring `B` inside
`κ(u)` with fraction field `κ(u)` (Stacks 00PH,
`exists_isDiscreteValuationRing_isFractionRing_of_not_isField`). The diagram obtained by
extending scalars to `B` has `Spec κ(u) ⟶ U ⟶ X` as its generic arrow, hence falls under the
hypothesis; two dotted arrows over the original ring therefore agree after `Spec B ⟶ Spec A`, and
`A ⟶ B` being injective and local they already agree
(`AlgebraicGeometry.hom_ext_of_closedPoint_eq_of_specMap_comp_eq`).

## References

* [Stacks Project, Tag 0CM3](https://stacks.math.columbia.edu/tag/0CM3)
* [Stacks Project, Tag 0CM4](https://stacks.math.columbia.edu/tag/0CM4)
* [Stacks Project, Tag 0CM5](https://stacks.math.columbia.edu/tag/0CM5)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- `AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion` — the implication from
condition (4) to condition (1) of Stacks 0208 — with its three instance arguments taken as
ordinary hypotheses, which is the shape in which the conditional criteria below assume it as
`h0208`. -/
private theorem isProper_of_genericDiscreteValuativeCriterion' {V W : Scheme.{u}} (p : V ⟶ W)
    (hW : IsLocallyNoetherian W) (hp : LocallyOfFiniteType p) (hq : QuasiCompact p)
    (hgen : GenericDiscreteValuativeCriterion p) : IsProper p :=
  have := hW
  have := hp
  have := hq
  isProper_of_genericDiscreteValuativeCriterion p hgen

/-- An affine scheme of finite type over `X` with dense image is a dense open subscheme of a
scheme proper and surjective over `X`: it immerses into `ℙⁿ_X`, and the scheme-theoretic image of
that immersion is a closed subscheme of `ℙⁿ_X` containing it as a dense open. -/
private theorem exists_isOpenImmersion_isProper_of_isAffine {U X : Scheme.{u}} (h : U ⟶ X)
    [IsAffine U] [IsLocallyNoetherian U] [LocallyOfFiniteType h] (hdense : DenseRange h) :
    ∃ (Z : Scheme.{u}) (i : U ⟶ Z) (g : Z ⟶ X), IsOpenImmersion i ∧ IsProper g ∧
      i ≫ g = h ∧ DenseRange i.base ∧ Function.Surjective g.base := by
  obtain ⟨n, j, hj, hjh⟩ := exists_immersion_projectiveSpace h
  have : IsImmersion j := hj
  have : IsNoetherian U := ⟨⟩
  have : QuasiCompact j := inferInstance
  have : IsOpenImmersion j.toImage := isOpenImmersion_toImage j (Or.inl inferInstance)
  have hcomp : j.toImage ≫ (j.imageι ≫ (ProjectiveSpace n X ↘ X)) = h := by
    rw [← Category.assoc, j.toImage_imageι, hjh]
  have hproper : IsProper (j.imageι ≫ (ProjectiveSpace n X ↘ X)) := inferInstance
  have hdensei : DenseRange j.toImage.base := j.toImage.denseRange
  have hdenseg : DenseRange (j.imageι ≫ (ProjectiveSpace n X ↘ X)).base := hdense.mono (by
    rintro x ⟨u, rfl⟩
    exact ⟨j.toImage.base u, by
      rw [← Scheme.Hom.comp_apply, hcomp]⟩)
  refine ⟨j.image, j.toImage, j.imageι ≫ (ProjectiveSpace n X ↘ X), inferInstance, hproper,
    hcomp, hdensei, ?_⟩
  have hclosed := (j.imageι ≫ (ProjectiveSpace n X ↘ X)).isClosedMap.isClosed_range
  exact Set.range_eq_univ.mp
    (hclosed.closure_eq.symm.trans (denseRange_iff_closure_range.mp hdenseg))

/-- A quasi-compact scheme of finite type over `X` with dense image is refined by an affine one:
the coproduct of a finite affine open covering is affine, surjects onto the source, and still has
dense image in `X`. -/
private theorem exists_isAffine_denseRange_refinement {U X : Scheme.{u}} (h : U ⟶ X)
    [CompactSpace U] [IsLocallyNoetherian U] [LocallyOfFiniteType h] [QuasiCompact h]
    (hdense : DenseRange h) :
    ∃ (P : Scheme.{u}) (q : P ⟶ U), IsAffine P ∧ Function.Surjective q ∧
      DenseRange (q ≫ h) ∧ LocallyOfFiniteType q ∧ QuasiCompact q := by
  let C := U.affineCover.finiteSubcover
  let P := ∐ fun i : C.I₀ => C.X i
  let q : P ⟶ U := Sigma.desc fun i => C.f i
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFiniteType) (Q := RingHom.FiniteType)
  have : LocallyOfFiniteType q := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  let e := AlgebraicGeometry.sigmaMk (fun i : C.I₀ => C.X i)
  have hqeval (i : C.I₀) (y : C.X i) : q (e ⟨i, y⟩) = C.f i y := by
    rw [AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  have : QuasiCompact q := by
    apply (quasiCompact_iff_forall_isAffineOpen (f := q)).2
    intro V hV
    have hpre : q ⁻¹' (V : Set U) =
        e '' Set.sigma Set.univ (fun i => (C.f i) ⁻¹' (V : Set U)) := by
      ext x
      obtain ⟨⟨i, y⟩, rfl⟩ := e.surjective x
      rw [e.injective.mem_set_image]
      simp [Set.mem_sigma_iff, hqeval]
    change IsCompact (q ⁻¹' (V : Set U))
    rw [hpre]
    exact (Set.isCompact_sigma Set.finite_univ fun i _ =>
      QuasiCompact.isCompact_preimage (f := C.f i) (U := (V : Set U)) V.2 hV.isCompact).image
        e.continuous_toFun
  have : IsAffine P := by dsimp [P]; infer_instance
  have hq : Function.Surjective q := by
    intro x
    have hx : x ∈ ⋃ i, Set.range (C.f i) := by
      rw [C.iUnion_range]; trivial
    rcases Set.mem_iUnion.mp hx with ⟨i, ⟨y, hy⟩⟩
    exact ⟨e ⟨i, y⟩, (hqeval i y).trans hy⟩
  have hdense' : DenseRange (q ≫ h) := hdense.mono (by
    rintro x ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hq y
    exact ⟨z, by simp⟩)
  exact ⟨P, q, inferInstance, hq, hdense', inferInstance, inferInstance⟩

/-- The refined criterion over a quasi-compact base, with the implication from condition (4) to
condition (1) of Stacks 0208 as the hypothesis `h0208`. The implication is available
(`isProper_of_genericDiscreteValuativeCriterion'`) and is discharged downstream; this statement
is the one the file has always had, and it is where the geometric argument lives. -/
private theorem isProper_of_exists_discreteLift_of_denseRange_of_compactSpace
    (h0208 : ∀ {V W : Scheme.{u}} (p : V ⟶ W), IsLocallyNoetherian W → LocallyOfFiniteType p →
      QuasiCompact p → GenericDiscreteValuativeCriterion p → IsProper p)
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [CompactSpace S] [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → D.commSq.HasLift) :
    IsProper f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace h
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian h
  obtain ⟨P, q, hPaffine, hqsurj, hdenseP, hqft, hqqc⟩ :=
    exists_isAffine_denseRange_refinement h hdense
  have : IsAffine P := hPaffine
  have : LocallyOfFiniteType q := hqft
  have : QuasiCompact q := hqqc
  have : LocallyOfFiniteType (q ≫ h) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (q ≫ h)
  obtain ⟨Z, i, g, hi, hproperg, hcomp, hdensei, hsurjg⟩ :=
    exists_isOpenImmersion_isProper_of_isAffine (q ≫ h) hdenseP
  have : IsOpenImmersion i := hi
  have : IsProper g := hproperg
  have : IsNoetherian P := ⟨⟩
  have hgeneric : GenericDiscreteValuativeCriterion (g ≫ f) := by
    intro η hη A hA hAK i₂ sq
    have : IsDiscreteValuationRing A := hA
    have : IsFractionRing A (Z.residueField η) := hAK
    have hdom : IsDominant i := (isDominant_iff i).mpr hdensei
    have hηrange : η ∈ Set.range i :=
      (AlgebraicGeometry.isDominant_iff_genericPoints_subset_range i).mp hdom hη
    let y : Spec (.of (Z.residueField η)) ⟶ Z := Z.fromSpecResidueField η
    have hy : Set.range y ⊆ Set.range i := by
      rw [Scheme.range_fromSpecResidueField]
      exact Set.singleton_subset_iff.mpr hηrange
    let v : Spec (.of (Z.residueField η)) ⟶ P := IsOpenImmersion.lift i y hy
    have hv : v ≫ i = y := IsOpenImmersion.lift_fac _ _ _
    let D : ValuativeCommSq f :=
      { R := A
        K := Z.residueField η
        i₁ := y ≫ g
        i₂ := i₂
        commSq := ⟨by rw [Category.assoc]; exact sq.w⟩ }
    have hfactor : (v ≫ q) ≫ h = D.i₁ := by
      calc (v ≫ q) ≫ h = (v ≫ i) ≫ g := by rw [Category.assoc, ← hcomp, Category.assoc]
        _ = y ≫ g := by rw [hv]
    obtain ⟨a, ha₁, ha₂⟩ := (hvaluative D hA (v ≫ q) hfactor).exists_lift
    have hvcg : ValuativeCriterion g := by
      rw [IsProper.eq_valuativeCriterion] at hproperg
      exact hproperg.1.1.1
    let Dg : ValuativeCommSq g :=
      { R := A
        K := Z.residueField η
        i₁ := y
        i₂ := a
        commSq := ⟨ha₁.symm⟩ }
    obtain ⟨b, hb₁, hb₂⟩ := (hvcg Dg).some.default
    refine ⟨⟨⟨b, hb₁, ?_⟩⟩, ?_⟩
    · calc b ≫ (g ≫ f) = (b ≫ g) ≫ f := by simp [Category.assoc]
        _ = a ≫ f := by rw [hb₂]
        _ = i₂ := ha₂
    · have : IsSeparated (g ≫ f) := inferInstance
      exact IsSeparated.valuativeCriterion (g ≫ f)
        { R := A
          K := Z.residueField η
          i₁ := Z.fromSpecResidueField η
          i₂ := i₂
          commSq := sq }
  have : IsProper (g ≫ f) := h0208 (g ≫ f) inferInstance inferInstance inferInstance hgeneric
  have : Surjective g := ⟨hsurjg⟩
  rw [isProper_iff]
  exact ⟨inferInstance, UniversallyClosed.of_comp_surjective g f, inferInstance⟩

/-- The refined lifting condition is inherited by the restriction of `f` to an open subscheme of
the base, the restriction of `h` to the preimage of its preimage. -/
private theorem liftCondition_morphismRestrict {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    (V : S.Opens)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → D.commSq.HasLift) :
    ∀ (D : ValuativeCommSq (f ∣_ V)) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ (h ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme),
      g ≫ (h ∣_ (f ⁻¹ᵁ V)) = D.i₁ → D.commSq.HasLift := by
  intro D hD g hg
  let iX := (f ⁻¹ᵁ V).ι
  let iS := V.ι
  let iU := (h ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
  have htriX : (f ∣_ V) ≫ iS = iX ≫ f := morphismRestrict_ι f V
  have htriU : (h ∣_ (f ⁻¹ᵁ V)) ≫ iX = iU ≫ h := morphismRestrict_ι h (f ⁻¹ᵁ V)
  let D₀ : ValuativeCommSq f :=
    { R := D.R
      K := D.K
      i₁ := D.i₁ ≫ iX
      i₂ := D.i₂ ≫ iS
      commSq := ⟨by
        calc (D.i₁ ≫ iX) ≫ f = D.i₁ ≫ ((f ∣_ V) ≫ iS) := by
              rw [htriX, Category.assoc]
          _ = (D.i₁ ≫ (f ∣_ V)) ≫ iS := by rw [Category.assoc]
          _ = (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂) ≫ iS := by
              rw [D.commSq.w]
          _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ (D.i₂ ≫ iS) := by
              rw [Category.assoc]⟩ }
  have hg₀ : (g ≫ iU) ≫ h = D₀.i₁ := by
    calc (g ≫ iU) ≫ h = (g ≫ (h ∣_ (f ⁻¹ᵁ V))) ≫ iX := by
          rw [Category.assoc, ← htriU, Category.assoc]
      _ = D₀.i₁ := by rw [hg]
  obtain ⟨b, hb₁, hb₂⟩ := (hvaluative D₀ hD (g ≫ iU) hg₀).exists_lift
  have hrange : Set.range b.base ⊆ Set.range iX.base := by
    rintro z ⟨a, rfl⟩
    refine ⟨⟨b.base a, ?_⟩, rfl⟩
    have hval : f.base (b.base a) = iS.base (D.i₂.base a) := by
      simpa [D₀] using congrArg (fun k : Spec (.of D.R) ⟶ S => k a) hb₂
    change f.base (b.base a) ∈ V
    rw [hval]
    exact (D.i₂.base a).property
  refine ⟨IsOpenImmersion.lift iX b hrange, ?_, ?_⟩
  · apply (cancel_mono iX).1
    calc (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫
            IsOpenImmersion.lift iX b hrange) ≫ iX =
          Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ b := by
            simp [IsOpenImmersion.lift_fac]
      _ = D₀.i₁ := hb₁
      _ = D.i₁ ≫ iX := rfl
  · apply (cancel_mono iS).1
    calc (IsOpenImmersion.lift iX b hrange ≫ (f ∣_ V)) ≫ iS = b ≫ f := by
          simp [htriX, Category.assoc]
      _ = D₀.i₂ := hb₂
      _ = D.i₂ ≫ iS := rfl

/-- The refined criterion for properness, with the implication from condition (4) to condition
(1) of Stacks 0208 as the hypothesis `h0208`. Let `f : X ⟶ S` and `h : U ⟶ X` be of finite type
with `S` locally Noetherian, `f` separated and `h(U)` dense in `X`. If every valuative diagram
for `f` over a discrete valuation ring whose generic arrow factors through `h` has a dotted
arrow, then `f` is proper.

The hypothesis is no longer needed: Stacks 0CM3 is
`isProper_of_denseRange_of_exists_discreteLift`, which discharges it. This statement is the one
the file has always had, and it is where the reduction to a quasi-compact base lives. -/
theorem isProper_of_exists_discreteLift_of_denseRange
    (h0208 : ∀ {V W : Scheme.{u}} (p : V ⟶ W), IsLocallyNoetherian W → LocallyOfFiniteType p →
      QuasiCompact p → GenericDiscreteValuativeCriterion p → IsProper p)
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → D.commSq.HasLift) :
    IsProper f := by
  classical
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (f := f)
    (fun i : S.affineCover.I₀ => (S.affineCover.f i).opensRange)
    S.affineCover.iSup_opensRange
  intro i
  let V : S.Opens := (S.affineCover.f i).opensRange
  have : IsAffine V.toScheme := isAffineOpen_opensRange (S.affineCover.f i)
  have hdenseV : DenseRange (h ∣_ (f ⁻¹ᵁ V)) := by
    let 𝒲 : Option X.affineCover.I₀ → X.Opens := fun i =>
      i.elim (f ⁻¹ᵁ V) (fun j => (X.affineCover.f j).opensRange)
    have hcover : TopologicalSpace.IsOpenCover 𝒲 := by
      apply TopologicalSpace.IsOpenCover.mk
      refine le_antisymm le_top ?_
      rw [← X.affineCover.iSup_opensRange]
      exact iSup_le fun j => le_iSup_of_le (some j) le_rfl
    change DenseRange (h ∣_ (f ⁻¹ᵁ V)).base
    rw [morphismRestrict_base]
    exact (TopologicalSpace.IsOpenCover.denseRange_iff_restrictPreimage hcover).mp hdense none
  exact isProper_of_exists_discreteLift_of_denseRange_of_compactSpace h0208
    (h ∣_ (f ⁻¹ᵁ V)) (f ∣_ V) hdenseV (liftCondition_morphismRestrict h f V hvaluative)

/-- **Stacks Project, Tag 0CM3.** Let `f : X ⟶ S` and `h : U ⟶ X` be morphisms of schemes with
`S` locally Noetherian, `f` and `h` of finite type, `f` separated and `h(U)` dense in `X`. If
every commutative solid diagram with `Spec(K) ⟶ U ⟶ X` along the top and `Spec(A) ⟶ S` along the
bottom, where `A` is a discrete valuation ring with field of fractions `K`, admits a dotted arrow
`Spec(A) ⟶ X` making it commute, then `f` is proper.

This is `isProper_of_exists_discreteLift_of_denseRange` with its hypothesis `h0208` discharged by
`isProper_of_genericDiscreteValuativeCriterion'`. -/
@[stacks 0CM3, ega "II 7.3.8" "(b)⇒(a)", ega "IV 15.7.5" "c⇒a", ega "IV 18.10.20" "partial"]
theorem isProper_of_denseRange_of_exists_discreteLift
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → D.commSq.HasLift) :
    IsProper f :=
  isProper_of_exists_discreteLift_of_denseRange
    isProper_of_genericDiscreteValuativeCriterion' h f hdense hvaluative

/-- The diagonal of a morphism of schemes is an immersion, hence locally of finite type. -/
private theorem locallyOfFiniteType_diagonal {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFiniteType (pullback.diagonal f) := inferInstance

/-- The diagonal of a morphism of schemes is a monomorphism, hence separated. -/
private theorem isSeparated_diagonal {X S : Scheme.{u}} (f : X ⟶ S) :
    IsSeparated (pullback.diagonal f) := inferInstance

/-- The diagonal of a morphism out of a locally Noetherian scheme is quasi-compact, since a
locally Noetherian scheme is quasi-separated. -/
@[ega "IV 8.13.5" "partial"]
private theorem quasiCompact_diagonal {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian X] :
    QuasiCompact (pullback.diagonal f) := inferInstance

/-- The fibre square of a morphism locally of finite type out of a locally Noetherian scheme is
locally Noetherian, both of its projections being base changes of that morphism. -/
@[ega "I 6.3.8" "special case"]
private theorem isLocallyNoetherian_pullback_self {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian X] [LocallyOfFiniteType f] : IsLocallyNoetherian (pullback f f) :=
  inferInstance

/-- A morphism of schemes whose diagonal is proper is separated: the diagonal is a monomorphism,
so properness makes it a closed immersion. -/
private theorem isSeparated_of_isProper_diagonal {X S : Scheme.{u}} (f : X ⟶ S)
    (hdiag : IsProper (pullback.diagonal f)) : IsSeparated f :=
  ⟨(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨hdiag, inferInstance⟩⟩

/-- The companion criterion for separatedness, with the implication from condition (4) to
condition (1) of Stacks 0208 as the hypothesis `h0208`. Let `f : X ⟶ S` be locally of finite type
with `S` locally Noetherian, and let `h : U ⟶ X` be of finite type with `h(U)` dense in `X`. If
every valuative diagram for `f` over a discrete valuation ring whose generic arrow factors
through `h` has at most one dotted arrow, then `f` is separated.

The hypothesis is no longer needed: Stacks 0CM4 is
`isSeparated_of_denseRange_of_subsingleton_discreteLift`, which asks the tag's hypotheses only
and takes a different route, through Stacks 0207 rather than through Stacks 0CM3. This statement
is the one the file has always had, and it is where the reduction to the diagonal lives. -/
theorem isSeparated_of_subsingleton_discreteLift_of_denseRange
    (h0208 : ∀ {V W : Scheme.{u}} (p : V ⟶ W), IsLocallyNoetherian W → LocallyOfFiniteType p →
      QuasiCompact p → GenericDiscreteValuativeCriterion p → IsProper p)
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → Subsingleton D.commSq.LiftStruct) :
    IsSeparated f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : LocallyOfFiniteType (pullback.diagonal f) := locallyOfFiniteType_diagonal f
  have : QuasiCompact (pullback.diagonal f) := quasiCompact_diagonal f
  have : IsSeparated (pullback.diagonal f) := isSeparated_diagonal f
  have : IsLocallyNoetherian (pullback f f) := isLocallyNoetherian_pullback_self f
  refine isSeparated_of_isProper_diagonal f
    (isProper_of_exists_discreteLift_of_denseRange h0208 h _ hdense fun D hD g hg => ?_)
  let a : Spec (.of D.R) ⟶ X := D.i₂ ≫ pullback.fst f f
  let b : Spec (.of D.R) ⟶ X := D.i₂ ≫ pullback.snd f f
  have ha : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ a = D.i₁ := by
    simpa [a] using (congrArg (fun q => q ≫ pullback.fst f f) D.commSq.w).symm
  have hb : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ b = D.i₁ := by
    simpa [b] using (congrArg (fun q => q ≫ pullback.snd f f) D.commSq.w).symm
  let Df : ValuativeCommSq f := ⟨_, _, D.i₁, a ≫ f, ⟨by simp [← ha, Category.assoc]⟩⟩
  have hab : a = b := congrArg CommSq.LiftStruct.l (@Subsingleton.elim _
    (hvaluative Df hD g hg) (⟨a, ha, rfl⟩ : Df.commSq.LiftStruct)
    ⟨b, hb, (congrArg (fun q => D.i₂ ≫ q) pullback.condition).symm⟩)
  exact ⟨⟨a, ha, by apply pullback.hom_ext <;> simp [a, b, hab]⟩⟩

/-- **Stacks Project, Tag 0CM4.** Let `f : X ⟶ S` be locally of finite type with `S` locally
Noetherian, and let `h : U ⟶ X` be of finite type with `h(U)` dense in `X`. If every valuative
diagram for `f` over a discrete valuation ring whose generic arrow factors through `h` has at
most one dotted arrow, then `f` is separated. -/
@[stacks 0CM4]
theorem isSeparated_of_denseRange_of_subsingleton_discreteLift
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → Subsingleton D.commSq.LiftStruct) :
    IsSeparated f := by
  have hdom : IsDominant h := (isDominant_iff h).mpr hdense
  refine ((isSeparated_tfae_of_locallyOfFiniteType f).out 4 1).mp ?_
  intro η hη A hA hAK i₂ sq
  obtain ⟨u, rfl⟩ := (isDominant_iff_genericPoints_subset_range h).mp hdom hη
  have _ : IsDiscreteValuationRing A := hA
  have _ : IsFractionRing A (X.residueField (h.base u)) := hAK
  let _ : Algebra (X.residueField (h.base u)) (U.residueField u) :=
    (h.residueFieldMap u).hom.toAlgebra
  have _ : Algebra.EssFiniteType (X.residueField (h.base u)) (U.residueField u) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap (f := h) u)
  let _ : Algebra A (U.residueField u) :=
    ((algebraMap (X.residueField (h.base u)) (U.residueField u)).comp
      (algebraMap A (X.residueField (h.base u)))).toAlgebra
  have _ : IsScalarTower A (X.residueField (h.base u)) (U.residueField u) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨B, hBdvr, hBfrac, hBloc⟩ :=
    _root_.exists_isDiscreteValuationRing_isFractionRing_of_not_isField
      (R := A) (X.residueField (h.base u)) (L := U.residueField u)
      (IsDiscreteValuationRing.not_isField A)
  have _ := hBdvr
  have _ := hBfrac
  have _ := hBloc
  have hring : CommRingCat.ofHom (algebraMap A B) ≫
      CommRingCat.ofHom (algebraMap B (U.residueField u)) =
      CommRingCat.ofHom A.subtype ≫ h.residueFieldMap u :=
    CommRingCat.hom_ext <| RingHom.ext fun a =>
      (IsScalarTower.algebraMap_apply A B (U.residueField u) a).symm
  have hspec := congrArg Spec.map hring
  rw [Spec.map_comp, Spec.map_comp] at hspec
  let D : ValuativeCommSq f :=
    { R := B
      K := U.residueField u
      i₁ := U.fromSpecResidueField u ≫ h
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ i₂
      commSq := ⟨by
        calc (U.fromSpecResidueField u ≫ h) ≫ f
            = (Spec.map (h.residueFieldMap u) ≫ X.fromSpecResidueField (h.base u)) ≫ f := by
              rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
          _ = Spec.map (h.residueFieldMap u) ≫
              (Spec.map (CommRingCat.ofHom A.subtype) ≫ i₂) := by
              rw [Category.assoc, sq.w]
          _ = (Spec.map (h.residueFieldMap u) ≫
              Spec.map (CommRingCat.ofHom A.subtype)) ≫ i₂ := (Category.assoc _ _ _).symm
          _ = (Spec.map (CommRingCat.ofHom (algebraMap B (U.residueField u))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ i₂ :=
              (congrArg (fun k => k ≫ i₂) hspec).symm
          _ = _ := Category.assoc _ _ _⟩ }
  have hsub : Subsingleton D.commSq.LiftStruct :=
    hvaluative D hBdvr (U.fromSpecResidueField u) rfl
  refine ⟨fun l₁ l₂ ↦ ?_⟩
  apply CommSq.LiftStruct.ext
  let mkLift : sq.LiftStruct → D.commSq.LiftStruct := fun l =>
    { l := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ l.l
      fac_left := by
        calc Spec.map (CommRingCat.ofHom (algebraMap B (U.residueField u))) ≫
              (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ l.l)
            = (Spec.map (CommRingCat.ofHom (algebraMap B (U.residueField u))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫ l.l :=
              (Category.assoc _ _ _).symm
          _ = (Spec.map (h.residueFieldMap u) ≫
              Spec.map (CommRingCat.ofHom A.subtype)) ≫ l.l :=
              congrArg (fun k => k ≫ l.l) hspec
          _ = Spec.map (h.residueFieldMap u) ≫
              (Spec.map (CommRingCat.ofHom A.subtype) ≫ l.l) := Category.assoc _ _ _
          _ = Spec.map (h.residueFieldMap u) ≫ X.fromSpecResidueField (h.base u) :=
              congrArg (fun k => Spec.map (h.residueFieldMap u) ≫ k) l.fac_left
          _ = U.fromSpecResidueField u ≫ h :=
              Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField h u
      fac_right := by rw [Category.assoc, l.fac_right] }
  have heq : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ l₁.l =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ l₂.l :=
    congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hsub (mkLift l₁) (mkLift l₂))
  have hπ : (Spec.map (CommRingCat.ofHom (algebraMap A B))) (IsLocalRing.closedPoint B) =
      IsLocalRing.closedPoint A := AlgebraicGeometry.Spec_closedPoint
  have hclosed : l₁.l (IsLocalRing.closedPoint A) = l₂.l (IsLocalRing.closedPoint A) := by
    have hpt : l₁.l ((Spec.map (CommRingCat.ofHom (algebraMap A B))) (IsLocalRing.closedPoint B))
        = l₂.l ((Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (IsLocalRing.closedPoint B)) :=
      congrArg (fun k : Spec (.of B) ⟶ X => k (IsLocalRing.closedPoint B)) heq
    rwa [hπ] at hpt
  exact hom_ext_of_closedPoint_eq_of_specMap_comp_eq (K := X.residueField (h.base u)) l₁.l l₂.l
    hclosed (l₁.fac_left.trans l₂.fac_left.symm)

/-- The criterion with a unique dotted arrow, with the implication from condition (4) to
condition (1) of Stacks 0208 as the hypothesis `h0208`. Let `f : X ⟶ S` and `h : U ⟶ X` be of
finite type with `S` locally Noetherian and `h(U)` dense in `X`. If every valuative diagram for
`f` over a discrete valuation ring whose generic arrow factors through `h` has a unique dotted
arrow, then `f` is proper.

The hypothesis is no longer needed: Stacks 0CM5 is
`isProper_of_denseRange_of_unique_discreteLift`. This statement is the one the file has always
had. -/
theorem isProper_of_unique_discreteLift_of_denseRange
    (h0208 : ∀ {V W : Scheme.{u}} (p : V ⟶ W), IsLocallyNoetherian W → LocallyOfFiniteType p →
      QuasiCompact p → GenericDiscreteValuativeCriterion p → IsProper p)
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) :
    IsProper f := by
  have : IsSeparated f :=
    isSeparated_of_subsingleton_discreteLift_of_denseRange h0208 h f hdense
      fun D hD g hg => have := (hvaluative D hD g hg).some; inferInstance
  exact isProper_of_exists_discreteLift_of_denseRange h0208 h f hdense
    fun D hD g hg => (CommSq.HasLift.iff D.commSq).2 ⟨(hvaluative D hD g hg).some.default⟩

/-- **Stacks Project, Tag 0CM5.** Let `f : X ⟶ S` and `h : U ⟶ X` be of finite type with `S`
locally Noetherian and `h(U)` dense in `X`. If every valuative diagram for `f` over a discrete
valuation ring whose generic arrow factors through `h` has a unique dotted arrow, then `f` is
proper.

There is no separatedness hypothesis on `f`: separatedness is what the uniqueness of the dotted
arrow buys, through Stacks 0CM4. -/
@[stacks 0CM5, ega "II 7.3.8" "(b)⇒(a)"]
theorem isProper_of_denseRange_of_unique_discreteLift
    {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType h] [QuasiCompact h] (hdense : DenseRange h)
    (hvaluative : ∀ (D : ValuativeCommSq f) (_ : IsDiscreteValuationRing D.R)
      (g : Spec (.of D.K) ⟶ U), g ≫ h = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) :
    IsProper f :=
  isProper_of_unique_discreteLift_of_denseRange
    isProper_of_genericDiscreteValuativeCriterion' h f hdense hvaluative

end AlgebraicGeometry

end
