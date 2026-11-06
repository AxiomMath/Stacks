module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableDenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Monomorphisms into disjoint unions of spectra of zero-dimensional local rings

A monomorphism of algebraic spaces over `S` whose target is a disjoint union of spectra of
zero-dimensional local rings is representable, so its source is a scheme. This is Stacks
06RZ. A field is a zero-dimensional local ring, so a monomorphism into a field-valued point
has a scheme as its source; such a monomorphism is either the inclusion of the empty
algebraic space or an isomorphism, which is Stacks 06MG.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_discreteTopology_points_of_isReasonableSpace`: a
  reasonable algebraic space with discrete point space is a scheme.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_mono_to_coproduct_spec_zeroDimensional`:
  **Stacks 06RZ**, with
  `AlgebraicGeometry.Space.isRepresentable_of_mono_to_coproduct_spec_zeroDimensional` for the
  restatement "the source is a scheme".
* `AlgebraicGeometry.Space.isEmpty_points_or_isIso_of_mono_to_spec_field`: **Stacks 06MG**, the
  dichotomy for a monomorphism of algebraic spaces into the spectrum of a field.

## Implementation notes

The target is given as a presheaf isomorphic to the functor of points of an object `Y` of the
big fppf site over `S` whose underlying scheme is a coproduct of spectra of zero-dimensional
local rings; the structure morphism to `S` is the one of `Y`. The index type may be empty, and
no finiteness is assumed of it.

The spectrum of a zero-dimensional local ring is a one-point space, so the underlying scheme of
`Y` is discrete and, by clause (1) of Stacks 03BX, so is the point space of its functor of
points. A monomorphism is injective on points by Stacks 06RV and continuous by clause (2) of
Stacks 03BX, so the point space of the source is discrete too.

Representability is then read off the schematic locus rather than from the source's groupoid
argument. A monomorphism is quasi-separated, and a discrete scheme is quasi-separated, so the
source is a quasi-separated algebraic space; the chain `(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ)` of Stacks 03JX
makes it reasonable, Stacks 03JI gives a representable open subspace whose point set is dense,
and in a discrete space a dense subset is everything. An open subspace is determined by its
point set, by Stacks 03BZ, so that subspace is the whole source.

In Stacks 06MG the conclusion "either `Z = ∅` or `Z = Spec(k)`" is read, as in Stacks 0481, as
"the source has no points, or the given monomorphism is an isomorphism"; the second alternative
concerns the given morphism and not merely an abstract isomorphism of the source with the field
point. Its target is presented exactly as for Stacks 06RZ, so the structure morphism of the
field point to `S` is part of the data.

Once the source is known to be a scheme the statement is the scheme-level dichotomy, whose
nonempty half is the private lemma below: a monomorphism of schemes out of a nonempty scheme
into the spectrum of a field is an isomorphism, because on global sections it is an epimorphism
of commutative rings out of a field and hence surjective, and injective because its source is a
field. That lemma is a duplicate of a private lemma of
`StacksFrontier/AlgebraicGeometry/Spaces/PointsAndCoverings/MonomorphismPoints.lean`, which also
drives Stacks 03DP in `StacksFrontier/AlgebraicGeometry/Scheme/Immersion/Monomorphism.lean`;
neither copy is public.

## References

* [Stacks Project, Tag 06RZ](https://stacks.math.columbia.edu/tag/06RZ)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Discreteness of a coproduct of spectra of zero-dimensional local rings -/

/-- The spectrum of a zero-dimensional local ring has exactly one point: every prime ideal is
the maximal ideal. -/
theorem subsingleton_primeSpectrum_of_ringKrullDim_eq_zero (A : Type u) [CommRing A]
    [IsLocalRing A] (hA : ringKrullDim A = 0) : Subsingleton (PrimeSpectrum A) :=
  have : Ring.KrullDimLE 0 A := (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := A)).2 hA
  Ring.KrullDimLE.subsingleton_primeSpectrum A

/-- A scheme isomorphic to a coproduct of spectra of zero-dimensional local rings is discrete:
each summand is a one-point space and a coproduct of schemes carries the disjoint-union
topology. -/
theorem discreteTopology_of_iso_coproduct_spec_zeroDimensional {Z : Scheme.{u}} {I : Type u}
    (A : I → CommRingCat.{u}) (hlocal : ∀ i, IsLocalRing (A i))
    (hdim : ∀ i, ringKrullDim (A i) = 0)
    (e : Z ≅ ∐ fun i : I ↦ Spec (A i)) : DiscreteTopology Z := by
  have hloc (i : I) : IsLocalRing (A i) := hlocal i
  have hsub (i : I) : Subsingleton (Spec (A i)) :=
    subsingleton_primeSpectrum_of_ringKrullDim_eq_zero (A i) (hdim i)
  have hdisc (i : I) : DiscreteTopology (Spec (A i)) := inferInstance
  have hcoprod : DiscreteTopology (∐ fun i : I ↦ Spec (A i) : Scheme.{u}) :=
    (AlgebraicGeometry.sigmaMk fun i : I ↦ Spec (A i)).discreteTopology_iff.mp inferInstance
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).discreteTopology_iff.mpr hcoprod

/-! ### Representability from a discrete point space -/

/-- A reasonable algebraic space over `S` whose point space is discrete is a scheme.

The representable open subspace of Stacks 03JI has dense point set, and a dense subset of a
discrete space is the whole of it, so that subspace is everything by Stacks 03BZ. -/
theorem isRepresentable_of_discreteTopology_points_of_isReasonableSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hreasonable : IsReasonableSpace B S hS X)
    (hdisc : DiscreteTopology (points B S hS X)) : X.IsRepresentable := by
  have := hdisc
  obtain ⟨G, hGopen, hGrep, hGdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isReasonableSpace B S hS hX hreasonable
  have := hGrep
  have htopiso : IsIso (Subfunctor.ι (⊤ : Subfunctor X)) :=
    (Subfunctor.eq_top_iff_isIso (⊤ : Subfunctor X)).mp rfl
  have hGrange : Set.range (pointsMap B S hS G.toFunctor G.ι) = Set.univ := by
    rw [← closure_discrete (Set.range (pointsMap B S hS G.toFunctor G.ι))]
    exact hGdense.closure_range
  have htoprange : Set.range (pointsMap B S hS (⊤ : Subfunctor X).toFunctor
      (⊤ : Subfunctor X).ι) = Set.univ :=
    Set.range_eq_univ.2
      (pointsHomeomorphOfIso B S hS (asIso (Subfunctor.ι (⊤ : Subfunctor X)))).surjective
  have hGtop : G = ⊤ :=
    eq_of_range_pointsMap_ι_eq B S hS hGopen (isOpenSubspace_top hX)
      (hGrange.trans htoprange.symm)
  have : IsIso G.ι := (Subfunctor.eq_top_iff_isIso G).mp hGtop
  exact isRepresentable_of_natIso G.toFunctor (asIso G.ι)

/-! ### Stacks 06RZ -/

/-- The source of a monomorphism of algebraic spaces over `S` into a disjoint union of spectra
of zero-dimensional local rings is a scheme. -/
theorem isRepresentable_of_mono_to_coproduct_spec_zeroDimensional
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    [Mono f] (Y : BigFppfOver B S hS) (eG : G ≅ yoneda.obj Y) (I : Type u)
    (A : I → CommRingCat.{u}) (hlocal : ∀ i, IsLocalRing (A i))
    (hdim : ∀ i, ringKrullDim (A i) = 0)
    (eY : (BigFppfOver.toScheme B S hS).obj Y ≅ ∐ fun i : I ↦ Spec (A i)) :
    F.IsRepresentable := by
  have hZ := BigFppfSite.contains_terminal B
  set g : F ⟶ yoneda.obj Y := f ≫ eG.hom with hg
  have hgmono : Mono g := by
    rw [hg]; exact mono_comp' inferInstance (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom eG))
  -- The target scheme, and so the point space of the target, is discrete.
  have hdiscY : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj Y) :=
    discreteTopology_of_iso_coproduct_spec_zeroDimensional A hlocal hdim eY
  have hdiscYpts : DiscreteTopology (points B S hS (yoneda.obj Y)) :=
    (schemePointsHomeomorph B S hS Y).discreteTopology_iff.mpr hdiscY
  -- A monomorphism is injective and continuous on points, so the source is discrete too.
  have hdiscF : DiscreteTopology (points B S hS F) :=
    have := hgmono
    DiscreteTopology.of_continuous_injective (continuous_pointsMap B S hS g)
      (pointsMap_injective_of_mono B S hS g)
  -- A discrete scheme is quasi-separated, so the target is a quasi-separated algebraic space.
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj Y) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj Y) hZ
      ⟨Y, inferInstance, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩
  -- A monomorphism is quasi-separated, so the source is quasi-separated as well.
  have hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hF hYqs
      (isQuasiSeparated_of_mono B S hS g hgmono)
  -- Stacks 03JX, `(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ)`.
  have hFreasonable : IsReasonableSpace B S hS F :=
    isReasonableSpace_of_isVeryReasonableSpace B S hS F hF
      (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ F hF
        (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS F hZ hF
          hFqs))
  exact isRepresentable_of_discreteTopology_points_of_isReasonableSpace B S hS hF hFreasonable
    hdiscF

/-- A morphism out of a representable presheaf into a representable one is, up to the chosen
isomorphisms, the image of a morphism of the site. -/
private theorem exists_yoneda_map_eq_of_isRepresentable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [F.IsRepresentable] (f : F ⟶ G)
    (Y : BigFppfOver B S hS) (eG : G ≅ yoneda.obj Y) :
    ∃ (V : BigFppfOver B S hS) (e : yoneda.obj V ≅ F) (p : V ⟶ Y),
      yoneda.map p = e.hom ≫ f ≫ eG.hom :=
  ⟨F.reprX, F.reprW, yoneda.preimage (F.reprW.hom ≫ f ≫ eG.hom), yoneda.map_preimage _⟩

/-- **Stacks 06RZ.** A monomorphism of algebraic spaces over `S` whose target is a disjoint
union of spectra of zero-dimensional local rings is representable; equivalently its source is a
scheme. -/
@[stacks 06RZ]
theorem relativelyRepresentable_of_mono_to_coproduct_spec_zeroDimensional
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    [Mono f] (Y : BigFppfOver B S hS) (eG : G ≅ yoneda.obj Y) (I : Type u)
    (A : I → CommRingCat.{u}) (hlocal : ∀ i, IsLocalRing (A i))
    (hdim : ∀ i, ringKrullDim (A i) = 0)
    (eY : (BigFppfOver.toScheme B S hS).obj Y ≅ ∐ fun i : I ↦ Spec (A i)) :
    yoneda.relativelyRepresentable f := by
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : F.IsRepresentable :=
    isRepresentable_of_mono_to_coproduct_spec_zeroDimensional B S hS hF f Y eG I A hlocal hdim eY
  obtain ⟨V, e, p, hp⟩ := exists_yoneda_map_eq_of_isRepresentable B S hS f Y eG
  have h1 : yoneda.relativelyRepresentable (e.hom ≫ f ≫ eG.hom) :=
    hp ▸ Functor.relativelyRepresentable.map yoneda p
  have h2 : yoneda.relativelyRepresentable (f ≫ eG.hom) := by
    simpa using MorphismProperty.RespectsIso.precomp yoneda.relativelyRepresentable e.inv _ h1
  simpa using
    MorphismProperty.RespectsIso.postcomp yoneda.relativelyRepresentable eG.inv _ h2

/-! ### Stacks 06MG -/

/-- **Stacks 06MG.** A monomorphism of algebraic spaces over `S` whose target is the spectrum
of a field `k` is either a morphism out of an algebraic space with no points, or an
isomorphism.

A field is a zero-dimensional local ring, so the source is a scheme by Stacks 06RZ, and the
dichotomy is then the scheme-level one. -/
@[stacks 06MG]
theorem isEmpty_points_or_isIso_of_mono_to_spec_field
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    [Mono f] (Y : BigFppfOver B S hS) (eG : G ≅ yoneda.obj Y) (k : Type u) [Field k]
    (eY : (BigFppfOver.toScheme B S hS).obj Y ≅ Spec (.of k)) :
    IsEmpty (points B S hS F) ∨ IsIso f := by
  have hrep : F.IsRepresentable :=
    isRepresentable_of_mono_to_coproduct_spec_zeroDimensional B S hS hF f Y eG
      PUnit.{u + 1} (fun _ => CommRingCat.of k)
      (by intro i; infer_instance)
      (by intro i; exact ringKrullDim_eq_zero_of_field k)
      (by
        let e₀ : (∐ fun _ : PUnit.{u + 1} => Spec (.of k)) ≅ Spec (.of k) :=
          coproductUniqueIso _
        exact eY.trans e₀.symm)
  have := hrep
  obtain ⟨V, e, p, hp⟩ := exists_yoneda_map_eq_of_isRepresentable B S hS f Y eG
  have hmonoyp : Mono (yoneda.map p) := by
    rw [hp]
    exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom e))
      (mono_comp' inferInstance (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom eG)))
  have : Mono p := yoneda.mono_of_mono_map hmonoyp
  have : Mono ((BigFppfOver.toScheme B S hS).map p) :=
    Functor.map_mono (BigFppfOver.toScheme B S hS) p
  rcases isEmpty_or_nonempty ((BigFppfOver.toScheme B S hS).obj V) with hVempty | hVne
  · left
    have : IsEmpty (points B S hS (yoneda.obj V)) :=
      (schemePointsHomeomorph B S hS V).toEquiv.isEmpty
    exact (pointsHomeomorphOfIso B S hS e).symm.toEquiv.isEmpty
  · right
    have : IsIso ((BigFppfOver.toScheme B S hS).map p ≫ eY.hom) :=
      AlgebraicGeometry.isIso_of_mono_to_spec_field ((BigFppfOver.toScheme B S hS).map p ≫ eY.hom)
    have : IsIso ((BigFppfOver.toScheme B S hS).map p) :=
      IsIso.of_isIso_comp_right ((BigFppfOver.toScheme B S hS).map p) eY.hom
    have : (BigFppfOver.toScheme B S hS).ReflectsIsomorphisms := inferInstance
    have : IsIso p := isIso_of_reflects_iso p (BigFppfOver.toScheme B S hS)
    have : IsIso (e.hom ≫ f ≫ eG.hom) := by rw [← hp]; infer_instance
    have : IsIso (f ≫ eG.hom) := IsIso.of_isIso_comp_left e.hom (f ≫ eG.hom)
    exact IsIso.of_isIso_comp_right f eG.hom

end AlgebraicGeometry.Space

end
