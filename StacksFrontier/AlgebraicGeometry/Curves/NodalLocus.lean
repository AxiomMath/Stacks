module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.LargestOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Basic

/-!
# The at-worst-nodal locus of a flat family of finite presentation

Let `f : X ⟶ S` be flat and locally of finite presentation. Among the open subschemes `U ⊆ X`
on which `f` restricts to a morphism which is at-worst-nodal of relative dimension one there is
a largest one, and its formation commutes with arbitrary base change.

The open subscheme is the supremum of all the opens with the property, which is itself one of
them because being at-worst-nodal of relative dimension one is étale local on the source. That
it is preserved by base change comes from a pointwise description of its underlying set: a
point `x` lies in it exactly when `f` is syntomic at `x`, the fibre of `f` through `x` has
local dimension one at `x`, and every point of the relative singular subscheme `Sing(f) ⊆ X`
above `x` is a point of unramifiedness of `Sing(f) ⟶ S`. Each of these three conditions is read
off the fibre of `f` through `x`, and so is insensitive to base change.

## Main definitions

* `AlgebraicGeometry.nodalLocus` is the open subscheme in question, the supremum of the opens
  on which the restricted morphism is at-worst-nodal of relative dimension one.

## Main results

* `AlgebraicGeometry.nodalLocus_isAtWorstNodalOfRelativeDimensionOne`: the restriction of `f` to
  `nodalLocus f` is at-worst-nodal of relative dimension one.
* `AlgebraicGeometry.le_nodalLocus`: every open on which the restriction of `f` is at-worst-nodal
  of relative dimension one is contained in `nodalLocus f`.
* `AlgebraicGeometry.nodalLocus_isGreatest`: the two statements above together, as the assertion
  that `nodalLocus f` is the greatest element of the set of opens with the property.
* `AlgebraicGeometry.nodalLocus_baseChange`: for a cartesian square with right edge `f`, the
  nodal locus of the base change of `f` is the inverse image of the nodal locus of `f`.

## Implementation notes

The locus is `AlgebraicGeometry.largestOpen` for the morphism property
`AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne`, so its maximality is the general
statement of Tag 0CEY for a property which is étale local on the source.

The pointwise description of the locus rests on a bridge between the two ways in which a
morphism property defined by a property of ring maps appears here: as a property of the
restriction `U.ι ≫ f` to an open subscheme, and as the pointwise predicate asserting the
existence of an affine chart around a point on which the map of sections has the ring property.
The bridge is stated for an arbitrary property of ring maps and specialised here to syntomicity
and to unramifiedness.

Base change of the relative singular subscheme enters through the Fitting ideal of the sheaf of
relative differentials; restriction to an open subscheme enters through the fact that an open
immersion is étale, which identifies the relative singular subscheme of a restriction with the
inverse image of the relative singular subscheme.

## References

* [Stacks Project, Tag 0DSC](https://stacks.math.columbia.edu/tag/0DSC)
* [Stacks Project, Tag 0CEY](https://stacks.math.columbia.edu/tag/0CEY)
* [Stacks Project, Tag 02V3](https://stacks.math.columbia.edu/tag/02V3)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Generalities on the largest open locus of a source-local property -/

/-- Every Zariski covering is an étale covering. -/
private theorem zariskiPrecoverage_le_etalePrecoverage :
    Scheme.zariskiPrecoverage.{u} ≤ Scheme.etalePrecoverage.{u} :=
  Scheme.precoverage_mono fun _ _ _ hi => have := hi; inferInstance

/-- An open subscheme is contained in the largest locus of a source-local property exactly when
the restriction of the morphism to it has the property. -/
private theorem le_largestOpen_iff (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens) :
    V ≤ largestOpen P f ↔ P (V.ι ≫ f) :=
  have : IsZariskiLocalAtSource P :=
    MorphismProperty.IsLocalAtSource.of_le zariskiPrecoverage_le_etalePrecoverage
  ⟨fun h => comp_ι_of_le h (largestOpen_isGreatest_etale P f).1,
    fun h => (largestOpen_isGreatest_etale P f).2 h⟩

/-- A point lies in the largest locus of a source-local property exactly when the restriction of
the morphism to some open neighbourhood of it has the property. -/
private theorem mem_largestOpen_iff (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    x ∈ largestOpen P f ↔ ∃ V : X.Opens, x ∈ V ∧ P (V.ι ≫ f) :=
  ⟨fun h => ⟨largestOpen P f, h, (largestOpen_isGreatest_etale P f).1⟩,
    fun ⟨_, hx, hV⟩ => (le_largestOpen_iff P f _).mpr hV hx⟩

/-! ### The chart bridge for properties of morphisms given by properties of ring maps -/

/-- Unramifiedness of morphisms of schemes is the affine-local property attached to the
conjunction of formal unramifiedness and finite type of ring maps, in the form that applies to
the class `AlgebraicGeometry.Unramified` itself. -/
private instance hasRingHomProperty_unramified' :
    HasRingHomProperty (@Unramified.{u})
      (fun {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T) =>
        g.FormallyUnramified ∧ g.FiniteType) :=
  hasRingHomProperty_unramified

/-- Unramifiedness is local on the source for the Zariski topology. -/
private instance unramified_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Unramified.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

/-- Unramifiedness is stable under postcomposition with an open immersion, an open immersion
being étale and hence unramified. -/
private instance unramified_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight (@Unramified.{u}) @IsOpenImmersion where
  postcomp i hi f hf := have := hi; MorphismProperty.comp_mem _ f i hf (unramified_of_etale i)

/-! ### The syntomic and the unramified locus as largest opens -/

/-- A point lies in the largest open on which a morphism is syntomic exactly when the morphism is
syntomic at that point. -/
private theorem mem_largestOpen_syntomic_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    x ∈ largestOpen (@Syntomic.{u}) f ↔ SyntomicAt f x :=
  (mem_largestOpen_iff (@Syntomic.{u}) f x).trans
    ⟨fun ⟨_, hx, hC⟩ => exists_appLE_of_comp_ι (@Syntomic.{u}) f hC hx,
      fun ⟨U, hxU, V, e, halg⟩ =>
        ⟨U.1, hxU, comp_ι_of_appLE (@Syntomic.{u}) f U.2 V.2 e halg⟩⟩

/-- A point lies in the largest open on which a morphism is unramified exactly when the morphism
is unramified at that point. -/
private theorem mem_largestOpen_unramified_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    x ∈ largestOpen (@Unramified.{u}) f ↔ UnramifiedAt f x := by
  refine (mem_largestOpen_iff (@Unramified.{u}) f x).trans
    ⟨fun ⟨_, hx, hC⟩ => ?_, fun ⟨U, hU, hxU, V, hV, e, halg⟩ => ?_⟩
  · obtain ⟨U, hxU, V, e, hQ⟩ := exists_appLE_of_comp_ι (@Unramified.{u}) f hC hx
    let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 e).hom.toAlgebra
    exact ⟨U.1, U.2, hxU, V.1, V.2, e, ⟨RingHom.formallyUnramified_algebraMap.mp hQ.1,
      RingHom.finiteType_algebraMap.mp hQ.2⟩⟩
  · let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have halg' : Algebra.Unramified Γ(S, V) Γ(X, U) := halg
    exact ⟨U, hxU, comp_ι_of_appLE (@Unramified.{u}) f hU hV e
      ⟨RingHom.formallyUnramified_algebraMap.mpr halg'.formallyUnramified,
        RingHom.finiteType_algebraMap.mpr halg'.finiteType⟩⟩

/-- A source-local property holds on an open subscheme exactly when a pointwise predicate cutting
out the largest open holds at every point of it. -/
private theorem comp_ι_iff_forall_mem (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens)
    {Q : X → Prop} (h : ∀ x, x ∈ largestOpen P f ↔ Q x) : P (V.ι ≫ f) ↔ ∀ x ∈ V, Q x :=
  (le_largestOpen_iff P f V).symm.trans
    ⟨fun H x hx => (h x).mp (H hx), fun H _ hx => (h _).mpr (H _ hx)⟩

/-- A morphism is syntomic on an open subscheme exactly when it is syntomic at every point
of it. -/
private theorem syntomic_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens) :
    Syntomic (V.ι ≫ f) ↔ ∀ x ∈ V, SyntomicAt f x :=
  comp_ι_iff_forall_mem _ f V (mem_largestOpen_syntomic_iff f)

/-- A morphism is unramified on an open subscheme exactly when it is unramified at every point
of it. -/
private theorem unramified_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens) :
    Unramified (V.ι ≫ f) ↔ ∀ x ∈ V, UnramifiedAt f x :=
  comp_ι_iff_forall_mem _ f V (mem_largestOpen_unramified_iff f)

/-! ### Fibre dimension along an étale morphism -/

/-! ### The pointwise syntomic condition of relative dimension one -/

/-- A morphism is syntomic of relative dimension one at a point when it is syntomic there and the
fibre through that point has local dimension one at it. -/
private def SyntomicDimOneAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  SyntomicAt f x ∧
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞)

/-- A morphism is syntomic of relative dimension one on an open subscheme exactly when it is
syntomic of relative dimension one at every point of it. -/
private theorem syntomicOfRelativeDimension_one_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (V : X.Opens) :
    SyntomicOfRelativeDimension 1 (V.ι ≫ f) ↔ ∀ x ∈ V, SyntomicDimOneAt f x := by
  constructor
  · rintro ⟨hsyn, hdim⟩ x hx
    refine ⟨(syntomic_comp_ι_iff f V).mp hsyn x hx, ?_⟩
    exact (topologicalKrullDimAt_fiber_comp_etale f V.ι ⟨x, hx⟩).symm.trans (hdim ⟨x, hx⟩)
  · intro h
    refine ⟨(syntomic_comp_ι_iff f V).mpr fun x hx => (h x hx).1, fun z => ?_⟩
    rw [topologicalKrullDimAt_fiber_comp_etale f V.ι z]
    exact (h (V.ι z) z.2).2

/-- The locus where a morphism is syntomic of relative dimension one is open: the morphism is
syntomic on an open neighbourhood, and the local dimension of its fibres is locally constant
there. -/
private theorem isOpen_setOf_syntomicDimOneAt {X S : Scheme.{u}} (f : X ⟶ S) :
    IsOpen {x : X | SyntomicDimOneAt f x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hsyn⟩ := (mem_largestOpen_iff (@Syntomic.{u}) f x).mp
    ((mem_largestOpen_syntomic_iff f x).mpr hx.1)
  have hloc := isLocallyConstant_fiberDimensionAt (U.ι ≫ f) hsyn
  set D : U.toScheme.Opens := ⟨_, hloc.isOpen_fiber ((1 : ℕ) : WithBot ℕ∞)⟩
  have hxD : (⟨x, hxU⟩ : U.toScheme) ∈ D := by
    change topologicalKrullDimAt ((U.ι ≫ f).fiber _) ((U.ι ≫ f).asFiber ⟨x, hxU⟩) = _
    rw [topologicalKrullDimAt_fiber_comp_etale f U.ι ⟨x, hxU⟩]
    exact hx.2
  refine ⟨U.ι ''ᵁ D, ?_, (U.ι ''ᵁ D).2, ⟨⟨x, hxU⟩, hxD, rfl⟩⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ : ∃ z : U.toScheme, z ∈ D ∧ U.ι z = y := hy
  refine ⟨(syntomic_comp_ι_iff f U).mp hsyn (U.ι z) (U.ι_image_le D ⟨z, hz, rfl⟩), ?_⟩
  rw [← topologicalKrullDimAt_fiber_comp_etale f U.ι z]
  exact hz

/-! ### The relative singular subscheme of a restriction and of a base change -/

/-- The canonical morphism from the closed subscheme cut out by the inverse image of an ideal
sheaf to the closed subscheme cut out by that ideal sheaf. -/
private def comapSubschemeHom {X Y : Scheme.{u}} (I : X.IdealSheafData) (g : Y ⟶ X) :
    (I.comap g).subscheme ⟶ I.subscheme :=
  (I.comapIso g).hom ≫ pullback.snd g I.subschemeι

/-- The inverse image of a closed subscheme along an open immersion is an open subscheme of that
closed subscheme. -/
private instance isOpenImmersion_comapSubschemeHom {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) [IsOpenImmersion g] : IsOpenImmersion (comapSubschemeHom I g) := by
  dsimp only [comapSubschemeHom]
  infer_instance

/-- The square relating the inclusions of a closed subscheme and of the inverse image of its
ideal sheaf commutes. -/
private theorem comapSubschemeHom_comp_subschemeι {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) :
    comapSubschemeHom I g ≫ I.subschemeι = (I.comap g).subschemeι ≫ g := by
  rw [comapSubschemeHom, Category.assoc, ← pullback.condition, ← Category.assoc,
    I.comapIso_hom_fst]

/-- The inclusion of the inverse-image closed subscheme followed by `g` and a morphism `f` out of
the target of `g` factors through the inclusion of the closed subscheme. -/
private theorem comapSubschemeHom_comp {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (I : X.IdealSheafData) :
    comapSubschemeHom I g ≫ (I.subschemeι ≫ f) = (I.comap g).subschemeι ≫ (g ≫ f) := by
  rw [← Category.assoc, comapSubschemeHom_comp_subschemeι, Category.assoc]

/-- In a cartesian square with right edge `f` and base edge `g`, the inclusion of the
inverse-image closed subscheme followed by the base change of `f` is a base change of the
inclusion of the closed subscheme followed by `f`. -/
private theorem isPullback_comapSubschemeHom {X' X S' S : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    (I : X.IdealSheafData) :
    IsPullback (comapSubschemeHom I g') ((I.comap g').subschemeι ≫ f') (I.subschemeι ≫ f) g := by
  dsimp only [comapSubschemeHom]
  simpa only [Category.assoc] using
    (IsPullback.of_iso_pullback
      (CommSq.mk (by simp only [← I.comapIso_hom_fst, Category.assoc,
        pullback.condition])) (I.comapIso g') (I.comapIso_hom_fst g') rfl).flip.paste_vert h

/-- The image of a point under the map from the inverse-image closed subscheme lies over the image
of that point in the ambient scheme. -/
private theorem subschemeι_comapSubschemeHom {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) (w : (I.comap g).subscheme) :
    I.subschemeι (comapSubschemeHom I g w) = g ((I.comap g).subschemeι w) := by
  rw [← Scheme.Hom.comp_apply, comapSubschemeHom_comp_subschemeι, Scheme.Hom.comp_apply]

/-- A point of a closed subscheme lying over the image of a point of the ambient morphism's source
has a preimage in the inverse-image closed subscheme above that point. -/
private theorem exists_comapSubschemeHom_eq {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) (y : Y) (z : I.subscheme) (h : g y = I.subschemeι z) :
    ∃ w, (I.comap g).subschemeι w = y ∧ comapSubschemeHom I g w = z := by
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback y z h
  have hhom : (I.comapIso g).hom ((I.comapIso g).inv w) = w := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    simp
  refine ⟨(I.comapIso g).inv w, ?_, ?_⟩
  · rw [← I.comapIso_hom_fst g, Scheme.Hom.comp_apply, hhom]
    exact hw1
  · rw [comapSubschemeHom, Scheme.Hom.comp_apply, hhom]
    exact hw2

/-- The inverse-image closed subscheme along the inclusion of an open subscheme sits in the
closed subscheme as the inverse image of that open subscheme. -/
private theorem range_comapSubschemeHom_ι {X : Scheme.{u}} (C : X.Opens)
    (I : X.IdealSheafData) :
    Set.range (comapSubschemeHom I C.ι) = (I.subschemeι ⁻¹ᵁ C : Set I.subscheme) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨w, rfl⟩
    change I.subschemeι _ ∈ C
    rw [subschemeι_comapSubschemeHom]
    exact ((I.comap C.ι).subschemeι w).2
  · intro z hz
    obtain ⟨w, -, hw⟩ := exists_comapSubschemeHom_eq I C.ι ⟨I.subschemeι z, hz⟩ z rfl
    exact ⟨w, hw⟩

/-- Unramifiedness over the base of the inverse-image closed subscheme along the inclusion of an
open subscheme is unramifiedness at the points of the closed subscheme lying over that open. -/
private theorem unramified_comapSubscheme_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (C : X.Opens) :
    Unramified ((I.comap C.ι).subschemeι ≫ (C.ι ≫ f)) ↔
      ∀ y ∈ I.subschemeι ⁻¹ᵁ C, UnramifiedAt (I.subschemeι ≫ f) y := by
  let G : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ C
  let e : (I.comap C.ι).subscheme ≅ G.toScheme :=
    IsOpenImmersion.isoOfRangeEq (comapSubschemeHom I C.ι) G.ι (by
      rw [range_comapSubschemeHom_ι C I, Scheme.Opens.range_ι])
  have hfac : e.hom ≫ G.ι = comapSubschemeHom I C.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have key : Unramified ((I.comap C.ι).subschemeι ≫ (C.ι ≫ f)) ↔
      Unramified (G.ι ≫ (I.subschemeι ≫ f)) := by
    rw [← comapSubschemeHom_comp f C.ι I, ← hfac, Category.assoc]
    refine ⟨fun h => ?_, fun h => IsZariskiLocalAtSource.comp h e.hom⟩
    have h' := IsZariskiLocalAtSource.comp h e.inv
    rwa [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h'
  exact key.trans (unramified_comp_ι_iff (I.subschemeι ≫ f) G)

/-! ### The pointwise at-worst-nodal condition -/

/-- A morphism is at worst nodal of relative dimension one at a point when it is syntomic of
relative dimension one there and every point of the relative singular subscheme above it is a
point of unramifiedness of the relative singular subscheme over the base. -/
private def NodalAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  SyntomicDimOneAt f x ∧
    ∀ y : (relativeSingularIdeal f).subscheme, (relativeSingularIdeal f).subschemeι y = x →
      UnramifiedAt ((relativeSingularIdeal f).subschemeι ≫ f) y

/-- A morphism is at worst nodal of relative dimension one on an open subscheme exactly when it
is syntomic of relative dimension one at every point of that open and the relative singular
subscheme is unramified over the base at every one of its points lying over that open. -/
private theorem isAtWorstNodalOfRelativeDimensionOne_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (C : X.Opens) :
    IsAtWorstNodalOfRelativeDimensionOne (C.ι ≫ f) ↔
      (∀ x ∈ C, SyntomicDimOneAt f x) ∧
        ∀ y ∈ (relativeSingularIdeal f).subschemeι ⁻¹ᵁ C,
          UnramifiedAt ((relativeSingularIdeal f).subschemeι ≫ f) y := by
  refine and_congr (syntomicOfRelativeDimension_one_comp_ι_iff f C) ?_
  rw [← relativeSingularIdeal_comap_etale f C.ι]
  exact unramified_comapSubscheme_iff f (relativeSingularIdeal f) C

/-- A point lies in the largest open on which a morphism is at worst nodal of relative
dimension one exactly when the morphism is at worst nodal of relative dimension one there. -/
private theorem mem_largestOpen_nodal_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    x ∈ largestOpen (@IsAtWorstNodalOfRelativeDimensionOne.{u}) f ↔ NodalAt f x := by
  refine (mem_largestOpen_iff (@IsAtWorstNodalOfRelativeDimensionOne.{u}) f x).trans
    ⟨fun ⟨C, hxC, hC⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · obtain ⟨hs, hu⟩ := (isAtWorstNodalOfRelativeDimensionOne_comp_ι_iff f C).mp hC
    refine ⟨hs x hxC, fun y hy => hu y ?_⟩
    change (relativeSingularIdeal f).subschemeι y ∈ C
    rw [hy]
    exact hxC
  · obtain ⟨C₁, hC₁sub, hC₁open, hxC₁⟩ :=
      isOpen_iff_forall_mem_open.mp (isOpen_setOf_syntomicDimOneAt f) x h1
    have hclosed : IsClosed ((relativeSingularIdeal f).subschemeι ''
        {y | UnramifiedAt ((relativeSingularIdeal f).subschemeι ≫ f) y}ᶜ) :=
      (IsClosedImmersion.isClosedEmbedding _).isClosedMap _
        (isOpen_setOf_unramifiedAt _).isClosed_compl
    refine ⟨⟨C₁, hC₁open⟩ ⊓ ⟨_, hclosed.isOpen_compl⟩, ⟨hxC₁, ?_⟩,
      (isAtWorstNodalOfRelativeDimensionOne_comp_ι_iff f _).mpr
        ⟨fun z hz => hC₁sub hz.1, fun y hy => ?_⟩⟩
    · rintro ⟨y, hy, hyx⟩
      exact hy (h2 y hyx)
    · by_contra hcon
      exact hy.2 ⟨y, hcon, rfl⟩

/-- Unramifiedness over the base of the inverse-image closed subscheme of a base change, at the
points above a point, is unramifiedness of the closed subscheme over the base at the points
above the image of that point. -/
private theorem unramifiedAt_comapSubscheme_iff_of_isPullback {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    (I : X.IdealSheafData) [LocallyOfFiniteType (I.subschemeι ≫ f)] (x' : X') :
    (∀ y' : (I.comap g').subscheme, (I.comap g').subschemeι y' = x' →
        UnramifiedAt ((I.comap g').subschemeι ≫ f') y') ↔
      ∀ y : I.subscheme, I.subschemeι y = g' x' → UnramifiedAt (I.subschemeι ≫ f) y := by
  have hsq := isPullback_comapSubschemeHom g' f' f g sq I
  constructor
  · intro h y hy
    obtain ⟨w, hw1, rfl⟩ := exists_comapSubschemeHom_eq I g' x' y hy.symm
    exact (unramifiedAt_iff_of_isPullback hsq _).mpr (h _ hw1)
  · intro h y' hy'
    refine (unramifiedAt_iff_of_isPullback hsq y').mp (h _ ?_)
    rw [subschemeι_comapSubschemeHom, hy']

/-- The pointwise at-worst-nodal condition is insensitive to base change: syntomicity, the local
dimension of the fibre, and unramifiedness of the relative singular subscheme over the base all
commute with base change. -/
private theorem nodalAt_iff_of_isPullback {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
    (x' : X') : NodalAt f' x' ↔ NodalAt f (g' x') := by
  have : Flat f' := MorphismProperty.of_isPullback sq ‹Flat f›
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback sq ‹_›
  have hsyn : SyntomicAt f' x' ↔ SyntomicAt f (g' x') :=
    Set.ext_iff.mp (syntomicLocus_eq_preimage g' f' f g sq) x'
  have hdim : topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') = ((1 : ℕ) : WithBot ℕ∞) ↔
      topologicalKrullDimAt (f.fiber (f (g' x'))) (f.asFiber (g' x')) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDimAt_fiber_eq_of_isPullback sq x']
  have hI : (relativeSingularIdeal f).comap g' = relativeSingularIdeal f' :=
    fittingIdeal_relativeDifferentials_comap g' f' f g sq 1
  have hunr : (∀ y' : (relativeSingularIdeal f').subscheme,
      (relativeSingularIdeal f').subschemeι y' = x' →
        UnramifiedAt ((relativeSingularIdeal f').subschemeι ≫ f') y') ↔
      ∀ y : (relativeSingularIdeal f).subscheme,
        (relativeSingularIdeal f).subschemeι y = g' x' →
          UnramifiedAt ((relativeSingularIdeal f).subschemeι ≫ f) y := by
    rw [← hI]
    exact unramifiedAt_comapSubscheme_iff_of_isPullback g' f' f g sq (relativeSingularIdeal f) x'
  exact and_congr (and_congr hsyn hdim) hunr

/-! ### The maximal at-worst-nodal open subscheme -/

/-- The **nodal locus** of a morphism of schemes: the supremum of the open subschemes of the
source on which the morphism restricts to a morphism which is at-worst-nodal of relative
dimension one. -/
def nodalLocus {X S : Scheme.{u}} (f : X ⟶ S) : X.Opens :=
  largestOpen (@IsAtWorstNodalOfRelativeDimensionOne.{u}) f

/-- The restriction of a morphism to its nodal locus is at-worst-nodal of relative dimension
one. -/
theorem nodalLocus_isAtWorstNodalOfRelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) :
    IsAtWorstNodalOfRelativeDimensionOne ((nodalLocus f).ι ≫ f) :=
  (largestOpen_isGreatest_etale (@IsAtWorstNodalOfRelativeDimensionOne.{u}) f).1

/-- Every open subscheme on which a morphism restricts to a morphism which is at-worst-nodal of
relative dimension one is contained in the nodal locus. -/
theorem le_nodalLocus {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens}
    (hU : IsAtWorstNodalOfRelativeDimensionOne (U.ι ≫ f)) : U ≤ nodalLocus f :=
  (largestOpen_isGreatest_etale (@IsAtWorstNodalOfRelativeDimensionOne.{u}) f).2 hU

/-- **Stacks Project, Tag 0DSC.** For a morphism of schemes which is flat and locally of finite
presentation there is a maximal open subscheme of its source on which it is at-worst-nodal of
relative dimension one: the restriction of the morphism to `nodalLocus f` is at-worst-nodal of
relative dimension one, and every open subscheme with that property is contained in
`nodalLocus f`. -/
@[stacks 0DSC "the maximal open subscheme"]
theorem nodalLocus_isGreatest {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] :
    IsGreatest {U : X.Opens | IsAtWorstNodalOfRelativeDimensionOne (U.ι ≫ f)} (nodalLocus f) :=
  largestOpen_isGreatest_etale (@IsAtWorstNodalOfRelativeDimensionOne.{u}) f

/-- **Stacks Project, Tag 0DSC.** Formation of the maximal at-worst-nodal open subscheme
commutes with arbitrary base change: in a cartesian square with right edge a flat morphism `f`
locally of finite presentation and base edge `g`, the nodal locus of the base change `f'` of `f`
is the inverse image of the nodal locus of `f`. -/
@[stacks 0DSC "compatibility with base change"]
theorem nodalLocus_baseChange {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S)
    (g : S' ⟶ S) (sq : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f] :
    nodalLocus f' = g' ⁻¹ᵁ nodalLocus f := by
  have : Flat f' := MorphismProperty.of_isPullback sq ‹Flat f›
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback sq ‹_›
  ext x'
  exact (mem_largestOpen_nodal_iff f' x').trans ((nodalAt_iff_of_isPullback g' f' f g sq x').trans
    (mem_largestOpen_nodal_iff f (g' x')).symm)

end AlgebraicGeometry

end
