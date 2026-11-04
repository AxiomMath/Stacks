module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence

/-!
# The completion of an affine scheme along a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X = Spec A` be an affine scheme over
`S` lying in that site and let `T ⊆ |X|` be a closed subset. **Stacks 0AIY** says that the
completion of `X` along `T` — the functor sending an object `U` of the big fppf site of `S` to
the set of morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` — is a *McQuillan* affine formal algebraic
space.

Writing `T = V(I)`, the ideals `J ⊆ A` with `V(J) = T` are exactly those with the same radical
as `I`; they are directed by reverse inclusion and `X_{/T}` is the colimit of the affine
thickenings `Spec (A ⧸ J)` over them. The presentation is McQuillan because `A` surjects onto
each `A ⧸ J` compatibly, so the projections from `lim_J A ⧸ J` onto the stages are surjective.

## Main definitions

* `AlgebraicGeometry.FormalSpace.supportedPoints`: the points of a represented presheaf whose
  underlying scheme point lies in a given subset; the set of points along which the completion
  is formed.
* `AlgebraicGeometry.FormalSpace.SupportIdeal` and
  `AlgebraicGeometry.FormalSpace.SupportIndex`: the ideals with a given zero locus, and the
  index of the presentation they form, ordered by reverse inclusion.
* `AlgebraicGeometry.FormalSpace.supportStage` and
  `AlgebraicGeometry.FormalSpace.supportDiagram`: the quotient spectrum `Spec (A ⧸ J)` as an
  affine scheme over `S`, and the diagram of those spectra.
* `AlgebraicGeometry.FormalSpace.supportComparison`: the canonical morphism from the colimit of
  the quotient stages to the completion.
* `AlgebraicGeometry.FormalSpace.HasStageAtlas`: the set-theoretic hypothesis that the chosen
  site carry an atlas for that colimit.

## Main results

* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf`:
  **Stacks 0AIY**, the completion of an affine scheme along a closed subset is a McQuillan
  affine formal algebraic space. This is the assertion of 0AIY about the completion; the
  companion assertion, that the displayed subfunctor of sections supported on `T` is already
  an fppf sheaf and so agrees with its sheafification, is not proved here.
* `AlgebraicGeometry.FormalSpace.isIso_supportComparison`: the completion along `V(I)` is the
  colimit of the spectra of the quotients of `A` by the ideals with the same zero locus.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_zeroLocusCompletion` and
  `AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_supportDiagram`: the two
  halves of the conclusion, for `T = V(I)`.
* `AlgebraicGeometry.FormalSpace.exists_supportStage_factor`: a section over an affine object
  of the site supported on `V(I)` factors through one of the stages, which is the heart of the
  proof.

## Implementation notes

McQuillan is condition (4) of Stacks 0AIC,
`AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation`: an affine formal algebraic space
with *some* presentation by affine thickenings whose section-ring projections are surjective.
It is not deduced here from condition (1) of 0AIC
(`AlgebraicGeometry.FormalSpace.hasAllSurjectivePresentations_of_exists_weaklyAdmissible`),
because the ring presenting the completion in the sense of that condition is the complete ring
`lim_J A ⧸ J`, not `A` itself: the topology on `A` given by the ideals with zero locus `T` is
in general neither separated nor complete, hence not weakly admissible. Instead surjectivity is
proved for the presentation by the `Spec (A ⧸ J)` directly, as in the source: the classes of a
single element of `A` lift any prescribed section of a single stage.

Closedness of `T` is used exactly once, to replace `T` by the zero locus of its vanishing
ideal; everything else is stated for `V(I)` with `I` an arbitrary ideal, which is the same
generality, the closed subsets of `Spec A` being precisely the zero loci of ideals. The ideals
`J` with `V(J) = T` need not contain a power of `I` when `I` is not finitely generated, which
is why the presentation uses all of them rather than the `I`-adic system. In the finitely
generated case the completion is the formal spectrum of the `I`-adic completion of `A`, which
is Stacks 0GBA in `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum`.

That each quotient spectrum `Spec (A ⧸ J)` lies in the site is not a hypothesis: the quotient
map makes it a closed subscheme of `Spec A`, and the size cutoff cutting out the site is closed
under passing to the source of a closed immersion
(`AlgebraicGeometry.Scheme.size_lt_of_isClosedImmersion`), so every stage lies in the site as
soon as `Spec A` does.

One hypothesis is carried which is not in the Stacks text, namely
`AlgebraicGeometry.FormalSpace.HasStageAtlas`: that the coproduct of the sheaves represented by
the stages be representable by an object of the site. This is set-theoretic data about the
chosen site rather than mathematical input, and Stacks can leave it implicit because its sites
are indexed by a cutoff it is free to enlarge. It is literally the atlas hypothesis of
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit`, which is the form
Stacks 0AIS takes for a colimit presentation, and the analogue for this index of
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` of Stacks 0AIF. It cannot be
discharged from the site's own closure properties, which give coproducts only over at most
countable index sets (`AlgebraicGeometry.Scheme.size_sigmaObj_lt`), whereas the ideals `J` with
`V(J) = T` form an uncountable family in general; the definition of an affine formal algebraic
space used here contains the set-theoretic condition of Stacks 0AIS and so demands such an
atlas for the same reason.

The completion is the library's `AlgebraicGeometry.Space.completionSheaf`, the fppf
sheafification of the subfunctor of sections supported on `T`, and
`AlgebraicGeometry.FormalSpace.hasImageIn_supportedPoints_iff` identifies the sections of that
subfunctor over `U` with the morphisms `U ⟶ X` all of whose scheme-theoretic points map into
`T`, which is the source's functor. Whether that subfunctor is itself an fppf sheaf — so that
sheafifying changes nothing and the statement proved here is literally about the source's
functor rather than about its sheafification — is a separate assertion, not established here
nor anywhere the library can currently cite. The affine scheme is presented as `Spec A` with a
morphism to `S`, as in Stacks 0GBA; every affine object of the site is of that form up to
isomorphism.

Surjectivity of the comparison on sections is proved by cover-density, as for Stacks 0GBA: the
affine objects of the site generate the fppf topology, and over an affine object every
supported section factors through a stage — uniquely up to passing to the intersection of two
stages, because each `Spec (A ⧸ J) ⟶ Spec A` is a closed immersion, hence a monomorphism.

## References

* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 00E0](https://stacks.math.columbia.edu/tag/00E0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

/-! ### Points supported in a subset of the representing scheme -/

/-- The points of the presheaf represented by an object of the site whose underlying scheme
point lies in `T`. -/
def supportedPoints (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (T : Set ((BigFppfOver.toScheme B S hS).obj U)) :
    Set (Space.points B S hS (yoneda.obj U)) :=
  {x | Space.pointsToScheme B S hS U x ∈ T}

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A]
  (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)

/-- A section of the presheaf represented by `Spec A` over `U` is supported in `T` exactly
when every point of the scheme `U` maps into `T`. -/
theorem hasImageIn_supportedPoints_iff
    (T : Set ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA f)))
    (U : BigFppfOver B S hS) (g : U ⟶ affineOver B S hS hA f) :
    Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
        (supportedPoints B S hS (affineOver B S hS hA f) T) U g ↔
      ∀ x, (BigFppfOver.toScheme B S hS).map g x ∈ T := by
  have key (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
      Space.pointsToScheme B S hS (affineOver B S hS hA f)
          ((Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g) p).class
            B S hS (yoneda.obj (affineOver B S hS hA f))) =
        (BigFppfOver.toScheme B S hS).map g (Space.schemePoint B S hS U p) := by
    rw [← Space.pointsMap_class, Space.pointsToScheme_pointsMap]
    rfl
  constructor
  · intro hg x
    have hx := hg (Space.schemePointRepresentative B S hS U x)
    change Space.pointsToScheme B S hS (affineOver B S hS hA f)
      ((Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g)
        (Space.schemePointRepresentative B S hS U x)).class
          B S hS (yoneda.obj (affineOver B S hS hA f))) ∈ T at hx
    rwa [key, Space.schemePointRepresentative_point] at hx
  · intro h p
    show Space.pointsToScheme B S hS (affineOver B S hS hA f)
      ((Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g) p).class
        B S hS (yoneda.obj (affineOver B S hS hA f))) ∈ T
    rw [key]
    exact h _

/-! ### The ideals cutting out the closed subset -/

/-- An ideal of `A` with the same zero locus as `I`, that is with the same radical. These are
the ideals `J` with `V(J) = T` of Stacks 0AIY. -/
abbrev SupportIdeal (I : Ideal A) := {J : Ideal A // J.radical = I.radical}

/-- The index of the presentation of the completion: the ideals with the same zero locus as
`I`, ordered by reverse inclusion, lifted to the universe of the index of a presentation of an
affine formal algebraic space. The quotient grows as the ideal shrinks, so reverse inclusion
makes the quotient spectra into a directed diagram. -/
abbrev SupportIndex (I : Ideal A) := ULift.{u + 1} (OrderDual (SupportIdeal I))

/-- The index `SupportIndex I` is nonempty: it contains the radical of `I`. -/
instance nonempty_supportIndex (I : Ideal A) : Nonempty (SupportIndex I) :=
  ⟨ULift.up (OrderDual.toDual ⟨I.radical, Ideal.radical_idem I⟩)⟩

/-- The index `SupportIndex I` is directed: the intersection of two ideals with the radical of
`I` again has the radical of `I`, and bounds both for reverse inclusion. -/
instance isDirected_supportIndex (I : Ideal A) : IsDirected (SupportIndex I) (· ≤ ·) := by
  refine ⟨fun i j ↦ ⟨ULift.up (OrderDual.toDual ⟨i.down.1 ⊓ j.down.1, ?_⟩), ?_, ?_⟩⟩
  · rw [Ideal.radical_inf, i.down.2, j.down.2, inf_idem]
  · exact (inf_le_left : i.down.1 ⊓ j.down.1 ≤ i.down.1)
  · exact (inf_le_right : i.down.1 ⊓ j.down.1 ≤ j.down.1)

/-! ### The diagram of quotient spectra -/

/-- The morphism `Spec (A ⧸ J) ⟶ Spec A` induced by the quotient map is a closed immersion. -/
private theorem isClosedImmersion_spec_map_mk (J : Ideal A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

include hA in
/-- A quotient of `A` has its spectrum in the site as soon as `Spec A` does: the quotient map
presents `Spec (A ⧸ J)` as a closed subscheme of `Spec A`, and the size cutoff defining the
site is closed under passing to the source of a closed immersion. -/
theorem contains_spec_quotient_of_contains (J : Ideal A) :
    B.Contains (Spec (.of (A ⧸ J))) := by
  have := isClosedImmersion_spec_map_mk J
  exact Scheme.size_lt_of_isClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) hA

variable (I : Ideal A)

/-- The affine scheme `Spec (A ⧸ J)` over `S`, as an object of the big affine fppf site, its
structure morphism being the one induced by `A ⧸ J` together with `Spec A ⟶ S`. -/
def supportStage (J : SupportIdeal I) : BigAffineFppf B S hS :=
  ⟨Over.mk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f) :
        B.obj (contains_spec_quotient_of_contains B hA J.1) ⟶ B.obj hS), by
    change IsAffine (Spec (.of (A ⧸ J.1)))
    infer_instance⟩

/-- Composing the quotient map by `J` with the factor map `A ⧸ J → A ⧸ K` gives the quotient
map by `K`. -/
theorem ofHom_mk_comp_ofHom_factor {J K : Ideal A} (h : J ≤ K) :
    CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom (Ideal.Quotient.factor h) =
      CommRingCat.ofHom (Ideal.Quotient.mk K) :=
  CommRingCat.hom_ext (RingHom.ext fun x ↦ Ideal.Quotient.factor_mk h x)

/-- The morphism of quotient spectra over `S` induced by an inclusion of ideals. -/
def supportTransition {J K : SupportIdeal I} (h : J.1 ≤ K.1) :
    supportStage B S hS hA f I K ⟶ supportStage B S hS hA f I J :=
  ObjectProperty.homMk <| Over.homMk
    (U := (supportStage B S hS hA f I K).1) (V := (supportStage B S hS hA f I J).1)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) ≫ f
      rw [← Category.assoc, ← Spec.map_comp, ofHom_mk_comp_ofHom_factor])

/-- An inclusion of indices of the diagram is the reverse inclusion of the ideals. -/
theorem supportIndex_le {I : Ideal A} {J K : SupportIndex I} (g : J ⟶ K) :
    K.down.1 ≤ J.down.1 := by
  have h : J ≤ K := leOfHom g
  exact h

/-- The diagram of the spectra of the quotients of `A` by the ideals with zero locus `T`,
indexed by those ideals ordered by reverse inclusion. -/
def supportDiagram : SupportIndex I ⥤ BigAffineFppf B S hS where
  obj J := supportStage B S hS hA f I J.down
  map {J K} g := supportTransition B S hS hA f I (supportIndex_le g)
  map_id J := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (supportIndex_le (𝟙 J)))) = 𝟙 _
    simp [Ideal.Quotient.factor_eq]
  map_comp {J K L} g h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (supportIndex_le (g ≫ h)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (supportIndex_le g))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (supportIndex_le h)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (Ideal.Quotient.factor_comp (supportIndex_le h) (supportIndex_le g)).symm

/-- Passing to a smaller ideal with the same zero locus is surjective on spectra: the larger
ideal lies in the radical of the smaller one, so the kernel of the comparison map lies in the
nilradical. -/
private theorem surjective_spec_support_factor {J K : Ideal A} (hJ : J.radical = K.radical)
    (h : K ≤ J) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  have hker : (RingHom.ker (Ideal.Quotient.factor h) : Set (A ⧸ K)) ⊆ nilradical (A ⧸ K) := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk] at hy
    obtain ⟨n, hn⟩ : x ∈ K.radical := by
      rw [← hJ]
      exact Ideal.le_radical (Ideal.Quotient.eq_zero_iff_mem.mp hy)
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hn
  have key : Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [← Set.range_eq_univ,
      range_comap_of_surjective (A ⧸ J) (Ideal.Quotient.factor h)
        (Ideal.Quotient.factor_surjective h),
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    exact hker
  exact key

/-- Each transition morphism of the diagram is a thickening: it is a closed immersion, being
induced by a surjection of rings, and it is surjective because the two ideals have the same
radical. -/
theorem isThickening_supportDiagram_map {J K : SupportIndex I} (g : J ⟶ K) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map ((supportDiagram B S hS hA f I).map g)) := by
  constructor
  · show IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (supportIndex_le g))))
    exact IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective (supportIndex_le g))
  · show Function.Surjective
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (supportIndex_le g))))
    exact surjective_spec_support_factor (J.down.2.trans K.down.2.symm) (supportIndex_le g)

/-! ### The quotient stages as sections of the completion -/

/-- The points supported on a zero locus are the points of the presheaf whose underlying
scheme point lies in that zero locus. -/
theorem supportedPoints_zeroLocus :
    supportedPoints B S hS (affineOver B S hS hA f) (PrimeSpectrum.zeroLocus (I : Set A)) =
      zeroLocusPoints B S hS hA f I := by
  ext x
  induction x using Quot.ind with
  | _ p =>
    have hmem : ∀ q : Space.FieldValuedPoint B S hS (yoneda.obj (affineOver B S hS hA f)),
        Space.pointsToScheme B S hS (affineOver B S hS hA f)
            (q.class B S hS (yoneda.obj (affineOver B S hS hA f))) =
          Space.schemePoint B S hS (affineOver B S hS hA f) q := fun _ ↦ rfl
    refine ⟨fun hp q hq ↦ ?_, fun h ↦ h p rfl⟩
    have hcl := congrArg (Space.pointsToScheme B S hS (affineOver B S hS hA f)) hq
    rw [hmem, hmem] at hcl
    show Space.schemePoint B S hS (affineOver B S hS hA f) q ∈
      PrimeSpectrum.zeroLocus (I : Set A)
    rw [hcl]
    exact hp

/-- A section of the presheaf represented by `Spec A` over `U` is supported on the zero locus
of `I` exactly when every point of the scheme `U` maps into that zero locus. -/
theorem hasImageIn_zeroLocusPoints_iff (U : BigFppfOver B S hS)
    (g : U ⟶ affineOver B S hS hA f) :
    Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I) U g ↔
      ∀ x, (BigFppfOver.toScheme B S hS).map g x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [← supportedPoints_zeroLocus B S hS hA f I]
  exact hasImageIn_supportedPoints_iff B S hS hA f _ U g

/-- The completion `X_{/V(I)}` of the affine scheme `X = Spec A` over `S` along the zero locus
of an ideal `I ⊆ A`. -/
abbrev zeroLocusCompletion : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f))
    (zeroLocusPoints B S hS hA f I)

/-- The morphism `Spec (A ⧸ J) ⟶ Spec A` over `S` induced by the quotient map. -/
def supportStageToAffine (J : SupportIdeal I) :
    ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I J)) ⟶
      affineOver B S hS hA f :=
  Over.homMk (U := (supportStage B S hS hA f I J).1) (V := affineOver B S hS hA f)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f
      rfl)

/-- The morphisms to `Spec A` are compatible with the transition morphisms of the diagram. -/
theorem supportStageToAffine_transition {J K : SupportIdeal I} (h : J.1 ≤ K.1) :
    ((BigAffineFppf.inclusion B S hS).map (supportTransition B S hS hA f I h)) ≫
        supportStageToAffine B S hS hA f I J =
      supportStageToAffine B S hS hA f I K := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1))
  rw [← Spec.map_comp, ofHom_mk_comp_ofHom_factor]

/-- Each quotient stage is supported on the zero locus of `I`: its morphism to `Spec A` has
point-set image inside `V(I)`, because `I` lies in the radical of the ideal defining the
stage. -/
theorem supportStage_hasImageIn (J : SupportIdeal I) :
    Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)
      ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I J))
      (supportStageToAffine B S hS hA f I J) := by
  rw [hasImageIn_zeroLocusPoints_iff]
  intro x
  show ∀ a, a ∈ (I : Set A) → Ideal.Quotient.mk J.1 a ∈ x.asIdeal
  intro a ha
  obtain ⟨n, hn⟩ : a ∈ J.1.radical := by
    rw [J.2]
    exact Ideal.le_radical ha
  refine x.isPrime.mem_of_pow_mem n ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hn]
  exact x.asIdeal.zero_mem

/-! ### The comparison morphism from the colimit of the stages -/

/-- The diagram of the sheaves represented by the quotient stages. -/
abbrev supportSheafDiagram :
    SupportIndex I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  supportDiagram B S hS hA f I ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- The section of the completion `X_{/V(I)}` over a quotient stage given by that stage's
morphism to `Spec A`, which is supported on `V(I)`. -/
def supportStageSection (J : SupportIdeal I) :
    (zeroLocusCompletion B S hS hA f I).obj.obj
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I J))) :=
  (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
    (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor).app
      (Opposite.op ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I J)))
      ⟨⟨supportStageToAffine B S hS hA f I J⟩,
        supportStage_hasImageIn B S hS hA f I J⟩

/-- Restricting the sheafification image of a section along `i` gives the sheafification image
of any section that the subfunctor restricts to. -/
private theorem sheafify_map_toSheafify_app {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {V W : BigFppfOver B S hS} (i : V ⟶ W) (x : P.obj (Opposite.op W)) (y : P.obj (Opposite.op V))
    (h : P.map i.op x = y) :
    ((BigFppfOver.topology B S hS).sheafify P).map i.op
        ((GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) P).app _ x) =
      (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) P).app _ y := by
  rw [← NatTrans.naturality_apply (GrothendieckTopology.toSheafify _ P) i.op, h]

/-- The canonical sections over the quotient stages are compatible with restriction along the
transition morphisms. -/
theorem supportStageSection_transition {J K : SupportIdeal I} (h : J.1 ≤ K.1) :
    (zeroLocusCompletion B S hS hA f I).obj.map
        ((BigAffineFppf.inclusion B S hS).map (supportTransition B S hS hA f I h)).op
        (supportStageSection B S hS hA f I J) =
      supportStageSection B S hS hA f I K := by
  exact sheafify_map_toSheafify_app B S hS _ _ _ <|
    Subtype.ext <| ULift.ext _ _ <| supportStageToAffine_transition B S hS hA f I h

/-- The morphism from a quotient stage into the completion `X_{/V(I)}`, corresponding under
Yoneda's lemma for sheaves to the canonical section over that stage. -/
def supportStageToCompletion (J : SupportIdeal I) :
    (supportSheafDiagram B S hS hA f I).obj (ULift.up J) ⟶ zeroLocusCompletion B S hS hA f I :=
  (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
    (supportStageSection B S hS hA f I J)

/-- The morphisms from the quotient stages into the completion form a cocone on the diagram of
represented stages. -/
theorem supportStageToCompletion_naturality {J K : SupportIndex I} (g : J ⟶ K) :
    (supportSheafDiagram B S hS hA f I).map g ≫
        supportStageToCompletion B S hS hA f I K.down =
      supportStageToCompletion B S hS hA f I J.down := by
  have hmap := congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
    (supportStageSection_transition B S hS hA f I (supportIndex_le g))
  rwa [Sheaf.sectionEquiv_symm_map] at hmap

/-- The cocone on the diagram of represented quotient stages whose vertex is the completion
`X_{/V(I)}`. -/
def supportCocone : Cocone (supportSheafDiagram B S hS hA f I) where
  pt := zeroLocusCompletion B S hS hA f I
  ι :=
    { app J := supportStageToCompletion B S hS hA f I J.down
      naturality _ _ g :=
        (supportStageToCompletion_naturality B S hS hA f I g).trans
          (Category.comp_id _).symm }

/-- The canonical comparison morphism from the colimit of the quotient stages `Spec (A ⧸ J)`,
over the ideals `J` with `V(J) = V(I)`, to the completion `X_{/V(I)}`. -/
def supportComparison :
    colimit (supportSheafDiagram B S hS hA f I) ⟶ zeroLocusCompletion B S hS hA f I :=
  colimit.desc (supportSheafDiagram B S hS hA f I) (supportCocone B S hS hA f I)

/-- On each quotient stage the comparison restricts to that stage's canonical morphism into
the completion. -/
theorem supportComparison_stage (J : SupportIdeal I) :
    colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J) ≫
        supportComparison B S hS hA f I =
      supportStageToCompletion B S hS hA f I J :=
  colimit.ι_desc (supportCocone B S hS hA f I) (ULift.up J)

/-! ### Factoring a supported section through a stage -/

/-- The morphism of the index attached to a reverse inclusion of ideals with the same zero
locus. -/
def supportIndexHom {I : Ideal A} {J K : SupportIdeal I} (h : K.1 ≤ J.1) :
    (ULift.up J : SupportIndex I) ⟶ ULift.up K :=
  homOfLE (by exact h)

/-- A section over an affine object of the site which is supported on `V(I)` factors through a
quotient stage. The corresponding ring map `ρ : A → Γ(U, 𝒪)` has `I` inside the radical of its
kernel, so `I ⊓ ker ρ` is an ideal with the same zero locus as `I` through which `ρ`
factors. -/
theorem exists_supportStage_factor (U : BigAffineFppf B S hS)
    (g : U.1 ⟶ affineOver B S hS hA f)
    (hg : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I) U.1 g) :
    ∃ (J : SupportIdeal I) (k : U.1 ⟶ (supportStage B S hS hA f I J).1),
      k ≫ supportStageToAffine B S hS hA f I J = g := by
  let X := (BigAffineFppf.toScheme B S hS).obj U
  let γ : X ⟶ Spec (.of A) := (BigFppfOver.toScheme B S hS).map g
  let ρ : A →+* Γ(X, ⊤) := (Spec.preimage (X.isoSpec.inv ≫ γ)).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = X.isoSpec.inv ≫ γ :=
    Spec.map_preimage _
  have hrad : I ≤ (RingHom.ker ρ).radical := by
    intro a ha
    have hnil : IsNilpotent (ρ a) := nilpotent_iff_mem_prime.mpr fun P hP => by
      have ht := (hasImageIn_zeroLocusPoints_iff B S hS hA f I U.1 g).mp hg
        (X.isoSpec.inv (⟨P, hP⟩ : PrimeSpectrum Γ(X, ⊤)))
      have ht' : (Spec.map (CommRingCat.ofHom ρ)) (⟨P, hP⟩ : PrimeSpectrum Γ(X, ⊤)) ∈
          PrimeSpectrum.zeroLocus (I : Set A) := by
        rw [hρ]
        exact ht
      exact ht' ha
    obtain ⟨n, hn⟩ := hnil
    exact ⟨n, RingHom.mem_ker.mpr ((map_pow ρ a n).trans hn)⟩
  have hle : I.radical ≤ (RingHom.ker ρ).radical :=
    (Ideal.radical_isRadical (RingHom.ker ρ)).radical_le_iff.mpr hrad
  let J : SupportIdeal I := ⟨I ⊓ RingHom.ker ρ, by
    rw [Ideal.radical_inf, inf_eq_left.mpr hle]⟩
  let ψ := Ideal.Quotient.lift J.1 ρ fun a ha => RingHom.mem_ker.mp (Ideal.mem_inf.mp ha).2
  have hψ : ψ.comp (Ideal.Quotient.mk J.1) = ρ := by
    ext a
    rfl
  let κ : X ⟶ Spec (.of (A ⧸ J.1)) := X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)
  have hκ : κ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) = γ := by
    dsimp only [κ]
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, hρ,
      Iso.hom_inv_id_assoc]
  let k : U.1 ⟶ (supportStage B S hS hA f I J).1 := Over.homMk (ObjectProperty.homMk κ) (by
    apply ObjectProperty.hom_ext
    show κ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f =
      B.inclusion.map U.1.hom
    rw [← Category.assoc, hκ]
    exact congrArg (fun t => B.inclusion.map t) g.w)
  refine ⟨J, k, ?_⟩
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact hκ

/-- Each morphism `Spec (A ⧸ J) ⟶ Spec A` is a monomorphism, being a closed immersion. -/
private theorem supportStageToAffine_mono (J : SupportIdeal I) :
    Mono (supportStageToAffine B S hS hA f I J) := by
  have := isClosedImmersion_spec_map_mk J.1
  have : Mono ((BigFppfOver.toScheme B S hS).map (supportStageToAffine B S hS hA f I J)) :=
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))))
  exact Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) inferInstance

/-- A section through a quotient stage, followed by the colimit insertion, agrees with the
section through any later stage. -/
private theorem sheafifiedYoneda_map_comp_colimit_ι {M L : SupportIdeal I}
    {U : BigFppfOver B S hS} (m : U ⟶ (supportStage B S hS hA f I M).1)
    (jm : (ULift.up M : SupportIndex I) ⟶ ULift.up L) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫
        colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up M) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (m ≫ (BigAffineFppf.inclusion B S hS).map
            ((supportDiagram B S hS hA f I).map jm)) ≫
        colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up L) := by
  rw [← colimit.w (supportSheafDiagram B S hS hA f I) jm]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm)

/-- Two factorizations of one section through quotient stages give the same morphism into the
colimit: they agree after passing to the intersection of the two ideals, whose zero locus is
again `V(I)`, because the morphism of that smaller stage to `Spec A` is a monomorphism. -/
private theorem supportStageLift_eq {J K : SupportIdeal I} {U : BigFppfOver B S hS}
    (k : U ⟶ (supportStage B S hS hA f I J).1) (l : U ⟶ (supportStage B S hS hA f I K).1)
    (h : k ≫ supportStageToAffine B S hS hA f I J =
      l ≫ supportStageToAffine B S hS hA f I K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map l ≫
        colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up K) := by
  let L : SupportIdeal I := ⟨J.1 ⊓ K.1, by rw [Ideal.radical_inf, J.2, K.2, inf_idem]⟩
  let j : (ULift.up J : SupportIndex I) ⟶ ULift.up L :=
    supportIndexHom (show L.1 ≤ J.1 from inf_le_left)
  let k' : (ULift.up K : SupportIndex I) ⟶ ULift.up L :=
    supportIndexHom (show L.1 ≤ K.1 from inf_le_right)
  have hj : (BigAffineFppf.inclusion B S hS).map ((supportDiagram B S hS hA f I).map j) ≫
        supportStageToAffine B S hS hA f I L =
      supportStageToAffine B S hS hA f I J :=
    supportStageToAffine_transition B S hS hA f I (show L.1 ≤ J.1 from inf_le_left)
  have hk : (BigAffineFppf.inclusion B S hS).map ((supportDiagram B S hS hA f I).map k') ≫
        supportStageToAffine B S hS hA f I L =
      supportStageToAffine B S hS hA f I K :=
    supportStageToAffine_transition B S hS hA f I (show L.1 ≤ K.1 from inf_le_right)
  have := supportStageToAffine_mono B S hS hA f I L
  have he : k ≫ (BigAffineFppf.inclusion B S hS).map ((supportDiagram B S hS hA f I).map j) =
      l ≫ (BigAffineFppf.inclusion B S hS).map ((supportDiagram B S hS hA f I).map k') :=
    (cancel_mono (supportStageToAffine B S hS hA f I L)).mp <|
      (Category.assoc _ _ _).trans <| (congrArg (k ≫ ·) hj).trans <| h.trans <|
        (congrArg (l ≫ ·) hk).symm.trans (Category.assoc _ _ _).symm
  rw [sheafifiedYoneda_map_comp_colimit_ι B S hS hA f I k j,
    sheafifiedYoneda_map_comp_colimit_ι B S hS hA f I l k', he]

/-- The section of the colimit of the quotient stages over an affine object of the site
attached to a supported section there, obtained from a chosen factorization through a stage. -/
private def supportSectionLift (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1)) :
    (colimit (supportSheafDiagram B S hS hA f I)).obj.obj (Opposite.op U.1) :=
  let e := exists_supportStage_factor B S hS hA f I U x.1.down x.2
  Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map e.choose_spec.choose ≫
      colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up e.choose))

/-- The section attached to a supported section is computed by any factorization through a
quotient stage, not just the chosen one. -/
private theorem supportSectionLift_eq (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1))
    (J : SupportIdeal I) (k : U.1 ⟶ (supportStage B S hS hA f I J).1)
    (hk : k ≫ supportStageToAffine B S hS hA f I J = x.1.down) :
    supportSectionLift B S hS hA f I U x =
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
          colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J)) := by
  apply congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
  apply supportStageLift_eq B S hS hA f I
  exact (exists_supportStage_factor B S hS hA f I U x.1.down x.2).choose_spec.choose_spec.trans
    hk.symm

/-- The sections attached to supported sections are natural in the affine object of the
site. -/
private theorem supportSectionLift_map {U V : BigAffineFppf B S hS} (g : U ⟶ V)
    (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op V.1)) :
    supportSectionLift B S hS hA f I U
        ((Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor.map g.hom.op x) =
      (colimit (supportSheafDiagram B S hS hA f I)).obj.map g.hom.op
        (supportSectionLift B S hS hA f I V x) := by
  obtain ⟨J, k, hk⟩ := exists_supportStage_factor B S hS hA f I V x.1.down x.2
  rw [supportSectionLift_eq B S hS hA f I V x J k hk,
    supportSectionLift_eq B S hS hA f I U _ J (g.hom ≫ k) (by
      show (g.hom ≫ k) ≫ _ = g.hom ≫ x.1.down
      rw [Category.assoc, hk])]
  exact (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
      ((congrArg (fun z => z ≫ colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J))
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp g.hom k)).trans
        (Category.assoc _ _ _))).trans
    (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) g.hom
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J)))

/-- Restricting the tautological section of a quotient stage along a factorization of a
supported section recovers the image of that section in the completion. -/
private theorem zeroLocusCompletion_map_supportStageSection (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1))
    (J : SupportIdeal I) (k : U.1 ⟶ (supportStage B S hS hA f I J).1)
    (hk : k ≫ supportStageToAffine B S hS hA f I J = x.1.down) :
    (zeroLocusCompletion B S hS hA f I).obj.map k.op (supportStageSection B S hS hA f I J) =
      (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
        (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor).app (Opposite.op U.1) x := by
  exact sheafify_map_toSheafify_app B S hS _ _ _ <| Subtype.ext <| ULift.ext _ _ hk

/-- The comparison morphism sends the section attached to a supported section back to that
section, which is one half of its being an isomorphism. -/
private theorem supportSectionLift_comparison (U : BigAffineFppf B S hS)
    (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
      (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1)) :
    (supportComparison B S hS hA f I).hom.app (Opposite.op U.1)
        (supportSectionLift B S hS hA f I U x) =
      (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
        (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)).toFunctor).app (Opposite.op U.1) x := by
  obtain ⟨J, k, hk⟩ := exists_supportStage_factor B S hS hA f I U x.1.down x.2
  have step1 : (supportComparison B S hS hA f I).hom.app (Opposite.op U.1)
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
            colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J))) =
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
            colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J)) ≫
          supportComparison B S hS hA f I) :=
    (Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) _ _).symm
  have step2 : ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
          colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J)) ≫
        supportComparison B S hS hA f I =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
        supportStageToCompletion B S hS hA f I J :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫ z)
        (supportComparison_stage B S hS hA f I J))
  have step3 : Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k ≫
          supportStageToCompletion B S hS hA f I J) =
      (zeroLocusCompletion B S hS hA f I).obj.map k.op
        (supportStageSection B S hS hA f I J) :=
    (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) k
        (supportStageToCompletion B S hS hA f I J)).trans
      (congrArg (fun s => (zeroLocusCompletion B S hS hA f I).obj.map k.op s)
        ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply
          (supportStageSection B S hS hA f I J)))
  rw [supportSectionLift_eq B S hS hA f I U x J k hk]
  exact ((step1.trans (congrArg
    (fun z => Sheaf.sectionEquiv (BigFppfOver.topology B S hS) z) step2)).trans step3).trans
    (zeroLocusCompletion_map_supportStageSection B S hS hA f I U x J k hk)

/-- A morphism back from the completion that sends the image of each supported section over
an affine object to its attached section is a left inverse of the comparison morphism. -/
private theorem supportComparison_comp_eq_id
    (β : zeroLocusCompletion B S hS hA f I ⟶ colimit (supportSheafDiagram B S hS hA f I))
    (hβ : ∀ (U : BigAffineFppf B S hS)
      (x : (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I)).toFunctor.obj (Opposite.op U.1)),
      β.hom.app (Opposite.op U.1)
          ((GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
            (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
              (zeroLocusPoints B S hS hA f I)).toFunctor).app (Opposite.op U.1) x) =
        supportSectionLift B S hS hA f I U x) :
    supportComparison B S hS hA f I ≫ β = 𝟙 _ := by
  let C := Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
    (zeroLocusPoints B S hS hA f I)
  apply colimit.hom_ext
  intro J
  have h1 : colimit.ι (supportSheafDiagram B S hS hA f I) J ≫
        supportComparison B S hS hA f I ≫ β =
      supportStageToCompletion B S hS hA f I J.down ≫ β :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ β) (supportComparison_stage B S hS hA f I J.down))
  let xJ : C.toFunctor.obj (Opposite.op (supportStage B S hS hA f I J.down).1) :=
    ⟨ULift.up (supportStageToAffine B S hS hA f I J.down),
      supportStage_hasImageIn B S hS hA f I J.down⟩
  have hsec : Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (supportStageToCompletion B S hS hA f I J.down) =
      supportStageSection B S hS hA f I J.down :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (X := (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I J.down))
        (F := zeroLocusCompletion B S hS hA f I)).apply_symm_apply
      (supportStageSection B S hS hA f I J.down)
  have hid : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (𝟙 (supportStage B S hS hA f I J.down).1) ≫
          colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J.down) =
      colimit.ι (supportSheafDiagram B S hS hA f I) J :=
    (congrArg (fun z => z ≫ colimit.ι (supportSheafDiagram B S hS hA f I) (ULift.up J.down))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_id
        (supportStage B S hS hA f I J.down).1)).trans (Category.id_comp _)
  have hstage : supportStageToCompletion B S hS hA f I J.down ≫ β =
      colimit.ι (supportSheafDiagram B S hS hA f I) J :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (X := (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I J.down))
        (F := colimit (supportSheafDiagram B S hS hA f I))).injective
      ((Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS)
            (supportStageToCompletion B S hS hA f I J.down) β).trans
        ((congrArg (fun s => β.hom.app
            (Opposite.op (supportStage B S hS hA f I J.down).1) s) hsec).trans
          (((hβ (supportStage B S hS hA f I J.down) xJ).trans
              (supportSectionLift_eq B S hS hA f I (supportStage B S hS hA f I J.down) xJ
                J.down (𝟙 _) (Category.id_comp _))).trans
            (congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) hid))))
  exact h1.trans (hstage.trans
    (Category.comp_id (colimit.ι (supportSheafDiagram B S hS hA f I) J)).symm)

/-- The colimit of the quotient spectra `Spec (A ⧸ J)`, over the ideals `J` with the same zero
locus as `I`, is the completion `X_{/V(I)}`: the canonical comparison morphism is an
isomorphism.

Surjectivity on sections is proved by cover-density: the affine objects of the site generate
the fppf topology, and over an affine object every supported section factors through a stage.
The factorization is unique up to the stage because each `Spec (A ⧸ J) ⟶ Spec A` is a closed
immersion, hence a monomorphism. -/
theorem isIso_supportComparison : IsIso (supportComparison B S hS hA f I) := by
  let C := Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
    (zeroLocusPoints B S hS hA f I)
  let Q := colimit (supportSheafDiagram B S hS hA f I)
  let t := BigAffineFppf.inclusion B S hS
  have : t.IsCoverDense (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) t
  have : t.IsLocallyFull (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isLocallyFull (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) t
  let η := GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) C.toFunctor
  let α₀ : t.op ⋙ C.toFunctor ⟶ t.op ⋙ Q.obj :=
    { app U := TypeCat.ofHom (supportSectionLift B S hS hA f I U.unop)
      naturality U V g := by
        ext x
        exact supportSectionLift_map B S hS hA f I g.unop x }
  let α : C.toFunctor ⟶ Q.obj := Functor.IsCoverDense.sheafHom α₀
  let β : zeroLocusCompletion B S hS hA f I ⟶ Q :=
    ⟨(BigFppfOver.topology B S hS).sheafifyLift α Q.property⟩
  have hηβ : η ≫ β.hom = α :=
    GrothendieckTopology.toSheafify_sheafifyLift (BigFppfOver.topology B S hS) α Q.property
  have hβ (U : BigAffineFppf B S hS) (x : C.toFunctor.obj (Opposite.op U.1)) :
      β.hom.app (Opposite.op U.1) (η.app (Opposite.op U.1) x) =
        supportSectionLift B S hS hA f I U x := by
    show (η ≫ β.hom).app (Opposite.op U.1) x = _
    rw [hηβ]
    exact congrArg (fun z => z.app (Opposite.op U) x)
      (Functor.IsCoverDense.sheafHom_restrict_eq α₀)
  refine ⟨⟨β, supportComparison_comp_eq_id B S hS hA f I β hβ, ?_⟩⟩
  apply Sheaf.hom_ext
  apply GrothendieckTopology.sheafify_hom_ext (BigFppfOver.topology B S hS) _ _
    (zeroLocusCompletion B S hS hA f I).property
  apply (Functor.IsCoverDense.restrictHomEquivHom (G := t)).symm.injective
  ext U x
  show (supportComparison B S hS hA f I).hom.app (Opposite.op U.unop.1)
    (β.hom.app (Opposite.op U.unop.1) (η.app (Opposite.op U.unop.1) x)) =
      η.app (Opposite.op U.unop.1) x
  rw [hβ]
  exact supportSectionLift_comparison B S hS hA f I U.unop x

/-! ### The completion is a McQuillan affine formal algebraic space -/

/-- The chosen big fppf site carries an atlas for the completion: the coproduct of the sheaves
represented by the quotient stages is representable by an object of the site. This is the
set-theoretic condition of Stacks 0AIS in the form in which a colimit presentation supplies
it. -/
abbrev HasStageAtlas : Prop :=
  ∃ (U : BigFppfOver B S hS) (F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))),
    Nonempty (F.obj ≅ (uliftYoneda.{u + 1}).obj U) ∧
      Nonempty (F ≅ ∐ fun J : SupportIndex I ↦
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj ((supportDiagram B S hS hA f I).obj J)))

/-- The completion `X_{/V(I)}` is the colimit of the quotient spectra of the ideals with the
same zero locus as `I`. -/
theorem nonempty_iso_zeroLocusCompletion_colimit :
    Nonempty (zeroLocusCompletion B S hS hA f I ≅
      colimit (supportSheafDiagram B S hS hA f I)) := by
  have := isIso_supportComparison B S hS hA f I
  exact ⟨(asIso (supportComparison B S hS hA f I)).symm⟩

/-- The completion of an affine scheme along the zero locus of an ideal is an affine formal
algebraic space: it is the directed colimit of the spectra of the quotients by the ideals with
the same zero locus, and those quotient maps are thickenings. -/
theorem isAffineFormalAlgebraicSpace_zeroLocusCompletion
    (hatlas : HasStageAtlas B S hS hA f I) :
    IsAffineFormalAlgebraicSpace B S hS (zeroLocusCompletion B S hS hA f I) := by
  refine ⟨satisfiesSetTheoreticCondition_of_colimit B S hS (supportDiagram B S hS hA f I)
      (fun {_ _} g ↦ isThickening_supportDiagram_map B S hS hA f I g) _
      (nonempty_iso_zeroLocusCompletion_colimit B S hS hA f I) hatlas,
    SupportIndex I, inferInstance, inferInstance, inferInstance,
    supportDiagram B S hS hA f I,
    fun {_ _} g ↦ isThickening_supportDiagram_map B S hS hA f I g,
    nonempty_iso_zeroLocusCompletion_colimit B S hS hA f I⟩

/-- The section-ring projections of the presentation of the completion are surjective: the
sections over the stage of `J` are `A ⧸ J`, the ring `A` surjects onto each of them, and the
classes of a single element of `A` form a compatible family. -/
theorem hasSurjectiveSectionProjections_supportDiagram :
    HasSurjectiveSectionProjections B S hS (supportDiagram B S hS hA f I) := by
  let χ : ∀ J : SupportIdeal I, CommRingCat.of (A ⧸ J.1) ≅
      Scheme.Γ.obj (Opposite.op ((BigAffineFppf.toScheme B S hS).obj
        (supportStage B S hS hA f I J))) :=
    fun J ↦ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J.1))).symm
  have hcompat : ∀ {k l : SupportIndex I} (g : k ⟶ l) (a : A),
      Scheme.Γ.map (((BigAffineFppf.toScheme B S hS).map
            ((supportDiagram B S hS hA f I).map g)).op)
          ((χ l.down).hom (Ideal.Quotient.mk l.down.1 a)) =
        (χ k.down).hom (Ideal.Quotient.mk k.down.1 a) := by
    intro k l g a
    let φ := CommRingCat.ofHom (Ideal.Quotient.factor (supportIndex_le g))
    have hnat : φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ k.down.1))).inv =
        (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ l.down.1))).inv ≫
          Scheme.Γ.map ((Spec.map φ).op) :=
      (Scheme.ΓSpecIso_inv_naturality φ).trans
        (congrArg (fun m ↦ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ l.down.1))).inv ≫ m)
          (Scheme.Γ_map_op (Spec.map φ)).symm)
    have happ := congrArg (fun m : CommRingCat.of (A ⧸ l.down.1) ⟶
        Scheme.Γ.obj (Opposite.op ((BigAffineFppf.toScheme B S hS).obj
          (supportStage B S hS hA f I k.down))) ↦ m (Ideal.Quotient.mk l.down.1 a)) hnat
    have hφ : φ (Ideal.Quotient.mk l.down.1 a) = Ideal.Quotient.mk k.down.1 a :=
      Ideal.Quotient.factor_mk (supportIndex_le g) a
    show Scheme.Γ.map ((Spec.map φ).op)
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ l.down.1))).inv (Ideal.Quotient.mk l.down.1 a)) =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ k.down.1))).inv (Ideal.Quotient.mk k.down.1 a)
    rw [← hφ]
    exact happ.symm
  intro i t
  obtain ⟨a, ha⟩ : ∃ a : A, (χ i.down).hom (Ideal.Quotient.mk i.down.1 a) = t := by
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((χ i.down).inv t)
    exact ⟨w, by
      rw [hw]
      exact (χ i.down).inv_hom_id_apply t⟩
  exact ⟨⟨fun k ↦ (χ k.unop.down).hom (Ideal.Quotient.mk k.unop.down.1 a),
    fun {_ _} g ↦ hcompat g.unop a⟩, ha⟩

/-- The completion of an affine scheme along the zero locus of an ideal is a McQuillan affine
formal algebraic space. -/
theorem hasSomeSurjectivePresentation_zeroLocusCompletion
    (hatlas : HasStageAtlas B S hS hA f I) :
    HasSomeSurjectivePresentation B S hS (zeroLocusCompletion B S hS hA f I) :=
  ⟨isAffineFormalAlgebraicSpace_zeroLocusCompletion B S hS hA f I hatlas,
    SupportIndex I, inferInstance, inferInstance, inferInstance,
    supportDiagram B S hS hA f I,
    fun {_ _} g ↦ isThickening_supportDiagram_map B S hS hA f I g,
    nonempty_iso_zeroLocusCompletion_colimit B S hS hA f I,
    hasSurjectiveSectionProjections_supportDiagram B S hS hA f I⟩

/-- **Stacks 0AIY.** Let `S` be a scheme, let `X = Spec A` be an affine scheme over `S` lying
in the big fppf site and let `T ⊆ |X|` be a closed subset. The completion of `X` along `T` —
the fppf sheaf attached to the functor sending `U` to the set of morphisms `f : U ⟶ X` with
`f(|U|) ⊆ T` — is a McQuillan affine formal algebraic space: it is the directed colimit of the
affine thickenings `Spec (A ⧸ J)` over the ideals `J` with `V(J) = T`, and the projections from
the inverse limit of the section rings of that presentation onto each stage are surjective. -/
@[stacks 0AIY "McQuillan affine formal algebraic space"]
theorem hasSomeSurjectivePresentation_completionSheaf
    (T : Set ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA f))) (hT : IsClosed T)
    (hatlas : HasStageAtlas B S hS hA f (PrimeSpectrum.vanishingIdeal T)) :
    HasSomeSurjectivePresentation B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f))
        (supportedPoints B S hS (affineOver B S hS hA f) T)) := by
  have hTz : T = PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal T : Set A) :=
    hT.closure_eq.symm.trans
      (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure T).symm
  have hpts : supportedPoints B S hS (affineOver B S hS hA f) T =
      zeroLocusPoints B S hS hA f (PrimeSpectrum.vanishingIdeal T) :=
    (congrArg (supportedPoints B S hS (affineOver B S hS hA f)) hTz).trans
      (supportedPoints_zeroLocus B S hS hA f (PrimeSpectrum.vanishingIdeal T))
  rw [hpts]
  exact hasSomeSurjectivePresentation_zeroLocusCompletion B S hS hA f _ hatlas

end AlgebraicGeometry.FormalSpace

end
