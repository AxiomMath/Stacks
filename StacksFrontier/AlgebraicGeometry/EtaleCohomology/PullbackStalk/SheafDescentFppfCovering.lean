module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentFppf

/-!
# Étale sheaves descend along fppf coverings

Let `{f i : X i ⟶ Y}` be an fppf covering of schemes. [Stacks, Tag 0GF3] says that the canonical
functor from sheaves on the small étale site of `Y` to descent data for small étale sheaves with
respect to the covering is an equivalence of categories.

This is the many-member version of [Stacks, Tag 0GF2], whose reduction to two inputs the library
runs for a one-member covering in
`AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_fppf`. The source
deduces it from that lemma applied to the single morphism `∐ X i ⟶ Y`, saying that "a formal
argument shows that descent data for `f` are the same thing as descent data for the covering"
and omitting the details, with a pointer to [Stacks, Tag 023X] for the analogous statement about
descent data for schemes, which is the only form the library has
(`AlgebraicGeometry.DescentData.familyCoproductEquivalence`). For sheaves that formal argument
needs the decomposition of the small étale topos of a disjoint union, which this library does not
have, so it is not the route taken here:
instead the argument for [Stacks, Tag 0GF2] already in the library is run again for a family,
which is possible because every one of its inputs is available for families. Namely
[Stacks, Tag 0CP0], that is
`AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_isAffine`, is stated in
this library for an arbitrary fppf covering, and the sections of the two base
changes occurring in the dévissage of [Stacks, Tag 0GF1] are built member by member exactly as
in the one-member case; only the member of the covering through which a given open subscheme
factors now varies with that open subscheme.

The two arguments that the library's reduction of [Stacks, Tag 0GF2] takes are taken here in
their family versions, and for the same reasons; see
`AlgebraicGeometry.SmallEtaleSheafFamilyDescentZariskiLocal` and
`AlgebraicGeometry.SmallEtaleSheafFamilyDescentIntegralDevissage`.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafFamilyDescentFunctor` is the canonical functor from sheaves
  on the small étale site of `Y` to descent data for a family of morphisms to `Y`. For a
  one-member family it is the functor of [Stacks, Tag 0GEY] used in the library's argument for
  [Stacks, Tag 0GF2]; see
  `AlgebraicGeometry.smallEtaleSheafFamilyDescentFunctor_unit`.
* `AlgebraicGeometry.SmallEtaleSheafFamilyDescentZariskiLocal` and
  `AlgebraicGeometry.SmallEtaleSheafFamilyDescentIntegralDevissage` are the family versions of
  the two arguments the library's reduction of [Stacks, Tag 0GF2] takes, and are taken here.
* `AlgebraicGeometry.FamilyFiniteDominationBySections` is the conclusion of
  [Stacks, Tag 0CP0] for a covering, transported into the big étale site.

## Main results

* `AlgebraicGeometry.smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering` and the
  same name suffixed by `_of_compactSpace` run the source's argument for [Stacks, Tag 0GF2] for a
  family, reducing [Stacks, Tag 0GF3] to those two inputs, over an affine base and over a
  quasi-compact quasi-separated base respectively.

## No [Stacks, Tag 0GF3] attribute on the two reduction theorems

`AlgebraicGeometry.smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering`, and the
same name suffixed by `_of_compactSpace`, have no attribute for [Stacks, Tag 0GF3], and must not
be given one while they stand as they are. A tag
counts only on a declaration proved under the source's own hypotheses, and the only hypothesis of
Tag 0GF3 is that `{f i : X i ⟶ Y}` be an fppf covering. Those two theorems take two further
explicit arguments, `zariskiLocal` and `devissage`, and neither is a hypothesis of the source:

* `AlgebraicGeometry.SmallEtaleSheafFamilyDescentZariskiLocal` is the family version of the
  closing step of the source's proof of [Stacks, Tag 0GF2], "using that the problem is local on
  `Y` we reduce to the case where we have a section which is Lemma 0GEY". It is not one of the
  lemmas of the source's Section 59.104, [Stacks, Tag 0GEX].
* `AlgebraicGeometry.SmallEtaleSheafFamilyDescentIntegralDevissage` is the family version of the
  integral branch of [Stacks, Tag 0GF1], which the source obtains as a formal consequence of
  [Stacks, Tag 0GEZ] and [Stacks, Tag 0GF0].

Both are discussed at greater length in the module docstring of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentFppf`, which records the
same for its own two reduction theorems and names what would earn the attribute: once
[Stacks, Tag 0GEZ] and [Stacks, Tag 0GF0] land, and with them [Stacks, Tag 0GF1] in full, and
once the locality holds, the two theorems below lose both arguments by substitution, with no
change to their conclusions.

## References

* [Stacks Project, Tag 0GF3](https://stacks.math.columbia.edu/tag/0GF3)
* [Stacks Project, Tag 0GF2](https://stacks.math.columbia.edu/tag/0GF2)
* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u t

namespace AlgebraicGeometry

/-- The functor sending a small étale sheaf on `Y` to its canonical descent datum for a family
of morphisms `f i : X i ⟶ Y` of a big étale site. For a one-member family this is the functor
of [Stacks, Tag 0GEY], `AlgebraicGeometry.smallEtaleSheafDescentFunctor`. -/
public noncomputable def smallEtaleSheafFamilyDescentFunctor (B : BigEtaleSite.{u})
    {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y) :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) ⥤
      (smallEtaleSheafPullbackSystem B).pseudofunctor.DescentData f :=
  (eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor ⋙
    (smallEtaleSheafPullbackSystem B).pseudofunctor.toDescentData f

/-- For a one-member family the canonical descent functor is the one used in the library's
argument for [Stacks, Tag 0GF2]. -/
public theorem smallEtaleSheafFamilyDescentFunctor_unit (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) :
    smallEtaleSheafFamilyDescentFunctor B (fun _ : Unit ↦ f) =
      smallEtaleSheafDescentFunctor B f := rfl

/-- **Effective descent for small étale sheaves along a family is local on the base.** Descent
is effective along a family `h i : X i ⟶ Z` of morphisms of a big étale site such that each
member of an open covering of `Z` admits a section of some member of the family.

This is the family version of
`AlgebraicGeometry.SmallEtaleSheafDescentZariskiLocal`, which the library's reduction of
[Stacks, Tag 0GF2] takes as an argument, and it is taken here for the same reason: it is the
closing step 'using that the problem is local on `Y` we reduce to the case where we have a
section, which is Lemma 0GEY' of the source argument, and the small étale sheaf pseudofunctor is
not known in this library to be a prestack for any topology other than the trivial one, which is
what `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`
consumes. -/
public abbrev SmallEtaleSheafFamilyDescentZariskiLocal (B : BigEtaleSite.{u}) (I : Type t) :
    Prop :=
  ∀ {X : I → B.Scheme} {Z : B.Scheme} (h : ∀ i, X i ⟶ Z) {K : Type u} (W : K → B.Scheme)
    (j : ∀ c, W c ⟶ Z),
    (∀ c, IsOpenImmersion (B.inclusion.map (j c))) →
    (∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) →
    (∀ c, ∃ i, ∃ s : W c ⟶ X i, s ≫ h i = j c) →
    (smallEtaleSheafFamilyDescentFunctor B h).IsEquivalence

/-- **The integral branch of the dévissage of [Stacks, Tag 0GF1], for a family.** Descent of
small étale sheaves along a family of morphisms is effective once it is effective after base
change along a surjective integral morphism `g` and after base change along
`pullback.fst g g ≫ g`.

This is the family version of
`AlgebraicGeometry.SmallEtaleSheafDescentIntegralDevissage`, which the library's reduction of
[Stacks, Tag 0GF2] takes as an argument, and it is taken here for the same reason: the source
proves [Stacks, Tag 0GF1] from [Stacks, Tag 0GEZ] and [Stacks, Tag 0GF0], so it is not available
here. -/
public abbrev SmallEtaleSheafFamilyDescentIntegralDevissage (B : BigEtaleSite.{u})
    (I : Type t) : Prop :=
  ∀ {X : I → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y),
    Surjective (B.inclusion.map g) → IsIntegralHom (B.inclusion.map g) →
    (smallEtaleSheafFamilyDescentFunctor B (fun i ↦ pullback.snd (f i) g)).IsEquivalence →
    (smallEtaleSheafFamilyDescentFunctor B
      (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))).IsEquivalence →
    (smallEtaleSheafFamilyDescentFunctor B f).IsEquivalence

/-- **The conclusion of [Stacks, Tag 0CP0] for a covering `{f i}`, inside a big étale site.**
There are a surjective integral morphism `g : Z ⟶ Y` of the site and an open covering of `Z`
each member of which maps to `Y` through some member of the covering. -/
public abbrev FamilyFiniteDominationBySections (B : BigEtaleSite.{u}) {I : Type t}
    {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y) : Prop :=
  ∃ (Z : B.Scheme) (g : Z ⟶ Y), Surjective (B.inclusion.map g) ∧
    IsIntegralHom (B.inclusion.map g) ∧
    ∃ (K : Type u) (W : K → B.Scheme) (j : ∀ c, W c ⟶ Z),
      (∀ c, IsOpenImmersion (B.inclusion.map (j c))) ∧
      (∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) ∧
      ∀ c, ∃ i, ∃ t : W c ⟶ X i, j c ≫ g = t ≫ f i

/-- The first dévissage input, for a family. If each member `W c` of an open covering of `Z`
maps to `Y` through some member `f i : X i ⟶ Y` of the family over `g : Z ⟶ Y`, then the
projection `X i ×_Y Z ⟶ Z` admits a section over `W c` for that member, so descent of small
étale sheaves along the base-changed family is effective. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_of_sections
    (B : BigEtaleSite.{u}) {I : Type t}
    (zariskiLocal : SmallEtaleSheafFamilyDescentZariskiLocal B I)
    {X : I → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y) {K : Type u}
    {W : K → B.Scheme} (j : ∀ c, W c ⟶ Z)
    (hopen : ∀ c, IsOpenImmersion (B.inclusion.map (j c)))
    (hcover : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hfac : ∀ c, ∃ i, ∃ t : W c ⟶ X i, j c ≫ g = t ≫ f i) :
    (smallEtaleSheafFamilyDescentFunctor B (fun i ↦ pullback.snd (f i) g)).IsEquivalence :=
  zariskiLocal (fun i ↦ pullback.snd (f i) g) W j hopen hcover fun c => by
    obtain ⟨i, t, ht⟩ := hfac c
    exact ⟨i, pullback.lift t (j c) ht.symm, pullback.lift_snd _ _ _⟩

/-- The second dévissage input, for a family. If each member `W c` of an open covering of `Z`
maps to `Y` through some member `f i : X i ⟶ Y` of the family over `g : Z ⟶ Y`, then the
projection `X i ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z` admits a section over the preimage of `W c` under the
first projection of `Z ×_Y Z` for that member, and those preimages are an open covering, so
descent of small étale sheaves along the base-changed family is effective. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections
    (B : BigEtaleSite.{u}) {I : Type t}
    (zariskiLocal : SmallEtaleSheafFamilyDescentZariskiLocal B I)
    {X : I → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y) (g : Z ⟶ Y) {K : Type u}
    {W : K → B.Scheme} (j : ∀ c, W c ⟶ Z)
    (hopen : ∀ c, IsOpenImmersion (B.inclusion.map (j c)))
    (hcover : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hfac : ∀ c, ∃ i, ∃ t : W c ⟶ X i, j c ≫ g = t ≫ f i) :
    (smallEtaleSheafFamilyDescentFunctor B
      (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))).IsEquivalence := by
  refine zariskiLocal (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))
    (fun c => pullback (j c) (pullback.fst g g))
    (fun c => pullback.snd (j c) (pullback.fst g g)) (fun c => ?_) (fun v => ?_) (fun c => ?_)
  · have := preservesPullbacks_bigEtaleSiteInclusion B
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (B.inclusion.map_isPullback (IsPullback.of_hasPullback (j c) (pullback.fst g g)))
      (hopen c)
  · exact exists_mem_range_inclusion_map_pullback_snd B j (pullback.fst g g) hcover v
  · obtain ⟨i, t, ht⟩ := hfac c
    refine ⟨i, pullback.lift (pullback.fst (j c) (pullback.fst g g) ≫ t)
      (pullback.snd (j c) (pullback.fst g g)) ?_, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, ← ht, ← Category.assoc, pullback.condition, Category.assoc]

/-- Recognition of the output of [Stacks, Tag 0CP0] for a covering inside a big étale site: the
dominating morphism is of finite presentation, hence of finite type, so its source lies in the
site by Stacks 000R (5), and the members of the open covering are open subschemes of that
source, so they lie in the site by Stacks 000R (3). -/
public theorem familyFiniteDominationBySections_of_exists (B : BigEtaleSite.{u}) {I : Type t}
    {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    (h : ∃ (Z : Scheme.{u}) (g : Z ⟶ B.inclusion.obj Y), Surjective g ∧ IsFinite g ∧
      FinitePresentation g ∧ ∃ (K : Type u) (U : K → Z.Opens), (⨆ c, U c) = ⊤ ∧
        ∀ c, ∃ i, ∃ t : (U c).toScheme ⟶ B.inclusion.obj (X i),
          (U c).ι ≫ g = t ≫ B.inclusion.map (f i)) :
    FamilyFiniteDominationBySections B f := by
  obtain ⟨Z, g, hgsurj, hgfin, hgfp, K, U, hUtop, hUfac⟩ := h
  have hZ : Z.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g Y.property
  refine ⟨B.obj Z hZ, ObjectProperty.homMk g, hgsurj, (inferInstance : IsIntegralHom g), K,
    fun c => B.obj (U c).toScheme (Scheme.size_lt_of_isOpenImmersion (U c).ι hZ),
    fun c => ObjectProperty.homMk (U c).ι,
    fun c => (inferInstance : IsOpenImmersion (U c).ι), fun z => ?_, fun c => ?_⟩
  · have hz : z ∈ ⨆ c, U c := by rw [hUtop]; exact Opens.mem_top z
    obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hz
    refine ⟨c, ?_⟩
    show z ∈ Set.range (U c).ι
    rwa [Scheme.Opens.range_ι]
  · obtain ⟨i, t, ht⟩ := hUfac c
    exact ⟨i, ObjectProperty.homMk t, ObjectProperty.hom_ext _ ht⟩

/-- **[Stacks, Tag 0CP0] for an fppf covering of an affine base, inside a big étale site.**
Nothing is carried: the affine case of [Stacks, Tag 0CP0] is unconditional in this library. -/
public theorem familyFiniteDominationBySections_of_isAffine (B : BigEtaleSite.{u}) {I : Type t}
    {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y) [IsAffine (B.inclusion.obj Y)]
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y)) :
    FamilyFiniteDominationBySections B f := by
  obtain ⟨Z, g, hgfin, hgsurj, hgfp, K, U, hUtop, hUfac⟩ :=
    exists_finite_surjective_openCover_factorization_of_isAffine
      (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) hf
  exact familyFiniteDominationBySections_of_exists B f
    ⟨Z, g, hgsurj, hgfin, hgfp, K, U, hUtop, hUfac⟩

/-- **[Stacks, Tag 0CP0] for an fppf covering of a quasi-compact quasi-separated base, inside a
big étale site.** Nothing is carried. -/
public theorem familyFiniteDominationBySections_of_compactSpace (B : BigEtaleSite.{u})
    {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    [CompactSpace (B.inclusion.obj Y)] [QuasiSeparatedSpace (B.inclusion.obj Y)]
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y)) :
    FamilyFiniteDominationBySections B f := by
  obtain ⟨Z, g, hgfin, hgsurj, hgfp, K, U, hUtop, hUfac⟩ :=
    exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage
      (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) hf
  exact familyFiniteDominationBySections_of_exists B f
    ⟨Z, g, hgsurj, hgfin, hgfp, K, U, hUtop, hUfac⟩

/-- **The reduction of [Stacks, Tag 0GF3] to its two dévissage inputs.** Descent of small étale
sheaves is effective along a family of morphisms dominated, in the sense of
[Stacks, Tag 0CP0], by a surjective integral morphism whose source carries an open covering each
member of which factors through some member of the family. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_finiteDomination
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    (zariskiLocal : SmallEtaleSheafFamilyDescentZariskiLocal B I)
    (devissage : SmallEtaleSheafFamilyDescentIntegralDevissage B I)
    (hdom : FamilyFiniteDominationBySections B f) :
    (smallEtaleSheafFamilyDescentFunctor B f).IsEquivalence := by
  obtain ⟨Z, g, hgsurj, hgint, K, W, j, hopen, hcover, hfac⟩ := hdom
  exact devissage f g hgsurj hgint
    (smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_of_sections B zariskiLocal
      f g j hopen hcover hfac)
    (smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections B
      zariskiLocal f g j hopen hcover hfac)

/-- **[Stacks, Tag 0GF3] for an affine base.** Let `{f i : X i ⟶ Y}` be a family of morphisms of
a big étale site whose underlying family of morphisms of schemes is an fppf covering, and let `Y`
be affine. Then the canonical functor from sheaves on the small étale site of `Y` to descent data
for small étale sheaves with respect to the covering is an equivalence of categories.

What is proved is the source's argument for [Stacks, Tag 0GF2] run for a family rather than its
reduction to the one-member case along the coproduct of the covering: [Stacks, Tag 0CP0] is
discharged for the covering with no hypothesis beyond affineness of the base, its output is
recognized inside the site, and the two base changes of the family that the dévissage of
[Stacks, Tag 0GF1] asks about are shown to admit sections over an open covering of their targets
— for each member of those open coverings, a section of the base change of the member of the
given covering through which it factors. The conclusion is the full equivalence of categories,
for an arbitrary index type, so nothing of the statement is narrowed to one of its halves. The
dévissage itself and the locality of effective descent on the base are the two arguments
`devissage` and `zariskiLocal`, in their family versions; because they are not hypotheses of the
source, this theorem registers no attribute for [Stacks, Tag 0GF3], and the module docstring says
what would earn it.

The source's own route is not taken: it reduces to [Stacks, Tag 0GF2] for the single morphism
`∐ X i ⟶ Y` and then identifies descent data for that morphism with descent data for the
covering by a formal argument whose details it omits, pointing at [Stacks, Tag 023X] for the
analogue for schemes. That identification needs the decomposition of the small étale topos of a
disjoint union, which this library does not have; its [Stacks, Tag 023X] is the statement for
descent data for schemes, `AlgebraicGeometry.DescentData.familyCoproductEquivalence`. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    [IsAffine (B.inclusion.obj Y)]
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y))
    (zariskiLocal : SmallEtaleSheafFamilyDescentZariskiLocal B I)
    (devissage : SmallEtaleSheafFamilyDescentIntegralDevissage B I) :
    (smallEtaleSheafFamilyDescentFunctor B f).IsEquivalence :=
  smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_finiteDomination B f zariskiLocal
    devissage (familyFiniteDominationBySections_of_isAffine B f hf)

/-- **[Stacks, Tag 0GF3] for a quasi-compact quasi-separated base.** Let `{f i : X i ⟶ Y}` be a
family of morphisms of a big étale site whose underlying family of morphisms of schemes is an
fppf covering, and let `Y` be quasi-compact and quasi-separated. Then the canonical functor from
sheaves on the small étale site of `Y` to descent data for small étale sheaves with respect to
the covering is an equivalence of categories.

This is the base of the source statement, which asks for no hypothesis on `Y`, up to quasi-
compactness and quasi-separatedness, which is what [Stacks, Tag 0CP0] asks for. The conclusion is
again the full equivalence of categories, for an arbitrary index type. The two arguments
`zariskiLocal` and `devissage` are the same two as on
`AlgebraicGeometry.smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering`, and there
are no others: the library's [Stacks, Tag 0CP0],
`AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage`,
holds at a quasi-compact quasi-separated base with nothing further supplied. For the same reason
as there, this theorem registers no attribute for [Stacks, Tag 0GF3]; see the module docstring. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_of_compactSpace
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    [CompactSpace (B.inclusion.obj Y)] [QuasiSeparatedSpace (B.inclusion.obj Y)]
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y))
    (zariskiLocal : SmallEtaleSheafFamilyDescentZariskiLocal B I)
    (devissage : SmallEtaleSheafFamilyDescentIntegralDevissage B I) :
    (smallEtaleSheafFamilyDescentFunctor B f).IsEquivalence :=
  smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_finiteDomination B f zariskiLocal
    devissage (familyFiniteDominationBySections_of_compactSpace B f hf)

end AlgebraicGeometry

end
