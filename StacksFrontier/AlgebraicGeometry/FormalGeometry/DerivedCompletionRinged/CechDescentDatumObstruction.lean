module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCech
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCechAlternating
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCechLocalIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# The displayed Čech complexes carry no descent datum

One route to [Stacks, Tag 099E] for a sheaf of ideals `ℐ ⊆ 𝒪` that is only *locally*
generated would be the passage from the complexes `K_{U_i} ⟶ 𝒪_{U_i}` on the slices of a
cover to a single `K ⟶ 𝒪` on the site. Two routes present themselves, and both consume the
*same* input: a family of comparison maps between the local models that is a **descent datum**,
i.e. a family of *isomorphisms of complexes* over the overlaps satisfying the cocycle condition,
since that is what `CategoryTheory.Pseudofunctor.DescentData` — the input of the effectivity
theorem [Stacks, Tag 04TR],
`CategoryTheory.GrothendieckTopology.essSurj_toDescentData_pseudofunctorOver` — consists of, for
any pseudofunctor into categories of complexes of sheaves of modules.

**This file proves that the complexes the tag displays admit no such family.** Take any ringed
site whose structure sheaf is not a zero object, let `1` be the unit global section of `𝒪`, and
for `0 < r < s` compare the two constant families

`f = (1, …, 1)` of length `r` and `g = (1, …, 1)` of length `s`.

They span the same ideal of sections — *the unit ideal* — over **every** object of the site, so
they generate the same sheaf of ideals, and they continue to do so after restriction along every
arrow and over every member of every covering: no refinement of any cover can separate them.
Accordingly the comparison map
`AlgebraicGeometry.RingedSite.sheafifiedCechRestrict` between their Čech objects is a
quasi-isomorphism over `𝒪` — `AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict`
applies on the nose. Yet the two complexes are **not isomorphic**: the extended alternating Čech
complex on `r` sections is zero in degrees above `r`, while the one on `g` has
`𝒪_{1 ⋯ 1} ≅ 𝒪 ≠ 0` in degree `s`.

So the quasi-isomorphism relating two generating families cannot be upgraded to an isomorphism of
complexes, not even locally, and not even when the two families agree on the unit ideal over
every object. The obstruction is a term count and not an arithmetic accident: it survives every
localization and every base change.

### The two lengths cannot be equalised away

The count is a count of *lengths*, so it is worth being precise about what it does and does not
close. A descent datum is a family of isomorphisms between the **restrictions** of the chosen
local models, so the lengths appearing over an overlap of `V_i` and `V_j` are the lengths `r_i`
and `r_j` of the families chosen on `V_i` and on `V_j`: they are fixed before the overlap is
reached, and the statements below apply whenever they differ.

One may try to make them agree in advance, by padding each chosen family with copies of `1` up to
a common length `N`. Two things stand in the way, and **both are proved here**. Such an `N` would
be a *uniform* bound on the number of local generators over the whole covering family, and the
finite-type condition supplies no such bound — it gives one covering family and, over each member
separately, some finite number of generators, with the covering family not even required to be
indexed by a finite type
(`AlgebraicGeometry.RingedSite.exists_coversTop_eq_idealOfGlobalSections_overIdeal`). And a common
length does not help even when it is available: the padded families still differ in their entries,
and then the degree-`N` terms are the localizations of `𝒪` at two different sections. Compare

`(1, 0)` and `(1, 1)`,

both of length two, both spanning the unit ideal of sections over every object, hence generating
the same sheaf of ideals, hence — `exists_iso_sheafifiedCech_oneZeroFamily` below — with
isomorphic Čech objects in `D(𝒪)` over `𝒪`. In degree two the complexes are `𝒪_{1 · 0} = 𝒪_0` and
`𝒪_{1 · 1} ≅ 𝒪`, and the first is **zero**: inverting the zero section makes every ring of
sections trivial. So they are not isomorphic as complexes either
(`isEmpty_iso_extendedAlternatingCech_oneZeroFamily`,
`isEmpty_iso_sheafifiedCech_oneZeroFamily`).

## What this rules out, and what it leaves

It rules out assembling descent data out of the tag's displayed complexes. Any route to the
gluing must therefore replace those complexes by models attached to the *ideal* rather than to a
generating family: for two finitely generated `I, I' ⊆ ℐ(U)` generating `ℐ|_U` there is a
covering `{U_j → U}` with `I𝒪(U_j) = I'𝒪(U_j)`
(`AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq`), and a model depending only on the
ideal is then *literally the same* over each `U_j`, so the descent datum is the identity and the
cocycle condition is vacuous. A model depending only on the ideal and functorial in the ring is
exactly [Stacks, Tag 099D], the interface
`Stacks.LocalCohomology.FunctorialCechData`.

It does **not** rule out the gluing itself, and it is not a statement about `D(𝒪)`: the two
objects *are* isomorphic there. What it says is that the 1-categorical effectivity theorem for
complexes of sheaves of modules cannot be fed by the displayed complexes, because its input is
isomorphisms of complexes.

This complements the other half of the obstruction, which is about the generating family rather
than the complex: a choice of finite generating family transported by every ring map does not
exist (`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators` and
`Stacks.FunctorialCechFamily.not_transportedFamily` of
`StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean`). Together they say: one
cannot choose the families coherently, and one cannot compare the complexes of two families
strictly. The complex must be built from the ideal.

**Status.** [Stacks, Tag 099E] is proved for an arbitrary sheaf of ideals, as
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech` of `FiniteTypeExtendedCech.lean`,
and [Stacks, Tag 099F] follows from it as
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of `FiniteTypeReflector.lean`.
Neither [Stacks, Tag 099D] nor any gluing is used there: the presheaf of Čech complexes of *all*
local generators of `ℐ` — a filtered colimit, hence a presheaf with no choice made — is
sheafified on `𝒞`, and on each slice the leg into it from the Čech complex of one generating
family is locally bijective on homology. Where the notes
below say that 099E is missing or needs gluing, they record the state of the library before
that construction.

## Main definitions

* `AlgebraicGeometry.RingedSite.oneGlobalSection` and
  `AlgebraicGeometry.RingedSite.zeroGlobalSection`: the unit and the zero global section of `𝒪`.
* `AlgebraicGeometry.RingedSite.oneFamily`: the constant family of `r` copies of the unit section,
  and `AlgebraicGeometry.RingedSite.oneZeroFamily` the length-two family `(1, 0)`.

## Main results

* `CategoryTheory.AlternatingCech.isZero_complex_X_of_lt`: the extended alternating Čech complex
  on `r` sections vanishes in degrees above `r`.
* `CategoryTheory.AlternatingCech.isZero_obj_univ_of_iso`: **if the extended alternating Čech
  complexes of two systems indexed by `Fin r` and `Fin s` with `r < s` are isomorphic, then the
  top object of the longer system is zero.**
* `AlgebraicGeometry.RingedSite.span_range_restrictGlobalSections_oneFamily`: the constant
  families span the unit ideal of sections over every object, hence all span the same one.
* `AlgebraicGeometry.RingedSite.idealOfGlobalSections_oneFamily`: and they generate the same
  sheaf of ideals.
* `AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict_oneFamily` and
  `AlgebraicGeometry.RingedSite.sheafifiedCechRestrict_oneFamily_comp_augmentation`: **the
  comparison of their Čech objects is a quasi-isomorphism over `𝒪`.**
* `AlgebraicGeometry.RingedSite.isEmpty_iso_extendedAlternatingCech_oneFamily` and
  `AlgebraicGeometry.RingedSite.isEmpty_iso_sheafifiedCech_oneFamily`: **and it is not an
  isomorphism of complexes — there is none**, on any ringed site whose structure sheaf is not a
  zero object.
* `CategoryTheory.AlternatingCech.isZero_obj_univ_of_iso_of_isZero`: the obstruction for two
  systems of the *same* length, where the degree count says nothing.
* `AlgebraicGeometry.RingedSite.isZero_awayModule_of_forall_globalSectionVal_eq_zero`: inverting
  the zero section gives the zero sheaf of modules.
* `AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_oneZeroFamily`,
  `AlgebraicGeometry.RingedSite.isEmpty_iso_extendedAlternatingCech_oneZeroFamily` and
  `AlgebraicGeometry.RingedSite.isEmpty_iso_sheafifiedCech_oneZeroFamily`: **the families `(1, 0)`
  and `(1, 1)` have the same length, generate the same sheaf of ideals, have isomorphic Čech
  objects in `D(𝒪)` over `𝒪`, and have no isomorphism of complexes between them** — so padding
  the chosen families to a common length does not produce a descent datum either.

## Implementation notes

The degree count is done once, abstractly, for an arbitrary system `F : Finset (Fin r) ⥤ 𝒜`:
above degree `r` the index type `CategoryTheory.AlternatingCech.Idx r p` is empty, so the term is
an empty product, which in a preadditive category is a zero object because its identity is the
only map into it; and in degree `r` the index type is a singleton — the full subset — so the term
is the single factor `F(Fin r)`. The two statements together are the whole obstruction; the
ringed-site input is only that `𝒪_{1} ≅ 𝒪`, which is
`AlgebraicGeometry.RingedSite.awaySheafIsoOfIsUnit` at the section `1`, exactly as
`AlgebraicGeometry.RingedSite.unitIsoAwayModuleEmpty` reads the degree-zero term.

Both spellings of the tag's object are covered: the statement is proved for
`AlgebraicGeometry.RingedSite.extendedAlternatingCech`, the complex of the display, and then
transported to `AlgebraicGeometry.RingedSite.sheafifiedCech`, the sheafified presheaf of Čech
complexes, along
`AlgebraicGeometry.RingedSite.sheafifiedCechIsoExtendedAlternatingCech`.

No `@[stacks 099E]` attribute is attached: nothing here proves any assertion of that tag. The
file measures one proposed route to it, which the proof of the tag,
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech` of `FiniteTypeExtendedCech.lean`,
does not take.

## References

* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR)
* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.AlternatingCech

variable {r s : ℕ} {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]

/-- **The extended alternating Čech complex on `r` sections vanishes in degrees above `r`**: no
subset of `Fin r` has more than `r` elements, so the degree-`p` term is an empty product, whose
identity is its only endomorphism. -/
theorem isZero_complex_X_of_lt (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} (hp : (r : ℤ) < p) :
    IsZero ((complex F).X p) := by
  rw [IsZero.iff_id_eq_zero]
  refine Pi.hom_ext _ _ fun b ↦ ?_
  exact (isEmpty_idx_of_lt hp).elim b

/-- The full subset is the unique subset of `Fin r` of cardinality `r`. This is not registered as
an instance: for `r = 0` it would compete with
`CategoryTheory.AlternatingCech.uniqueIdxZero`. -/
@[instance_reducible]
def uniqueIdxCard (r : ℕ) : Unique (Idx r (r : ℤ)) where
  default := ⟨Finset.univ, by simp⟩
  uniq S := Subtype.ext (Finset.eq_univ_of_card _ (by
    have h : (S.1.card : ℤ) = (r : ℤ) := S.2
    have h' : S.1.card = r := by exact_mod_cast h
    simp [h']))

/-- **The top term of the extended alternating Čech complex on `r` sections is the single factor
`F(Fin r)`**, the full subset being the only subset of cardinality `r`. -/
def complexXIsoObjUniv (F : Finset (Fin r) ⥤ 𝒜) :
    (complex F).X (r : ℤ) ≅ F.obj Finset.univ :=
  let := uniqueIdxCard r
  productUniqueIso _

/-- **The extended alternating Čech complexes of two systems indexed by `Fin r` and by `Fin s`
with `r < s` are isomorphic only if the top object of the longer system is a zero object.**

In degree `s` the shorter complex is zero, there being no subset of `Fin r` of cardinality `s`,
while the longer one is the single factor at the full subset. This is a count of terms: it uses
nothing about the systems, so no localization, base change or refinement of a covering can evade
it. -/
theorem isZero_obj_univ_of_iso (hrs : r < s) (F : Finset (Fin r) ⥤ 𝒜) (G : Finset (Fin s) ⥤ 𝒜)
    (e : complex F ≅ complex G) : IsZero (G.obj Finset.univ) := by
  have h0 : IsZero ((complex F).X (s : ℤ)) :=
    isZero_complex_X_of_lt F (by exact_mod_cast hrs)
  have h1 : IsZero ((complex G).X (s : ℤ)) :=
    h0.of_iso ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) (s : ℤ)).mapIso e).symm
  exact h1.of_iso (complexXIsoObjUniv G).symm

/-- **An isomorphism of the extended alternating Čech complexes of two systems indexed by the
same `Fin r` identifies their top objects**, both being the single factor in degree `r`. -/
def complexObjUnivIso {F G : Finset (Fin r) ⥤ 𝒜} (e : complex F ≅ complex G) :
    F.obj Finset.univ ≅ G.obj Finset.univ :=
  (complexXIsoObjUniv F).symm ≪≫
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) (r : ℤ)).mapIso e ≪≫ complexXIsoObjUniv G

/-- **Two systems indexed by the same `Fin r` whose top objects are not both zero have
non-isomorphic extended alternating Čech complexes.** This is the obstruction for families of
*equal* length, where the degree count of
`CategoryTheory.AlternatingCech.isZero_obj_univ_of_iso` says nothing. -/
theorem isZero_obj_univ_of_iso_of_isZero {F G : Finset (Fin r) ⥤ 𝒜} (e : complex F ≅ complex G)
    (hF : IsZero (F.obj Finset.univ)) : IsZero (G.obj Finset.univ) :=
  hF.of_iso (complexObjUnivIso e).symm

end CategoryTheory.AlternatingCech

namespace AlgebraicGeometry.RingedSite

section Sections

variable (X : RingedSite.{u, v, w})

/-- **The unit global section `1` of the structure sheaf**, obtained as the empty subproduct of
the empty family: `AlgebraicGeometry.RingedSite.prodGlobalSection` at `S = ∅` is `1` by
construction. -/
def oneGlobalSection : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}) :=
  prodGlobalSection (X := X) (fun i : Fin 0 ↦ i.elim0) ∅

/-- The unit global section takes the value `1` over every object. -/
@[simp]
theorem globalSectionVal_oneGlobalSection (U : X.Cᵒᵖ) :
    globalSectionVal (oneGlobalSection X) U = 1 := by
  simp [oneGlobalSection]

/-- The family of `r` copies of the unit global section. For `r ≥ 1` it generates the unit ideal
sheaf, whatever `r` is, which is what makes it the test case for comparing Čech complexes of
different lengths. -/
def oneFamily (r : ℕ) : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}) :=
  fun _ ↦ oneGlobalSection X

/-- Every member of `AlgebraicGeometry.RingedSite.oneFamily` is the unit global section. -/
@[simp]
theorem oneFamily_apply (r : ℕ) (i : Fin r) : oneFamily X r i = oneGlobalSection X := rfl

/-- Every subproduct of the constant family of units is `1`, hence so is every power of it. -/
theorem isUnit_pow_globalSectionVal_prodGlobalSection_oneFamily (r : ℕ) (S : Finset (Fin r))
    (U : X.Cᵒᵖ) (n : ℕ) :
    IsUnit (globalSectionVal (prodGlobalSection (oneFamily X r) S) U ^ n) := by
  simp

/-- **The zero global section of the structure sheaf.** -/
def zeroGlobalSection : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}) :=
  (Presheaf.globalSectionsEquivSections _).symm
    ⟨fun _ ↦ 0, fun {U V} g ↦ by
      change (X.O.obj.map g).hom 0 = 0
      exact map_zero _⟩

/-- The zero global section takes the value `0` over every object. -/
@[simp]
theorem globalSectionVal_zeroGlobalSection (U : X.Cᵒᵖ) :
    globalSectionVal (zeroGlobalSection X) U = 0 := by
  simp [zeroGlobalSection, globalSectionVal]

/-- The length-two family `(1, 0)`. It spans the unit ideal of sections over every object, exactly
as `(1, 1)` does, and it has the *same length*, so that no padding of the two families to a common
length can bring them together. -/
def oneZeroFamily : Fin 2 → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}) :=
  ![oneGlobalSection X, zeroGlobalSection X]

/-- The full subproduct of `(1, 0)` is `0`. -/
@[simp]
theorem globalSectionVal_prodGlobalSection_oneZeroFamily_univ (U : X.Cᵒᵖ) :
    globalSectionVal (prodGlobalSection (oneZeroFamily X) Finset.univ) U = 0 := by
  rw [globalSectionVal_prodGlobalSection, Fin.prod_univ_two]
  simp [oneZeroFamily]

end Sections

section Span

variable (X : RingedSite.{u, u, u}) {r : ℕ}

/-- **The constant family of units spans the unit ideal of sections over every object.** In
particular any two of these families, of any two positive lengths, span the same ideal of sections
over every object of the site — the hypothesis of
`AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict`, with no covering needed. -/
theorem span_range_restrictGlobalSections_oneFamily (hr : 0 < r) (V : X.Cᵒᵖ) :
    Ideal.span (Set.range (restrictGlobalSections X (oneFamily X r) V)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span ⟨⟨0, hr⟩, globalSectionVal_oneGlobalSection X V⟩)

/-- A family whose sections span the unit ideal over every object generates the unit sheaf of
ideals, so it generates every sheaf of ideals generated by a family. -/
private theorem idealOfGlobalSections_le_of_span_eq_top {s : ℕ}
    (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (g : Fin s → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (hg : ∀ V : X.Cᵒᵖ, Ideal.span (Set.range (restrictGlobalSections X g V)) = ⊤) :
    idealOfGlobalSections X f ≤ idealOfGlobalSections X g :=
  idealOfGlobalSections_le X _ fun _ V ↦
    mem_idealOfGlobalSections_of_mem_span X g V (by rw [hg V]; exact Submodule.mem_top)

/-- **The constant families of units all generate the unit sheaf of ideals**, so two of them of
different lengths generate the same sheaf of ideals: each one's generators are literally among the
other's. -/
theorem idealOfGlobalSections_oneFamily {r' : ℕ} (hr : 0 < r) (hr' : 0 < r') :
    idealOfGlobalSections X (oneFamily X r) = idealOfGlobalSections X (oneFamily X r') :=
  le_antisymm
    (idealOfGlobalSections_le_of_span_eq_top X _ _
      (span_range_restrictGlobalSections_oneFamily X hr'))
    (idealOfGlobalSections_le_of_span_eq_top X _ _
      (span_range_restrictGlobalSections_oneFamily X hr))

/-- **`(1, 0)` spans the unit ideal of sections over every object too** — its first member is
already `1`. So it spans the same ideal of sections as `(1, 1)` over every object, and the two
have the same length. -/
theorem span_range_restrictGlobalSections_oneZeroFamily (V : X.Cᵒᵖ) :
    Ideal.span (Set.range (restrictGlobalSections X (oneZeroFamily X) V)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span ⟨0, globalSectionVal_oneGlobalSection X V⟩)

/-- **`(1, 0)` and `(1, 1)` generate the same sheaf of ideals** — the unit one. Each family spans
the whole ring of sections over every object, so every section of either generated ideal sheaf is
already a section of the other. -/
theorem idealOfGlobalSections_oneZeroFamily :
    idealOfGlobalSections X (oneZeroFamily X) = idealOfGlobalSections X (oneFamily X 2) :=
  le_antisymm
    (idealOfGlobalSections_le_of_span_eq_top X _ _
      (span_range_restrictGlobalSections_oneFamily X (r := 2) (by norm_num)))
    (idealOfGlobalSections_le_of_span_eq_top X _ _
      (span_range_restrictGlobalSections_oneZeroFamily X))

end Span

section Obstruction

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r s : ℕ}

/-- `𝒪_{1_S} ≅ 𝒪` for every subproduct of the constant family of units: inverting an already
invertible section changes nothing. This is
`AlgebraicGeometry.RingedSite.unitIsoAwayModuleEmpty` with the empty subset replaced by an
arbitrary one. -/
def unitIsoAwayModuleOneFamily (r : ℕ) (S : Finset (Fin r)) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      awayModule X (prodGlobalSection (oneFamily X r) S) :=
  SheafOfModules.unitIsoRestrictScalarsUnit
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      (awaySheafIsoOfIsUnit _
        (isUnit_pow_globalSectionVal_prodGlobalSection_oneFamily X r S)))

/-- **The complexes the tag displays admit no isomorphism between two constant families of units
of different lengths.** On any ringed site whose structure sheaf is not a zero object, and for
`r < s`, there is no isomorphism of complexes of sheaves of `𝒪`-modules between the extended
alternating Čech complex of `(1, …, 1)` of length `r` and that of length `s`, even though the two
families span the unit ideal of sections over every object of the site.

In degree `s` the first complex is zero, no subset of `Fin r` having `s` elements, and the second
is the single factor `𝒪_{1 ⋯ 1} ≅ 𝒪`. -/
theorem isEmpty_iso_extendedAlternatingCech_oneFamily (hrs : r < s)
    (hX : ¬ IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsEmpty (extendedAlternatingCech X (oneFamily X r) ≅
      extendedAlternatingCech X (oneFamily X s)) :=
  ⟨fun e ↦ hX
    ((AlternatingCech.isZero_obj_univ_of_iso hrs
      (awayLocalizationFunctor X (oneFamily X r))
      (awayLocalizationFunctor X (oneFamily X s)) e).of_iso
        (unitIsoAwayModuleOneFamily X s Finset.univ))⟩

/-- **Inverting the zero section gives the zero sheaf of modules.** Every power of the section
becomes invertible in `𝒪_h` (`AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf`); for the zero
section that says `0` is invertible over each object, so each ring of sections of `𝒪_h` is
trivial, and `𝒪_h` read as a sheaf of `𝒪`-modules has the same sections. -/
theorem isZero_awayModule_of_forall_globalSectionVal_eq_zero
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (h0 : ∀ U : X.Cᵒᵖ, globalSectionVal h U = 0) : IsZero (awayModule X h) := by
  rw [IsZero.iff_id_eq_zero]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  have hu : IsUnit ((0 : (awaySheaf h).val.obj U)) := by
    have := isUnit_toAwaySheaf h U 1
    rwa [pow_one, h0 U, map_zero] at this
  have : Subsingleton ((awaySheaf h).val.obj U) :=
    subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
  have : Subsingleton ((awayModule X h).val.obj U) := this
  ext x
  exact congrArg _ (Subsingleton.elim x 0)

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]

/-- The subfamily inclusion of the constant family of units of length `r` into the one of
length `s`, for `r ≤ s`. -/
def oneFamilyEmbedding (hle : r ≤ s) : Fin r ↪o Fin s := Fin.castLEOrderEmb hle

omit [HasWeakSheafify X.J CommRingCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The constant family of units of length `s`, restricted along `oneFamilyEmbedding`, is the
constant family of units of length `r`. -/
theorem oneFamily_oneFamilyEmbedding (hle : r ≤ s) (i : Fin r) :
    oneFamily X s (oneFamilyEmbedding hle i) = oneFamily X r i := rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The comparison of the Čech objects of two constant families of units is a
quasi-isomorphism.** They span the same ideal of sections over every object, so
`AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict` applies with no covering
intervening. -/
theorem quasiIso_sheafifiedCechRestrict_oneFamily (hr : 0 < r) (hle : r ≤ s) :
    QuasiIso (sheafifiedCechRestrict X (oneFamily X r) (oneFamily X s) (oneFamilyEmbedding hle)
      (oneFamily_oneFamilyEmbedding X hle)) :=
  quasiIso_sheafifiedCechRestrict X _ _ _ _ fun V ↦ by
    rw [span_range_restrictGlobalSections_oneFamily X (lt_of_lt_of_le hr hle) V,
      span_range_restrictGlobalSections_oneFamily X hr V]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **And it is a map over `𝒪`.** -/
theorem sheafifiedCechRestrict_oneFamily_comp_augmentation (hle : r ≤ s) :
    sheafifiedCechRestrict X (oneFamily X r) (oneFamily X s) (oneFamilyEmbedding hle)
          (oneFamily_oneFamilyEmbedding X hle) ≫
        sheafifiedCechAugmentation X (oneFamily X r) =
      sheafifiedCechAugmentation X (oneFamily X s) :=
  sheafifiedCechRestrict_comp_augmentation X _ _ _ _

/-- **The sheafified presheaf of Čech complexes admits no isomorphism between two constant
families of units of different lengths either.** The two spellings of the tag's object are
isomorphic (`AlgebraicGeometry.RingedSite.sheafifiedCechIsoExtendedAlternatingCech`), so the
obstruction transports.

Together with
`AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict_oneFamily` and
`AlgebraicGeometry.RingedSite.sheafifiedCechRestrict_oneFamily_comp_augmentation` this is the
obstruction in its sharpest form: a quasi-isomorphism over `𝒪` between the two objects exists and
an isomorphism of complexes does not, so no family of isomorphisms of complexes — no descent
datum for a pseudofunctor into complexes of sheaves of modules — can be assembled from the
displayed complexes of two generating families of different lengths. -/
theorem isEmpty_iso_sheafifiedCech_oneFamily (hrs : r < s)
    (hX : ¬ IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsEmpty (sheafifiedCech X (oneFamily X r) ≅ sheafifiedCech X (oneFamily X s)) :=
  ⟨fun e ↦ (isEmpty_iso_extendedAlternatingCech_oneFamily X hrs hX).elim
    ((sheafifiedCechIsoExtendedAlternatingCech X (oneFamily X r)).symm ≪≫ e ≪≫
      sheafifiedCechIsoExtendedAlternatingCech X (oneFamily X s))⟩

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **Equalising the lengths does not help: `(1, 0)` and `(1, 1)` have the same length, generate
the same sheaf of ideals, and their Čech complexes are not isomorphic.** In degree two the first
is `𝒪_{1 · 0} = 𝒪_0`, which is zero because inverting `0` makes every ring of sections trivial,
and the second is `𝒪_{1 · 1} ≅ 𝒪`.

This closes the route of padding every chosen generating family with copies of `1` up to a common
length: a common length makes the degree counts agree and leaves the entries differing, and the
top terms of the two complexes are then the localizations at two different sections, which need
not agree. -/
theorem isEmpty_iso_extendedAlternatingCech_oneZeroFamily
    (hX : ¬ IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsEmpty (extendedAlternatingCech X (oneZeroFamily X) ≅
      extendedAlternatingCech X (oneFamily X 2)) :=
  ⟨fun e ↦ hX
    ((AlternatingCech.isZero_obj_univ_of_iso_of_isZero e
      (isZero_awayModule_of_forall_globalSectionVal_eq_zero X _
        (globalSectionVal_prodGlobalSection_oneZeroFamily_univ X))).of_iso
      (unitIsoAwayModuleOneFamily X 2 Finset.univ))⟩

/-- **The same for the sheafified presheaf of Čech complexes.** -/
theorem isEmpty_iso_sheafifiedCech_oneZeroFamily
    (hX : ¬ IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsEmpty (sheafifiedCech X (oneZeroFamily X) ≅ sheafifiedCech X (oneFamily X 2)) :=
  ⟨fun e ↦ (isEmpty_iso_extendedAlternatingCech_oneZeroFamily X hX).elim
    ((sheafifiedCechIsoExtendedAlternatingCech X (oneZeroFamily X)).symm ≪≫ e ≪≫
      sheafifiedCechIsoExtendedAlternatingCech X (oneFamily X 2))⟩

section Derived

attribute [local instance] HasDerivedCategory.standard

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **And yet `(1, 0)` and `(1, 1)` do have isomorphic Čech objects in `D(𝒪)`, over `𝒪`.** They
generate the same sheaf of ideals, so
`AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_idealOfGlobalSections_eq` applies.

This is the obstruction at its sharpest. Two families of the *same length* generating the *same*
sheaf of ideals, isomorphic in `D(𝒪)` compatibly with the augmentations, and not isomorphic as
complexes: the comparison that the gluing of [Stacks, Tag 099E] needs exists in the derived
category and nowhere else, so the 1-categorical effectivity of descent for complexes of sheaves
of modules, whose input is isomorphisms of complexes, cannot consume it. -/
theorem exists_iso_sheafifiedCech_oneZeroFamily :
    ∃ e : DerivedCategory.Q.obj (sheafifiedCech X (oneZeroFamily X)) ≅
        DerivedCategory.Q.obj (sheafifiedCech X (oneFamily X 2)),
      e.hom ≫ DerivedCategory.Q.map (sheafifiedCechAugmentation X (oneFamily X 2)) =
        DerivedCategory.Q.map (sheafifiedCechAugmentation X (oneZeroFamily X)) :=
  exists_iso_sheafifiedCech_of_idealOfGlobalSections_eq X (oneZeroFamily X) (oneFamily X 2)
    (idealOfGlobalSections_oneZeroFamily X)

end Derived

end Obstruction

end AlgebraicGeometry.RingedSite

end
