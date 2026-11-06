module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentabilityFromSizeBound
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import StacksCore.Tactic.StacksAttribute

/-!
# Nonzero maps out of small subcomplexes

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf of
rings on `C`. Write `D(O)` for the derived category of `O`-modules and `|K|` for the size of an
object of `D(O)`, the least number of sections of a complex representing it
(`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedObjectSize`).

Conclusion (1) of Stacks 0GYZ asserts the existence of a cardinal `κ` such that every nonzero
object of the subcategory `QC(O)` of cartesian objects receives a nonzero morphism from a
*cartesian* object of size at most `κ`. The source obtains it from the following two independent
ingredients.

*The detection step.* If `K` is nonzero then some cohomology presheaf `H^i(F)` of a representing
complex `F` is nonzero, so it has a nonzero section over some object `U` of `C`. Lifting that
section to a cycle and presenting the cycle as a map out of the free `O`-module on the
representable at `U` exhibits a one-term subcomplex `S ⊆ F`, concentrated in degree `i` and no
larger than that free module, with the property that *every* subcomplex of `F` containing `S`
already has a nonzero cohomology class mapping to a nonzero class of `F`. In particular the
inclusion of such a subcomplex is nonzero in `D(O)`. This is bound (a) of the source, the one
measured by `|∐_V j_{U!} O_U(V)|`, and it is proved here outright as
`exists_small_subcomplex_detecting_nonzero`.

*The enlargement step.* The subcomplex produced by the detection step need not represent a
cartesian object, and the key claim of Stacks 0GYZ is that it can be enlarged to one that does
without exceeding `κ`. That claim is the content of bounds (b) and (c) of the source — the
cardinals of Stacks 0GYI and of Stacks 0GYY — and it is not proved in this file: it is isolated as
the hypothesis `HasCartesianEnlargement`, and conclusion (1) of Stacks 0GYZ is derived from it
here. It is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementExists`, as
`exists_hasCartesianEnlargement`, and that file combines the two into both conclusions of
Stacks 0GYZ at one cardinal and with no hypothesis beyond commutativity of the section rings of
`O`.

Conclusion (1) therefore appears here in two forms.
`exists_nonzero_map_of_derivedObjectSize_le` is the detection step packaged as a theorem about
`D(O)`: it holds outright, but places no cartesianness demand on the source object, and it carries
the `0GYZ` tag with a clause saying so.
`exists_nonzero_map_of_size_le_of_cartesianEnlargement` is conclusion (1) verbatim, with the
enlargement claim as a hypothesis; it carries no tag, the tag sitting instead on
the unconditional statement in `CartesianEnlargementExists`. Its shape is that of the hypothesis
`hnonzero` of `exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound`, so the two compose.
Conclusion (2) of Stacks 0GYZ is not treated here.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.singleGeneratorBound`: the number of sections
  of the one-term complexes on the free modules on the representables. This is bound (a) of
  Stacks 0GYZ.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.HasCartesianEnlargement`: the key claim of
  Stacks 0GYZ, that a small subcomplex of a complex representing a cartesian object is contained in
  a small subcomplex which again represents a cartesian object.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_small_subcomplex_detecting_nonzero`:
  a complex representing a nonzero object of `D(O)` has a subcomplex of size at most
  `singleGeneratorBound O` such that every subcomplex of the complex containing it has nonzero
  image in `D(O)`.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_nonzero_map_of_derivedObjectSize_le`:
  every nonzero object of `D(O)` receives a nonzero morphism from an object of size at most
  `singleGeneratorBound O`.
* `exists_nonzero_map_of_size_le_of_cartesianEnlargement`, in the same namespace: conclusion (1)
  of Stacks 0GYZ, granting `HasCartesianEnlargement`.

## Implementation notes

The detection step is run entirely through morphisms, never through elements of the homology
presheaf: the chosen cohomology class is carried by a map `b` out of the free module on a
representable, and the conclusion `DerivedCategory.Q.map h ≠ 0` is reached by exhibiting the
composite `b ≫ F.homologyπ i` as a factor of `HomologicalComplex.homologyMap h i`. Sections are
used only twice, to produce `b` — once to see that a nonzero presheaf of modules has a nonzero
section, and once to lift that section through the epimorphism `F.homologyπ i`. This avoids having
to identify the sections of `F.cycles i` with the cycles of the complex of sections.

The generated subcomplex is the one-term complex on the categorical image of the map presenting
the cycle, rather than the image of a map of complexes; that keeps the comparison of sizes
degreewise, where `PresheafOfModules.surjective_of_epi` applies.

`HasCartesianEnlargement` demands a monomorphism `H ⟶ F` together with a factorization of the
given inclusion through it, rather than an inclusion of subobjects of `F`; that is the form in
which the detection step consumes it, and it is what the construction of the source produces.

The proof of `HasCartesianEnlargement` turns on a single bridge. Its hypothesis and its conclusion
are stated through `IsQC`, i.e. through the invertibility of `comparison bc a`, which is by
definition an adjoint transpose under `bc.baseChangeAdj a`. The one-step enlargement the source
runs is Stacks 0GYI, whose hypothesis and conclusion are instead the invertibility of
`α.app (F^•(V)) ≫ Q.map b`, where `α` presents a *left derived* functor of termwise extension of
scalars and `b` is the degreewise base-change map of sections. The two are forms of one condition,
and that they agree is `CartesianObjects.isIso_comparison_Q_iff_isLeftDerived`, which assumes no
flatness and so applies here.

With that bridge the proof is an assembly, carried out in `CartesianEnlargementExists`.
`exists_iterated_enlargement_containing_sections` runs the iteration; the family of sections to be
added at a stage is the one Stacks 0GYI returns for each morphism of `C`, read through
`isIso_comparison_Q_iff_isLeftDerived`, and packaged per morphism as
`exists_sections_rule_isIso_comparison_at_union`;
`Stacks.SubcomplexEnlargement.familyIsColimit` presents the union as the filtered colimit of the
stages; `Stacks.SubcomplexEnlargement.derivedBaseChangeHomology_preservesFilteredColimits_ulift`
computes the cohomology of its derived base change as the colimit of theirs; and
`Stacks.SubcomplexEnlargement.isIso_colimMap_of_stagewise` turns the stagewise kernel and image
conditions into invertibility at the union. The cardinal `κ` is the supremum over the morphisms of
`C` of the cardinals those statements produce, which exists because the morphisms of `C` form a
type in the module universe — the same reason `singleGeneratorBound` exists, and proved the same
way, by `Cardinal.bddAbove_of_small`.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-! ### Counting sections -/

/-- A degreewise epimorphism of complexes does not increase the number of sections: the induced
map on the disjoint union of all section modules is surjective in each degree over each object. -/
lemma complexSectionSize_le_of_epi_f
    {F G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} (q : F ⟶ G)
    (hq : ∀ i : ℤ, Epi (q.f i)) :
    complexSectionSize.{w} O G ≤ complexSectionSize.{w} O F := by
  show Cardinal.mk (Σ i : ℤ, Σ V : C, (G.X i).obj (op V)) ≤
    Cardinal.mk (Σ i : ℤ, Σ V : C, (F.X i).obj (op V))
  refine Cardinal.mk_le_of_surjective
    (f := fun p : (Σ i : ℤ, Σ V : C, (F.X i).obj (op V)) =>
      (⟨p.1, p.2.1, (ConcreteCategory.hom ((q.f p.1).app (op p.2.1))) p.2.2⟩ :
        Σ i : ℤ, Σ V : C, (G.X i).obj (op V))) ?_
  rintro ⟨i, V, y⟩
  have := hq i
  obtain ⟨x, hx⟩ := PresheafOfModules.surjective_of_epi (f := q.f i) (op V) y
  exact ⟨⟨i, V, x⟩, by simp only [hx]⟩

/-- The size of an object of `D(O)` is at most the number of sections of any complex representing
it, the size being the infimum of those numbers. -/
lemma derivedObjectSize_le_complexSectionSize
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    derivedObjectSize.{w} O (DerivedCategory.Q.obj F) ≤ complexSectionSize.{w} O F :=
  csInf_le' ⟨F, ⟨Iso.refl _⟩, rfl⟩

/-- **Bound (a) of Stacks 0GYZ.** The number of sections of the one-term complexes on the free
`O`-modules on the representables, taken over all degrees and all objects of `C`. The supremum
exists because the index type lies in the module universe. -/
def singleGeneratorBound : Cardinal.{max u v r w} :=
  ⨆ p : ULift.{max u v r w, 0} ℤ × C,
    complexSectionSize.{w} O
      ((HomologicalComplex.single (PresheafOfModules.{max u v r w} O)
        (ComplexShape.up ℤ) p.1.down).obj (freeRepresentableModule.{w} O p.2))

/-- Each of the one-term complexes on the free modules on the representables is bounded by
`singleGeneratorBound O`, that cardinal being their supremum. -/
lemma complexSectionSize_single_le_singleGeneratorBound (i : ℤ) (U : C) :
    complexSectionSize.{w} O
        ((HomologicalComplex.single (PresheafOfModules.{max u v r w} O)
          (ComplexShape.up ℤ) i).obj (freeRepresentableModule.{w} O U)) ≤
      singleGeneratorBound.{w} O :=
  le_ciSup (f := fun p : ULift.{max u v r w, 0} ℤ × C =>
    complexSectionSize.{w} O
      ((HomologicalComplex.single (PresheafOfModules.{max u v r w} O)
        (ComplexShape.up ℤ) p.1.down).obj (freeRepresentableModule.{w} O p.2)))
    Cardinal.bddAbove_of_small (⟨ULift.up i, U⟩)

/-! ### Sections and the free modules on the representables -/

/-- A presheaf of modules which is not a zero object has a nonzero section over some object:
otherwise its identity morphism, being zero on every section, is the zero morphism. -/
lemma exists_nonzero_section_of_not_isZero {M : PresheafOfModules.{max u v r w} O}
    (hM : ¬ IsZero M) : ∃ (U : C) (m : M.obj (op U)), m ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hM ((IsZero.iff_id_eq_zero M).2 ?_)
  ext X m
  simpa using hcon X.unop m

/-- **Every section is hit by a map from the free module on a representable**, the canonical
generator going to the given section. -/
lemma exists_freeRepresentableModule_lift (U : C) (M : PresheafOfModules.{max u v r w} O)
    (m : M.obj (op U)) :
    ∃ a : freeRepresentableModule.{w} O U ⟶ M,
      (ConcreteCategory.hom (a.app (op U))) (freeRepresentableModuleGen.{w} O U) = m :=
  Stacks.SheafOfModules.exists_tensorPresheafLift_eval.{u, v, r, w} O U M m

/-- A map out of the free module on a representable whose value at the canonical generator is
nonzero is itself nonzero. -/
lemma ne_zero_of_gen_ne_zero {M : PresheafOfModules.{max u v r w} O} {U : C}
    (a : freeRepresentableModule.{w} O U ⟶ M)
    (ha : (ConcreteCategory.hom (a.app (op U))) (freeRepresentableModuleGen.{w} O U) ≠ 0) :
    a ≠ 0 := fun h => ha (by rw [h]; simp)

/-! ### The subcomplex generated by a cycle -/

/-- **The one-term subcomplex generated by a cycle.** A map `c` out of the free `O`-module on a
representable which is annihilated by the differential of `F` in degree `i` factors through a
subcomplex of `F` concentrated in degree `i`, namely the one-term complex on the image of `c`,
whose number of sections is at most `singleGeneratorBound O`. -/
theorem exists_single_subcomplex_of_cycle
    {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} (i : ℤ) {U : C}
    (c : freeRepresentableModule.{w} O U ⟶ F.X i) (hc : c ≫ F.d i (i + 1) = 0) :
    ∃ (S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : S ⟶ F)
      (t : freeRepresentableModule.{w} O U ⟶ S.X i),
      Mono g ∧ complexSectionSize.{w} O S ≤ singleGeneratorBound.{w} O ∧ t ≫ g.f i = c := by
  have hic : ∀ k : ℤ, (ComplexShape.up ℤ).Rel i k → Limits.image.ι c ≫ F.d i k = 0 := by
    intro k hk
    obtain rfl : k = i + 1 := hk.symm
    rw [← cancel_epi (Limits.factorThruImage c), comp_zero, ← Category.assoc,
      Limits.image.fac, hc]
  refine ⟨(HomologicalComplex.single (PresheafOfModules.{max u v r w} O)
      (ComplexShape.up ℤ) i).obj (Limits.image c),
    HomologicalComplex.mkHomFromSingle (Limits.image.ι c) hic,
    Limits.factorThruImage c ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (Limits.image c)).inv,
    ?_, ?_, ?_⟩
  · refine HomologicalComplex.mono_of_mono_f _ (fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i
        (Limits.image c) j hj).mono _
  · refine le_trans (complexSectionSize_le_of_epi_f.{w} O
      ((HomologicalComplex.single (PresheafOfModules.{max u v r w} O)
        (ComplexShape.up ℤ) i).map (Limits.factorThruImage c)) (fun j => ?_))
      (complexSectionSize_single_le_singleGeneratorBound.{w} O i U)
    by_cases hj : j = i
    · subst hj
      rw [HomologicalComplex.single_map_f_self]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i
        (Limits.image c) j hj).epi _
  · rw [Category.assoc, HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc,
      Limits.image.fac]

/-! ### Detecting nonvanishing in the derived category -/

/-- **A small subcomplex detecting nonvanishing.** A complex `F` whose image in `D(O)` is nonzero
contains a subcomplex `S` with at most `singleGeneratorBound O` sections such that every
subcomplex of `F` through which the inclusion of `S` factors has nonzero image in `D(O)`.

The subcomplex is the one generated by a cycle carrying a nonzero cohomology class. Any subcomplex
`H` containing it carries a cohomology class in the same degree mapping to that nonzero class, so
`HomologicalComplex.homologyMap h i`, and hence `DerivedCategory.Q.map h`, is nonzero. -/
theorem exists_small_subcomplex_detecting_nonzero
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
    (hF : ¬ IsZero (DerivedCategory.Q.obj F)) :
    ∃ (S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : S ⟶ F),
      Mono g ∧ complexSectionSize.{w} O S ≤ singleGeneratorBound.{w} O ∧
        ∀ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F), Mono h →
          ∀ k : S ⟶ H, k ≫ h = g → DerivedCategory.Q.map h ≠ 0 := by
  classical
  have hacy : ¬ ∀ j : ℤ, F.ExactAt j := by
    intro hex
    refine hF ?_
    have hq : QuasiIso (0 : F ⟶ F) := by
      rw [quasiIso_iff]
      intro j
      exact (quasiIsoAt_iff_exactAt (0 : F ⟶ F) j (hex j)).mpr (hex j)
    have hiso : IsIso (0 : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj F) := by
      rw [← Functor.map_zero DerivedCategory.Q F F]
      exact inferInstance
    exact (IsZero.iff_id_eq_zero _).mpr (isIsoZeroSelfEquiv _ hiso)
  obtain ⟨i, hi⟩ := not_forall.1 hacy
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hi
  obtain ⟨U, m, hm⟩ := exists_nonzero_section_of_not_isZero.{w} O hi
  obtain ⟨z, hz⟩ := PresheafOfModules.surjective_of_epi (f := F.homologyπ i) (op U) m
  obtain ⟨b, hb⟩ := exists_freeRepresentableModule_lift.{w} O U (F.cycles i) z
  have hcls : b ≫ F.homologyπ i ≠ 0 := by
    refine ne_zero_of_gen_ne_zero.{w} O _ ?_
    rw [PresheafOfModules.comp_app, ConcreteCategory.comp_apply, hb, hz]
    exact hm
  have hc : (b ≫ F.iCycles i) ≫ F.d i (i + 1) = 0 := by
    rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  obtain ⟨S, g, t, hgmono, hgsize, hgfac⟩ :=
    exists_single_subcomplex_of_cycle.{w} O i (b ≫ F.iCycles i) hc
  refine ⟨S, g, hgmono, hgsize, ?_⟩
  intro H h hh k hk
  -- the cycle, transported into `H`
  have hcH : (t ≫ k.f i) ≫ h.f i = b ≫ F.iCycles i := by
    rw [Category.assoc, ← HomologicalComplex.comp_f, hk, hgfac]
  have hdH : (t ≫ k.f i) ≫ H.d i (i + 1) = 0 := by
    have := hh
    rw [← cancel_mono (h.f (i + 1)), Category.assoc, ← h.comm i (i + 1), ← Category.assoc,
      hcH, Category.assoc, HomologicalComplex.iCycles_d, comp_zero, zero_comp]
  -- the corresponding cohomology class of `H` maps to the chosen class of `F`
  have hcyc : H.liftCycles (t ≫ k.f i) (i + 1) (by simp) hdH ≫
      HomologicalComplex.cyclesMap h i = b := by
    rw [← cancel_mono (F.iCycles i), Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, HomologicalComplex.liftCycles_i, hcH]
  have hfactor : H.liftCycles (t ≫ k.f i) (i + 1) (by simp) hdH ≫
      H.homologyπ i ≫ HomologicalComplex.homologyMap h i = b ≫ F.homologyπ i := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcyc]
  have hhom : HomologicalComplex.homologyMap h i ≠ 0 := by
    intro hzero
    refine hcls ?_
    rw [← hfactor, hzero, comp_zero, comp_zero]
  -- a zero morphism of `D(O)` would have zero homology
  intro hQ
  refine hhom ?_
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality
    (C := PresheafOfModules.{max u v r w} O) h i
  rw [hQ, Functor.map_zero, zero_comp] at hnat
  have : IsIso ((DerivedCategory.homologyFunctorFactors
    (PresheafOfModules.{max u v r w} O) i).hom.app H) := inferInstance
  exact (cancel_epi ((DerivedCategory.homologyFunctorFactors
    (PresheafOfModules.{max u v r w} O) i).hom.app H)).1 (hnat.symm.trans comp_zero.symm)

/-! ### Nonzero maps from objects of bounded size -/

/-- **Every nonzero object of `D(O)` receives a nonzero morphism from an object of size at most
`singleGeneratorBound O`.** This is the detection step of conclusion (1) of Stacks 0GYZ with the
cartesianness demand dropped from both objects: the subcomplex produced by
`exists_small_subcomplex_detecting_nonzero` is used as the source as it stands, with no
enlargement. -/
@[stacks 0GYZ "part (1) for D(O) in place of QC(O): cartesianness dropped from both objects"]
theorem exists_nonzero_map_of_derivedObjectSize_le (K : DMod.{w} O) (hK : ¬ IsZero K) :
    ∃ (E : DMod.{w} O) (f : E ⟶ K),
      f ≠ 0 ∧ derivedObjectSize.{w} O E ≤ singleGeneratorBound.{w} O := by
  obtain ⟨F, hFK, -⟩ := exists_representative_of_derivedObjectSize.{w} O K
  have e : DerivedCategory.Q.obj F ≅ K := hFK.some
  obtain ⟨S, g, hgmono, hgsize, hdet⟩ :=
    exists_small_subcomplex_detecting_nonzero.{w} O F (fun hz => hK (hz.of_iso e.symm))
  refine ⟨DerivedCategory.Q.obj S, DerivedCategory.Q.map g ≫ e.hom, ?_, ?_⟩
  · intro hzero
    refine hdet S g hgmono (𝟙 S) (Category.id_comp g) ?_
    simpa using (cancel_mono e.hom).1 (hzero.trans (zero_comp).symm)
  · exact le_trans (derivedObjectSize_le_complexSectionSize.{w} O S) hgsize

/-! ### Conclusion (1) of Stacks 0GYZ from the key claim -/

/-- **The key claim of Stacks 0GYZ.** For the cardinal `κ`, every subcomplex with at most `κ`
sections of a complex representing a cartesian object is contained in a subcomplex which again
represents a cartesian object and still has at most `κ` sections.

This is what the source obtains from the cardinals of Stacks 0GYI and Stacks 0GYY. It is the one
ingredient of conclusion (1) of Stacks 0GYZ that is not proved in this file; it is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementExists`, as
`exists_hasCartesianEnlargement`, for every sufficiently large cardinal and under commutativity of
the section rings of `O`.

That commutativity is a hypothesis of the source and should not be read as an added one:
Stacks 0GYI is a lemma of More on Algebra, where every ring is commutative. It is also already
present wherever base change along a restriction map of `O` exists at all — extension of scalars
`M ↦ M ⊗_{O(V)} O(U)` needs a commutative `O(V)` — and both of this repository's terms of
`BaseChangeData` carry it. -/
def HasCartesianEnlargement (bc : BaseChangeData.{w} O) (κ : Cardinal.{max u v r w}) : Prop :=
  ∀ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
    IsQC.{w} bc (DerivedCategory.Q.obj F) →
      ∀ (S : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g : S ⟶ F), Mono g →
        complexSectionSize.{w} O S ≤ κ →
          ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F) (k : S ⟶ H),
            Mono h ∧ k ≫ h = g ∧ IsQC.{w} bc (DerivedCategory.Q.obj H) ∧
              complexSectionSize.{w} O H ≤ κ

/-- **Conclusion (1) of Stacks 0GYZ, granting the key claim.** If `κ` bounds the number of sections
of the one-term complexes on the free modules on the representables and has the enlargement
property, then every nonzero cartesian object receives a nonzero morphism from a cartesian object
of size at most `κ`.

The detection step `exists_small_subcomplex_detecting_nonzero` supplies a small subcomplex of a
representative whose every enlargement maps nonzero into the representative; the enlargement
property turns one such enlargement into a cartesian object, and smallness is preserved.

This is the shape of the hypothesis `hnonzero` of
`exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound`, so the two compose.

It carries no `0GYZ` tag: the enlargement claim is an assertion of the source's proof, not a
hypothesis of its statement, so a declaration assuming it does not state the lemma. The tag sits
instead on `exists_cardinal_small_nonzero_map_and_factorization`, which discharges the claim by
`exists_hasCartesianEnlargement` and uses this theorem to conclude. -/
theorem exists_nonzero_map_of_size_le_of_cartesianEnlargement (bc : BaseChangeData.{w} O)
    {κ : Cardinal.{max u v r w}} (hκ : singleGeneratorBound.{w} O ≤ κ)
    (henl : HasCartesianEnlargement.{w} O bc κ) (K : QC.{w} bc) (hK : ¬ IsZero K.obj) :
    ∃ (E : QC.{w} bc) (f : E ⟶ K), f ≠ 0 ∧ derivedObjectSize.{w} O E.obj ≤ κ := by
  obtain ⟨F, hFK, -⟩ := exists_representative_of_derivedObjectSize.{w} O K.obj
  have e : DerivedCategory.Q.obj F ≅ K.obj := hFK.some
  have hFQC : IsQC.{w} bc (DerivedCategory.Q.obj F) :=
    ObjectProperty.prop_of_iso (fun L => IsQC.{w} bc L) e.symm K.property
  obtain ⟨S, g, hgmono, hgsize, hdet⟩ :=
    exists_small_subcomplex_detecting_nonzero.{w} O F (fun hz => hK (hz.of_iso e.symm))
  obtain ⟨H, h, k, hhmono, hk, hHQC, hHsize⟩ :=
    henl F hFQC S g hgmono (hgsize.trans hκ)
  refine ⟨⟨DerivedCategory.Q.obj H, hHQC⟩,
    ObjectProperty.homMk (DerivedCategory.Q.map h ≫ e.hom), ?_, ?_⟩
  · intro hzero
    have hunder : DerivedCategory.Q.map h ≫ e.hom = 0 := by
      simpa using congrArg (ObjectProperty.ι (fun L => IsQC.{w} bc L)).map hzero
    refine hdet H h hhmono k hk ?_
    simpa using (cancel_mono e.hom).1 (hunder.trans (zero_comp).symm)
  · exact le_trans (derivedObjectSize_le_complexSectionSize.{w} O H) hHsize

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
