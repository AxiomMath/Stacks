module

public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded objects of the derived category of modules on a category are essentially small

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf
of rings on `C`. Write `D(O)` for the derived category of `O`-modules in the small-Hom model of
Tag 079Q, as in `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`. The *size* of an
object of `D(O)` is the least size of a complex representing it, as in Stacks 0GYZ. This file
shows that the objects of `D(O)` of size at most a cardinal `κ` are, up to isomorphism, the
members of a family `E : ι → D(O)` indexed by a type `ι` in the module universe, which is the
form of the bound used by weak Brown representability (Stacks 0GYG).

A presheaf of modules `M` all of whose section modules have
cardinality at most `κ` is a quotient of one fixed object, namely the direct sum of `#C · κ`
copies of the free modules on the representables: by
`Stacks.SheafOfModules.exists_tensorPresheafLift_eval` every section of `M` over `U` is the
image of the tautological generator under some map out of the free module on the representable
at `U`, and there are at most `κ` sections over each `U`. Quotients of a fixed object are
classified by its subobjects, and the category of presheaves of modules is Grothendieck abelian
with the site, ring and module universes independent
(`Stacks.SheafOfModules.presheafModulesGrothendieck`), hence well powered, so there are only
module-universe-many of them. A *complex* of such modules is then determined by a family of
subobjects indexed by `ℤ` together with its differentials, and the differentials range over
hom-sets, which are again module-universe-small. Passing to the derived category and discarding
the indices whose size exceeds `κ` gives the family.

## Main definitions

* `complexSectionSize`: the number of sections of a complex of `O`-modules, counted over all
  objects of `C` and in all degrees.
* `derivedObjectSize`: the size of an object of `D(O)`, the least size of a complex representing
  it. This is the `|K|` of Stacks 0GYZ.
* `sectionBoundObject`: the fixed presheaf of modules of which every module with at most `#T`
  sections over each object is a quotient.
* `BoundedComplexIndex`: the index type classifying complexes whose terms are quotients of a fixed
  object.

## Main results

* `exists_epi_sectionBoundObject`: a module with at most `#T` sections over each object is a
  quotient of `sectionBoundObject O T`.
* `exists_boundedComplexIndex_iso`: a complex with at most `#T` sections in each degree over each
  object is isomorphic to one coming from `BoundedComplexIndex`.
* `exists_small_family_of_derivedObjectSize_le`: **essential smallness.** For every cardinal `κ`
  there is a family `E : ι → D(O)`, indexed by a type in the module universe and consisting of
  objects of size at most `κ`, which contains every object of `D(O)` of size at most `κ` up to
  isomorphism.

## Implementation notes

The bound is taken as a *type* `T` rather than a cardinal wherever the construction uses it, so
that no step has to unfold `Cardinal` to its underlying quotient; the translation between the
two happens once, in `exists_small_family_of_derivedObjectSize_le`, through `Cardinal.mk_out`.

`BoundedComplexIndex` is an `abbrev`, not a `def`: its projections are used to build the terms
and differentials of a complex, and that reduction has to happen at instance transparency.

The infimum defining `derivedObjectSize` is attained, because a nonempty set of cardinals has a
least element; that is what turns a bound on the infimum into an actual small representative.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- Presheaves of `O`-modules form a Grothendieck abelian category at the module universe of the
small-Hom model of Tag 079Q used for `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod`,
with the site, ring and module universes independent. -/
@[sga "3 I 3.1.1" "more general"]
instance isGrothendieckAbelian_presheafOfModules :
    IsGrothendieckAbelian.{max u v r w} (PresheafOfModules.{max u v r w} O) :=
  Stacks.SheafOfModules.presheafModulesGrothendieck.{u, v, r, w} O

/-! ### Every module with few sections is a quotient of one fixed module -/

/-- The free `O`-module on the representable presheaf at `U`, with the representable lifted into
the module universe. Sections of a module over `U` are the maps out of it
(`Stacks.SheafOfModules.exists_tensorPresheafLift_eval`). -/
noncomputable def freeRepresentableModule (U : C) : PresheafOfModules.{max u v r w} O :=
  Stacks.SheafOfModules.tensorPresheaf.{u, v, max u v w, r} O
    (Stacks.SheafOfModules.freeRepresentable.{u, v, max r w} U)

/-- The tautological generating section of `freeRepresentableModule O U` over `U`: the unit of
`O(U)` tensored with the basis vector of the identity of `U`. -/
noncomputable def freeRepresentableModuleGen (U : C) :
    (freeRepresentableModule.{w} O U).obj (op U) :=
  (1 : O.obj (op U)) ⊗ₜ[ℤ]
    (FreeAbelianGroup.of (ULift.up (𝟙 U)) :
      (Stacks.SheafOfModules.freeRepresentable.{u, v, max r w} U).obj (op U))

/-- The direct sum of copies of the free modules on the representables, one copy for each pair
of an object of `C` and an element of `T`. Every `O`-module admitting an injection of each of
its section modules into `T` is a quotient of this one. -/
noncomputable def sectionBoundObject (T : Type (max u v r w)) :
    PresheafOfModules.{max u v r w} O :=
  ∐ (fun p : C × T => freeRepresentableModule.{w} O p.1)

/-- **A module with few sections is a quotient of `sectionBoundObject O T`**: if each section
module of `M` injects into `T`, there is an epimorphism `sectionBoundObject O T ⟶ M`. -/
theorem exists_epi_sectionBoundObject (T : Type (max u v r w))
    (M : PresheafOfModules.{max u v r w} O)
    (hM : ∀ U : C, Nonempty ((M.obj (op U)) ↪ T)) :
    ∃ a : sectionBoundObject.{w} O T ⟶ M, Epi a := by
  classical
  have e : ∀ U : C, (M.obj (op U)) ↪ T := fun U => (hM U).some
  have hne : ∀ U : C, Nonempty (M.obj (op U)) := fun U => ⟨0⟩
  let sec : ∀ U : C, T → (M.obj (op U)) := fun U => @Function.invFun _ _ (hne U) (e U)
  have hsec : ∀ (U : C) (y : M.obj (op U)), sec U (e U y) = y := fun U y =>
    @Function.leftInverse_invFun _ _ (hne U) _ (e U).injective y
  have hlift : ∀ (U : C) (m : M.obj (op U)), ∃ a : freeRepresentableModule.{w} O U ⟶ M,
      (ConcreteCategory.hom (a.app (op U))) (freeRepresentableModuleGen.{w} O U) = m :=
    fun U m => Stacks.SheafOfModules.exists_tensorPresheafLift_eval.{u, v, r, w} O U M m
  choose pick hpick using hlift
  refine ⟨Sigma.desc (fun p : C × T => pick p.1 (sec p.1 p.2)), ?_⟩
  apply PresheafOfModules.epi_of_surjective
  intro X y
  refine ⟨(ConcreteCategory.hom
    ((Sigma.ι (fun p : C × T => freeRepresentableModule.{w} O p.1)
      (X.unop, e X.unop y)).app X)) (freeRepresentableModuleGen.{w} O X.unop), ?_⟩
  have hval : (ConcreteCategory.hom ((pick X.unop (sec X.unop (e X.unop y))).app X))
      (freeRepresentableModuleGen.{w} O X.unop) = y := by
    rw [hsec]; exact hpick X.unop y
  refine (ConcreteCategory.comp_apply
    ((Sigma.ι (fun p : C × T => freeRepresentableModule.{w} O p.1)
      (X.unop, e X.unop y)).app X)
    ((Sigma.desc (fun p : C × T => pick p.1 (sec p.1 p.2))).app X)
    (freeRepresentableModuleGen.{w} O X.unop)).symm.trans ?_
  refine (congrArg (fun t => (ConcreteCategory.hom t) (freeRepresentableModuleGen.{w} O X.unop))
    (PresheafOfModules.comp_app
      (Sigma.ι (fun p : C × T => freeRepresentableModule.{w} O p.1) (X.unop, e X.unop y))
      (Sigma.desc (fun p : C × T => pick p.1 (sec p.1 p.2))) X)).symm.trans ?_
  exact congrArg (fun (t : freeRepresentableModule.{w} O X.unop ⟶ M) =>
    (ConcreteCategory.hom (t.app X)) (freeRepresentableModuleGen.{w} O X.unop))
    (Sigma.ι_desc (fun p : C × T => pick p.1 (sec p.1 p.2)) (X.unop, e X.unop y)) |>.trans hval

/-! ### Quotients of a fixed module are classified by its subobjects -/

variable {O}

/-- The quotient of `P` by a subobject of it. -/
noncomputable def subobjectQuotient {P : PresheafOfModules.{max u v r w} O} (s : Subobject P) :
    PresheafOfModules.{max u v r w} O :=
  cokernel s.arrow

/-- **A quotient of `P` is the quotient by a subobject of `P`.** -/
theorem exists_subobject_iso_of_epi {P M : PresheafOfModules.{max u v r w} O} (a : P ⟶ M)
    [Epi a] : ∃ s : Subobject P, Nonempty (subobjectQuotient.{w} s ≅ M) := by
  refine ⟨Subobject.mk (kernel.ι a), ⟨?_⟩⟩
  refine (cokernel.mapIso (Subobject.mk (kernel.ι a)).arrow (kernel.ι a)
    (Subobject.underlyingIso (kernel.ι a)) (Iso.refl P) ?_).trans
      (asIso (Abelian.factorThruCoimage a))
  simp [Subobject.underlyingIso_hom_comp_eq_mk]

/-! ### Complexes whose terms are quotients of a fixed module -/

/-- Presentation data for a cochain complex whose terms are quotients of `P`: a family of
subobjects of `P` indexed by the degrees, together with differentials between the quotients
composing to zero. -/
abbrev BoundedComplexIndex (P : PresheafOfModules.{max u v r w} O) : Type _ :=
  Σ o : ℤ → Subobject P,
    {d : ∀ i : ℤ, subobjectQuotient.{w} (o i) ⟶ subobjectQuotient.{w} (o (i + 1)) //
      ∀ i : ℤ, d i ≫ d (i + 1) = 0}

/-- The cochain complex presented by `BoundedComplexIndex` data. -/
noncomputable def boundedComplexOfIndex {P : PresheafOfModules.{max u v r w} O}
    (D : BoundedComplexIndex.{w} P) : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ where
  X i := subobjectQuotient.{w} (D.1 i)
  d i j := if h : i + 1 = j then D.2.1 i ≫ eqToHom (by rw [h]) else 0
  shape i j h := dite_eq_right h
  d_comp_d' i j k hij hjk := by
    subst hij hjk
    simp [D.2.2 i]

/-- **There are only module-universe-many presentation data.** -/
lemma small_boundedComplexIndex (P : PresheafOfModules.{max u v r w} O) :
    Small.{max u v r w} (BoundedComplexIndex.{w} P) := by
  have : Small.{max u v r w} (ℤ → Subobject P) := inferInstance
  exact small_sigma _

/-- **A complex with few sections is presented by `BoundedComplexIndex` data**: if each section
module of each term of `F` injects into `T`, then `F` is isomorphic to the complex presented by
some `BoundedComplexIndex` data on `sectionBoundObject O T`. -/
theorem exists_boundedComplexIndex_iso (T : Type (max u v r w))
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
    (hF : ∀ (i : ℤ) (U : C), Nonempty ((F.X i).obj (op U) ↪ T)) :
    ∃ D : BoundedComplexIndex.{w} (sectionBoundObject.{w} O T),
      Nonempty (boundedComplexOfIndex.{w} D ≅ F) := by
  classical
  have hstep : ∀ i : ℤ, ∃ s : Subobject (sectionBoundObject.{w} O T),
      Nonempty (subobjectQuotient.{w} s ≅ F.X i) := by
    intro i
    obtain ⟨a, ha⟩ := exists_epi_sectionBoundObject.{w} O T (F.X i) (hF i)
    have := ha
    exact exists_subobject_iso_of_epi.{w} a
  choose s hs using hstep
  have e : ∀ i : ℤ, subobjectQuotient.{w} (s i) ≅ F.X i := fun i => (hs i).some
  refine ⟨⟨s, fun i => (e i).hom ≫ F.d i (i + 1) ≫ (e (i + 1)).inv, ?_⟩, ⟨?_⟩⟩
  · exact fun i => by simp
  · refine HomologicalComplex.Hom.isoOfComponents e ?_
    rintro i _ rfl
    simp [boundedComplexOfIndex]

/-! ### The size of an object of the derived category -/

variable (O)

/-- The number of sections of a complex of `O`-modules, counted over all objects of `C` and in
all degrees. This is the `|F^•|` of Stacks 0GYZ. -/
noncomputable def complexSectionSize
    (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) : Cardinal.{max u v r w} :=
  Cardinal.mk (Σ i : ℤ, Σ U : C, (F.X i).obj (op U))

/-- The size of an object of `D(O)`: the least size of a complex of `O`-modules representing it.
This is the `|K|` of Stacks 0GYZ. -/
noncomputable def derivedObjectSize (K : DMod.{w} O) : Cardinal.{max u v r w} :=
  sInf {c | ∃ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
    Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ c = complexSectionSize.{w} O F}

/-- The size of an object of `D(O)` only depends on its isomorphism class. -/
lemma derivedObjectSize_of_iso {K K' : DMod.{w} O} (e : K ≅ K') :
    derivedObjectSize.{w} O K = derivedObjectSize.{w} O K' := by
  have hset :
      {c : Cardinal.{max u v r w} | ∃ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
        Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ c = complexSectionSize.{w} O F} =
      {c : Cardinal.{max u v r w} | ∃ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
        Nonempty (DerivedCategory.Q.obj F ≅ K') ∧ c = complexSectionSize.{w} O F} := by
    ext c
    exact ⟨fun ⟨F, hF, hc⟩ => ⟨F, ⟨hF.some.trans e⟩, hc⟩,
      fun ⟨F, hF, hc⟩ => ⟨F, ⟨hF.some.trans e.symm⟩, hc⟩⟩
  exact congrArg sInf hset

/-- The infimum defining `derivedObjectSize` is attained: every object of `D(O)` is represented
by a complex whose size is exactly the size of the object. -/
theorem exists_representative_of_derivedObjectSize (K : DMod.{w} O) :
    ∃ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K) ∧
        complexSectionSize.{w} O F = derivedObjectSize.{w} O K := by
  classical
  obtain ⟨F, hF, hc⟩ := csInf_mem (show
    {c : Cardinal.{max u v r w} | ∃ F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ c = complexSectionSize.{w} O F}.Nonempty from
    ⟨_, (DerivedCategory.Q (C := PresheafOfModules.{max u v r w} O)).objPreimage K,
      ⟨(DerivedCategory.Q (C := PresheafOfModules.{max u v r w} O)).objObjPreimageIso K⟩, rfl⟩)
  exact ⟨F, hF, hc.symm⟩

/-- A complex of size at most `κ` has at most `κ` sections in each degree over each object. -/
lemma mk_sections_le_of_complexSectionSize_le
    {F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} {κ : Cardinal.{max u v r w}}
    (hF : complexSectionSize.{w} O F ≤ κ) (i : ℤ) (U : C) :
    Cardinal.mk ((F.X i).obj (op U)) ≤ κ :=
  le_trans (Cardinal.mk_le_of_injective
    (f := fun x : (F.X i).obj (op U) => (⟨i, U, x⟩ :
      Σ i : ℤ, Σ U : C, (F.X i).obj (op U)))
    (by intro x y h; simpa using h)) hF

/-- **Essential smallness of the objects of bounded size.** For every cardinal `κ` there is a
family of objects of `D(O)`, indexed by a type in the module universe and each of size at most
`κ`, which contains every object of `D(O)` of size at most `κ` up to isomorphism. -/
theorem exists_small_family_of_derivedObjectSize_le (κ : Cardinal.{max u v r w}) :
    ∃ (ι : Type (max u v r w)) (E : ι → DMod.{w} O),
      (∀ i, derivedObjectSize.{w} O (E i) ≤ κ) ∧
        ∀ K : DMod.{w} O, derivedObjectSize.{w} O K ≤ κ → ∃ i, Nonempty (E i ≅ K) := by
  classical
  have hsmall := small_boundedComplexIndex.{w} (sectionBoundObject.{w} O κ.out)
  let Fam : Shrink.{max u v r w} (BoundedComplexIndex.{w} (sectionBoundObject.{w} O κ.out)) →
      DMod.{w} O := fun t =>
    DerivedCategory.Q.obj (boundedComplexOfIndex.{w} ((equivShrink _).symm t))
  refine ⟨{t // derivedObjectSize.{w} O (Fam t) ≤ κ}, fun t => Fam t.1,
    fun t => t.2, ?_⟩
  intro K hK
  obtain ⟨F, hFK, hFsize⟩ := exists_representative_of_derivedObjectSize.{w} O K
  have hbound : ∀ (i : ℤ) (U : C), Nonempty ((F.X i).obj (op U) ↪ κ.out) := by
    intro i U
    refine (Cardinal.le_def _ _).1 ?_
    rw [Cardinal.mk_out]
    exact mk_sections_le_of_complexSectionSize_le.{w} O (hFsize.trans_le hK) i U
  obtain ⟨D, hD⟩ := exists_boundedComplexIndex_iso.{w} κ.out F hbound
  have hFamD : Fam (equivShrink _ D) = DerivedCategory.Q.obj (boundedComplexOfIndex.{w} D) := by
    simp only [Fam, Equiv.symm_apply_apply]
  have hiso : Fam (equivShrink _ D) ≅ K :=
    (eqToIso hFamD).trans ((DerivedCategory.Q.mapIso hD.some).trans hFK.some)
  exact ⟨⟨equivShrink _ D, by rw [derivedObjectSize_of_iso.{w} O hiso]; exact hK⟩, ⟨hiso⟩⟩

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
