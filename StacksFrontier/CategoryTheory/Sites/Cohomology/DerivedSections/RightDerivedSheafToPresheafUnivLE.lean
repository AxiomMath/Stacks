module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheafNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived functors of the sheaf-to-presheaf inclusion, in a coefficient universe of its own

For a small site `C` with `C : Type u`, the second half of [Stacks, Tag 03AY] — the natural
identification `Rᵖ i ≅ H̲ᵖ` of the right derived functors of the inclusion
`i = sheafToPresheaf J AddCommGrpCat` with the cohomology presheaves — is available in
`Cech/RightDerivedSheafToPresheafNaturality.lean` only with the **coefficient universe pinned to
the homs of the site**: `Stacks.Cohomology.rightDerivedSheafToPresheafIso` has a single universe
parameter and its coefficients are `AddCommGrpCat.{u}`.

That pinning is the one step between `Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber`, whose
coefficient universe is already free of the space, and the vanishing of a higher direct image at
the universes of the derived clause of [Stacks, Tag 0DCU]; it is the obstruction recorded in the
implementation notes of `LocallyQuasiCompact/ProperHigherDirectImageVanishing.lean`. This file
removes it: `rightDerivedSheafToPresheafIso` below is stated for `AddCommGrpCat.{max u t}` with
`t` free, valued in the cohomology presheaf of `DerivedSections/FreeYonedaSectionsUnivLE.lean`.

The pinning was *incidental*, not essential. The implementation notes of
`Cech/RightDerivedSheafToPresheafNaturality.lean` locate it in
`Stacks.Cohomology.Locality.mapExtendHomologyIso`, which needs its source and target categories
in one `Type` universe; but that condition is satisfied at any coefficient universe dominating
the site, since `Sheaf J AddCommGrpCat.{max u t} : Type (max u t + 1)` has its homs in
`max u t`. What actually pins the chain of Section 21.7 is only that
`Stacks.Cohomology.Locality.freeYonedaSheaf` is built on `yoneda`, hence on
`AddCommGrpCat.free : Type u ⥤ AddCommGrpCat.{u}`. Replacing it by
`Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda`, which is built on `uliftYoneda.{t}`, frees the
coefficients, and the rest of the argument is re-derived here from universe-general inputs.

## Main definitions

In the root namespace `Stacks.Cohomology`:

* `factorBCDEquiv`: the last three comparison isomorphisms of Section 21.7 in an arbitrary
  abelian category, as an isomorphism of abelian groups; `Stacks.Cohomology.factorBCDApply` is
  its underlying function.

In the namespace `Stacks.Cohomology.FreeYonedaUnivLE`:

* `coyonedaIsoSections`: free-Yoneda corepresentability with the coefficient universe freed.
* `extEquivSections`: the bridge `Extᵖ(L V, G) ≃+ Hᵖ(I^•(V))` of Section 21.7, freed.
* `cohomologyPresheafIsoResolution`, `rightDerivedObjIsoCohomologyPresheaf`,
  `rightDerivedSheafToPresheafIso`: **Stacks 03AY**, second half, with the coefficient universe
  independent of the site.

## Main results

* `Stacks.Cohomology.factorBCDApply_extAddEquiv_naturality_obj`: `factorBCDApply` composed with
  Mathlib's `InjectiveResolution.extAddEquivCohomologyClass` is natural in the **first** `Ext`
  variable. This is the object-variable companion of
  `Stacks.Cohomology.factorBCDApply_naturality`, and it is what replaces the ~550 lines of
  `Locality.extEquivHomComplexHomology_naturality`: Mathlib's
  `InjectiveResolution.mk₀_comp_extMk` does at the `extMk` level what that argument does at the
  `SmallShiftedHom` level.
* `extEquivSections_naturality`, `extEquivSections_naturality_coeff`: the bridge is natural in
  the object of the site and in the sheaf.

## Implementation notes

The generic section is stated for `A : Type (v + 1)` with `[Category.{v} A]`, the same convention
as the generic section of `Cech/RightDerivedSheafToPresheafNaturality.lean`, and for the same
reason: `Stacks.Cohomology.Locality.mapExtendHomologyIso` needs the target `AddCommGrpCat.{v}` of
`preadditiveCoyoneda.obj (op X)` to live in the same `Type` universe as `A`. The instance used
below is `A = Sheaf J AddCommGrpCat.{max u t}`, which satisfies it.

Several steps are written in term mode (`Eq.trans`, `congrArg`) rather than with `rw`, because
the two sides of the associativity rearrangements are typed at two spellings of one object
(`I.cochainComplex` versus `HomologicalComplex.extend I.cocomplex ComplexShape.embeddingUpNat`,
and `(HomologicalComplex.homologyFunctor _ _ p).obj K` versus `K.homology p`) which are
definitionally equal only at default transparency, so `rw`'s motive check rejects them.

`Stacks.Cohomology.FreeYonedaUnivLE.mapHomologyIso_evaluation_naturality` states its left-hand
side as a `ShortComplex.homologyMap` rather than a `HomologicalComplex.homologyMap`, which it is
definitionally; written the second way the whole proof is blocked by the same motive check.

These declarations carry no tag. [Stacks, Tag 0DCU] has eight claim-sites and the covering set of
the tag is not complete until all of them are in the library; the first half of
[Stacks, Tag 03AY] and the pinned second half already carry theirs.

## References

* [Stacks Project, Tag 03AY](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology

universe uA v

section GenericObject

variable {A : Type uA} [Category.{v} A] [Abelian A]

/-- Pasting two commuting squares side by side, in the associated form `a ≫ (b ≫ e)`. -/
private theorem comp_comp_eq_of_comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z V T : C}
    {a : W ⟶ X} {b : X ⟶ Y} {c : W ⟶ Z} {d : Z ⟶ Y} {e : Y ⟶ V} {f : Z ⟶ T} {g : T ⟶ V}
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e = f ≫ g) : a ≫ (b ≫ e) = c ≫ (f ≫ g) := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- `Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda` is natural in its object: it
intertwines `Stacks.Cohomology.Locality.precompCM` along `single g` with the degreewise action of
`preadditiveCoyoneda.map g.op`. -/
theorem homComplexSingleIsoCoyoneda_naturality_obj {X' X : A} (g : X' ⟶ X)
    (L : CochainComplex A ℤ) :
    Locality.precompCM ((CochainComplex.singleFunctor A 0).map g) ≫
        (Locality.homComplexSingleIsoCoyoneda X' L).hom =
      (Locality.homComplexSingleIsoCoyoneda X L).hom ≫
        (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (Quiver.Hom.op g))
          (ComplexShape.up ℤ)).app L := by
  ext j (c : CochainComplex.HomComplex.Cochain _ _ j)
  obtain ⟨f, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective c j (by ring)
  simp only [HomologicalComplex.comp_f, Locality.homComplexSingleIsoCoyoneda,
    Locality.precompCM, HomologicalComplex.Hom.isoOfComponents_hom_f, AddCommGrpCat.hom_comp,
    NatTrans.mapHomologicalComplex_app_f]
  change (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0 : ℤ) + j = j))
      ((CochainComplex.HomComplex.Cochain.ofHom
          ((CochainComplex.singleFunctor A 0).map g)).comp
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0 : ℤ) + j = j))
        (zero_add j))
    = g ≫ (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by ring : (0 : ℤ) + j = j))
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (by ring : (0 : ℤ) + j = j))
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_precomp,
    CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
    CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]

/-- `Stacks.Cohomology.Locality.mapExtendHomologyIso` is natural in the additive-functor variable:
it intertwines `NatTrans.mapHomologicalComplex τ` on the `ℤ`-extension with its `ℕ`-indexed
counterpart. This is the functor-variable companion of
`Stacks.Cohomology.mapExtendHomologyIso_naturality_complex`. -/
theorem mapExtendHomologyIso_naturality_functor {D E : Type uA} [Category.{v} D] [Category.{v} E]
    [Abelian D] [Abelian E] {F F' : D ⥤ E} [F.Additive] [F'.Additive] (τ : F ⟶ F')
    (X : CochainComplex D ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          (HomologicalComplex.extend X ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (Locality.mapExtendHomologyIso F' X n).hom =
      (Locality.mapExtendHomologyIso F X n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app X) n := by
  have hnat := Locality.mapExtendIso_naturality τ X
  have hj : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  have keyF : (Locality.mapExtendHomologyIso F X n).hom =
      HomologicalComplex.homologyMap (Locality.mapExtendIso F X).hom (n : ℤ) ≫
        (HomologicalComplex.extendHomologyIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj X)
          ComplexShape.embeddingUpNat hj).hom := rfl
  have keyF' : (Locality.mapExtendHomologyIso F' X n).hom =
      HomologicalComplex.homologyMap (Locality.mapExtendIso F' X).hom (n : ℤ) ≫
        (HomologicalComplex.extendHomologyIso ((F'.mapHomologicalComplex (ComplexShape.up ℕ)).obj X)
          ComplexShape.embeddingUpNat hj).hom := rfl
  rw [keyF, keyF', ← Category.assoc, ← HomologicalComplex.homologyMap_comp, hnat,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality, ← Category.assoc]

end GenericObject

section GenericAssembly

variable {A : Type (v + 1)} [Category.{v} A] [Abelian A]

/-- **Naturality of `Stacks.Cohomology.factorBCDApply` in the object.** A morphism `g : X' ⟶ X`
turns precomposition of a cocycle by `single g` into the map induced on the homology of the
corepresentable complexes by `preadditiveCoyoneda.map g.op`. This is the object-variable
companion of `Stacks.Cohomology.factorBCDApply_naturality`: the `homologyAddEquiv` factor is
`Stacks.Cohomology.Locality.precompCM_homologyAddEquiv_symm`, the corepresentability factor is
`homComplexSingleIsoCoyoneda_naturality_obj` and the extension factor is
`mapExtendHomologyIso_naturality_functor`. -/
theorem factorBCDApply_mk_precomp {X' X : A} (g : X' ⟶ X) {Z : A} (I : InjectiveResolution Z)
    (p : ℕ) (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)) :
    factorBCDApply X' I p (CochainComplex.HomComplex.CohomologyClass.mk
        (z.precomp ((CochainComplex.singleFunctor A 0).map g))) =
      (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (Quiver.Hom.op g))
          (ComplexShape.up ℕ)).app I.cocomplex) p)
        (factorBCDApply X I p (CochainComplex.HomComplex.CohomologyClass.mk z)) := by
  have hD := Locality.precompCM_homologyAddEquiv_symm
    ((CochainComplex.singleFunctor A 0).map g) (p : ℤ) z
  have hC :
      HomologicalComplex.homologyMap
          (Locality.precompCM ((CochainComplex.singleFunctor A 0).map g)) (p : ℤ) ≫
        HomologicalComplex.homologyMap
          (Locality.homComplexSingleIsoCoyoneda X' I.cochainComplex).hom (p : ℤ) =
      HomologicalComplex.homologyMap
          (Locality.homComplexSingleIsoCoyoneda X I.cochainComplex).hom (p : ℤ) ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (Quiver.Hom.op g))
            (ComplexShape.up ℤ)).app I.cochainComplex) (p : ℤ) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      homComplexSingleIsoCoyoneda_naturality_obj]
  have hB :
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (Quiver.Hom.op g))
            (ComplexShape.up ℤ)).app I.cochainComplex) (p : ℤ) ≫
        (Locality.mapExtendHomologyIso (preadditiveCoyoneda.obj (Opposite.op X'))
          I.cocomplex p).hom =
      (Locality.mapExtendHomologyIso (preadditiveCoyoneda.obj (Opposite.op X))
          I.cocomplex p).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (Quiver.Hom.op g))
            (ComplexShape.up ℕ)).app I.cocomplex) p :=
    mapExtendHomologyIso_naturality_functor
      (preadditiveCoyoneda.map (Quiver.Hom.op g)) I.cocomplex p
  have h2 := ConcreteCategory.congr_hom (comp_comp_eq_of_comp_eq_of_comp_eq hC hB)
    ((CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)).symm
      (CochainComplex.HomComplex.CohomologyClass.mk z))
  simp only [ConcreteCategory.comp_apply] at h2
  rw [hD] at h2
  exact h2

/-- The last three comparison isomorphisms computing `Ext` from an injective resolution, as an
isomorphism of abelian groups rather than a map: `Stacks.Cohomology.factorBCDApply` is its
underlying function (`factorBCDEquiv_apply`). -/
noncomputable def factorBCDEquiv (X : A) {Z : A} (I : InjectiveResolution Z) (p : ℕ) :
    CochainComplex.HomComplex.CohomologyClass ((CochainComplex.singleFunctor A 0).obj X)
        I.cochainComplex (p : ℤ) ≃+
      (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology p :=
  ((CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex (p : ℤ)).symm).trans <|
  (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (p : ℤ)).mapIso
      (Locality.homComplexSingleIsoCoyoneda X I.cochainComplex)).addCommGroupIsoToAddEquiv).trans
    (Locality.mapExtendHomologyIso (preadditiveCoyoneda.obj (Opposite.op X))
      I.cocomplex p).addCommGroupIsoToAddEquiv

/-- The underlying function of the additive equivalence `factorBCDEquiv` is `factorBCDApply`. -/
theorem factorBCDEquiv_apply (X : A) {Z : A} (I : InjectiveResolution Z) (p : ℕ)
    (cls : CochainComplex.HomComplex.CohomologyClass ((CochainComplex.singleFunctor A 0).obj X)
      I.cochainComplex (p : ℤ)) :
    factorBCDEquiv X I p cls = factorBCDApply X I p cls :=
  rfl

/-- **`Stacks.Cohomology.factorBCDApply` composed with Mathlib's
`InjectiveResolution.extAddEquivCohomologyClass` is natural in the first `Ext` variable.**
Precomposing an `Ext` class with `Abelian.Ext.mk₀ g` corresponds to the map induced on the
homology of the corepresentable complexes by `preadditiveCoyoneda.map g.op`. The `Ext`-level step
is Mathlib's `InjectiveResolution.mk₀_comp_extMk`, and the rest is
`factorBCDApply_mk_precomp`. -/
theorem factorBCDApply_extAddEquiv_naturality_obj [HasExt.{v} A] {Z : A}
    (I : InjectiveResolution Z) (p : ℕ) {X' X : A} (g : X' ⟶ X) (ξ : Abelian.Ext X Z p) :
    factorBCDApply X' I p
        (I.extAddEquivCohomologyClass ((Abelian.Ext.mk₀ g).comp ξ (zero_add p))) =
      (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (Quiver.Hom.op g))
          (ComplexShape.up ℕ)).app I.cocomplex) p)
        (factorBCDApply X I p (I.extAddEquivCohomologyClass ξ)) := by
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective ξ (p + 1) rfl
  rw [InjectiveResolution.mk₀_comp_extMk]
  simp only [InjectiveResolution.extAddEquivCohomologyClass_apply,
    InjectiveResolution.extEquivCohomologyClass_extMk]
  simp only [Category.assoc]
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_precomp]
  exact factorBCDApply_mk_precomp g I p _

end GenericAssembly

end Stacks.Cohomology

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe t u

noncomputable section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u t}]

/-- The section-presheaf cochain complex of an injective resolution, at a coefficient universe
independent of the site: `Stacks.Cohomology.Locality.sectionComplex` with the coefficients
freed. -/
abbrev sectionComplex (G : Sheaf J AddCommGrpCat.{max u t}) (I : InjectiveResolution G) :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u t}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{max u t}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

/-- The Hom-complex `Hom(L U, I^•)` of an injective resolution, at a coefficient universe
independent of the site: `Stacks.Cohomology.Locality.homComplex` with the coefficients freed. -/
abbrev homComplex (G : Sheaf J AddCommGrpCat.{max u t}) (I : InjectiveResolution G) (V : C) :
    CochainComplex AddCommGrpCat.{max u t} ℕ :=
  ((preadditiveCoyoneda.obj (Opposite.op ((freeYoneda.{t} J).obj V))).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex

/-- The map of Hom-complex homology induced by `L g`, for `g : Y ⟶ U` in the site. -/
abbrev homComplexMap (G : Sheaf J AddCommGrpCat.{max u t}) (I : InjectiveResolution G) (n : ℕ)
    {Y U : C} (g : Y ⟶ U) :
    (homComplex.{t} J G I U).homology n ⟶ (homComplex.{t} J G I Y).homology n :=
  HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex
      (preadditiveCoyoneda.map (Quiver.Hom.op ((freeYoneda.{t} J).map g)))
      (ComplexShape.up ℕ)).app I.cocomplex) n

/-- **The free-Yoneda corepresentability isomorphism, with the coefficient universe freed.**
`Hom(L U, -) ≅ (-)(U)` as functors `Sheaf J AddCommGrpCat ⥤ AddCommGrpCat`. This is
`Stacks.Cohomology.Locality.eFun` built on `freeYoneda` rather than on `yoneda`; its components
are `Stacks.Cohomology.FreeYonedaUnivLE.sectionsAddEquiv`. -/
def coyonedaIsoSections (U : C) :
    preadditiveCoyoneda.obj (Opposite.op ((freeYoneda.{t} J).obj U)) ≅
      sheafToPresheaf J AddCommGrpCat.{max u t} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op U) :=
  NatIso.ofComponents (fun F ↦ (sectionsAddEquiv.{t} U F).toAddCommGrpIso) (by
    intro F G β
    ext (α : (freeYoneda.{t} J).obj U ⟶ F)
    change sectionsEquiv.{t} U G (α ≫ β) = β.hom.app (Opposite.op U) (sectionsEquiv.{t} U F α)
    exact sectionsEquiv_naturality.{t} U α β)

/-- **`coyonedaIsoSections` is natural in the object of the site.** This is
`Stacks.Cohomology.Locality.eFun_naturality` with the coefficient universe freed; the content is
`Stacks.Cohomology.FreeYonedaUnivLE.sectionsEquiv_naturality_left`. -/
theorem coyonedaIsoSections_naturality {Y U : C} (g : Y ⟶ U) :
    preadditiveCoyoneda.map (Quiver.Hom.op ((freeYoneda.{t} J).map g)) ≫
        (coyonedaIsoSections.{t} J Y).hom =
      (coyonedaIsoSections.{t} J U).hom ≫
        Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u t})
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).map g.op) := by
  ext F (α : (freeYoneda.{t} J).obj U ⟶ F)
  change sectionsEquiv.{t} Y F ((freeYoneda.{t} J).map g ≫ α) =
    F.obj.map g.op (sectionsEquiv.{t} U F α)
  exact sectionsEquiv_naturality_left.{t} g F α

/-- **Homology commutes with evaluation, naturally in the evaluation point.** This is
`Stacks.Cohomology.Locality.mapHomologyIso_evaluation_naturality` with the coefficient universe
freed. -/
theorem mapHomologyIso_evaluation_naturality (G : Sheaf J AddCommGrpCat.{max u t})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U) :
    ShortComplex.homologyMap (((sectionComplex.{t} J G I).sc n).mapNatTrans
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).map g.op)) ≫
        (ShortComplex.mapHomologyIso ((sectionComplex.{t} J G I).sc n)
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op Y))).hom =
      (ShortComplex.mapHomologyIso ((sectionComplex.{t} J G I).sc n)
          ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op U))).hom ≫
        ((sectionComplex.{t} J G I).homology n).map g.op := by
  rw [ShortComplex.homologyMap_mapNatTrans, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rfl

/-- **Free-Yoneda corepresentability, assembled degreewise and passed to homology**, with the
coefficient universe freed: `Hⁿ(Hom(L V, I^•)) ≃+ Hⁿ(I^•(V))`. This is
`Stacks.Cohomology.Locality.homComplexHomologyEquivSectionHomology` with the coefficients no
longer pinned to the homs of the site. -/
def homComplexHomologyEquivSections (G : Sheaf J AddCommGrpCat.{max u t})
    (I : InjectiveResolution G) (n : ℕ) (V : C) :
    (homComplex.{t} J G I V).homology n ≃+ ((sectionComplex.{t} J G I).homology n).obj
      (Opposite.op V) :=
  (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J V) (ComplexShape.up ℕ)).app
        I.cocomplex)) ≪≫
    ShortComplex.mapHomologyIso ((sectionComplex.{t} J G I).sc n)
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op V))).addCommGroupIsoToAddEquiv

/-- Morphism-level naturality square of `homComplexHomologyEquivSections` in the object of the
site. -/
theorem homComplexHomologyEquivSections_naturality_hom (G : Sheaf J AddCommGrpCat.{max u t})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U) :
    homComplexMap.{t} J G I n g ≫
        (HomologicalComplex.homologyMap
            ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J Y)
              (ComplexShape.up ℕ)).app I.cocomplex).hom n ≫
          (ShortComplex.mapHomologyIso ((sectionComplex.{t} J G I).sc n)
            ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op Y))).hom) =
      HomologicalComplex.homologyMap
          ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J U)
            (ComplexShape.up ℕ)).app I.cocomplex).hom n ≫
        ((ShortComplex.mapHomologyIso ((sectionComplex.{t} J G I).sc n)
            ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op U))).hom ≫
          ((sectionComplex.{t} J G I).homology n).map g.op) := by
  have hstep1 :
      homComplexMap.{t} J G I n g ≫
          HomologicalComplex.homologyMap
            ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J Y)
              (ComplexShape.up ℕ)).app I.cocomplex).hom n =
        HomologicalComplex.homologyMap
            ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J U)
              (ComplexShape.up ℕ)).app I.cocomplex).hom n ≫
          HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex
              (Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u t})
                ((evaluation Cᵒᵖ AddCommGrpCat.{max u t}).map g.op)) (ComplexShape.up ℕ)).app
              I.cocomplex) n := by
    rw [homComplexMap, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    congr 1
    have heY : ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J Y)
          (ComplexShape.up ℕ)).app I.cocomplex).hom
        = (NatTrans.mapHomologicalComplex (coyonedaIsoSections.{t} J Y).hom
            (ComplexShape.up ℕ)).app I.cocomplex := rfl
    have heU : ((NatIso.mapHomologicalComplex (coyonedaIsoSections.{t} J U)
          (ComplexShape.up ℕ)).app I.cocomplex).hom
        = (NatTrans.mapHomologicalComplex (coyonedaIsoSections.{t} J U).hom
            (ComplexShape.up ℕ)).app I.cocomplex := rfl
    rw [heY, heU, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, ← NatTrans.mapHomologicalComplex_comp,
      coyonedaIsoSections_naturality]
  exact comp_comp_eq_of_comp_eq_of_comp_eq hstep1
    (mapHomologyIso_evaluation_naturality.{t} J G I n g)

/-- **`homComplexHomologyEquivSections` is natural in the object of the site.** -/
theorem homComplexHomologyEquivSections_naturality (G : Sheaf J AddCommGrpCat.{max u t})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (η : (homComplex.{t} J G I U).homology n) :
    homComplexHomologyEquivSections.{t} J G I n Y (homComplexMap.{t} J G I n g η) =
      ((sectionComplex.{t} J G I).homology n).map g.op
        (homComplexHomologyEquivSections.{t} J G I n U η) := by
  have h2 := congrArg (fun m : _ ⟶ _ ↦ (ConcreteCategory.hom m) η)
    (homComplexHomologyEquivSections_naturality_hom.{t} J G I n g)
  simp only [ConcreteCategory.comp_apply] at h2
  exact h2

section Ext

variable [HasExt.{max u t} (Sheaf J AddCommGrpCat.{max u t})]

omit [HasExt.{max u t} (Sheaf J AddCommGrpCat.{max u t})] in
/-- **`homComplexHomologyEquivSections` is natural in the sheaf.** This is
`Stacks.Cohomology.homComplexHomologyEquivSectionHomology_naturality_coeff` with the coefficient
universe freed. -/
theorem homComplexHomologyEquivSections_naturality_coeff
    {G H : Sheaf J AddCommGrpCat.{max u t}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f)
    (p : ℕ) (U : C) (η : (homComplex.{t} J G I U).homology p) :
    homComplexHomologyEquivSections.{t} J H I' p U
        ((HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj
            (Opposite.op ((freeYoneda.{t} J).obj U))).mapHomologicalComplex
              (ComplexShape.up ℕ)).map φ.hom) p) η) =
      ((HomologicalComplex.homologyMap
        (((sheafToPresheaf J AddCommGrpCat.{max u t}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p).app (Opposite.op U))
        (homComplexHomologyEquivSections.{t} J G I p U η) := by
  let S : Sheaf J AddCommGrpCat.{max u t} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max u t}) :=
    sheafToPresheaf J AddCommGrpCat.{max u t}
  let E : (Cᵒᵖ ⥤ AddCommGrpCat.{max u t}) ⥤ AddCommGrpCat.{max u t} :=
    (evaluation Cᵒᵖ AddCommGrpCat.{max u t}).obj (Opposite.op U)
  let e : preadditiveCoyoneda.obj (Opposite.op ((freeYoneda.{t} J).obj U)) ≅ S ⋙ E :=
    coyonedaIsoSections.{t} J U
  have hn := (NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).hom.naturality φ.hom
  have hn' := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u t} (ComplexShape.up ℕ) p).map) hn
  simp only [HomologicalComplex.homologyFunctor_map] at hn'
  simp only [HomologicalComplex.homologyMap_comp] at hn'
  have hm' :
      (HomologicalComplex.homologyMap
        (((S ⋙ E).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) p) ≫
        (ShortComplex.mapHomologyIso ((sectionComplex.{t} J H I').sc p) E).hom =
      (ShortComplex.mapHomologyIso ((sectionComplex.{t} J G I).sc p) E).hom ≫
        ((HomologicalComplex.homologyMap
          ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) p).app (Opposite.op U)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u t})
        (ComplexShape.up ℕ) p).map ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)) E
  exact (congrArg
      (fun x ↦ (ConcreteCategory.hom
        (ShortComplex.mapHomologyIso ((sectionComplex.{t} J H I').sc p) E).hom) x)
      (ConcreteCategory.congr_hom hn' η)).trans
    (ConcreteCategory.congr_hom hm'
      ((ConcreteCategory.hom (HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).hom.app I.cocomplex) p)) η))

/-- **The bridge of Section 21.7 with the coefficient universe freed**: for an injective
resolution `I` of `G`, `Extⁿ(L V, G) ≃+ Hⁿ(I^•(V))`. This is
`Stacks.Cohomology.Locality.extEquivSectionHomology` built on `freeYoneda` rather than on
`yoneda`, so its coefficients are `AddCommGrpCat.{max u t}` with `t` free of the site. -/
def extEquivSections (G : Sheaf J AddCommGrpCat.{max u t}) (I : InjectiveResolution G) (n : ℕ)
    (V : C) :
    Abelian.Ext ((freeYoneda.{t} J).obj V) G n ≃+
      ((sectionComplex.{t} J G I).homology n).obj (Opposite.op V) :=
  (I.extAddEquivCohomologyClass.trans
      (Stacks.Cohomology.factorBCDEquiv ((freeYoneda.{t} J).obj V) I n)).trans
    (homComplexHomologyEquivSections.{t} J G I n V)

/-- **`extEquivSections` is natural in the object of the site.** -/
theorem extEquivSections_naturality (G : Sheaf J AddCommGrpCat.{max u t})
    (I : InjectiveResolution G) (n : ℕ) {Y U : C} (g : Y ⟶ U)
    (ξ : Abelian.Ext ((freeYoneda.{t} J).obj U) G n) :
    extEquivSections.{t} J G I n Y
        ((Abelian.Ext.mk₀ ((freeYoneda.{t} J).map g)).comp ξ (zero_add n)) =
      ((sectionComplex.{t} J G I).homology n).map g.op (extEquivSections.{t} J G I n U ξ) := by
  simp only [extEquivSections, AddEquiv.trans_apply]
  rw [Stacks.Cohomology.factorBCDEquiv_apply, Stacks.Cohomology.factorBCDEquiv_apply,
    Stacks.Cohomology.factorBCDApply_extAddEquiv_naturality_obj I n ((freeYoneda.{t} J).map g) ξ]
  exact homComplexHomologyEquivSections_naturality.{t} J G I n g _

/-- **`extEquivSections` is natural in the sheaf.** -/
theorem extEquivSections_naturality_coeff {G H : Sheaf J AddCommGrpCat.{max u t}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f) (p : ℕ) (U : C)
    (ξ : Abelian.Ext ((freeYoneda.{t} J).obj U) G p) :
    extEquivSections.{t} J H I' p U (ξ.comp (Abelian.Ext.mk₀ f) (add_zero p)) =
      ((HomologicalComplex.homologyMap
        (((sheafToPresheaf J AddCommGrpCat.{max u t}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p).app (Opposite.op U))
        (extEquivSections.{t} J G I p U ξ) := by
  simp only [extEquivSections, AddEquiv.trans_apply]
  rw [Stacks.Cohomology.factorBCDEquiv_apply, Stacks.Cohomology.factorBCDEquiv_apply,
    Stacks.Cohomology.extAddEquivCohomologyClass_naturality_coeff f I I' φ p
      ((freeYoneda.{t} J).obj U) ξ,
    Stacks.Cohomology.factorBCDApply_naturality]
  exact homComplexHomologyEquivSections_naturality_coeff.{t} J f I I' φ p U _

/-- **The homology presheaves of the section complex are the cohomology presheaves**, with the
coefficient universe freed. This is `Stacks.Cohomology.cohomologyPresheafIsoResolution` with the
coefficients no longer pinned to the homs of the site. -/
def cohomologyPresheafIsoResolution (G : Sheaf J AddCommGrpCat.{max u t})
    (I : InjectiveResolution G) (p : ℕ) :
    (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u t})
          (ComplexShape.up ℕ) p).obj (sectionComplex.{t} J G I) ≅
      cohomologyPresheaf.{max u t, t} G p := by
  refine (NatIso.ofComponents (fun ⟨U⟩ ↦
    (extEquivSections.{t} J G I p U).toAddCommGrpIso) ?_).symm
  rintro ⟨U⟩ ⟨V⟩ f
  ext ξ
  exact extEquivSections_naturality.{t} J G I p f.unop ξ

/-- **`cohomologyPresheafIsoResolution` is natural in the sheaf, inverse direction.** -/
theorem cohomologyPresheafIsoResolution_inv_naturality
    {G H : Sheaf J AddCommGrpCat.{max u t}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f) (p : ℕ) :
    (cohomologyPresheafFunctor.{max u t, t} J p).map f ≫
        (cohomologyPresheafIsoResolution.{t} J H I' p).inv =
      (cohomologyPresheafIsoResolution.{t} J G I p).inv ≫
        ((sheafToPresheaf J AddCommGrpCat.{max u t}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map φ.hom := by
  ext ⟨U⟩ ξ
  exact extEquivSections_naturality_coeff.{t} J f I I' φ p U ξ

/-- **`cohomologyPresheafIsoResolution` is natural in the sheaf.** -/
theorem cohomologyPresheafIsoResolution_hom_naturality
    {G H : Sheaf J AddCommGrpCat.{max u t}} (f : G ⟶ H)
    (I : InjectiveResolution G) (I' : InjectiveResolution H) (φ : I.Hom I' f) (p : ℕ) :
    ((sheafToPresheaf J AddCommGrpCat.{max u t}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map φ.hom ≫
        (cohomologyPresheafIsoResolution.{t} J H I' p).hom =
      (cohomologyPresheafIsoResolution.{t} J G I p).hom ≫
        (cohomologyPresheafFunctor.{max u t, t} J p).map f := by
  rw [← Iso.eq_comp_inv, Category.assoc,
    cohomologyPresheafIsoResolution_inv_naturality.{t} J f I I' φ p,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max u t})]

/-- **Stacks 03AY, objectwise, with the coefficient universe freed.** -/
def rightDerivedObjIsoCohomologyPresheaf (G : Sheaf J AddCommGrpCat.{max u t}) (p : ℕ) :
    ((sheafToPresheaf J AddCommGrpCat.{max u t}).rightDerived p).obj G ≅
      cohomologyPresheaf.{max u t, t} G p :=
  (injectiveResolution G).isoRightDerivedObj (sheafToPresheaf J AddCommGrpCat.{max u t}) p ≪≫
    cohomologyPresheafIsoResolution.{t} J G (injectiveResolution G) p

/-- The forward map of `rightDerivedObjIsoCohomologyPresheaf` is the forward map of
`InjectiveResolution.isoRightDerivedObj` followed by that of `cohomologyPresheafIsoResolution`. -/
theorem rightDerivedObjIsoCohomologyPresheaf_hom (G : Sheaf J AddCommGrpCat.{max u t}) (p : ℕ) :
    (rightDerivedObjIsoCohomologyPresheaf.{t} J G p).hom =
      ((injectiveResolution G).isoRightDerivedObj
        (sheafToPresheaf J AddCommGrpCat.{max u t}) p).hom ≫
        (cohomologyPresheafIsoResolution.{t} J G (injectiveResolution G) p).hom :=
  rfl

/-- **Stacks 03AY, right derived functors, with the coefficient universe freed.** On a small site
the `p`-th right derived functor of the inclusion of abelian sheaves into abelian presheaves is
naturally isomorphic to the degree-`p` cohomology presheaf functor — at any coefficient universe
dominating the site, rather than only at the universe of its homs.

This is `Stacks.Cohomology.rightDerivedSheafToPresheafIso`, whose single universe parameter forces
the coefficients to be `AddCommGrpCat.{u}`, read in the cohomology presheaf of
`DerivedSections/FreeYonedaSectionsUnivLE.lean`. -/
@[sga "4 IV 4.8" "partial", sga "4 V 2.4.2" "(2.4.2.2), special case"]
def rightDerivedSheafToPresheafIso (p : ℕ) :
    (sheafToPresheaf J AddCommGrpCat.{max u t}).rightDerived p ≅
      cohomologyPresheafFunctor.{max u t, t} J p :=
  NatIso.ofComponents (fun G ↦ rightDerivedObjIsoCohomologyPresheaf.{t} J G p) (by
    intro G H f
    let φ : (injectiveResolution G).Hom (injectiveResolution H) f :=
      ⟨InjectiveResolution.desc f _ _, by
        simpa using InjectiveResolution.desc_commutes_zero f
          (injectiveResolution H) (injectiveResolution G)⟩
    rw [rightDerivedObjIsoCohomologyPresheaf_hom, rightDerivedObjIsoCohomologyPresheaf_hom,
      ← Category.assoc,
      InjectiveResolution.isoRightDerivedObj_hom_naturality f _ _ φ.hom
        (by simpa using φ.ι_f_zero_comp_hom_f_zero),
      Category.assoc,
      cohomologyPresheafIsoResolution_hom_naturality.{t} J f _ _ φ p, Category.assoc])

end Ext

end

end Stacks.Cohomology.FreeYonedaUnivLE

end
