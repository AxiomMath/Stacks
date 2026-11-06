module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayColimit
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.SliceRestrictionColimits

/-!
# Inverting a global section commutes with restriction to a slice site

Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪` and let `U` be an object of
`𝒞`. The section `f` restricts to a global section `f|_U` of the structure sheaf of the localized
ringed site `(𝒞/U, 𝒪_U)`, and

`(𝒪_f)|_U ≅ (𝒪_U)_{f|_U}`

as sheaves of `𝒪_U`-modules, compatibly with the canonical maps out of the structure sheaf.

This is the **base change of the localization `𝒪_f` along a slice restriction**. It is the
comparison recorded as missing in the "What remains for Tag 0998" section of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/VanishingIdeal.lean`:
`AlgebraicGeometry.RingedSite.awaySheaf` inverts a *global* section, so a section `f ∈ 𝒪(U)` is
handled by passing to `AlgebraicGeometry.RingedSite.over X U`, where it becomes a global section
because `Over.mk (𝟙 U)` is terminal — and nothing then related the sheaf obtained there to the
sheaf obtained upstairs.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalSectionOver`: a global section of `𝒪`, read as a global
  section of `𝒪_U`.
* `AlgebraicGeometry.RingedSite.awaySmulOver`: multiplication by `f|_U`, as the restriction of
  multiplication by `f`.
* `AlgebraicGeometry.RingedSite.awaySequenceOverIso`: the sequential diagram
  `𝒪 --f--> 𝒪 --f--> ⋯` restricts to the sequential diagram `𝒪_U --f|_U--> 𝒪_U --f|_U--> ⋯`.

## Main results

* `AlgebraicGeometry.RingedSite.awayModuleOverIso`: **`(𝒪_f)|_U ≅ (𝒪_U)_{f|_U}`.**
* `AlgebraicGeometry.RingedSite.overFunctor_map_unitToAwayModule_comp_awayModuleOverIso`: the
  identification carries the restriction of `𝒪 ⟶ 𝒪_f` to `𝒪_U ⟶ (𝒪_U)_{f|_U}`.
* `AlgebraicGeometry.RingedSite.awayModuleProdOverIso`: the same for a subproduct `f_S` of a
  finite family, which is what the terms of the extended alternating Čech complex are. Its
  naturality in `S`, and the resulting identification of the whole Čech complex, are in
  `CechSliceRestriction.lean`.

## Implementation notes

`𝒪_f` is a sheafification, so it has no description of its sections; the proof therefore uses no
sectionwise argument about it. Instead both sides are identified as the *same sequential
colimit*:

* upstairs `𝒪_f = colim(𝒪 --f--> 𝒪 --f--> ⋯)` is
  `AlgebraicGeometry.RingedSite.isColimitAwayModuleCocone`;
* restriction to a slice preserves colimits, which is
  `Stacks.SheafOfModules.preservesColimits_overFunctor_of_small` — Mathlib's
  `SheafOfModules.overPushforwardOverAdj` would need `Over.star U` and hence binary products on
  the site, which a site need not have, and that hypothesis is what that result removes;
* the restricted diagram *is* the diagram of the slice, because the terms are the structure
  sheaf — `SheafOfModules.overFunctor` carries `SheafOfModules.unit` to `SheafOfModules.unit` by
  `rfl` — and the maps are multiplication by `f`, whose restriction acts on sections over `V/U`
  by multiplication by the value of `f` over `V`. The comparison is built with
  `CategoryTheory.NatTrans.ofSequence`, so only the squares over `n ⟶ n + 1` are checked;
* downstairs the same presentation, read on the slice, is the colimit of that diagram.

Two colimit cocones over isomorphic diagrams have isomorphic vertices, which is
`CategoryTheory.Limits.IsColimit.coconePointsIsoOfNatIso`; compatibility with the canonical maps
out of `𝒪` is that isomorphism read on the zeroth leg, together with
`AlgebraicGeometry.RingedSite.awayModuleCoconeι_zero`.

Nothing here carries a `stacks` attribute: the localization of the structure sheaf of a ringed
site at a global section is not a notion the source names, and neither is its base change along
`𝒞/U ⥤ 𝒞`.

### What remains for Tag 099E

**Status.** [Stacks, Tag 099E] is proved for an arbitrary sheaf of ideals, as
`AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech` of `FiniteTypeExtendedCech.lean`, and
[Stacks, Tag 099F] follows from it as
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of `FiniteTypeReflector.lean`.
Neither [Stacks, Tag 099D] nor any gluing is used there: the presheaf of Čech complexes of *all*
local generators of `ℐ` — a filtered colimit, hence a presheaf with no choice made — is sheafified
on `𝒞`, and on each slice the leg into it from the Čech complex of one generating family is locally
bijective on homology. Where the notes below say that 099E is missing or needs gluing, they record
the state of the library before that construction.

Tag 099E asks for a map `K ⟶ 𝒪` in `D(𝒪)` whose restriction to every `U` carrying a finite
generating family `f_1, …, f_r` of `ℐ|_U` is the extended alternating Čech complex of that
family, compatibly with the maps to `𝒪_U`. The construction of this file is the first step of
the first half — that the *terms* of that complex are compatible with restriction. In dependency
order:

1. **`Č(f)|_U ≅ Č(f|_U)`.** *Proved*, in `CechSliceRestriction.lean`, as
   `AlgebraicGeometry.RingedSite.extendedAlternatingCechOverIso`, compatibly with the
   augmentations out of the structure sheaf. It uses two statements about
   `CategoryTheory.AlternatingCech.complex` — that a natural isomorphism of localization systems
   induces an isomorphism of complexes, and that an additive functor preserving the products
   involved commutes with the formation of the complex — proved in
   `ExtendedCechFunctoriality.lean` as `CategoryTheory.AlternatingCech.complexMapIso` and
   `CategoryTheory.AlternatingCech.mapComplexIso`, together with the input they consume:
   the identification `awayModuleProdOverIso` below *natural in `S`*, which is
   `AlgebraicGeometry.RingedSite.awayLocalizationFunctorOverIso` there.

2. **Independence of the chosen finite generating family, at the level of sheaves.** For two
   finite families generating the same `ℐ|_U` the two Čech complexes must be isomorphic in
   `D(𝒪_U)` over `𝒪_U`. The ring-level statement is proved —
   `Stacks.IdealCechComplex.canonicalIso` of
   `StacksFrontier/RingTheory/Cech/IdealCechComplexRestriction.lean`, which is even canonical and
   coherent — but its proof is the universal property of the augmentation among objects with
   `I`-power-torsion cohomology,
   `Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHom`, and no analogue of that
   universal property exists for sheaves of modules on a ringed site.
   The inputs it would need are exactly the ones recorded as missing in the "What remains for Tag
   0998" section of `VanishingIdeal.lean` and in `VanishingCriterion.lean`, namely the two
   implications of [Stacks, Tag 0997] and the short exact sequence of [Stacks, Tag 00EJ].

3. **A strictly functorial model, i.e. [Stacks, Tag 099D].** This is the missing input that
   neither 1 nor 2 supplies, and it is why the source proves 099E through 099D rather than
   through the Čech complexes directly.

   It is a *gap*, not an impossibility, and in particular it is not what
   `StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean` refutes. That file proves
   `Stacks.FunctorialCechFamily.not_transportedFamily`: there is no choice, for every pair
   `(A, I)`, of a finite generating family of `I` whose members transport along every ring map.
   That closes one *route* to 099D — taking `K(A, I)` to be the Čech complex of a chosen family —
   and nothing else; the source constructs its `K(A, I)` as a filtered colimit over finite-type
   `ℤ`-algebras of a complex built from an injective resolution on a chaotic site, which is not a
   Čech complex and carries an action of the automorphism group of the pair. Against 099E it says
   nothing at all: 099E's statement quantifies the generating family *universally* and asserts an
   isomorphism for each one, so no choice function on objects appears in it, and the
   generator-independence that a choice function would have provided is already proved without one,
   at ring level, by `Stacks.LocalCohomology.exists_extendedCechObject_iso_of_span_eq`. The source
   glues the local complexes by *sheafifying a presheaf complex*: for a finitely generated
   `I ⊆ ℐ(U)` it forms the presheaf of complexes `U'/U ↦ K(𝒪(U'), I𝒪(U'))`, and two such presheaves
   for two generating `I`, `I'` literally *coincide* over the objects above a covering of `U`, so
   their sheafifications are the same complex. A comparison in `D(𝒪_U)` cannot do this: objects of
   a derived category do not glue along a cover, and an isomorphism in `D` is not an equality of
   complexes. The interface for 099D is `Stacks.LocalCohomology.FunctorialCechData` in
   `StacksFrontier/RingTheory/DerivedCompletion/FunctorialCechComplex.lean`, and **no term of it is
   constructed anywhere in the library**; the source's own construction of one is a filtered
   colimit over finite-type `ℤ`-algebras of a complex built from an injective resolution on a
   chaotic site, resting on Dualizing Complexes 47.10.2 and 47.10.3.

4. **Gluing, given 099D.** Even with a functorial Čech datum, three further pieces are absent:
   the presheaf of modules on `𝒞/U` built from `K(𝒪(-), I𝒪(-))` and its semilinearity; the
   locality of sheafification on a slice under a covering sieve, which is what turns "the two
   presheaf complexes agree above a cover" into "their sheafifications agree"; and the descent of
   a compatible family of complexes of module sheaves on the slices `𝒞/U` to a complex on `𝒞`.
   For the last, `StacksCore/CategoryTheory/Sites/Descent/DescentData.lean` has the general
   descent-data framework of [Stacks, Tags 026B, 026D, 026E], but effectivity for sheaves of
   modules — membership in the essential image of `Pseudofunctor.toDescentData` — is not proved.
   The source's step of replacing `𝒞` by the full subcategory of objects over which `ℐ` is
   finitely generated, a special cocontinuous functor ([Stacks, Tags 03CG, 03A0]), is likewise
   not available for module sheaves or their derived categories.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

section Restrict

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- Restriction of a global section of the structure sheaf to the slice site over `U`: its
value over an object `V/U` is its value over `V`. -/
def globalSectionOver (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u}) :=
  (Presheaf.globalSectionsEquivSections _).symm
    { val := fun V => (Presheaf.globalSectionsEquivSections _ h).1 (op V.unop.left)
      property := fun {_V _W} a =>
        (Presheaf.globalSectionsEquivSections _ h).2 (a.unop.left.op) }

/-- The value of `f|_U` over `V/U` is the value of `f` over `V`. -/
@[simp]
theorem globalSectionVal_globalSectionOver
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (V : (Over U)ᵒᵖ) :
    globalSectionVal (globalSectionOver X U h) V = globalSectionVal h (op V.unop.left) := by
  show (Presheaf.globalSectionsEquivSections _
    ((Presheaf.globalSectionsEquivSections _).symm _)).1 V = _
  rw [Equiv.apply_symm_apply]

/-- Restriction of modules to the slice carries the structure sheaf to the structure sheaf. -/
theorem overFunctor_obj_unit :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :=
  rfl

end Restrict

section Smul

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Sections of a restricted sheaf of modules over `V/U` are its sections over `V`. -/
theorem overFunctor_obj_val_obj
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (V : (Over U)ᵒᵖ) :
    ((SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj M).val.obj V =
      M.val.obj (op V.unop.left) :=
  rfl

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **Multiplication by `f` restricts to multiplication by `f|_U`.** -/
theorem overFunctor_map_awaySmul_app_apply (V : (Over U)ᵒᵖ)
    (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))).val.obj V) :
    (((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
        ((awaySmul X h).asHom.app
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))).val.app V).hom x =
      globalSectionVal (globalSectionOver X U h) V • x := by
  rw [globalSectionVal_globalSectionOver]
  exact awaySmul_app_apply X h (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (op V.unop.left) x

/-- Multiplication by `f|_U`, as an endomorphism of the structure sheaf of the slice: the
restriction of multiplication by `f`. -/
def awaySmulOver :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :=
  (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
    ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- `awaySmulOver` acts on sections by multiplication by the value of `f|_U`. -/
theorem awaySmulOver_app_apply (V : (Over U)ᵒᵖ)
    (x : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))).val.obj V) :
    ((awaySmulOver X U h).val.app V).hom x =
      globalSectionVal (globalSectionOver X U h) V • x :=
  overFunctor_map_awaySmul_app_apply X U h V x

/-- The sequential diagram of the slice is the restriction of the sequential diagram. -/
def awaySequenceOverHom :
    awaySequence X
        ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⋙
        SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ⟶
      awaySequence (X.over U) (awaySmulOver X U h) :=
  NatTrans.ofSequence (F := awaySequence X
      ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⋙
        SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
    (G := awaySequence (X.over U) (awaySmulOver X U h))
    (fun _ => 𝟙 _) (fun n => by
      have h₁ : (awaySequence X
            ((awaySmul X h).asHom.app
              (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))).map
              (homOfLE (Nat.le_add_right n 1)) =
          (awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
        awaySequence_map_succ X _ n
      have h₂ : (awaySequence (X.over U) (awaySmulOver X U h)).map
            (homOfLE (Nat.le_add_right n 1)) = awaySmulOver X U h :=
        awaySequence_map_succ (X.over U) _ n
      dsimp only [Functor.comp_map]
      rw [h₁, h₂]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Each component of `awaySequenceOverHom` is an isomorphism. -/
instance isIso_awaySequenceOverHom_app (n : ℕ) :
    IsIso ((awaySequenceOverHom X U h).app n) := by
  have happ : (awaySequenceOverHom X U h).app n =
      𝟙 ((awaySequence X ((awaySmul X h).asHom.app
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⋙
        SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj
          n) := rfl
  rw [happ]
  exact IsIso.id _

/-- The comparison `awaySequenceOverHom` of sequential diagrams is an isomorphism. -/
instance isIso_awaySequenceOverHom : IsIso (awaySequenceOverHom X U h) :=
  NatIso.isIso_of_isIso_app _

/-- **The sequential diagram presenting `𝒪_f` restricts to the one presenting `(𝒪_U)_{f|_U}`.** -/
def awaySequenceOverIso :
    awaySequence X
        ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⋙
        SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ≅
      awaySequence (X.over U) (awaySmulOver X U h) :=
  asIso (awaySequenceOverHom X U h)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Restriction to a slice preserves the sequential colimits that present `𝒪_f`. -/
theorem preservesColimitsOfSize_overFunctor :
    PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
    Stacks.SheafOfModules.preservesColimits_overFunctor_of_small
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  preservesColimitsOfSize_shrink _

attribute [local instance] preservesColimitsOfSize_overFunctor

/-- The colimit cocone presenting `𝒪_f`, restricted to the slice. -/
def awayModuleOverColimit :
    IsColimit ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapCocone
      (awayModuleCocone X h
        ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (fun V x => awaySmul_app_apply X h _ V x))) :=
  isColimitOfPreserves _
    (isColimitAwayModuleCocone X h
      ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (fun V x => awaySmul_app_apply X h _ V x))

/-- The colimit cocone presenting `(𝒪_U)_{f|_U}`. -/
def awaySliceColimit :
    IsColimit (awayModuleCocone (X.over U) (globalSectionOver X U h) (awaySmulOver X U h)
      (fun V x => awaySmulOver_app_apply X U h V x)) :=
  isColimitAwayModuleCocone (X.over U) (globalSectionOver X U h) (awaySmulOver X U h)
    (fun V x => awaySmulOver_app_apply X U h V x)

/-- **Inverting a global section commutes with restriction to a slice site:**
`(𝒪_f)|_U ≅ (𝒪_U)_{f|_U}` as sheaves of `𝒪_U`-modules. -/
def awayModuleOverIso :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj
        (awayModule X h) ≅
      awayModule (X.over U) (globalSectionOver X U h) :=
  IsColimit.coconePointsIsoOfNatIso (awayModuleOverColimit X U h) (awaySliceColimit X U h)
    (awaySequenceOverIso X U h)

/-- **The identification is compatible with the canonical maps out of the structure sheaf**:
the restriction of `𝒪 ⟶ 𝒪_f` is `𝒪_U ⟶ (𝒪_U)_{f|_U}`. -/
theorem overFunctor_map_unitToAwayModule_comp_awayModuleOverIso :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
        (unitToAwayModule X h) ≫
        (awayModuleOverIso X U h).hom =
      unitToAwayModule (X.over U) (globalSectionOver X U h) := by
  have hleg := IsColimit.comp_coconePointsIsoOfNatIso_hom (awayModuleOverColimit X U h)
    (awaySliceColimit X U h) (awaySequenceOverIso X U h) 0
  have hsrc : ((SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapCocone
        (awayModuleCocone X h
          ((awaySmul X h).asHom.app (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
          (fun V x => awaySmul_app_apply X h _ V x))).ι.app 0 =
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
        (unitToAwayModule X h) := by
    show (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
      (awayModuleCoconeι X h 0) = _
    rw [awayModuleCoconeι_zero]
  have htgt : (awayModuleCocone (X.over U) (globalSectionOver X U h) (awaySmulOver X U h)
        (fun V x => awaySmulOver_app_apply X U h V x)).ι.app 0 =
      unitToAwayModule (X.over U) (globalSectionOver X U h) :=
    awayModuleCoconeι_zero (X.over U) (globalSectionOver X U h)
  rw [hsrc] at hleg
  rw [htgt] at hleg
  refine hleg.trans ?_
  have happ : (awaySequenceOverIso X U h).hom.app 0 =
      𝟙 ((awaySequence X ((awaySmul X h).asHom.app
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ⋙
        SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj
          0) := rfl
  rw [happ]
  exact Category.id_comp _

end Smul

section Transport

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)

/-- `(𝒪_f)|_U ≅ (𝒪_U)_{f'}` for any global section `f'` of `𝒪_U` equal to the restriction of
`f`: the identification of `awayModuleOverIso`, transported along that equality. -/
def awayModuleOverIsoOfEq
    {h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    {h' : Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u})}
    (e : globalSectionOver X U h = h') :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj
        (awayModule X h) ≅
      awayModule (X.over U) h' :=
  e ▸ awayModuleOverIso X U h

/-- The transported identification is still compatible with the canonical maps out of the
structure sheaf. -/
theorem overFunctor_map_unitToAwayModule_comp_awayModuleOverIsoOfEq
    {h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})}
    {h' : Presheaf.globalSections ((X.over U).O.obj ⋙ forget CommRingCat.{u})}
    (e : globalSectionOver X U h = h') :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
        (unitToAwayModule X h) ≫
        (awayModuleOverIsoOfEq X U e).hom =
      unitToAwayModule (X.over U) h' := by
  subst e
  exact overFunctor_map_unitToAwayModule_comp_awayModuleOverIso X U h

end Transport

section Prod

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- Restriction to a slice commutes with forming the subproduct `f_S` of a finite family: both
sides are the global section whose value over `V/U` is `∏_{i ∈ S} f_i|_V`. -/
theorem globalSectionOver_prodGlobalSection (S : Finset (Fin r)) :
    globalSectionOver X U (prodGlobalSection f S) =
      prodGlobalSection (fun i => globalSectionOver X U (f i)) S := by
  refine (Presheaf.globalSectionsEquivSections _).injective (Subtype.ext (funext fun V => ?_))
  show globalSectionVal (globalSectionOver X U (prodGlobalSection f S)) V =
    globalSectionVal (prodGlobalSection (fun i => globalSectionOver X U (f i)) S) V
  rw [globalSectionVal_globalSectionOver, globalSectionVal_prodGlobalSection,
    globalSectionVal_prodGlobalSection]
  exact Finset.prod_congr rfl fun i _ => (globalSectionVal_globalSectionOver X U (f i) V).symm

/-- **Inverting a subproduct commutes with restriction to a slice site:**
`(𝒪_{f_S})|_U ≅ (𝒪_U)_{(f|_U)_S}` for every subset `S` of the index set. -/
def awayModuleProdOverIso (S : Finset (Fin r)) :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).obj
        (awayModule X (prodGlobalSection f S)) ≅
      awayModule (X.over U) (prodGlobalSection (fun i => globalSectionOver X U (f i)) S) :=
  awayModuleOverIsoOfEq X U (globalSectionOver_prodGlobalSection X U f S)

/-- The identification of the Čech terms is compatible with the canonical maps out of the
structure sheaf. -/
theorem overFunctor_map_unitToAwayModule_comp_awayModuleProdOverIso (S : Finset (Fin r)) :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
          (unitToAwayModule X (prodGlobalSection f S)) ≫
        (awayModuleProdOverIso X U f S).hom =
      unitToAwayModule (X.over U)
        (prodGlobalSection (fun i => globalSectionOver X U (f i)) S) :=
  overFunctor_map_unitToAwayModule_comp_awayModuleOverIsoOfEq X U
    (globalSectionOver_prodGlobalSection X U f S)

end Prod

end AlgebraicGeometry.RingedSite

end
