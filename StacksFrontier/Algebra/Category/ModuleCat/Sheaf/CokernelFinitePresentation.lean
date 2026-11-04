module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
import StacksCore.Tactic.StacksAttribute

/-!
# Cokernels of maps from finite-type to finitely presented modules on a ringed site

On a ringed site, if `φ : G ⟶ F` is a morphism of sheaves of modules with `F` of finite
presentation and `G` of finite type, then `coker φ` is of finite presentation.

The argument is the one in the source, carried out locally. Over an object `U` where `F` has
a finite presentation `free P.relations.I ⟶ free P.generators.I ⟶ F` and `G` has finitely
many generators `σ.π : free σ.I ⟶ G`, one lifts `σ.π ≫ φ` through the surjection
`P.generators.π`; such a lift exists after passing to a covering family, because the
generating sections of `G` lift locally along an epimorphism. Given a lift `ℓ`, the morphism
`free (P.relations.I ⊕ σ.I) ⟶ free P.generators.I` built from the relations of `F` and from
`ℓ` has `P.generators.π ≫ coker.π φ` as its cokernel, which is a finite presentation of
`coker φ`. Finite presentation is a local condition, so these local presentations assemble.

## Main results

* `Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel`: the statement above,
  Stacks 0H98.
* `Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits` and
  `overFunctor_preservesFiniteColimits`: restriction of sheaves of modules along a morphism
  of the site, and restriction from the site to a slice, preserve finite colimits.
* `Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation` and
  `mapFiniteGeneratingSections`: a finite presentation, resp. a finite generating family, is
  carried along any finite-colimit-preserving functor which takes the unit sheaf to the unit
  sheaf.
* `Stacks.SheafOfModules.LocalCokernel.exists_local_lift`: a morphism from a finite free
  sheaf of modules into the target of an epimorphism from a finite free sheaf lifts through
  that epimorphism after restriction to the members of a covering sieve.
* `Stacks.SheafOfModules.LocalCokernel.finitePresentation_cokernel_of_presentation_of_lift`:
  the global form of the lemma, from a finite presentation of `F`, finitely many generators
  of `G` and a lift.

## Implementation notes

Modules are sheaves of modules over the sheaf of rings underlying the structure sheaf of the
ringed site, `AlgebraicGeometry.RingedSite.ringSheaf`, and the cokernel is taken in their
abelian category. The sheafification hypotheses are those under which Mathlib's
universe-polymorphic site API provides the free sheaf of modules on a slice and the abelian
structure; they are hypotheses of the constructions used, not extra finiteness conditions.

Two functors have to be shown to preserve finite colimits and neither preservation is in
Mathlib: restriction along a morphism `V ⟶ U` of the site (`SheafOfModules.overMap`) and
restriction from the site to a slice (`SheafOfModules.overFunctor`). Both are checked by the
same route: each preserves finite limits (objectwise, since the underlying presheaf of a
restriction is a reindexing) and each preserves epimorphisms (an epimorphism of sheaves of
modules is a locally surjective map of underlying abelian sheaves, and local surjectivity is
stable under whiskering along a continuous functor), and an additive functor between abelian
categories which preserves finite limits and epimorphisms preserves finite colimits.

The abelian structure used in the statement is Mathlib's `SheafOfModules.instAbelian`, so the
high-priority instance `AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules` is
removed for the final declaration; the two agree, but the statement is pinned to the former
so that it is the cokernel of the surrounding development.

## References

* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace Stacks.SheafOfModules.LocalCokernel

/-- An epimorphism of sheaves of modules is locally surjective on underlying presheaves. -/
theorem locallySurjective_of_epi
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    {M N : SheafOfModules.{w} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  have h := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
    ((SheafOfModules.toSheaf R).map f)).mpr inferInstance
  exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
    ((SheafOfModules.toSheaf R).map f)).mp h

/-- Restriction along a morphism of the site acts on sections by reindexing, so the map it
induces on sections over an object of the slice is literally the given one. -/
theorem overMap_map_hom_app
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U V : C} (g : V ⟶ U)
    {M N : SheafOfModules.{w} (R.over U)} (f : M ⟶ N)
    (W : Over V) :
    ConcreteCategory.hom
        (((SheafOfModules.overMap R g).map f).val.app (Opposite.op W)) =
      ConcreteCategory.hom (f.val.app (Opposite.op ((Over.map g).obj W))) := by
  rfl

/-- The comparison of unit sheaves along a restriction carries `1` to `1`. -/
theorem overMapUnitIso_hom_app
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U V : C} (g : V ⟶ U)
    (W : Over V) :
    ConcreteCategory.hom
        ((SheafOfModules.overMapUnitIso (R := R) g).hom.val.app (Opposite.op W))
        (1 : (R.over V).obj.obj (Opposite.op W)) =
        (1 : (R.over V).obj.obj (Opposite.op W)) := by
  show (1 : (R.over V).obj.obj (Opposite.op W)) = _
  rfl

/-- A functor into sheaves of modules preserves finite limits if, after each evaluation functor
from the source, the evaluation functors of the target are computed by the source's. -/
private theorem preservesFiniteLimits_of_evaluation
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S)
    (h : ∀ W, PreservesFiniteLimits (F ⋙ SheafOfModules.evaluation S W)) :
    PreservesFiniteLimits F := by
  refine ⟨fun K _ _ => ⟨fun {G} => ⟨fun {c} hc => ?_⟩⟩⟩
  refine ⟨isLimitOfReflects (SheafOfModules.forget S) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  exact isLimitOfPreserves (F ⋙ SheafOfModules.evaluation S W) hc

/-- A functor between categories of sheaves of modules preserves epimorphisms if it preserves
locally surjective maps of underlying abelian sheaves. -/
private theorem preservesEpimorphisms_of_isLocallySurjective
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S)
    (h : ∀ {A B : SheafOfModules.{w} R} (g : A ⟶ B),
      Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map g).hom →
      Presheaf.IsLocallySurjective K ((SheafOfModules.toSheaf S).map (F.map g)).hom) :
    F.PreservesEpimorphisms := by
  refine ⟨fun {A B} g _ => ?_⟩
  have : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map g).hom :=
    locallySurjective_of_epi g
  have := h g this
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf S).map (F.map g)) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).2 this
  exact (SheafOfModules.toSheaf S).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- Restriction of sheaves of modules along a morphism of the site preserves finite limits:
limits of sheaves of modules are computed objectwise, and restriction reindexes objects. -/
theorem overMap_preservesFiniteLimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U V : C} (f : V ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap R f :
      SheafOfModules.{w} (R.over U) ⥤ SheafOfModules.{w} (R.over V)) := by
  exact preservesFiniteLimits_of_evaluation _ fun W => inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.evaluation (R.over U) (Opposite.op ((Over.map f).obj W.unop))))

/-- Restriction of sheaves of modules along a morphism of the site preserves epimorphisms:
an epimorphism is a locally surjective map of underlying abelian sheaves, and local
surjectivity is stable under whiskering along `Over.map`. -/
theorem overMap_preservesEpimorphisms
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U V : C} (f : V ⟶ U)
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify (J.over U) AddCommGrpCat.{w}] :
    (SheafOfModules.overMap R f :
      SheafOfModules.{w} (R.over U) ⥤ SheafOfModules.{w} (R.over V)).PreservesEpimorphisms := by
  exact preservesEpimorphisms_of_isLocallySurjective _ fun g _ =>
    Presheaf.isLocallySurjective_whisker (J.over V) (J.over U)
    (Over.map f) ((SheafOfModules.toSheaf (R.over U)).map g).hom

/-- An additive functor between abelian categories which preserves finite limits and
epimorphisms preserves finite colimits. -/
theorem finiteColimits_of_finiteLimits_epi
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type w} [Category B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [F.PreservesEpimorphisms] : PreservesFiniteColimits F := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).2
  intro S hS
  let : Epi S.g := hS.epi_g
  exact ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp
    inferInstance S hS).1, inferInstance⟩

/-- Restriction of sheaves of modules along a morphism of the site preserves finite
colimits. -/
theorem overMap_preservesFiniteColimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U V : C} (f : V ⟶ U)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify (J.over U) AddCommGrpCat.{w}]
    [HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify (J.over V) AddCommGrpCat.{w}] :
    PreservesFiniteColimits (SheafOfModules.overMap R f :
      SheafOfModules.{w} (R.over U) ⥤ SheafOfModules.{w} (R.over V)) := by
  let F := SheafOfModules.overMap R f
  let : F.Additive := ⟨by intros; ext W; rfl⟩
  let : PreservesFiniteLimits F := overMap_preservesFiniteLimits f
  let : F.PreservesEpimorphisms := overMap_preservesEpimorphisms f
  exact finiteColimits_of_finiteLimits_epi F

/-- Restriction of sheaves of modules from the site to a slice preserves finite limits. -/
theorem overFunctor_preservesFiniteLimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} (V : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor R V :
      SheafOfModules.{w} R ⥤ SheafOfModules.{w} (R.over V)) := by
  exact preservesFiniteLimits_of_evaluation _ fun W => inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.evaluation R (Opposite.op W.unop.left)))

/-- Restriction of sheaves of modules from the site to a slice preserves epimorphisms. -/
theorem overFunctor_preservesEpimorphisms
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} (V : C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}] :
    (SheafOfModules.overFunctor R V :
      SheafOfModules.{w} R ⥤ SheafOfModules.{w} (R.over V)).PreservesEpimorphisms := by
  exact preservesEpimorphisms_of_isLocallySurjective _ fun g _ =>
    Presheaf.isLocallySurjective_whisker (J.over V) J
    (Over.forget V) ((SheafOfModules.toSheaf R).map g).hom

/-- Restriction of sheaves of modules from the site to a slice preserves finite colimits. -/
theorem overFunctor_preservesFiniteColimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} (V : C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify (J.over V) AddCommGrpCat.{w}] :
    PreservesFiniteColimits (SheafOfModules.overFunctor R V :
      SheafOfModules.{w} R ⥤ SheafOfModules.{w} (R.over V)) := by
  let F := SheafOfModules.overFunctor R V
  let : F.Additive := ⟨by intros; ext W; rfl⟩
  let : PreservesFiniteLimits F := overFunctor_preservesFiniteLimits V
  let : F.PreservesEpimorphisms := overFunctor_preservesEpimorphisms V
  exact finiteColimits_of_finiteLimits_epi F

/-- The image of a presentation of a sheaf of modules under a functor preserving finite
colimits and taking the unit sheaf to the unit sheaf. -/
noncomputable def mapFinitePresentation
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} (P : M.Presentation) [P.IsFinite]
    (T : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S)
    [PreservesFiniteColimits T] (η : SheafOfModules.unit S ≅ T.obj (SheafOfModules.unit R)) :
    (T.obj M).Presentation := by
  let eRel : SheafOfModules.free (R := S) P.relations.I ≅
      T.obj (SheafOfModules.free (R := R) P.relations.I) :=
    SheafOfModules.mapFreeIso T P.relations.I η
  let eGen : SheafOfModules.free (R := S) P.generators.I ≅
      T.obj (SheafOfModules.free (R := R) P.generators.I) :=
    SheafOfModules.mapFreeIso T P.generators.I η
  let rel : SheafOfModules.free (R := S) P.relations.I ⟶
      SheafOfModules.free (R := S) P.generators.I :=
    eRel.hom ≫ T.map ((SheafOfModules.freeHomEquiv _).symm P.relations.s) ≫
      T.map (kernel.ι P.generators.π) ≫ eGen.inv
  let gen : SheafOfModules.free (R := S) P.generators.I ⟶ T.obj M :=
    eGen.hom ≫ T.map P.generators.π
  have hrel : rel ≫ gen = 0 := by
    simp [rel, gen, ← Functor.map_comp, kernel.condition]
  have hcol : IsColimit (CokernelCofork.ofπ gen hrel) := by
    letI : PreservesColimit (parallelPair
        ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π) 0) T :=
      inferInstance
    refine IsColimit.equivOfNatIsoOfIso
      (parallelPairIsoMk eRel.symm eGen.symm (by simp [rel]) (by simp)) _ _ ?_
      (isColimitOfPreserves T P.isColimit)
    exact Cocone.ext (Iso.refl _) <| by
      rintro (_ | _) <;> simp [rel, gen, ← Functor.map_comp, kernel.condition]
  exact SheafOfModules.presentationOfIsCokernelFree rel gen hrel hcol

/-- The image of a finite presentation under such a functor is again finite. -/
theorem mapFinitePresentation_isFinite
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} (P : M.Presentation) [P.IsFinite]
    (T : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S)
    [PreservesFiniteColimits T] (η : SheafOfModules.unit S ≅ T.obj (SheafOfModules.unit R)) :
    (mapFinitePresentation P T η).IsFinite :=
  ⟨⟨inferInstanceAs (Finite P.generators.I)⟩,
   ⟨inferInstanceAs (Finite P.relations.I)⟩⟩

/-- The image of a generating family of a sheaf of modules under a functor preserving finite
colimits and epimorphisms and taking the unit sheaf to the unit sheaf. -/
noncomputable def mapFiniteGeneratingSections
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} (σ : M.GeneratingSections) [σ.IsFiniteType]
    (T : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S)
    [PreservesFiniteColimits T] [T.PreservesEpimorphisms]
    (η : SheafOfModules.unit S ≅ T.obj (SheafOfModules.unit R)) :
    (T.obj M).GeneratingSections where
  I := σ.I
  s := (T.obj M).freeHomEquiv
    ((SheafOfModules.mapFreeIso T σ.I η).hom ≫ T.map σ.π)
  epi := by simp only [Equiv.symm_apply_apply]; infer_instance

/-- The image of a finite generating family under such a functor is again finite. -/
theorem mapFiniteGeneratingSections_isFiniteType
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : SheafOfModules.{w} R} (σ : M.GeneratingSections) [σ.IsFiniteType]
    (T : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S)
    [PreservesFiniteColimits T] [T.PreservesEpimorphisms]
    (η : SheafOfModules.unit S ≅ T.obj (SheafOfModules.unit R)) :
    (mapFiniteGeneratingSections σ T η).IsFiniteType :=
  ⟨inferInstanceAs (Finite σ.I)⟩

/-- On a site with a terminal object, a section over that object is a global section. -/
noncomputable def sectionOfModuleAtTerminal
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R}
    (T : D) (hT : IsTerminal T)
    (x : ToType (M.val.obj (Opposite.op T))) : M.sections :=
  M.val.sectionsMk
    (fun Z => M.val.map (hT.from Z.unop).op x)
    (by
      intro X Y f
      have hc : f.unop ≫ hT.from X.unop = hT.from Y.unop :=
        hT.hom_ext _ _
      have hcomp : (hT.from X.unop).op ≫ f = (hT.from Y.unop).op := by
        apply Quiver.Hom.unop_inj
        simpa only [unop_comp, Quiver.Hom.unop_op] using hc
      rw [← M.val.map_comp_apply, hcomp])

/-- A morphism from a finite free sheaf of modules into the target of an epimorphism from a
finite free sheaf lifts through that epimorphism after restriction to the members of a
covering sieve. This is the local lifting step of the Stacks 0H98 argument. -/
theorem exists_local_lift
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    {U : C}
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
    {N : SheafOfModules.{w} (R.over U)} {I K : Type w} [Finite I] [Finite K]
    (e : SheafOfModules.free K ⟶ N) [Epi e]
    (h : SheafOfModules.free I ⟶ N) :
    ∃ S : Sieve (Over.mk (𝟙 U)), S ∈ (J.over U) (Over.mk (𝟙 U)) ∧
      ∀ {V : C} (g : V ⟶ U)
        [PreservesFiniteColimits (SheafOfModules.overMap R g)],
        S.arrows (Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 U)) g (by simp)) →
        ∃ ℓ : SheafOfModules.free (R := R.over V) I ⟶
            SheafOfModules.free (R := R.over V) K,
          ℓ ≫ (SheafOfModules.mapFreeIso (SheafOfModules.overMap R g) K
              (SheafOfModules.overMapUnitIso (R := R) g)).hom ≫
              (SheafOfModules.overMap R g).map e =
            (SheafOfModules.mapFreeIso (SheafOfModules.overMap R g) I
              (SheafOfModules.overMapUnitIso (R := R) g)).hom ≫
              (SheafOfModules.overMap R g).map h := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let m := (PresheafOfModules.toPresheaf (R.over U).obj).map e.val
  have : Presheaf.IsLocallySurjective (J.over U) m := locallySurjective_of_epi e
  let sec (i : I) := (N.freeHomEquiv h) i
  let secVal (i : I) := (sec i).val (Opposite.op (Over.mk (𝟙 U)))
  let Si (i : I) := Presheaf.imageSieve m (U := Over.mk (𝟙 U)) (secVal i)
  let S := Finset.univ.inf Si
  have hS : S ∈ (J.over U) (Over.mk (𝟙 U)) :=
    Finset.inf_induction (p := (· ∈ (J.over U) (Over.mk (𝟙 U)))) ((J.over U).top_mem _)
      (fun _ h₁ _ h₂ => (J.over U).intersection_covering h₁ h₂)
      fun i _ => Presheaf.imageSieve_mem (J.over U) m (secVal i)
  refine ⟨S, hS, ?_⟩
  intro V g hcol hg
  let T := SheafOfModules.overMap R g
  let : PreservesFiniteColimits T := hcol
  let eI : SheafOfModules.free (R := R.over V) I ≅
      T.obj (SheafOfModules.free (R := R.over U) I) :=
    SheafOfModules.mapFreeIso T I (SheafOfModules.overMapUnitIso (R := R) g)
  let eK : SheafOfModules.free (R := R.over V) K ≅
      T.obj (SheafOfModules.free (R := R.over U) K) :=
    SheafOfModules.mapFreeIso T K (SheafOfModules.overMapUnitIso (R := R) g)
  have hgi (i : I) :
      (Si i).arrows (Over.homMk (U := Over.mk g)
        (V := Over.mk (𝟙 U)) g (by simp)) :=
    (Finset.inf_le (Finset.mem_univ i) : S ≤ Si i) _ hg
  let a0 : Over.mk g ⟶ Over.mk (𝟙 U) :=
    Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 U)) g (by simp)
  let c : (Over.map g).obj (Over.mk (𝟙 V)) ⟶ Over.mk g :=
    Over.homMk (U := (Over.map g).obj (Over.mk (𝟙 V)))
      (V := Over.mk g) (𝟙 V) (by simp)
  let b : (Over.map g).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U) := c ≫ a0
  let xG (i : I) := Presheaf.localPreimage m (secVal i)
    (U := Opposite.op (Over.mk (𝟙 U)))
    (V := Over.mk g) a0 (hgi i)
  let x (i : I) :=
    ((PresheafOfModules.toPresheaf (R.over U).obj).obj
      (SheafOfModules.free (R := R.over U) K).val).map c.op (xG i)
  let M' := T.obj (SheafOfModules.free (R := R.over U) K)
  let hx (i : I) : ToType (M'.val.obj (Opposite.op (Over.mk (𝟙 V)))) := by
    show ToType (((PresheafOfModules.toPresheaf (R.over U).obj).obj
      (SheafOfModules.free (R := R.over U) K).val).obj
        (Opposite.op ((Over.map g).obj (Over.mk (𝟙 V)))))
    exact x i
  let xsec (i : I) := sectionOfModuleAtTerminal (M := M')
    (Over.mk (𝟙 V)) (Over.mkIdTerminal (X := V)) (hx i)
  let ℓ : SheafOfModules.free (R := R.over V) I ⟶
      SheafOfModules.free (R := R.over V) K :=
    (SheafOfModules.free (R := R.over V) K).freeHomEquiv.symm fun i =>
      (SheafOfModules.free (R := R.over V) K).unitHomEquiv
        ((T.obj (SheafOfModules.free (R := R.over U) K)).unitHomEquiv.symm (xsec i) ≫ eK.inv)
  have hlocal (i : I) :
      (ConcreteCategory.hom (m.app (Opposite.op (Over.mk g)))) (xG i) =
        (ConcreteCategory.hom
          (((PresheafOfModules.toPresheaf (R.over U).obj).obj N.val).map a0.op))
          (secVal i) :=
    Presheaf.app_localPreimage m (secVal i) a0 (hgi i)
  have hcancel (y : ToType ((T.obj (SheafOfModules.free (R := R.over U) K)).val.obj
      (Opposite.op (Over.mk (𝟙 V))))) :
      eK.hom.val.app (Opposite.op (Over.mk (𝟙 V)))
          (eK.inv.val.app (Opposite.op (Over.mk (𝟙 V))) y) = y := by
    have hh : eK.inv.val.app (Opposite.op (Over.mk (𝟙 V))) ≫
        eK.hom.val.app (Opposite.op (Over.mk (𝟙 V))) = 𝟙 _ :=
      congrArg (fun f => f.val.app (Opposite.op (Over.mk (𝟙 V)))) eK.inv_hom_id
    show ((eK.inv.val.app (Opposite.op (Over.mk (𝟙 V))) ≫
      eK.hom.val.app (Opposite.op (Over.mk (𝟙 V)))) y) = y
    rw [hh]
    rfl
  have hℓ (i : I) : SheafOfModules.ιFree i ≫ ℓ =
      (T.obj (SheafOfModules.free (R := R.over U) K)).unitHomEquiv.symm (xsec i) ≫ eK.inv := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp [ℓ]
  have hat {M N : SheafOfModules.{w} (R.over V)} {a b : M ⟶ N} (h : a = b)
      (x : ToType (M.val.obj (Opposite.op (Over.mk (𝟙 V))))) :
      a.val.app (Opposite.op (Over.mk (𝟙 V))) x = b.val.app (Opposite.op (Over.mk (𝟙 V))) x := by
    rw [h]
  have hℓ_eval (i : I) :
      ℓ.val.app (Opposite.op (Over.mk (𝟙 V)))
        ((SheafOfModules.ιFree i).val.app (Opposite.op (Over.mk (𝟙 V)))
          (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))) =
      (eK.inv.val.app (Opposite.op (Over.mk (𝟙 V))))
        (((T.obj (SheafOfModules.free (R := R.over U) K)).unitHomEquiv.symm (xsec i)).val.app
          (Opposite.op (Over.mk (𝟙 V)))
          (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))) := by
    exact hat (hℓ i) (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))
  have hsecVal (i : I) : (xsec i).val (Opposite.op (Over.mk (𝟙 V))) = hx i := by
    show ((PresheafOfModules.toPresheaf (R.over V).obj).obj M'.val).map
      (Over.mkIdTerminal.from (Over.mk (𝟙 V))).op (hx i) = hx i
    have hid : Over.mkIdTerminal.from (Over.mk (𝟙 V)) = 𝟙 _ :=
      Over.mkIdTerminal.hom_ext _ _
    rw [hid, op_id_unop]
    exact Functor.map_id_apply
      ((PresheafOfModules.toPresheaf (R.over V).obj).obj M'.val)
      (Opposite.op (Over.mk (𝟙 V))) (hx i)
  have hunit (i : I) :
      ((T.obj (SheafOfModules.free (R := R.over U) K)).unitHomEquiv.symm
        (xsec i)).val.app (Opposite.op (Over.mk (𝟙 V)))
      (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V)))) = hx i := by
    rw [← SheafOfModules.unitHomEquiv_apply_coe, Equiv.apply_symm_apply]
    exact hsecVal i
  have hIbase (i : I) :
      eI.hom.val.app (Opposite.op (Over.mk (𝟙 V)))
          ((SheafOfModules.ιFree i).val.app (Opposite.op (Over.mk (𝟙 V)))
            (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))) =
        (T.map (SheafOfModules.ιFree i)).val.app (Opposite.op (Over.mk (𝟙 V)))
          ((SheafOfModules.overMapUnitIso (R := R) g).hom.val.app
            (Opposite.op (Over.mk (𝟙 V)))
            (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))) := by
    exact hat (SheafOfModules.ιFree_mapFreeIso_hom T I
      (SheafOfModules.overMapUnitIso (R := R) g) i)
      (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))
  have hterm (i : I) :
      ((T.obj N).freeHomEquiv
        (ℓ ≫ eK.hom ≫ T.map e) i).val (Opposite.op (Over.mk (𝟙 V))) =
      ((T.obj N).freeHomEquiv
        (eI.hom ≫ T.map h) i).val (Opposite.op (Over.mk (𝟙 V))) := by
    show ((T.obj N).unitHomEquiv
        (SheafOfModules.ιFree i ≫ ℓ ≫ eK.hom ≫ T.map e)).val
        (Opposite.op (Over.mk (𝟙 V))) =
      ((T.obj N).unitHomEquiv
        (SheafOfModules.ιFree i ≫ eI.hom ≫ T.map h)).val
        (Opposite.op (Over.mk (𝟙 V)))
    rw [SheafOfModules.unitHomEquiv_apply_coe,
      SheafOfModules.unitHomEquiv_apply_coe]
    show (T.map e).val.app (Opposite.op (Over.mk (𝟙 V)))
        (eK.hom.val.app (Opposite.op (Over.mk (𝟙 V)))
          (ℓ.val.app (Opposite.op (Over.mk (𝟙 V)))
            ((SheafOfModules.ιFree i).val.app (Opposite.op (Over.mk (𝟙 V)))
              (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))))) =
      (T.map h).val.app (Opposite.op (Over.mk (𝟙 V)))
        (eI.hom.val.app (Opposite.op (Over.mk (𝟙 V)))
          ((SheafOfModules.ιFree i).val.app (Opposite.op (Over.mk (𝟙 V)))
            (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))))
    rw [hℓ_eval, hunit, hIbase]
    show (ConcreteCategory.hom (((SheafOfModules.overMap R g).map e).val.app
        (Opposite.op (Over.mk (𝟙 V)))))
        ((ConcreteCategory.hom (eK.hom.val.app (Opposite.op (Over.mk (𝟙 V)))))
          ((ConcreteCategory.hom (eK.inv.val.app (Opposite.op (Over.mk (𝟙 V))))) (hx i))) =
      (ConcreteCategory.hom (((SheafOfModules.overMap R g).map h).val.app
        (Opposite.op (Over.mk (𝟙 V)))))
        ((ConcreteCategory.hom (((SheafOfModules.overMap R g).map
          (SheafOfModules.ιFree i)).val.app (Opposite.op (Over.mk (𝟙 V)))))
          ((ConcreteCategory.hom ((SheafOfModules.overMapUnitIso (R := R) g).hom.val.app
            (Opposite.op (Over.mk (𝟙 V)))))
            (1 : (R.over V).obj.obj (Opposite.op (Over.mk (𝟙 V))))))
    rw [overMap_map_hom_app (R := R) g e (Over.mk (𝟙 V)),
      overMap_map_hom_app (R := R) g h (Over.mk (𝟙 V)),
      overMap_map_hom_app (R := R) g (SheafOfModules.ιFree i) (Over.mk (𝟙 V)),
      overMapUnitIso_hom_app (R := R) g (Over.mk (𝟙 V))]
    rw [hcancel, show hx i = x i from rfl]
    let W := (Over.map g).obj (Over.mk (𝟙 V))
    let oneUnit : ToType ((SheafOfModules.unit (R.over U)).val.obj (Opposite.op W)) :=
      Eq.mp (show ToType ((R.over U).obj.obj (Opposite.op W)) =
        ToType ((SheafOfModules.unit (R.over U)).val.obj (Opposite.op W)) from rfl)
        (1 : ToType ((R.over U).obj.obj (Opposite.op W)))
    have hsecAtG : (sec i).val
          (Opposite.op W) =
        (h.val.app (Opposite.op W))
          ((SheafOfModules.ιFree i).val.app (Opposite.op W) oneUnit) := by
      show (N.unitHomEquiv (SheafOfModules.ιFree i ≫ h)).val
        (Opposite.op W) = _
      rw [SheafOfModules.unitHomEquiv_apply_coe]
      show (ConcreteCategory.hom
        ((SheafOfModules.ιFree i).val.app (Opposite.op W) ≫
          h.val.app (Opposite.op W)))
        oneUnit = _
      rw [ConcreteCategory.comp_apply]
    have hrestrict : (sec i).val
          (Opposite.op W) =
        (N.val.presheaf.map b.op)
          (secVal i) :=
      (N.val.sections_property (sec i) b.op).symm
    have hmap : (ConcreteCategory.hom (e.val.app (Opposite.op W))) (x i) =
        (N.val.presheaf.map b.op) (secVal i) := by
      calc
        _ = (N.val.presheaf.map c.op)
            ((ConcreteCategory.hom (m.app (Opposite.op (Over.mk g)))) (xG i)) := by
          dsimp [x]
          exact NatTrans.naturality_apply m c.op (xG i)
        _ = (N.val.presheaf.map c.op)
            ((N.val.presheaf.map a0.op) (secVal i)) :=
          congrArg (fun z => (N.val.presheaf.map c.op) z) (hlocal i)
        _ = (N.val.presheaf.map b.op) (secVal i) := by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
            show a0.op ≫ c.op = b.op by simp [b]]
    exact hmap.trans (hrestrict.symm.trans hsecAtG)
  refine ⟨ℓ, ?_⟩
  apply (T.obj N).freeHomEquiv.injective
  funext i
  apply PresheafOfModules.sections_ext
  intro Z
  let a := (Over.mkIdTerminal (X := V)).from Z.unop
  exact (((T.obj N).val.sections_property _ a.op).symm.trans
    (congrArg (fun z => (T.obj N).val.map a.op z) (hterm i))).trans
    ((T.obj N).val.sections_property _ a.op)

/-- The global form of Stacks 0H98: from a finite presentation of `F`, a finite generating
family of `G` and a lift of `σ.π ≫ φ` through the surjection `P.generators.π`, the cokernel
of `φ` has a finite presentation. -/
theorem finitePresentation_cokernel_of_presentation_of_lift
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {F G : SheafOfModules.{w} R} (φ : G ⟶ F)
    (P : F.Presentation) [P.IsFinite]
    (σ : G.GeneratingSections) [σ.IsFiniteType]
    (lift : SheafOfModules.free σ.I ⟶ SheafOfModules.free P.generators.I)
    (hlift : lift ≫ P.generators.π = σ.π ≫ φ) :
    ∃ T : (cokernel φ).Presentation, T.IsFinite := by
  let : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let rel : SheafOfModules.free P.relations.I ⟶ SheafOfModules.free P.generators.I :=
    (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  let e := SheafOfModules.freeSumIso (R := R) P.relations.I σ.I
  let f : SheafOfModules.free (P.relations.I ⊕ σ.I) ⟶
      SheafOfModules.free P.generators.I :=
    e.inv ≫ coprod.desc rel lift
  let g : SheafOfModules.free P.generators.I ⟶ cokernel φ :=
    P.generators.π ≫ cokernel.π φ
  have hP : IsColimit (CokernelCofork.ofπ (f := rel) P.generators.π
      (by simp [rel, Category.assoc])) := by
    simpa [rel, SheafOfModules.GeneratingSections.π, Category.assoc] using P.isColimit
  have hrel : rel ≫ g = 0 := by simp [g, rel, Category.assoc]
  have hlift' : lift ≫ g = 0 := by simp [g, reassoc_of% hlift]
  have hdesc : coprod.desc rel lift ≫ g = 0 := by
    rw [coprod.desc_comp, hrel, hlift']
    apply coprod.hom_ext <;> simp [coprod.inl_desc, coprod.inr_desc]
  have hf : f ≫ g = 0 := by
    apply (cancel_epi e.hom).1
    simpa [f, Category.assoc] using hdesc
  have hc : IsColimit (CokernelCofork.ofπ g hf) :=
    CokernelCofork.IsColimit.ofπ' g hf (by
      intro Z k hk
      have hk' : coprod.desc rel lift ≫ k = 0 := by
        apply (cancel_epi e.inv).1
        simpa [f, Category.assoc] using hk
      have hrel : rel ≫ k = 0 := by
        rw [← coprod.inl_desc_assoc]
        simpa using congrArg (fun q => coprod.inl ≫ q) hk'
      have hliftk : lift ≫ k = 0 := by
        rw [← coprod.inr_desc_assoc]
        simpa using congrArg (fun q => coprod.inr ≫ q) hk'
      let z : F ⟶ Z := hP.desc (CokernelCofork.ofπ k hrel)
      have hz : P.generators.π ≫ z = k := hP.fac _ WalkingParallelPair.one
      have hφ : φ ≫ z = 0 := by
        apply σ.epi.left_cancellation
        calc
          σ.π ≫ φ ≫ z = (σ.π ≫ φ) ≫ z := by simp [Category.assoc]
          _ = (lift ≫ P.generators.π) ≫ z := by rw [← hlift]
          _ = lift ≫ k := by simp [Category.assoc, hz]
          _ = 0 := hliftk
      refine ⟨(cokernelIsCokernel φ).desc (CokernelCofork.ofπ z hφ), ?_⟩
      simp [g, Category.assoc, hz])
  exact ⟨SheafOfModules.presentationOfIsCokernelFree f g hf hc,
    ⟨⟨inferInstanceAs (Finite P.generators.I)⟩, ⟨inferInstanceAs (Finite (P.relations.I ⊕ σ.I))⟩⟩⟩

/-- A finite presentation of a restriction to a slice restricts further along any morphism of
the site. -/
theorem exists_finitePresentation_overMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} R) {U V : C} (f : V ⟶ U)
    (P : (F.over U).Presentation) [P.IsFinite] :
    ∃ Q : (F.over V).Presentation, Q.IsFinite := by
  let T := SheafOfModules.overMap R f
  let : PreservesFiniteColimits T := overMap_preservesFiniteColimits f
  let Q := mapFinitePresentation P T (SheafOfModules.overMapUnitIso f)
  let : Q.IsFinite := mapFinitePresentation_isFinite P T _
  exact ⟨Q.ofIsIso ((SheafOfModules.overFunctorMap R f).app F).hom, inferInstance⟩

/-- A finite generating family of a restriction to a slice restricts further along any
morphism of the site. -/
theorem exists_finiteGeneratingSections_overMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (G : SheafOfModules.{w} R) {U V : C} (f : V ⟶ U)
    (σ : (G.over U).GeneratingSections) [σ.IsFiniteType] :
    ∃ τ : (G.over V).GeneratingSections, τ.IsFiniteType := by
  let T := SheafOfModules.overMap R f
  let : PreservesFiniteColimits T := overMap_preservesFiniteColimits f
  let : T.PreservesEpimorphisms := overMap_preservesEpimorphisms f
  let τ := mapFiniteGeneratingSections σ T (SheafOfModules.overMapUnitIso f)
  let : τ.IsFiniteType := mapFiniteGeneratingSections_isFiniteType σ T _
  exact ⟨τ.ofEpi ((SheafOfModules.overFunctorMap R f).app G).hom, inferInstance⟩

/-- Over an object where `F` has a finite presentation and `G` finitely many generators, the
cokernel of `φ` has a finite presentation after restriction to the members of a covering
sieve. -/
theorem exists_cover_finitePresentation_cokernel
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {F G : SheafOfModules.{w} R} (φ : G ⟶ F) (U : C)
    (P : (F.over U).Presentation) [P.IsFinite]
    (σ : (G.over U).GeneratingSections) [σ.IsFiniteType] :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
      ∃ Q : ((cokernel φ).over V).Presentation, Q.IsFinite := by
  obtain ⟨S, hS, hLift⟩ := exists_local_lift
    P.generators.π (σ.π ≫ φ.over U)
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 U)) S, hS, ?_⟩
  intro V f hf
  let T := SheafOfModules.overMap R f
  let : PreservesFiniteColimits T := overMap_preservesFiniteColimits f
  let : T.PreservesEpimorphisms := overMap_preservesEpimorphisms f
  have hf' : S (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 U)) f (by simp)) := by
    simpa using (Sieve.overEquiv_symm_iff ((Sieve.overEquiv (Over.mk (𝟙 U))) S)
      (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 U)) f (by simp))).2 hf
  obtain ⟨ℓ, hℓ⟩ := hLift f hf'
  let Q := mapFinitePresentation P T (SheafOfModules.overMapUnitIso f)
  let τ := mapFiniteGeneratingSections σ T (SheafOfModules.overMapUnitIso f)
  let : Q.IsFinite := mapFinitePresentation_isFinite P T _
  let : τ.IsFiniteType := mapFiniteGeneratingSections_isFiniteType σ T _
  have hℓ' : ℓ ≫ Q.generators.π = τ.π ≫ T.map (φ.over U) := by
    dsimp only [Q, τ, mapFinitePresentation, mapFiniteGeneratingSections,
      SheafOfModules.presentationOfIsCokernelFree,
      SheafOfModules.generatorsOfIsCokernelFree, SheafOfModules.GeneratingSections.π]
    simpa only [Equiv.symm_apply_apply, Functor.map_comp, Category.assoc] using hℓ
  obtain ⟨Q', hQ'⟩ := finitePresentation_cokernel_of_presentation_of_lift
    (T.map (φ.over U)) Q τ ℓ hℓ'
  let : Q'.IsFinite := hQ'
  let e : cokernel (T.map (φ.over U)) ≅ cokernel (φ.over V) :=
    cokernel.mapIso _ _ ((SheafOfModules.overFunctorMap R f).app G)
      ((SheafOfModules.overFunctorMap R f).app F)
      ((SheafOfModules.overFunctorMap R f).hom.naturality φ)
  let : PreservesFiniteColimits (SheafOfModules.overFunctor R V) :=
    overFunctor_preservesFiniteColimits V
  let e' : cokernel (φ.over V) ≅ (cokernel φ).over V :=
    asIso (cokernelComparison φ (SheafOfModules.overFunctor R V))
  exact ⟨Q'.ofIsIso (e ≪≫ e').hom, inferInstance⟩

-- The abelian structure in the statement is Mathlib's `SheafOfModules.instAbelian`.
attribute [-instance] AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules in
/-- **Stacks Project, Tag 0H98.** The cokernel of a morphism from a finite-type sheaf of
modules to a finitely presented sheaf of modules on a ringed site is finitely presented. -/
@[stacks 0H98, instance]
theorem isFinitePresentation_cokernel
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : G ⟶ F)
    [F.IsFinitePresentation] [G.IsFiniteType] :
    (cokernel φ).IsFinitePresentation := by
  classical
  let : HasSheafify X.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : ∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w} :=
    fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  obtain ⟨qF, hqF⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  let : qF.IsFinitePresentation := hqF
  obtain ⟨qG, hqG⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  let : qG.IsFiniteType := hqG
  let B : Set X.C := fun U => ∃ P : ((cokernel φ).over U).Presentation, P.IsFinite
  let Y : B → X.C := Subtype.val
  have hlocal (U : X.C) (P : (F.over U).Presentation) [P.IsFinite] :
      Sieve.ofObjects Y U ∈ X.J U := by
    apply X.J.transitive (qG.coversTop U)
    intro V f hf
    obtain ⟨j, ⟨g⟩⟩ := hf
    obtain ⟨P', hP'⟩ := exists_finitePresentation_overMap F f P
    let : P'.IsFinite := hP'
    let := hqG.isFiniteType j
    obtain ⟨σ, hσ⟩ := exists_finiteGeneratingSections_overMap G g (qG.generators j)
    let : σ.IsFiniteType := hσ
    obtain ⟨S, hS, hfin⟩ := exists_cover_finitePresentation_cokernel φ V P' σ
    exact X.J.superset_covering (fun W a ha => ⟨⟨W, hfin a ha⟩, ⟨𝟙 W⟩⟩) hS
  have hY : X.J.CoversTop Y := by
    intro U
    apply X.J.transitive (qF.coversTop U)
    intro V f hf
    obtain ⟨i, ⟨g⟩⟩ := hf
    obtain ⟨P, hP⟩ := exists_finitePresentation_overMap F g (qF.presentation i)
    let : P.IsFinite := hP
    exact hlocal V P
  exact ⟨{ I := B
           X := Y
           coversTop := hY
           presentation i := i.property.choose },
    ⟨fun i => i.property.choose_spec⟩⟩

end Stacks.SheafOfModules.LocalCokernel

end
