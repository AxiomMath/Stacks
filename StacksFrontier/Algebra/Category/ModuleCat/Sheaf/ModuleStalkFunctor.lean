module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a sheaf of modules at a point of a site, as a functor

Let `(C, J)` be a site, `Φ` a point of it with fibre functor `Φ.fiber : C ⥤ Type w`, and `R` a
presheaf of rings on `C`. Mathlib's `GrothendieckTopology.Point.presheafFiber` computes the
stalk at `Φ` of a presheaf with values in any suitable category as the filtered colimit over
`Φ.fiber.Elementsᵒᵖ`, the opposite of the category of neighbourhoods of `Φ`. This file assembles
the corresponding construction for presheaves and sheaves of *modules*: the stalk `M_Φ` of a
presheaf of `R`-modules is a module over the stalk `R_Φ` of `R`, and the assignment `M ↦ M_Φ` is
a functor which is exact.

The stalk functor is the composite of the pushforward along the projection
`Φ.fiber.Elements ⥤ C` with `PresheafOfModules.colimitFunctor` for the colimit cocone
`Φ.presheafFiberCocone R` of the ring presheaf. On underlying abelian groups it is Mathlib's
`presheafFiber` by definition; it is exact, it inverts locally bijective morphisms (so the stalk
of a presheaf agrees with the stalk of its sheafification), and it restricts to a left exact
functor on sheaves of modules.

## Main definitions

* `Stacks.presheafModuleFiber Φ R` is the stalk functor
  `PresheafOfModules R ⥤ ModuleCat (Φ.presheafFiber.obj R)` at a point `Φ` of a site.
* `Stacks.toPresheafModuleFiber` is the canonical additive map `M(U) →+ M_Φ` attached to a
  neighbourhood `(U, x)` of `Φ` — the germ map.
* `Stacks.sheafModuleFiber Φ R` is the stalk functor on sheaves of modules over a sheaf of
  rings `R`.
* `Stacks.commRingPresheafFiberIso` and `Stacks.commRingSheafFiberIso` identify the
  `RingCat`-valued stalk of the ring presheaf underlying a presheaf, respectively sheaf, of
  commutative rings with the underlying ring of its `CommRingCat`-valued stalk.
* `Stacks.sheafModuleFiberOfCommRing Φ O` is the stalk functor on sheaves of modules over the
  ring sheaf of a sheaf of commutative rings `O`, valued in modules over the `CommRingCat`-valued
  stalk of `O`; `Stacks.moduleStalk` is its value on an object, and
  `Stacks.IsFlatModuleStalk` says that value is a flat module over the stalk of `O`.

## Main results

* `Stacks.presheafModuleFiberCompForget₂` and `Stacks.sheafModuleFiberCompForget₂` : the stalk of
  a presheaf (respectively sheaf) of modules has, as its underlying abelian group, the stalk of
  the underlying presheaf (respectively sheaf) of abelian groups. Both hold by definition
  (`Iso.refl`).
* `Stacks.toPresheafModuleFiber_smul`, `Stacks.toPresheafModuleFiber_w`,
  `Stacks.toPresheafModuleFiber_naturality`,
  `Stacks.toPresheafModuleFiber_jointly_surjective`,
  `Stacks.toPresheafModuleFiber_eq_iff` : the germ API. The germ map is additive, it is
  compatible with scalars and with restriction, it is natural in the presheaf of modules, every
  element of the stalk is a germ, and two germs over the same neighbourhood agree iff they agree
  after restriction to a smaller neighbourhood.
* `Stacks.instPreservesFiniteLimitsPresheafModuleFiber` and
  `Stacks.instPreservesFiniteColimitsPresheafModuleFiber` : the stalk functor on presheaves of
  modules is exact.
* `Stacks.isIso_presheafModuleFiber_map` : the stalk functor inverts a morphism of presheaves of
  modules which is locally injective and locally surjective. In particular
  `Stacks.isIso_presheafModuleFiber_map_sheafificationAdjunction_unit` : the stalk of a presheaf
  of modules agrees with the stalk of its sheafification.
* `Stacks.instPreservesFiniteLimitsSheafModuleFiber` and
  `Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing` : the stalk functor on sheaves of
  modules preserves finite limits.
* `Stacks.isIso_of_isIso_sheafModuleFiber`, `Stacks.mono_of_mono_sheafModuleFiber` and
  `Stacks.epi_of_epi_sheafModuleFiber` : the stalks at a conservative family of points detect
  isomorphisms, monomorphisms and epimorphisms of sheaves of modules.

## Implementation notes

The module universe is forced to equal the ring universe and the fibre universe `w`, because
`PresheafOfModules.colimitFunctor` is stated for a presheaf of rings `R : Cᵒᵖ ⥤ RingCat.{w}` on a
category which is `LocallySmall.{w}`, `IsCofiltered` and `InitiallySmall.{w}`, and produces
modules in `ModuleCat.{w}`. The site's object and morphism universes `u` and `v` stay free
throughout, except where a cited Mathlib result fixes them.

Right exactness of the stalk functor on *sheaves* of modules is not proved here:
`SheafOfModules.forget` is a right adjoint and does not preserve colimits, so such an argument
has to go through sheafification, via
`isIso_presheafModuleFiber_map_sheafificationAdjunction_unit`.

## References

* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 00YL](https://stacks.math.columbia.edu/tag/00YL)
* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}

/-! ### The stalk functor on presheaves of modules -/

section Presheaf

variable (Φ : J.Point.{w}) (R : Cᵒᵖ ⥤ RingCat.{w})

/-- The stalk at a point `Φ` of a site of a presheaf of `R`-modules, as a functor to modules
over the stalk `Φ.presheafFiber.obj R` of the presheaf of rings `R`. It is the composite of the
pushforward along the projection `Φ.fiber.Elements ⥤ C` from the category of neighbourhoods of
`Φ` with the colimit-module functor for the colimit cocone computing the stalk of `R`. -/
noncomputable def presheafModuleFiber :
    PresheafOfModules.{w} R ⥤ ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R) :=
  PresheafOfModules.pushforward (F := CategoryOfElements.π Φ.fiber) (𝟙 _) ⋙
    PresheafOfModules.colimitFunctor (Φ.isColimitPresheafFiberCocone R)

/-- The underlying abelian group of the stalk of a presheaf of modules is the stalk of the
underlying presheaf of abelian groups. This is an equality of functors, not merely an
isomorphism. -/
noncomputable def presheafModuleFiberCompForget₂ :
    presheafModuleFiber Φ R ⋙
        forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R)) AddCommGrpCat.{w} ≅
      PresheafOfModules.toPresheaf R ⋙ Φ.presheafFiber (A := AddCommGrpCat.{w}) :=
  Iso.refl _

variable {R}

/-- The germ map `M(U) →+ M_Φ` attached to a neighbourhood `(U, x)` of the point `Φ`. On
underlying abelian groups it is Mathlib's `Point.toPresheafFiber`. -/
noncomputable def toPresheafModuleFiber (M : PresheafOfModules.{w} R) (U : C)
    (x : Φ.fiber.obj U) : M.obj (op U) →+ (presheafModuleFiber Φ R).obj M :=
  (Φ.toPresheafFiber U x M.presheaf).hom

/-- On elements, the germ map `Stacks.toPresheafModuleFiber` is Mathlib's
`Point.toPresheafFiber`. -/
@[simp]
lemma toPresheafModuleFiber_apply (M : PresheafOfModules.{w} R) (U : C) (x : Φ.fiber.obj U)
    (m : M.obj (op U)) :
    toPresheafModuleFiber Φ M U x m = Φ.toPresheafFiber U x M.presheaf m :=
  rfl

/-- The germ map is compatible with the action of scalars: the germ of `r • m` is the germ of
`r` acting on the germ of `m`. -/
@[simp]
lemma toPresheafModuleFiber_smul (M : PresheafOfModules.{w} R) (U : C) (x : Φ.fiber.obj U)
    (r : R.obj (op U)) (m : M.obj (op U)) :
    toPresheafModuleFiber Φ M U x (r • m) =
      (Φ.toPresheafFiber U x R r : (Φ.presheafFiber (A := RingCat.{w})).obj R) •
        toPresheafModuleFiber Φ M U x m :=
  (PresheafOfModules.ModuleColimit.smul_eq (cR := Φ.presheafFiberCocone R)
    (hcR := Φ.isColimitPresheafFiberCocone R)
    (hcM := colimit.isColimit
      ((PresheafOfModules.pushforward (F := CategoryOfElements.π Φ.fiber)
        (𝟙 _)).obj M).presheaf) (U := op (Φ.fiber.elementsMk U x)) r m).symm

/-- The germ maps are compatible with restriction along a morphism of neighbourhoods. -/
lemma toPresheafModuleFiber_w (M : PresheafOfModules.{w} R) {U V : C} (f : U ⟶ V)
    (x : Φ.fiber.obj U) (m : M.obj (op V)) :
    toPresheafModuleFiber Φ M V (Φ.fiber.map f x) m =
      toPresheafModuleFiber Φ M U x (M.map f.op m) :=
  (Φ.toPresheafFiber_w_apply f x M.presheaf m).symm

/-- The germ maps are natural in the presheaf of modules. -/
lemma toPresheafModuleFiber_naturality {M M' : PresheafOfModules.{w} R} (g : M ⟶ M') (U : C)
    (x : Φ.fiber.obj U) (m : M.obj (op U)) :
    (presheafModuleFiber Φ R).map g (toPresheafModuleFiber Φ M U x m) =
      toPresheafModuleFiber Φ M' U x (g.app (op U) m) :=
  Φ.toPresheafFiber_naturality_apply ((PresheafOfModules.toPresheaf R).map g) U x m

/-- Every element of the stalk of a presheaf of modules is the germ of a section over some
neighbourhood of the point. -/
lemma toPresheafModuleFiber_jointly_surjective (M : PresheafOfModules.{w} R)
    (m : (presheafModuleFiber Φ R).obj M) :
    ∃ (U : C) (x : Φ.fiber.obj U) (s : M.obj (op U)), toPresheafModuleFiber Φ M U x s = m := by
  obtain ⟨U, x, s, h⟩ := Φ.toPresheafFiber_jointly_surjective (P := M.presheaf) m
  exact ⟨U, x, s, h⟩

/-- Two sections over the same neighbourhood have the same germ exactly when they agree after
restriction to a smaller neighbourhood. -/
lemma toPresheafModuleFiber_eq_iff (M : PresheafOfModules.{w} R) (U : C) (x : Φ.fiber.obj U)
    (s t : M.obj (op U)) :
    toPresheafModuleFiber Φ M U x s = toPresheafModuleFiber Φ M U x t ↔
      ∃ (V : C) (f : V ⟶ U) (y : Φ.fiber.obj V), Φ.fiber.map f y = x ∧
        M.map f.op s = M.map f.op t :=
  Φ.toPresheafFiber_eq_iff' (P := M.presheaf) U x s t

/-! ### Exactness of the stalk functor on presheaves of modules -/

/-- The stalk functor on presheaves of modules preserves finite limits. -/
noncomputable instance instPreservesFiniteLimitsPresheafModuleFiber (R : Cᵒᵖ ⥤ RingCat.{w}) :
    PreservesFiniteLimits (presheafModuleFiber Φ R) :=
  haveI : PreservesFiniteLimits (presheafModuleFiber Φ R ⋙
      forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R)) AddCommGrpCat.{w}) :=
    preservesFiniteLimits_of_natIso (presheafModuleFiberCompForget₂ Φ R).symm
  preservesFiniteLimits_of_reflects_of_preserves (presheafModuleFiber Φ R)
    (forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R)) AddCommGrpCat.{w})

/-- The stalk functor on presheaves of modules preserves finite colimits. -/
noncomputable instance instPreservesFiniteColimitsPresheafModuleFiber (R : Cᵒᵖ ⥤ RingCat.{w}) :
    PreservesFiniteColimits (presheafModuleFiber Φ R) :=
  haveI : PreservesFiniteColimits (presheafModuleFiber Φ R ⋙
      forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R)) AddCommGrpCat.{w}) :=
    preservesFiniteColimits_of_natIso (presheafModuleFiberCompForget₂ Φ R).symm
  preservesFiniteColimits_of_reflects_of_preserves (presheafModuleFiber Φ R)
    (forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R)) AddCommGrpCat.{w})

/-- The stalk functor inverts a morphism of presheaves of modules whose underlying morphism of
presheaves of abelian groups is locally injective and locally surjective. -/
lemma isIso_presheafModuleFiber_map {R : Cᵒᵖ ⥤ RingCat.{w}} {M M' : PresheafOfModules.{w} R}
    (g : M ⟶ M')
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map g)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map g)] :
    IsIso ((presheafModuleFiber Φ R).map g) := by
  rw [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R)) AddCommGrpCat.{w}),
    ← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat.{w}), isIso_iff_bijective]
  exact Φ.toPresheafFiber_map_bijective ((PresheafOfModules.toPresheaf R).map g)

end Presheaf

/-! ### The stalk functor on sheaves of modules -/

section Sheaf

variable (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w})

/-- The stalk at a point `Φ` of a site of a sheaf of `R`-modules, as a functor to modules over
the stalk of the sheaf of rings `R`. -/
noncomputable def sheafModuleFiber :
    SheafOfModules.{w} R ⥤ ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj) :=
  SheafOfModules.forget R ⋙ presheafModuleFiber Φ R.obj

/-- On underlying abelian groups, the stalk of a sheaf of modules is the stalk of the underlying
sheaf of abelian groups. -/
noncomputable def sheafModuleFiberCompForget₂ :
    sheafModuleFiber Φ R ⋙
        forget₂ (ModuleCat.{w} ((Φ.presheafFiber (A := RingCat.{w})).obj R.obj))
          AddCommGrpCat.{w} ≅
      SheafOfModules.toSheaf R ⋙ Φ.sheafFiber (A := AddCommGrpCat.{w}) :=
  Iso.refl _

/-- The stalk functor on sheaves of modules preserves finite limits. -/
noncomputable instance instPreservesFiniteLimitsSheafModuleFiber
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesFiniteLimits (sheafModuleFiber Φ R) :=
  comp_preservesFiniteLimits _ _

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The stalk of a presheaf of modules agrees with the stalk of its sheafification: the
sheafification functor followed by the stalk functor on sheaves of modules is the stalk functor
on presheaves of modules. -/
lemma isIso_presheafModuleFiber_map_sheafificationAdjunction_unit
    (M : PresheafOfModules.{w} R.obj) :
    IsIso ((presheafModuleFiber Φ R.obj).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app M)) := by
  have h := J.W_toSheafify M.presheaf
  rw [← PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app (R := R)
    (𝟙 R.obj)] at h
  have := h.isLocallyInjective
  have := h.isLocallySurjective
  exact isIso_presheafModuleFiber_map Φ _

end Sheaf

/-! ### Stalks at a conservative family of points detect isomorphisms, monomorphisms and
epimorphisms of sheaves of modules -/

section Conservative

variable {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} (R : Sheaf J RingCat.{w})
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- A morphism of sheaves of modules which is an isomorphism on the stalks at a conservative
family of points is an isomorphism. -/
lemma isIso_of_isIso_sheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    {M N : SheafOfModules.{w} R} (f : M ⟶ N)
    (hf : ∀ Φ : P.FullSubcategory, IsIso ((sheafModuleFiber Φ.obj R).map f)) : IsIso f := by
  rw [← isIso_iff_of_reflects_iso f (SheafOfModules.toSheaf R),
    (hP.jointlyReflectIsomorphisms AddCommGrpCat.{w}).isIso_iff]
  intro Φ
  have := hf Φ
  exact (NatIso.isIso_map_iff (sheafModuleFiberCompForget₂ Φ.obj R) f).1
    (Functor.map_isIso (forget₂ (ModuleCat.{w} ((Φ.obj.presheafFiber (A := RingCat.{w})).obj R.obj))
      AddCommGrpCat.{w}) ((sheafModuleFiber Φ.obj R).map f))

/-- A morphism of sheaves of modules which is a monomorphism on the stalks at a conservative
family of points is a monomorphism. -/
lemma mono_of_mono_sheafModuleFiber (hP : P.IsConservativeFamilyOfPoints)
    {M N : SheafOfModules.{w} R} (f : M ⟶ N)
    (hf : ∀ Φ : P.FullSubcategory, Mono ((sheafModuleFiber Φ.obj R).map f)) : Mono f := by
  refine (SheafOfModules.toSheaf R).mono_of_mono_map ?_
  refine ((hP.jointlyReflectMonomorphisms AddCommGrpCat.{w}).mono_iff _).2 (fun Φ ↦ ?_)
  have := hf Φ
  exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (sheafModuleFiberCompForget₂ Φ.obj R) (Arrow.mk f))).1
    (Functor.map_mono (forget₂ (ModuleCat.{w} ((Φ.obj.presheafFiber (A := RingCat.{w})).obj R.obj))
      AddCommGrpCat.{w}) ((sheafModuleFiber Φ.obj R).map f))

/-- A morphism of sheaves of modules which is an epimorphism on the stalks at a conservative
family of points is an epimorphism. -/
lemma epi_of_epi_sheafModuleFiber [HasWeakSheafify J AddCommGrpCat.{w}]
    (hP : P.IsConservativeFamilyOfPoints)
    {M N : SheafOfModules.{w} R} (f : M ⟶ N)
    (hf : ∀ Φ : P.FullSubcategory, Epi ((sheafModuleFiber Φ.obj R).map f)) : Epi f := by
  refine (SheafOfModules.toSheaf R).epi_of_epi_map ?_
  refine ((hP.jointlyReflectEpimorphisms AddCommGrpCat.{w}).epi_iff _).2 (fun Φ ↦ ?_)
  have := hf Φ
  exact ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (sheafModuleFiberCompForget₂ Φ.obj R) (Arrow.mk f))).1
    (Functor.map_epi (forget₂ (ModuleCat.{w} ((Φ.obj.presheafFiber (A := RingCat.{w})).obj R.obj))
      AddCommGrpCat.{w}) ((sheafModuleFiber Φ.obj R).map f))

end Conservative

/-! ### Modules over the stalk of a sheaf of commutative rings -/

section CommRing

variable (Φ : J.Point.{w})

/-- The `RingCat`-valued stalk of the ring presheaf underlying a presheaf of commutative rings
is the underlying ring of the `CommRingCat`-valued stalk. -/
noncomputable def commRingPresheafFiberIso (O : Cᵒᵖ ⥤ CommRingCat.{w}) :
    (Φ.presheafFiber (A := RingCat.{w})).obj (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ≅
      (forget₂ CommRingCat.{w} RingCat.{w}).obj
        ((Φ.presheafFiber (A := CommRingCat.{w})).obj O) :=
  (Φ.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).app O

/-- Restriction of scalars along a morphism of rings preserves finite limits: it does not change
the underlying abelian group. -/
lemma preservesFiniteLimits_restrictScalars {R S : RingCat.{w}} (f : R ⟶ S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{w} f.hom) :=
  ⟨fun _ _ _ ↦ ⟨fun {K} ↦ ModuleCat.preservesLimit_restrictScalars _ K⟩⟩

/-- Restriction of scalars along a morphism of rings preserves finite colimits: it does not
change the underlying abelian group. -/
lemma preservesFiniteColimits_restrictScalars {R S : RingCat.{w}} (f : R ⟶ S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{w} f.hom) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

variable (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The same comparison as `Stacks.commRingPresheafFiberIso`, stated for the ring sheaf
`Stacks.commRingSheafToRingSheaf O` of a sheaf of commutative rings `O`. -/
noncomputable def commRingSheafFiberIso :
    (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O).obj ≅
      (forget₂ CommRingCat.{w} RingCat.{w}).obj
        ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  commRingPresheafFiberIso Φ O.obj

/-- The stalk at a point `Φ` of a site of a sheaf of modules over the ring sheaf of a sheaf of
commutative rings `O`, as a functor to modules over the `CommRingCat`-valued stalk of `O`. -/
noncomputable def sheafModuleFiberOfCommRing :
    SheafOfModules.{w} (commRingSheafToRingSheaf O) ⥤
      ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  sheafModuleFiber Φ (commRingSheafToRingSheaf O) ⋙
    ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom

/-- The stalk of a sheaf of modules at a point, as a module over the stalk of the sheaf of
commutative rings. This is the object part of `Stacks.sheafModuleFiberOfCommRing`. -/
noncomputable abbrev moduleStalk (F : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  (sheafModuleFiberOfCommRing Φ O).obj F

/-- The stalk of `F` at `Φ` is a flat module over the stalk of `O` at `Φ`. -/
noncomputable abbrev IsFlatModuleStalk
    (F : SheafOfModules.{w} (commRingSheafToRingSheaf O)) : Prop :=
  letI : Module ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) (moduleStalk Φ O F) :=
    (moduleStalk Φ O F).isModule
  Module.Flat ((Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) (moduleStalk Φ O F)

/-- The stalk functor `Stacks.sheafModuleFiberOfCommRing` preserves finite limits. -/
lemma preservesFiniteLimits_sheafModuleFiberOfCommRing
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesFiniteLimits (sheafModuleFiberOfCommRing Φ O) := by
  have h : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom) :=
    preservesFiniteLimits_restrictScalars _
  exact comp_preservesFiniteLimits (sheafModuleFiber Φ (commRingSheafToRingSheaf O))
    (ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom)

end CommRing

end Stacks
