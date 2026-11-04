module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules

/-!
# The equivalence of the two readings of a sheaf of `Λ`-modules, against the constant sheaves
and against restriction to a slice

Let `(C, J)` be a site, `Λ` a ring and `R` a sheaf of rings equipped with a locally bijective
morphism `α` out of the constant presheaf of rings on `Λ`. The equivalence

`Stacks.ConstantRingModules.toModuleSheaf Λ J α : SheafOfModules R ≌ Sheaf J (ModuleCat Λ)`

of `StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules` identifies the
two readings of "a sheaf of `Λ`-modules on `C`". This file records the two compatibilities that
make the identification usable, namely compatibility with the constant-sheaf functors and
compatibility with restriction to a slice site `C/U`, and the one statement that combines them.

Both are needed in the same shape by Stacks 094H (whose bounded case is a local statement about
locally constant sheaves, so it passes to a slice and compares constant sheaves there) and by
Stacks 09BE (whose input Stacks 09BD is available only for sheaves of modules over the constant
sheaf of rings, and only on a slice site). They are proved here once.

## Main definitions

* `Stacks.ConstantRingModules.constSheafOfModules`: the constant sheaves of modules over `R`,
  i.e. the constant presheaf of modules over the constant presheaf of rings, sheafified along
  `α`.
* `Stacks.ConstantRingModules.constantSheafModuleSheafIso`: **the constant-sheaf
  compatibility**, `constantSheaf J (ModuleCat Λ) ≅ constSheafOfModules ⋙ toModuleSheaf`.
* `Stacks.ConstantRingModules.toModuleSheafOverIso`: **the slicing compatibility**, the square
  relating `toModuleSheaf` on `C` and on `C/U` to restriction of sheaves of modules and
  restriction of `ModuleCat Λ`-valued sheaves.
* `Stacks.ConstantRingModules.toModuleSheafOverMapIso`: the same square along a morphism of the
  site rather than along `Over.forget U`.
* `Stacks.ConstantRingModules.constantSheafOverFunctorIso`: the two combined, identifying the
  constant sheaves on the slice site `C/U` with the restrictions of the constant sheaves of
  modules read through the equivalence on `C/U`.
* `Stacks.ConstantRingModules.constantModuleSheafFunctorIso`: the constant-sheaf compatibility
  at the constant sheaf of rings itself, stated for
  `Stacks.SheafOfModules.Constant.constantModuleSheafFunctor`, which is the constant sheaf of
  modules functor the rest of the library uses.

## Implementation notes

**Why `constSheafOfModules` is not Mathlib's `PresheafOfModules.constFunctor`.** Mathlib's
`PresheafOfModules.constFunctor` builds the constant presheaf of modules from a cocone on the
presheaf of rings, and its statement ties the module universe to the ring universe: it is
declared for `R : Cᵒᵖ ⥤ RingCat.{w}` with values in `PresheafOfModules.{w} R`. The equivalence
being transported here keeps those two universes independent, so the constant presheaf of
modules is taken instead as `Functor.const Cᵒᵖ ⋙ Stacks.PresheafOfModules.ofFunctor Λ`, which
is the same construction with the universes free. The two agree where both are defined, which is
`Stacks.ConstantRingModules.constFunctorIso`, and that is what carries the results here over to
`Stacks.SheafOfModules.Constant.constantModuleSheafFunctor`.

**How the constant-sheaf compatibility is proved.** The comparison map itself is the unit of
Mathlib's sheafification adjunction for presheaves of modules, read through the equivalence
between presheaves of modules over the constant presheaf of rings and `ModuleCat Λ`-valued
presheaves. That it is an isomorphism after sheafification is local bijectivity, and local
bijectivity of a morphism of `ModuleCat Λ`-valued presheaves is a property of the underlying
functions, so it is inherited from the sheafification map of the underlying presheaf of abelian
groups, where it is an instance. The two-out-of-three step is then taken in `J.W` through
`presheafToSheaf`, and `GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso` turns the result
back into an isomorphism of sheaves.

**The slicing square is an identity on sections.** Reading a sheaf of modules over `R` as a
`ModuleCat Λ`-valued sheaf restricts the scalars and leaves the sections alone; restricting to
`C/U` reindexes the sections along `Over.forget U` and leaves the `Λ`-action alone. The two
commute componentwise on the nose, so every component of the square is the identity.

The compatibility of `constantSheaf` itself with restriction to a slice is not proved here: it
is `Stacks.ConstantSheaf.overPullbackConstantSheafIso`, already in the library, and it is the
third factor of `constantSheafOverFunctorIso`.

No `@[stacks]` attribute is attached to anything in this file. No statement of the source is a
compatibility of an equivalence of categories; these are the identifications that let a theorem
about one of the two readings discharge an obligation stated about the other.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 09BD](https://stacks.math.columbia.edu/tag/09BD)
* [Stacks Project, Tag 09BE](https://stacks.math.columbia.edu/tag/09BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe a r v u

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] (Λ : Type r) [Ring Λ]

/-! ### The constant presheaf of modules over the constant presheaf of rings -/

/-- The constant presheaf of modules over the constant presheaf of rings on `Λ`: the constant
`ModuleCat Λ`-valued presheaf, read as a presheaf of modules. Unlike Mathlib's
`PresheafOfModules.constFunctor` this leaves the module universe independent of the ring
universe; the two agree where both are defined, which is
`Stacks.ConstantRingModules.constFunctorIso`. -/
abbrev constPresheafOfModules :
    ModuleCat.{a} Λ ⥤ _root_.PresheafOfModules.{a} (constRing (C := C) Λ) :=
  Functor.const Cᵒᵖ ⋙ ofFunctor.{a} Λ

/-- The constant presheaf of modules over the constant presheaf of rings on `Λ` agrees with
Mathlib's, which is built from the constant cocone on the constant presheaf of rings. Both
assign the fixed module to every object; the comparison undoes the restriction of scalars along
the identity of `Λ`. -/
def constFunctorIso :
    _root_.PresheafOfModules.constFunctor (constCocone Cᵒᵖ (RingCat.of Λ)) ≅
      constPresheafOfModules.{r} (C := C) Λ :=
  NatIso.ofComponents
    (fun M => _root_.PresheafOfModules.isoMk
      (fun _ => ModuleCat.restrictScalarsId'App _ rfl M) (by intros; ext x; rfl))
    (by intros; ext X x; rfl)

/-! ### The constant-sheaf compatibility -/

section Sheaves

variable (J : GrothendieckTopology C) {R : Sheaf J RingCat.{r}}
  (α : constRing (C := C) Λ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- The unit of the sheafification of presheaves of modules over the constant presheaf of rings,
read on `ModuleCat Λ`-valued presheaves: a presheaf of modules maps to the underlying
`ModuleCat Λ`-valued presheaf of the sheaf of modules it generates. -/
def toFunctorUnit :
    toFunctor.{a} Λ ⟶ _root_.PresheafOfModules.sheafification α ⋙
      toModuleSheaf.{a} Λ J α ⋙ sheafToPresheaf J (ModuleCat.{a} Λ) :=
  Functor.whiskerRight (_root_.PresheafOfModules.sheafificationAdjunction α).unit
      (toFunctor.{a} Λ) ≫
    Functor.whiskerLeft (_root_.PresheafOfModules.sheafification α)
      (toModuleSheafCompSheafToPresheafIso.{a} Λ J α).inv

/-- The unit is locally injective: on sections it is the sheafification map of the underlying
presheaf of abelian groups, and local injectivity only looks at the underlying functions. -/
instance isLocallyInjective_toFunctorUnit
    (P : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)) :
    Presheaf.IsLocallyInjective J ((toFunctorUnit.{a} Λ J α).app P) := by
  have h : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf) :=
    inferInstance
  constructor
  intro _X x y hxy
  exact h.equalizerSieve_mem x y hxy

/-- The unit is locally surjective, for the same reason as it is locally injective. -/
instance isLocallySurjective_toFunctorUnit
    (P : _root_.PresheafOfModules.{a} (constRing (C := C) Λ)) :
    Presheaf.IsLocallySurjective J ((toFunctorUnit.{a} Λ J α).app P) := by
  have h : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.presheaf) :=
    inferInstance
  constructor
  intro _X x
  exact h.imageSieve_mem x

variable [HasWeakSheafify J (ModuleCat.{a} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{a} Λ)]

/-- The constant sheaves of modules over `R`: the constant presheaf of modules over the constant
presheaf of rings on `Λ`, sheafified along `α`. -/
abbrev constSheafOfModules : ModuleCat.{a} Λ ⥤ SheafOfModules.{a} R :=
  constPresheafOfModules.{a} Λ ⋙ _root_.PresheafOfModules.sheafification α

/-- The comparison of the constant presheaf with the underlying `ModuleCat Λ`-valued presheaf of
the constant sheaf of modules over `R`. -/
def constComparison :
    Functor.const Cᵒᵖ (C := ModuleCat.{a} Λ) ⟶
      (constSheafOfModules.{a} Λ J α ⋙ toModuleSheaf.{a} Λ J α) ⋙
        sheafToPresheaf J (ModuleCat.{a} Λ) :=
  Functor.whiskerLeft (Functor.const Cᵒᵖ) (ofFunctorCompToFunctorIso.{a} Λ).inv ≫
    Functor.whiskerLeft (constPresheafOfModules.{a} Λ) (toFunctorUnit.{a} Λ J α)

/-- The component of `constComparison` at every module is locally injective. -/
instance isLocallyInjective_constComparison (M : ModuleCat.{a} Λ) :
    Presheaf.IsLocallyInjective J ((constComparison.{a} Λ J α).app M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    ((ofFunctorCompToFunctorIso.{a} Λ).inv.app ((Functor.const Cᵒᵖ).obj M) ≫
      (toFunctorUnit.{a} Λ J α).app ((constPresheafOfModules.{a} Λ).obj M)))

/-- The component of `constComparison` at every module is locally surjective. -/
instance isLocallySurjective_constComparison (M : ModuleCat.{a} Λ) :
    Presheaf.IsLocallySurjective J ((constComparison.{a} Λ J α).app M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    ((ofFunctorCompToFunctorIso.{a} Λ).inv.app ((Functor.const Cᵒᵖ).obj M) ≫
      (toFunctorUnit.{a} Λ J α).app ((constPresheafOfModules.{a} Λ).obj M)))

/-- The comparison of the constant sheaf with the constant sheaf of modules over `R` read
through the equivalence: the adjoint of `Stacks.ConstantRingModules.constComparison`. -/
def constTheta :
    constantSheaf J (ModuleCat.{a} Λ) ⟶
      constSheafOfModules.{a} Λ J α ⋙ toModuleSheaf.{a} Λ J α :=
  Functor.whiskerRight (constComparison.{a} Λ J α) (presheafToSheaf J (ModuleCat.{a} Λ)) ≫
    Functor.whiskerLeft (constSheafOfModules.{a} Λ J α ⋙ toModuleSheaf.{a} Λ J α)
      (sheafificationAdjunction J (ModuleCat.{a} Λ)).counit

omit [J.WEqualsLocallyBijective (ModuleCat Λ)] in
/-- The comparison of sheaves restricts to the comparison of presheaves along the sheafification
map of the constant presheaf, by the triangle identity of the sheafification adjunction. -/
theorem toSheafify_constTheta (M : ModuleCat.{a} Λ) :
    CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
        (sheafToPresheaf J (ModuleCat.{a} Λ)).map ((constTheta.{a} Λ J α).app M) =
      (constComparison.{a} Λ J α).app M := by
  have h := ((sheafificationAdjunction J (ModuleCat.{a} Λ)).homEquiv
    ((Functor.const Cᵒᵖ).obj M)
    ((constSheafOfModules.{a} Λ J α ⋙
      toModuleSheaf.{a} Λ J α).obj M)).apply_symm_apply ((constComparison.{a} Λ J α).app M)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit] at h
  exact h

/-- The comparison is an isomorphism at every module: the comparison of presheaves is locally
bijective, hence inverted by sheafification, and so is the sheafification map of the constant
presheaf, so the comparison of sheaves is inverted by sheafification too -- which for a morphism
of sheaves means that it is an isomorphism. -/
instance isIso_constTheta_app (M : ModuleCat.{a} Λ) : IsIso ((constTheta.{a} Λ J α).app M) := by
  rw [← GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso, GrothendieckTopology.W_iff]
  have h1 : IsIso ((presheafToSheaf J (ModuleCat.{a} Λ)).map
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
    (J.W_iff _).mp (J.W_toSheafify _)
  have h2 : IsIso ((presheafToSheaf J (ModuleCat.{a} Λ)).map
      ((constComparison.{a} Λ J α).app M)) :=
    (J.W_iff _).mp ((J.W_iff_isLocallyBijective _).mpr ⟨inferInstance, inferInstance⟩)
  rw [← toSheafify_constTheta.{a} Λ J α M, Functor.map_comp] at h2
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h2

/-- The comparison `constTheta` of the constant sheaf with the constant sheaf of modules is an
isomorphism. -/
instance isIso_constTheta : IsIso (constTheta.{a} Λ J α) := NatIso.isIso_of_isIso_app _

/-- **Reading a sheaf of modules over `R` as a sheaf of `Λ`-modules carries the constant sheaves
of modules to the constant sheaves.** -/
def constantSheafModuleSheafIso :
    constantSheaf J (ModuleCat.{a} Λ) ≅
      constSheafOfModules.{a} Λ J α ⋙ toModuleSheaf.{a} Λ J α :=
  asIso (constTheta.{a} Λ J α)

/-! ### The slicing compatibility -/

section Slice

variable (U : C)

/-- The restriction to the slice site `C/U` of a morphism out of the constant presheaf of rings
on `Λ`: the constant presheaf of rings on `C/U` is the restriction of the one on `C`, so this is
a whiskering. -/
abbrev overRingMap : constRing (C := Over U) Λ ⟶ (R.over U).obj :=
  Functor.whiskerLeft (Over.forget U).op α

/-- The restriction `overRingMap` of `α` to the slice site `C/U` is locally injective. -/
instance isLocallyInjective_overRingMap :
    Presheaf.IsLocallyInjective (J.over U) (overRingMap Λ J α U) :=
  Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α

/-- The restriction `overRingMap` of `α` to the slice site `C/U` is locally surjective. -/
instance isLocallySurjective_overRingMap :
    Presheaf.IsLocallySurjective (J.over U) (overRingMap Λ J α U) :=
  Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α

variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{a}]

/-- **Reading a sheaf of modules over `R` as a sheaf of `Λ`-modules commutes with restriction to
a slice site.** Both functors act on sections only by reindexing and by restriction of scalars,
and those are independent of each other, so every component of the square is the identity. -/
def toModuleSheafOverIso :
    toModuleSheaf.{a} Λ J α ⋙ J.overPullback (ModuleCat.{a} Λ) U ≅
      SheafOfModules.overFunctor.{a} R U ⋙
        toModuleSheaf.{a} Λ (J.over U) (overRingMap Λ J α U) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

variable [HasWeakSheafify (J.over U) (ModuleCat.{a} Λ)]
  [∀ F : (Over U)ᵒᵖ ⥤ ModuleCat.{a} Λ,
    (Over.forget U).op.HasPointwiseRightKanExtension F]

/-- **The two compatibilities combined.** The constant sheaves on the slice site `C/U` are the
restrictions to `C/U` of the constant sheaves of modules over `R`, read through the equivalence
on `C/U`.

This is the shape in which the bounded case of Stacks 094H and the derived-category step of
Stacks 09BE both need the identification of the two readings: each argues locally on `C/U`, over
constant sheaves of modules produced by the other reading. The third factor, that the constant
sheaf itself commutes with restriction to a slice, is
`Stacks.ConstantSheaf.overPullbackConstantSheafIso`. -/
def constantSheafOverFunctorIso :
    constantSheaf (J.over U) (ModuleCat.{a} Λ) ≅
      constSheafOfModules.{a} Λ J α ⋙ SheafOfModules.overFunctor.{a} R U ⋙
        toModuleSheaf.{a} Λ (J.over U) (overRingMap Λ J α U) :=
  Stacks.ConstantSheaf.overPullbackConstantSheafIso J (ModuleCat.{a} Λ) U ≪≫
    Functor.isoWhiskerRight (constantSheafModuleSheafIso.{a} Λ J α)
      (J.overPullback (ModuleCat.{a} Λ) U) ≪≫
    Functor.isoWhiskerLeft (constSheafOfModules.{a} Λ J α) (toModuleSheafOverIso.{a} Λ J α U)

end Slice

section SliceMap

variable {X Y : C} (f : X ⟶ Y)
  [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify (J.over X) AddCommGrpCat.{a}]
  [(J.over Y).WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify (J.over Y) AddCommGrpCat.{a}]

/-- **The slicing compatibility along a morphism of the site.** The same square as
`Stacks.ConstantRingModules.toModuleSheafOverIso` with `Over.map f` in place of
`Over.forget U`: reading a sheaf of modules over `R` as a sheaf of `Λ`-modules commutes with
restriction from `C/Y` to `C/X` along `f`. This is the form the conclusion of Stacks 09BD
is stated in, where the chain map produced lives over the slices of the arrows of the covering
sieve. -/
def toModuleSheafOverMapIso :
    toModuleSheaf.{a} Λ (J.over Y) (overRingMap Λ J α Y) ⋙
        J.overMapPullback (ModuleCat.{a} Λ) f ≅
      SheafOfModules.overMap.{a} R f ⋙
        toModuleSheaf.{a} Λ (J.over X) (overRingMap Λ J α X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end SliceMap

end Sheaves

/-! ### The constant sheaf of rings -/

section ConstantRingSheaf

variable (J : GrothendieckTopology C)
  [HasWeakSheafify J RingCat.{r}] [J.WEqualsLocallyBijective RingCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  [HasWeakSheafify J (ModuleCat.{r} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{r} Λ)]

/-- **The constant-sheaf compatibility, for the constant sheaf of modules functor the library
uses.** Reading a sheaf of modules over the constant sheaf of rings on `Λ` as a sheaf of
`Λ`-modules carries `Stacks.SheafOfModules.Constant.constantModuleSheafFunctor` to
`constantSheaf J (ModuleCat Λ)`. -/
def constantModuleSheafFunctorIso :
    Stacks.SheafOfModules.Constant.constantModuleSheafFunctor J (R := Λ) ⋙
        toModuleSheaf.{r} Λ J (constantRingMap Λ J) ≅ constantSheaf J (ModuleCat.{r} Λ) :=
  Functor.isoWhiskerRight (Functor.isoWhiskerRight (constFunctorIso (C := C) Λ)
      (_root_.PresheafOfModules.sheafification (constantRingMap Λ J)))
      (toModuleSheaf.{r} Λ J (constantRingMap Λ J)) ≪≫
    (constantSheafModuleSheafIso.{r} Λ J (constantRingMap Λ J)).symm

end ConstantRingSheaf

end Stacks.ConstantRingModules

end
