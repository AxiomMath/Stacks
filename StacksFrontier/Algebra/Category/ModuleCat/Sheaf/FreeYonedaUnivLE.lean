module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Logic.Small.Defs

/-!
# The free module on a representable corepresents sections, at independent universes

Let `C` be a site, `R` a sheaf of rings on it and `v` a module universe.  The functor
`M ↦ M(U)` on sheaves of `R`-modules is corepresented by the sheafification of the free
presheaf of modules on the representable at `U`, the object usually written `O_U`.  This file
supplies that corepresentation with the universes of the site, of its homs, of the rings and
of the modules **mutually independent**.

`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroGenerators.lean` already has it
(`SheafOfModules.sheafifiedFreeYonedaEquiv`), but only for `[SmallCategory.{u} C]` with the
ring and module universes both equal to `u`, as forced by `ExtensionByZero.lean`.  The
obstruction is `PresheafOfModules.free`, whose target universe is the ring universe: the free
module on `F.obj X` has sections `F.obj X →₀ R.obj X`, which live in `max t r`.  The
replacement is `PresheafOfModules.freeObjShrink` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean`, whose sections are
shrunk into `v`; that file constructs the descent map out of it and uses it to produce a
separator, but states no bijection and no functoriality, which is what is added here.

## Main definitions

* `PresheafOfModules.freeGenShrink`: the tautological generating section of
  `freeObjShrink R F` attached to a section of `F`.
* `PresheafOfModules.freeMapShrink`: functoriality of `freeObjShrink` in the presheaf of
  types.
* `PresheafOfModules.fromFreeYonedaShrink`: the map `O_U ⟶ M` of presheaves of modules
  attached to a section of `M` over `U`.
* `SheafOfModules.freeYonedaSheafUnivLE`: the sheaf of modules `O_U`.

## Main results

* `PresheafOfModules.freeObjShrink_hom_ext`: two maps out of `freeObjShrink R F` agreeing on
  every generating section are equal.
* `PresheafOfModules.freeYonedaShrinkEquiv`: `Hom(O_U, M) ≃ M(U)` for presheaves of modules.
* `SheafOfModules.freeYonedaSheafUnivLEEquiv` and
  `SheafOfModules.freeYonedaSheafUnivLEEquiv_comp`: `Hom(O_U, M) ≃ M(U)` for sheaves of
  modules, and its naturality in `M`.

## Implementation notes

`Shrink` is declared `@[no_expose]` in Mathlib, so its body is opaque across modules even
with `import all`.  The consequence is specific: a goal mentioning an
element of `(freeObjShrink R F).obj X` is not type-correct at the `implicit` transparency
level that `rw` checks its motive at, so every rewrite against a lemma phrased in the raw
type `Shrink (F.obj X →₀ R.obj X)` is refused.  Elaboration and `exact` are unaffected, since
they work at default transparency.  Each proof below therefore does its rewriting inside a
hypothesis stated at the raw type and closes with `exact`, or transports along `congrArg`;
no transparency option is involved, and none is needed.

The two local-bijectivity instances for the identity of the ring presheaf already exist at
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroGenerators.lean:197` and `:200`, but
under `[SmallCategory.{u} C]` with the ring universe equal to the module universe, so they do
not fire here; they are restated under distinct names rather than duplicated under the same
one.

The smallness hypotheses are the ones the constructions actually use —
`Small.{v} (R.obj X)` and `LocallySmall.{v} C` — rather than `UnivLE`, matching the
convention of `SeparatorUnivLE.lean`; `UnivLE.{r, v}` and `UnivLE.{w, v}` supply them.
-/

@[expose] public section

universe t v w u r

open CategoryTheory Limits Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{w} C] (R : Cᵒᵖ ⥤ RingCat.{r}) [∀ X, Small.{v} (R.obj X)]

section Gen

variable (F : Cᵒᵖ ⥤ Type t) [∀ X, Small.{v} (F.obj X)]

/-- The tautological generating section of `freeObjShrink R F` attached to a section of `F`:
the shrunk single generator with coefficient `1`. -/
noncomputable def freeGenShrink {X : Cᵒᵖ} (i : F.obj X) :
    (freeObjShrink R F : PresheafOfModules.{v} R).obj X :=
  Shrink.addEquiv.symm (Finsupp.single i 1)

/-- A scalar multiple of a generating section is the shrunk single generator with that
coefficient. -/
lemma freeGenShrink_smul {X : Cᵒᵖ} (i : F.obj X) (c : R.obj X) :
    c • freeGenShrink R F i =
      (Shrink.addEquiv (α := F.obj X →₀ R.obj X)).symm (Finsupp.single i c) := by
  have h := Shrink.addEquiv_symm_smul (α := F.obj X →₀ R.obj X) c
    (Finsupp.single i (1 : R.obj X))
  rw [Finsupp.smul_single, smul_eq_mul, mul_one] at h
  exact h.symm

/-- `freeObjDescShrink` evaluates on a generating section to the prescribed value. -/
private theorem freeObjDescShrink_app_freeGenShrink {F : Cᵒᵖ ⥤ Type t}
    [∀ X, Small.{v} (F.obj X)] {M : PresheafOfModules.{v} R} (φ : ∀ X, F.obj X → M.obj X)
    (hφ : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (i : F.obj X),
      φ Y (F.map f i) = M.map f (φ X i))
    {X : Cᵒᵖ} (i : F.obj X) :
    (freeObjDescShrink φ hφ).app X (freeGenShrink R F i) = φ X i := by
  have h := freeObjDescShrink_app_single φ hφ X i 1
  rw [one_smul] at h
  exact h

/-- Restriction carries the generating section at `i` to the generating section at the
restriction of `i`. -/
lemma map_freeGenShrink {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : F.obj X) :
    (freeObjShrink R F : PresheafOfModules.{v} R).map f (freeGenShrink R F i) =
      freeGenShrink R F (F.map f i) := by
  have h := freeAbPresheafShrink_map_apply R F f
    ((Shrink.addEquiv (α := F.obj X →₀ R.obj X)).symm (Finsupp.single i (1 : R.obj X)))
  rw [AddEquiv.apply_symm_apply, Finsupp.mapDomainMapRange_single, map_one] at h
  exact h

/-- **The generating sections determine a map out of `freeObjShrink R F`.** -/
lemma freeObjShrink_hom_ext {M : PresheafOfModules.{v} R}
    {α β : (freeObjShrink R F : PresheafOfModules.{v} R) ⟶ M}
    (h : ∀ (X : Cᵒᵖ) (i : F.obj X),
      α.app X (freeGenShrink R F i) = β.app X (freeGenShrink R F i)) :
    α = β := by
  refine PresheafOfModules.hom_ext (fun X ↦ ModuleCat.hom_ext (LinearMap.ext ?_))
  intro x
  obtain ⟨y, rfl⟩ := (Shrink.addEquiv (α := F.obj X →₀ R.obj X)).symm.surjective x
  have key : ((α.app X).hom.toAddMonoidHom.comp
        (Shrink.addEquiv (α := F.obj X →₀ R.obj X)).symm.toAddMonoidHom) =
      ((β.app X).hom.toAddMonoidHom.comp
        (Shrink.addEquiv (α := F.obj X →₀ R.obj X)).symm.toAddMonoidHom) := by
    refine Finsupp.addHom_ext (fun i c ↦ ?_)
    have eα := congrArg (fun z ↦ (ModuleCat.Hom.hom (α.app X)) z) (freeGenShrink_smul R F i c)
    have eβ := congrArg (fun z ↦ (ModuleCat.Hom.hom (β.app X)) z) (freeGenShrink_smul R F i c)
    refine eα.symm.trans (Eq.trans ?_ eβ)
    rw [map_smul, map_smul, h X i]
  exact DFunLike.congr_fun key y

omit [∀ X, Small.{v} (F.obj X)] in
/-- The family of generating sections attached to a morphism of presheaves of types is
natural, which is what `freeObjDescShrink` asks of it. -/
lemma freeGenShrink_natural {G : Cᵒᵖ ⥤ Type t} [∀ X, Small.{v} (G.obj X)] (ψ : F ⟶ G) :
    ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (i : F.obj X),
      freeGenShrink R G (ψ.app Y (F.map f i)) =
        (freeObjShrink R G : PresheafOfModules.{v} R).map f
          (freeGenShrink R G (ψ.app X i)) := by
  intro X Y f i
  rw [map_freeGenShrink]
  have hn : ψ.app Y (F.map f i) = G.map f (ψ.app X i) := by
    simp [NatTrans.naturality_apply]
  exact congrArg (freeGenShrink R G) hn

variable {F} in
/-- **Functoriality of `freeObjShrink` in the presheaf of types.** -/
noncomputable def freeMapShrink {G : Cᵒᵖ ⥤ Type t} [∀ X, Small.{v} (G.obj X)] (ψ : F ⟶ G) :
    (freeObjShrink R F : PresheafOfModules.{v} R) ⟶ freeObjShrink R G :=
  freeObjDescShrink (fun X i ↦ freeGenShrink R G (ψ.app X i)) (freeGenShrink_natural R F ψ)

variable {F} in
/-- `freeMapShrink` carries generating sections to generating sections. -/
lemma freeMapShrink_gen {G : Cᵒᵖ ⥤ Type t} [∀ X, Small.{v} (G.obj X)] (ψ : F ⟶ G)
    {X : Cᵒᵖ} (i : F.obj X) :
    (freeMapShrink R ψ).app X (freeGenShrink R F i) = freeGenShrink R G (ψ.app X i) := by
  exact freeObjDescShrink_app_freeGenShrink R _ (freeGenShrink_natural R F ψ) i

end Gen

section Yoneda

variable [LocallySmall.{v} C]

omit [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} C] in
/-- Restricting a fixed section of `M` over `U` along the sections of the representable at `U`
is natural, which is what `freeObjDescShrink` asks of it. -/
lemma restrictₛₗ_natural {M : PresheafOfModules.{v} R} {U : C} (x : M.obj (op U)) :
    ∀ ⦃Y Z : Cᵒᵖ⦄ (f : Y ⟶ Z) (g : (yoneda.obj U).obj Y),
      M.restrictₛₗ ((yoneda.obj U).map f g).op x = M.map f (M.restrictₛₗ g.op x) := by
  intro Y Z f g
  change M.map ((f.unop ≫ g).op) x = M.map f (M.map g.op x)
  rw [← M.map_comp_apply]
  rfl

/-- The map of presheaves of modules out of the free presheaf on the representable at `U`
determined by a section of `M` over `U`: the one carrying the tautological generator to it. -/
noncomputable def fromFreeYonedaShrink {M : PresheafOfModules.{v} R} {U : C}
    (x : M.obj (op U)) :
    (freeObjShrink R (yoneda.obj U) : PresheafOfModules.{v} R) ⟶ M :=
  freeObjDescShrink (fun _Y g ↦ M.restrictₛₗ g.op x) (restrictₛₗ_natural R x)

/-- `fromFreeYonedaShrink` carries the generator at `g` to the restriction along `g`. -/
lemma fromFreeYonedaShrink_gen {M : PresheafOfModules.{v} R} {U : C} (x : M.obj (op U))
    {Y : Cᵒᵖ} (g : Y.unop ⟶ U) :
    (fromFreeYonedaShrink R x).app Y (freeGenShrink R (yoneda.obj U) g) = M.map g.op x := by
  exact freeObjDescShrink_app_freeGenShrink (F := yoneda.obj U) R (fun _Y g ↦ M.restrictₛₗ g.op x)
    (restrictₛₗ_natural R x) g

/-- Restricting the tautological generator along `g` gives the generator at `g`. -/
lemma map_freeGenShrink_id {U : C} {Y : Cᵒᵖ} (g : Y.unop ⟶ U) :
    (freeObjShrink R (yoneda.obj U) : PresheafOfModules.{v} R).map g.op
        (freeGenShrink R (yoneda.obj U) (𝟙 U)) =
      freeGenShrink R (yoneda.obj U) g := by
  rw [map_freeGenShrink]
  exact congrArg (freeGenShrink R (yoneda.obj U)) (Category.comp_id g)

/-- **Sections over `U` are corepresented by the free presheaf of modules on the representable
at `U`**, with the universes of the site, of its homs, of the rings and of the modules
independent. -/
noncomputable def freeYonedaShrinkEquiv {M : PresheafOfModules.{v} R} {U : C} :
    ((freeObjShrink R (yoneda.obj U) : PresheafOfModules.{v} R) ⟶ M) ≃ M.obj (op U) where
  toFun α := α.app (op U) (freeGenShrink R (yoneda.obj U) (𝟙 U))
  invFun x := fromFreeYonedaShrink R x
  left_inv α := by
    refine freeObjShrink_hom_ext R _ (fun Y g ↦ ?_)
    rw [fromFreeYonedaShrink_gen, ← map_freeGenShrink_id R g,
      PresheafOfModules.naturality_apply]
  right_inv x := by
    change (fromFreeYonedaShrink R x).app (op U)
      (freeGenShrink R (yoneda.obj U) (𝟙 U)) = x
    rw [fromFreeYonedaShrink_gen]
    change M.map (𝟙 (op U)) x = x
    rw [M.map_id]
    rfl

/-- Reading off the generating section is natural in the target: both sides are the same
evaluation. -/
lemma freeYonedaShrinkEquiv_comp {M N : PresheafOfModules.{v} R} {U : C}
    (α : (freeObjShrink R (yoneda.obj U) : PresheafOfModules.{v} R) ⟶ M) (φ : M ⟶ N) :
    freeYonedaShrinkEquiv R (α ≫ φ) = φ.app (op U) (freeYonedaShrinkEquiv R α) := rfl

end Yoneda

/-- The identity of a presheaf of rings is locally injective.  Restated here because
`SheafOfModules.isLocallyInjective_id` is under `[SmallCategory.{u} C]` with the ring universe
equal to the module universe. -/
instance isLocallyInjective_idRing {J : GrothendieckTopology C} :
    Presheaf.IsLocallyInjective J (𝟙 R) :=
  Presheaf.isLocallyInjective_of_injective J _ (fun _ _ _ h ↦ h)

/-- The identity of a presheaf of rings is locally surjective.  Restated here because
`SheafOfModules.isLocallySurjective_id` is under `[SmallCategory.{u} C]` with the ring universe
equal to the module universe. -/
instance isLocallySurjective_idRing {J : GrothendieckTopology C} :
    Presheaf.IsLocallySurjective J (𝟙 R) :=
  Presheaf.isLocallySurjective_of_surjective J _ (fun _ x ↦ ⟨x, rfl⟩)

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [∀ X, Small.{v} (R.obj.obj X)] [LocallySmall.{v} C]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The sheaf of modules `O_U`: the sheafification of the free presheaf of modules on the
representable at `U`, in a module universe independent of the universes of the site, of its
homs and of the rings. -/
noncomputable def freeYonedaSheafUnivLE (U : C) : SheafOfModules.{v} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (PresheafOfModules.freeObjShrink R.obj (yoneda.obj U))

/-- **Sections over `U` are corepresented by `O_U`**, with the universes of the site, of its
homs, of the rings and of the modules independent: sheafification is a left adjoint, and the
free presheaf of modules on the representable at `U` corepresents evaluation at `U`. -/
noncomputable def freeYonedaSheafUnivLEEquiv (M : SheafOfModules.{v} R) (U : C) :
    (freeYonedaSheafUnivLE R U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    (PresheafOfModules.freeYonedaShrinkEquiv R.obj)

/-- Reading off the generating section is natural in the target.  Both bijections in play are
exactly that evaluation, so this is `rfl`. -/
lemma freeYonedaSheafUnivLEEquiv_comp {M N : SheafOfModules.{v} R} {U : C}
    (ψ : freeYonedaSheafUnivLE R U ⟶ M) (φ : M ⟶ N) :
    freeYonedaSheafUnivLEEquiv R N U (ψ ≫ φ)
      = φ.val.app (op U) (freeYonedaSheafUnivLEEquiv R M U ψ) := rfl

end SheafOfModules

end
