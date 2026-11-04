module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import StacksCore.Tactic.StacksAttribute

/-!
# Two spellings of `j_{U!} O_U`, and the isomorphism between them

The extension by zero of the structure sheaf of the localised site `C/U` is the sheafification of
a presheaf of free modules on the arrows into `U`, with a `ULift` raising the module universe
above the hom-sets of the site. There are two such presheaves:

* `Stacks.SheafOfModules.extensionByZeroUnitPresheaf`, with sections `ULift (X ⟶ U) →₀ R(X)`;
* `Stacks.SheafOfModules.extensionByZeroUnitPresheafULift`, with sections
  `ULift ((X ⟶ U) →₀ R(X))`.

We construct the isomorphism between them and between their sheafifications
`extensionByZeroUnit` and `extensionByZeroUnitULift`.

## Main definitions

* `Stacks.SheafOfModules.presheafULift`: the functor
  `PresheafOfModules.{v} R ⥤ PresheafOfModules.{max v t} R` raising the universe of the values of
  a presheaf of modules by wrapping them in `ULift`.
* `Stacks.SheafOfModules.moduleULift`: the same for sheaves of modules.
* `Stacks.SheafOfModules.extensionByZeroUnitPresheafBase`: the presheaf with sections
  `(X ⟶ U) →₀ R(X)`.
* `Stacks.SheafOfModules.extensionByZeroUnitULift`: the sheafification of
  `presheafULift.obj extensionByZeroUnitPresheafBase`.
* `Stacks.SheafOfModules.extensionByZeroUnitPresheafULiftIso`: the isomorphism
  `extensionByZeroUnitPresheaf R U ≅ presheafULift.obj (extensionByZeroUnitPresheafBase R U)`.
* `Stacks.SheafOfModules.extensionByZeroUnitULiftIso`: the isomorphism
  `extensionByZeroUnitULift R U ≅ extensionByZeroUnit R U`.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.SheafOfModules

/-! ### Raising the universe of the values of a presheaf of modules -/

/-- Raise the universe of the values of a presheaf of modules, keeping the site and the
coefficient ring presheaf fixed: the sections over `X` become `ULift (M(X))`. -/
noncomputable def presheafULift.{t, v, w, u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{w}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{max v t} R where
  obj M :=
    letI : ∀ X, Module (R.obj X) ((M.presheaf ⋙ AddCommGrpCat.uliftFunctor.{t}).obj X) :=
      fun X => inferInstanceAs (Module _ (ULift.{t} (M.obj X)))
    PresheafOfModules.ofPresheaf (M.presheaf ⋙ AddCommGrpCat.uliftFunctor.{t})
      (fun _ _ f r x => congrArg ULift.up (M.map_smul f r x.down))
  map f :=
    { app := fun X => (ModuleCat.uliftFunctor.{t} _).map (f.app X)
      naturality := fun g => by
        ext x
        exact congrArg ULift.up (congrArg (fun φ => φ x.down) (f.naturality g)) }

/-- Raise the universe of the values of a sheaf of modules: the sections over `X` become
`ULift (M(X))`. -/
noncomputable def moduleULift.{t, v, w, u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{v} R ⥤ SheafOfModules.{max v t} R where
  obj M :=
    { val := (presheafULift.{t} R.obj).obj M.val
      isSheaf := Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor M.isSheaf }
  map f := ⟨(presheafULift.{t} R.obj).map f.val⟩

universe u₁ v₁ w t

variable {C : Type u₁} [Category.{v₁} C]

/-! ### The second spelling of the extension by zero of the structure sheaf -/

section Base

variable (R : Cᵒᵖ ⥤ RingCat.{w})

/-- The restriction map of the unlifted extension-by-zero presheaf: an arrow `f : X ⟶ Y` of
`Cᵒᵖ` composes the indexing arrows with `f.unop` and restricts the coefficients. -/
noncomputable def extensionByZeroUnitBaseRestriction (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((X.unop ⟶ U) →₀ R.obj X) →+ ((Y.unop ⟶ U) →₀ R.obj Y) :=
  (Finsupp.mapDomain.addMonoidHom (fun h : X.unop ⟶ U => f.unop ≫ h)).comp
    (Finsupp.mapRange.addMonoidHom (R.map f).hom.toAddMonoidHom)

/-- `extensionByZeroUnitBaseRestriction R U f` sends `Finsupp.single h r` to
`Finsupp.single (f.unop ≫ h) (R.map f r)`. -/
@[simp]
lemma extensionByZeroUnitBaseRestriction_single (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : X.unop ⟶ U) (r : R.obj X) :
    extensionByZeroUnitBaseRestriction R U f (Finsupp.single h r) =
      Finsupp.single (f.unop ≫ h) (R.map f r) := by
  simp [extensionByZeroUnitBaseRestriction, Finsupp.mapDomain.addMonoidHom,
    Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- `extensionByZeroUnitBaseRestriction R U f` is semilinear along `R.map f`. -/
lemma extensionByZeroUnitBaseRestriction_smul (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X)
    (x : (X.unop ⟶ U) →₀ R.obj X) :
    extensionByZeroUnitBaseRestriction R U f (r • x) =
      R.map f r • extensionByZeroUnitBaseRestriction R U f x := by
  rw [extensionByZeroUnitBaseRestriction, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    show (Finsupp.mapRange.addMonoidHom (R.map f).hom.toAddMonoidHom) (r • x) =
      Finsupp.mapRange (R.map f) (map_zero (R.map f).hom) (r • x) from rfl,
    show (Finsupp.mapRange.addMonoidHom (R.map f).hom.toAddMonoidHom) x =
      Finsupp.mapRange (R.map f) (map_zero (R.map f).hom) x from rfl,
    Finsupp.mapRange_smul' r (R.map f r) x (fun a => map_mul (R.map f).hom r a),
    show (Finsupp.mapDomain.addMonoidHom (fun h : X.unop ⟶ U => f.unop ≫ h))
        (R.map f r • Finsupp.mapRange (R.map f) (map_zero (R.map f).hom) x) =
      Finsupp.mapDomain _ (R.map f r • Finsupp.mapRange (R.map f)
        (map_zero (R.map f).hom) x) from rfl,
    Finsupp.mapDomain_smul]
  rfl

/-- The presheaf of abelian groups underlying the unlifted extension by zero. -/
noncomputable def extensionByZeroUnitBaseAb (U : C) : Cᵒᵖ ⥤ AddCommGrpCat.{max v₁ w} where
  obj X := AddCommGrpCat.of ((X.unop ⟶ U) →₀ R.obj X)
  map f := AddCommGrpCat.ofHom (extensionByZeroUnitBaseRestriction R U f)
  map_id X := AddCommGrpCat.hom_ext <| Finsupp.addHom_ext fun h r ↦ by simp
  map_comp f g := AddCommGrpCat.hom_ext <| Finsupp.addHom_ext fun h r ↦ by simp

/-- The `R(X)`-module structure on the sections of `extensionByZeroUnitBaseAb R U` over `X`. -/
noncomputable instance extensionByZeroUnitBaseAbModule (U : C) (X : Cᵒᵖ) :
    Module (R.obj X) ((extensionByZeroUnitBaseAb R U).obj X) :=
  inferInstanceAs (Module (R.obj X) ((X.unop ⟶ U) →₀ R.obj X))

/-- The presheaf of `R`-modules whose sections over `X` are the finitely supported `R(X)`-linear
combinations of the arrows `X ⟶ U`, a module in `Type (max v₁ w)`. -/
noncomputable def extensionByZeroUnitPresheafBase (U : C) : PresheafOfModules.{max v₁ w} R :=
  PresheafOfModules.ofPresheaf (extensionByZeroUnitBaseAb R U)
    (fun {_ _} f r x => extensionByZeroUnitBaseRestriction_smul R U f r x)

/-- The restriction maps of `extensionByZeroUnitPresheafBase R U` send `Finsupp.single h r` to
`Finsupp.single (f.unop ≫ h) (R.map f r)`. -/
lemma extensionByZeroUnitPresheafBase_map_single (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : X.unop ⟶ U) (r : R.obj X) :
    (extensionByZeroUnitPresheafBase R U).map f (Finsupp.single h r) =
      Finsupp.single (f.unop ≫ h) (R.map f r) :=
  extensionByZeroUnitBaseRestriction_single R U f h r

/-- The universe lift of `extensionByZeroUnitPresheafBase R U`: its sections over `X` are
`ULift ((X ⟶ U) →₀ R(X))`. -/
noncomputable abbrev extensionByZeroUnitPresheafULift (U : C) :
    PresheafOfModules.{max u₁ v₁ w t} R :=
  (presheafULift.{max u₁ v₁ w t} R).obj (extensionByZeroUnitPresheafBase R U)

end Base

/-! ### The comparison isomorphism -/

section Compare

variable (R : Cᵒᵖ ⥤ RingCat.{w})

/-- The `R(X)`-linear equivalence `(ULift (X ⟶ U) →₀ R(X)) ≃ ULift ((X ⟶ U) →₀ R(X))`. -/
noncomputable def extensionByZeroUnitULiftSectionsEquiv (U : C) (X : Cᵒᵖ) :
    (ULift.{max u₁ v₁ w t} (X.unop ⟶ U) →₀ R.obj X) ≃ₗ[R.obj X]
      ULift.{max u₁ v₁ w t} ((X.unop ⟶ U) →₀ R.obj X) :=
  (Finsupp.domLCongr Equiv.ulift).trans ULift.moduleEquiv.symm

/-- `extensionByZeroUnitULiftSectionsEquiv R U X` sends `Finsupp.single (ULift.up h) r` to
`ULift.up (Finsupp.single h r)`. -/
@[simp]
lemma extensionByZeroUnitULiftSectionsEquiv_single (U : C) (X : Cᵒᵖ) (h : X.unop ⟶ U)
    (r : R.obj X) :
    extensionByZeroUnitULiftSectionsEquiv.{u₁, v₁, w, t} R U X (Finsupp.single (ULift.up h) r) =
      ULift.up (Finsupp.single h r) :=
  congrArg ULift.up (Finsupp.equivMapDomain_single _ _ _)

/-- The isomorphism of presheaves of modules
`extensionByZeroUnitPresheaf R U ≅ extensionByZeroUnitPresheafULift R U`, given on sections by
`extensionByZeroUnitULiftSectionsEquiv`. -/
noncomputable def extensionByZeroUnitPresheafULiftIso (U : C) :
    extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ≅
      extensionByZeroUnitPresheafULift.{u₁, v₁, w, t} R U :=
  PresheafOfModules.isoMk
    (fun X => (extensionByZeroUnitULiftSectionsEquiv.{u₁, v₁, w, t} R U X).toModuleIso)
    (fun {X Y} f => by
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      rintro ⟨a⟩ r
      change extensionByZeroUnitULiftSectionsEquiv.{u₁, v₁, w, t} R U Y
          ((extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).map f
            (Finsupp.single (ULift.up a) r)) =
        ULift.up ((extensionByZeroUnitPresheafBase R U).map f
          (extensionByZeroUnitULiftSectionsEquiv.{u₁, v₁, w, t} R U X
            (Finsupp.single (ULift.up a) r)).down)
      rw [extensionByZeroUnitPresheaf_map_single, extensionByZeroUnitULiftSectionsEquiv_single,
        extensionByZeroUnitULiftSectionsEquiv_single, extensionByZeroUnitPresheafBase_map_single]
      rfl)

end Compare

section Sheaf

variable {J : GrothendieckTopology C}

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

/-- The sheafification of the presheaf `extensionByZeroUnitPresheafULift R U`, whose sections over
`X` are `ULift ((X ⟶ U) →₀ R(X))`. -/
noncomputable def extensionByZeroUnitULift (R : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{max u₁ v₁ w t} R :=
  (PresheafOfModules.sheafification.{max u₁ v₁ w t} (𝟙 R.obj)).obj
    (extensionByZeroUnitPresheafULift.{u₁, v₁, w, t} R.obj U)

/-- The isomorphism `extensionByZeroUnitULift R U ≅ extensionByZeroUnit R U`, the sheafification of
`extensionByZeroUnitPresheafULiftIso`. -/
noncomputable def extensionByZeroUnitULiftIso (R : Sheaf J RingCat.{w}) (U : C) :
    extensionByZeroUnitULift.{u₁, v₁, w, t} R U ≅ extensionByZeroUnit.{u₁, v₁, w, t} R U :=
  ((PresheafOfModules.sheafification.{max u₁ v₁ w t} (𝟙 R.obj)).mapIso
    (extensionByZeroUnitPresheafULiftIso.{u₁, v₁, w, t} R.obj U)).symm

end Sheaf

end Stacks.SheafOfModules

end
