module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Extension of scalars along a locally faithfully flat morphism reflects the zero sheaf

Let `θ : A₁ ⟶ A₂` be a morphism of presheaves of commutative rings on a site `(C, J)` whose
underlying presheaves of rings are sheaves, and let
`Stacks.Sheaves.RingedToposModules.extendScalars` be the associated extension of scalars
`Mod(A₁) ⥤ Mod(A₂)` of Stacks 03CZ, which is the sectionwise tensor product
`V ↦ A₂(V) ⊗_{A₁(V)} M(V)` followed by sheafification.

Flatness of `θ` makes that functor left exact
(`Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits`).  This module records
what *faithful* flatness buys instead: the functor reflects the zero object, i.e.
`A₂ ⊗_{A₁} M = 0` forces `M = 0`.  As with the flatness criterion of Stacks 0GN1, faithful
flatness is only asked for *locally*: every object of the site is required to have a covering
whose members `V` have `A₂(V)` faithfully flat over `A₁(V)`.  That hypothesis is
`Stacks.Sheaves.RingedToposModules.LocallyFaithfullyFlat`.

The argument is the one of commutative algebra, run objectwise and glued by the site.  Over a
member `V` of the covering, `M(V) ⟶ A₂(V) ⊗_{A₁(V)} M(V)`, `x ↦ 1 ⊗ x`, is injective — this is
Mathlib's `Module.FaithfullyFlat.tensorProduct_mk_injective` — so the unit of the presheaf-level
change-of-rings adjunction is *locally* injective.  Sheafification units are locally injective
unconditionally, and the unit of the sheaf-level adjunction
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` is the composite of the two
(`Stacks.Sheaves.RingedToposModules.forget_map_extendRestrictScalarsAdjunction_unit_app`), hence
locally injective.  A locally injective morphism whose source is a sheaf is injective on
sections, so that unit is a monomorphism; and a monomorphism into a zero object forces the
source to be zero.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.LocallyFaithfullyFlat`: every object of the site has a
  covering whose members `V` have `A₂(V)` faithfully flat over `A₁(V)`.

## Main results

* `Stacks.Sheaves.RingedToposModules.isLocallyInjective_changeOfRingsAdjunction_unit_app`: the
  presheaf-level unit `P ⟶ A₂ ⊗_{p,A₁} P` is locally injective.
* `Stacks.Sheaves.RingedToposModules.isLocallyInjective_extendScalars_unit_app`: the
  sheaf-level unit `M ⟶ A₂ ⊗_{A₁} M` is locally injective.
* `Stacks.Sheaves.RingedToposModules.mono_extendScalars_unit_app`: that unit is a
  monomorphism.
* `Stacks.Sheaves.RingedToposModules.isZero_of_isZero_extendScalars_obj`: **extension of
  scalars along a locally faithfully flat morphism reflects the zero sheaf of modules.**

## Implementation notes

The covering in `LocallyFaithfullyFlat` is given as a family of arrows whose generated sieve
belongs to the topology, which is how
`Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat`
phrases "there exists a covering" for the flatness criterion of Stacks 0GN1, so that the two
hypotheses are supplied by one and the same covering datum.

Faithful flatness of the sections map is asked for in the `RingHom.FaithfullyFlat` spelling,
matching the `RingHom.Flat` spelling in which the flatness criterion asks for flatness.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.Sheaves.RingedToposModules

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)

/-- **`θ` is locally faithfully flat**: every object of the site has a covering family whose
members `V` have `A₂(V)` faithfully flat over `A₁(V)`.

This is the faithful-flatness counterpart of the hypothesis of the flatness criterion of
Stacks 0GN1, and is phrased with the same covering datum: a family of arrows whose generated
sieve is a covering sieve. -/
public def LocallyFaithfullyFlat : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
    Sieve.ofArrows X f ∈ J U ∧ ∀ i, ((θ.app (op (X i))).hom).FaithfullyFlat

/-- **Over an object at which `θ` is faithfully flat, `x ↦ 1 ⊗ x` is injective.**  This is
Mathlib's `Module.FaithfullyFlat.tensorProduct_mk_injective` read at the sections of the unit of
the change-of-rings adjunction of Stacks 03CU. -/
public theorem injective_changeOfRingsAdjunction_unit_app_app (V : Cᵒᵖ)
    (hV : ((θ.app V).hom).FaithfullyFlat) (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    Function.Injective (((changeOfRingsAdjunction θ).unit.app P).app V).hom := by
  let : Algebra (A₁.obj V) (A₂.obj V) := (θ.app V).hom.toAlgebra
  have : Module.FaithfullyFlat (A₁.obj V) (A₂.obj V) := hV
  let : Module (A₁.obj V) (P.obj V) := (P.obj V).isModule
  intro a b hab
  rw (transparency := .default) [changeOfRingsAdjunction_unit_app_apply,
    changeOfRingsAdjunction_unit_app_apply] at hab
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := A₁.obj V) (B := A₂.obj V) _ hab

/-- **The unit `P ⟶ A₂ ⊗_{p,A₁} P` of the change-of-rings adjunction of Stacks 03CU is locally
injective** when `θ` is locally faithfully flat: over the members of the covering supplied by
the hypothesis it is injective, by
`Stacks.Sheaves.RingedToposModules.injective_changeOfRingsAdjunction_unit_app_app`, and
restriction to a covering family is what local injectivity asks for. -/
public theorem isLocallyInjective_changeOfRingsAdjunction_unit_app
    (hθ : LocallyFaithfullyFlat J θ) (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map ((changeOfRingsAdjunction θ).unit.app P)) := by
  constructor
  intro U x y hxy
  obtain ⟨I, X, f, hcov, hff⟩ := hθ U.unop
  apply J.superset_covering
    ((Sieve.generate_le_iff (Presieve.ofArrows X f)
      (Presheaf.equalizerSieve x y)).2 ((Presieve.ofArrows_le_iff).2 ?_)) hcov
  intro i
  rw [Presheaf.equalizerSieve_apply]
  let ψ := (changeOfRingsAdjunction θ).unit.app P
  change (ψ.app U).hom x = (ψ.app U).hom y at hxy
  apply injective_changeOfRingsAdjunction_unit_app_app θ (op (X i)) (hff i) P
  have hrel := congrArg
    ((((changeOfRings θ ⋙ restrictScalars θ).obj P).map (f i).op).hom) hxy
  rwa [← PresheafOfModules.naturality_apply ψ (f i).op x,
    ← PresheafOfModules.naturality_apply ψ (f i).op y] at hrel

/-- **A locally injective morphism of sheaves of modules is injective on sections.**  Local
injectivity makes the sieve on which two sections with the same image agree a covering sieve,
and the source being a sheaf is separated for it. -/
public theorem injective_val_app_of_isLocallyInjective {R : Sheaf J RingCat.{w}}
    {M N : SheafOfModules.{w} R} (φ : M ⟶ N)
    (hφ : PresheafOfModules.IsLocallyInjective J φ.val) (V : Cᵒᵖ) :
    Function.Injective (φ.val.app V) := by
  intro x y hxy
  exact M.isSheaf.isSeparated _ _
    (Presheaf.equalizerSieve_mem J ((PresheafOfModules.toPresheaf R.obj).map φ.val) x y hxy) x y
    (fun _ _ hf => by exact hf)

section Sheaves

variable (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The unit `M ⟶ A₂ ⊗_{A₁} M` of the extension/restriction of scalars adjunction of Stacks
03CZ is locally injective** when `θ` is locally faithfully flat.

The unit is the presheaf-level change-of-rings unit followed by a sheafification unit
(`Stacks.Sheaves.RingedToposModules.forget_map_extendRestrictScalarsAdjunction_unit_app`); the
first factor is locally injective by
`Stacks.Sheaves.RingedToposModules.isLocallyInjective_changeOfRingsAdjunction_unit_app` and the
second unconditionally. -/
public theorem isLocallyInjective_extendScalars_unit_app (hθ : LocallyFaithfullyFlat J θ)
    (M : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    PresheafOfModules.IsLocallyInjective J
      ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
        ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M)) := by
  set u₂ := (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings θ).obj M.val)
  have h2 : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf A₁)).map ((restrictScalars θ).map u₂)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf A₂)).map u₂))
  have fac : (PresheafOfModules.toPresheaf (ringPresheaf A₁)).map
        ((changeOfRingsAdjunction θ).unit.app M.val) ≫
      (PresheafOfModules.toPresheaf (ringPresheaf A₁)).map ((restrictScalars θ).map u₂) =
      (PresheafOfModules.toPresheaf (ringPresheaf A₁)).map
        ((SheafOfModules.forget (commRingSheaf J A₁ h₁)).map
          ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M)) := by
    rw [forget_map_extendRestrictScalarsAdjunction_unit_app]
    exact ((PresheafOfModules.toPresheaf (ringPresheaf A₁)).map_comp _ _).symm
  exact (Presheaf.isLocallyInjective_iff_of_fac J fac).2
    (isLocallyInjective_changeOfRingsAdjunction_unit_app J θ hθ M.val)

end Sheaves

section Reflection

variable (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The unit `M ⟶ A₂ ⊗_{A₁} M` is a monomorphism** when `θ` is locally faithfully flat: it is
locally injective, hence injective on sections, hence a monomorphism. -/
public theorem mono_extendScalars_unit_app (hθ : LocallyFaithfullyFlat J θ)
    (M : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    Mono ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M) :=
  SheafOfModules.mono_of_sectionwise_injective _
    (injective_val_app_of_isLocallyInjective J _
      (isLocallyInjective_extendScalars_unit_app J θ h₁ h₂ hθ M))

/-- **Extension of scalars along a locally faithfully flat morphism reflects the zero sheaf of
modules**: if `A₂ ⊗_{A₁} M` vanishes then so does `M`.

The unit `M ⟶ A₂ ⊗_{A₁} M` is a monomorphism by
`Stacks.Sheaves.RingedToposModules.mono_extendScalars_unit_app`, and restriction of scalars
carries the vanishing of the target over, so the identity of `M` is cancelled against it. -/
public theorem isZero_of_isZero_extendScalars_obj (hθ : LocallyFaithfullyFlat J θ)
    (M : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (h : IsZero ((extendScalars J θ h₁ h₂).obj M)) : IsZero M := by
  have hmono := mono_extendScalars_unit_app J θ h₁ h₂ hθ M
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M)).1
    ((Functor.map_isZero (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)) h).eq_of_tgt
      _ _)

end Reflection

section ComparisonPresheaf

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}} (a : O ⟶ A₁)
variable (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A morphism of presheaves of commutative rings whose target has a sheaf of rings underlying
it, read as a morphism into that sheaf of rings.  Stating it at this type is what lets the sheaf
of rings be solved for from the shape of the type, so that
`PresheafOfModules.sheafification` and `PresheafOfModules.sheafificationAdjunction` can be
applied to it. -/
public abbrev ringMapToCommRingSheaf : ringPresheaf O ⟶ (commRingSheaf J A₁ h₁).obj :=
  Functor.whiskerRight a (forget₂ CommRingCat.{w} RingCat.{w})

variable [Presheaf.IsLocallyInjective J (ringMapToCommRingSheaf J a h₁)]
  [Presheaf.IsLocallySurjective J (ringMapToCommRingSheaf J a h₁)]

/-- **Restriction of scalars along a locally bijective morphism of presheaves of rings is fully
faithful on sheaves of modules**, read as a statement about `Hom`-subsingletons.

`A₁` being an associated sheaf of `O` makes
`Stacks.Sheaves.RingedToposModules.ringMapToCommRingSheaf` locally bijective, so sheafification
of presheaves of `O`-modules is left adjoint to the underlying presheaf of `O`-modules of a sheaf
of `A₁`-modules with a counit that is an isomorphism; a right adjoint with invertible counit is
fully faithful. -/
public theorem subsingleton_hom_forget_restrictScalars
    (M W : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (hsub : Subsingleton (M ⟶ W)) :
    Subsingleton
      ((SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙
          PresheafOfModules.restrictScalars (ringMapToCommRingSheaf J a h₁)).obj M ⟶
        (SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙
          PresheafOfModules.restrictScalars (ringMapToCommRingSheaf J a h₁)).obj W) :=
  @Equiv.subsingleton _ _
    ((PresheafOfModules.sheafificationAdjunction
      (ringMapToCommRingSheaf J a h₁)).fullyFaithfulROfIsIsoCounit.homEquiv
        (X := M) (Y := W)).symm hsub

/-- **Extension of scalars reflects the zero sheaf when faithful flatness is only available over
a comparison presheaf.**  Let `a : O ⟶ A₁` exhibit `A₁` as an associated sheaf of a presheaf of
commutative rings `O` — so `a` is locally bijective — and suppose the *composite*
`O ⟶ A₁ ⟶ A₂` is locally faithfully flat.  Then `A₂ ⊗_{A₁} M = 0` forces `M = 0`.

This is the form in which the hypothesis is actually available for the canonical morphism from
the small étale site of a scheme to its small Zariski site: there faithful flatness of the
sections map holds over `𝒪_S(f(V))`, the comparison presheaf whose associated sheaf is
`ε⁻¹𝒪_{S_Zar}`, and *not* objectwise over `ε⁻¹𝒪_{S_Zar}` itself, whose sections are a
sheafification value and strictly larger in general.  It is the faithful-flatness counterpart of
the detour that
`Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat`
takes for the flatness criterion of Stacks 0GN1.

`Stacks.Sheaves.RingedToposModules.isZero_of_isZero_extendScalars_obj` is this statement with
`O = A₁` and `a` the identity.

The proof does not compare the two tensor products.  The vanishing of `A₂ ⊗_{A₁} M` makes every
morphism out of `M` into a restriction of scalars of a sheaf of `A₂`-modules zero, and
restriction of scalars along `a` is fully faithful
(`Stacks.Sheaves.RingedToposModules.subsingleton_hom_forget_restrictScalars`), so every morphism
of presheaves of `O`-modules out of `M` into such a sheaf is zero as well.  Applied to the unit
`M ⟶ A₂ ⊗_{p,O} M` of the presheaf-level change of rings along the composite, followed by a
sheafification unit, this says that a *locally injective* morphism out of `M` vanishes, which
forces the sections of `M` to be singletons, `M` being separated. -/
public theorem isZero_of_isZero_extendScalars_obj_of_locallyFaithfullyFlat_comp
    (hσ : LocallyFaithfullyFlat J (a ≫ θ))
    (M : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (h : IsZero ((extendScalars J θ h₁ h₂).obj M)) : IsZero M := by
  set P := (SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙
    PresheafOfModules.restrictScalars (ringMapToCommRingSheaf J a h₁)).obj M
  set N := (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
    ((changeOfRings (a ≫ θ)).obj P)
  set W := (SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj N
  have hsubP := subsingleton_hom_forget_restrictScalars J a h₁ M W
    (@Equiv.subsingleton _ _ ((extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv M N).symm
      ⟨h.eq_of_src⟩)
  set u₂ := (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A₂ h₂) (𝟙 _)).unit.app ((changeOfRings (a ≫ θ)).obj P)
  have h2 : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf O)).map
        ((restrictScalars (a ≫ θ)).map u₂)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (ringPresheaf A₂)).map u₂))
  set g : P ⟶ (SheafOfModules.forget (commRingSheaf J A₁ h₁) ⋙
      PresheafOfModules.restrictScalars (ringMapToCommRingSheaf J a h₁)).obj W :=
    (changeOfRingsAdjunction (a ≫ θ)).unit.app P ≫ (restrictScalars (a ≫ θ)).map u₂
  have fac : (PresheafOfModules.toPresheaf (ringPresheaf O)).map
        ((changeOfRingsAdjunction (a ≫ θ)).unit.app P) ≫
      (PresheafOfModules.toPresheaf (ringPresheaf O)).map ((restrictScalars (a ≫ θ)).map u₂) =
      (PresheafOfModules.toPresheaf (ringPresheaf O)).map g :=
    ((PresheafOfModules.toPresheaf (ringPresheaf O)).map_comp _ _).symm
  have hgli := (Presheaf.isLocallyInjective_iff_of_fac J fac).2
    (isLocallyInjective_changeOfRingsAdjunction_unit_app J (a ≫ θ) hσ P)
  have hinj : ∀ (V : Cᵒᵖ), Function.Injective ((0 : M ⟶ W).val.app V) := by
    intro V x y _
    refine M.isSheaf.isSeparated _ _ (hgli.equalizerSieve_mem x y ?_) x y
      (fun _ _ hf => by exact hf)
    rw [hsubP.elim g 0]
    simp
    rfl
  have hmono : Mono (0 : M ⟶ W) := SheafOfModules.mono_of_sectionwise_injective _ hinj
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono (0 : M ⟶ W)).1 (by simp)

end ComparisonPresheaf

end Stacks.Sheaves.RingedToposModules

end
