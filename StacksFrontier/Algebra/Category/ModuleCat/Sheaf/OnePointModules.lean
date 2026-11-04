module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos

/-!
# Modules on the one-point ringed space

Let `R` be a commutative ring and let `({*}, R)` be the one-point ringed space, whose structure
sheaf is the skyscraper sheaf with value `R`.  Taking sections on the whole space is an
equivalence

`Mod(𝒪_{({*}, R)}) ≌ Mod(R)`,

with quasi-inverse the sheaf associated to an `R`-module.  This is the identification of modules
on the coefficient point with `R`-modules that Stacks 01BH uses to recognise a pullback along
`π : X ⟶ ({*}, R)` as the associated sheaf, and it is the abelian half of the identification
`D({*}, R) = D(R)` of Cohomology, Section 0FKU.

## Main definitions

* `Stacks.AssociatedSheaf.coefficientPointSheafOfModules` — a presheaf of modules on the
  coefficient point, regarded as a sheaf of modules.
* `Stacks.AssociatedSheaf.coefficientPointForgetEquivalence` — forgetting the sheaf condition is
  an equivalence on the coefficient point.
* `Stacks.AssociatedSheaf.onePointPresheafEquivalence` and
  `Stacks.AssociatedSheaf.onePointEquivalence` — **the one-point identification**
  `Mod(R) ≌ Mod(𝒪_{({*}, R)})`, at the presheaf level and for sheaves of modules.

## Main results

* `Stacks.AssociatedSheaf.isSheaf_of_presheafOfModules_coefficientPoint` — every presheaf of
  modules on the coefficient point is a sheaf; its sections off the point are zero, which on the
  one-point space is the whole of the sheaf condition.
* `Stacks.AssociatedSheaf.bijective_one_tmul` — if `R → S` is a ring isomorphism then
  `m ↦ 1 ⊗ m` is a bijection `M ≃ S ⊗_R M`.  This is what makes the unit of the one-point
  identification invertible.
* `Stacks.AssociatedSheaf.presheafGlobalSections_eq_pointSections` — on the coefficient point the
  global sections of construction (3) of Stacks 01BH *are* sections on the whole space read as an
  `R`-module through the canonical identification `R ≅ 𝒪_{pt}({*})`.
* `Stacks.AssociatedSheaf.onePointEquivalence_inverse` — the quasi-inverse of the identification
  is sections on the whole space.
* `Stacks.AssociatedSheaf.onePointEquivalence_functor_obj_val` — the sheaf of modules attached to
  `M` has sections `𝒪(U) ⊗_R M`, that is, it is construction (3) of Stacks 01BH.
* `Stacks.AssociatedSheaf.onePointPresheafEquivalence_unit_app_apply` — the unit of the
  identification is `m ↦ 1 ⊗ m`.

## Implementation notes

The equivalence is not obtained from full faithfulness together with essential surjectivity: that
route produces the quasi-inverse by `Classical.choice` and nothing can then be computed with it.
Instead the adjunction `associatedSheaf ⊣ globalSections` of clause (4) of Stacks 01BH is shown to
have invertible unit and counit and `CategoryTheory.Adjunction.toEquivalence` is applied, so both
functors of the equivalence are the explicit ones and the three characterising lemmas above hold.

Invertibility of the counit is full faithfulness of global sections, which on the coefficient
point is `Stacks.AssociatedSheaf.pointSectionsFullyFaithful` transported along
`presheafGlobalSections_eq_pointSections`; that transport is an equality of functors rather than an
isomorphism, because the two differ only in the ring map along which scalars are restricted and
those two ring maps are equal.  Invertibility of the unit is `bijective_one_tmul`, applied to the
canonical identification `R ≅ 𝒪_{pt}({*})`: the unit is `m ↦ 1 ⊗ m` on the nose, by
`Stacks.AssociatedSheaf.presheafGlobalSectionsAdjunction_unit_app_apply`.

Passing between presheaves and sheaves of modules on the point costs nothing, and in particular
needs no sheafification: a presheaf of modules there has zero sections off the point, because the
structure sheaf of the coefficient point has the zero ring there, and on a one-point space that is
exactly the sheaf condition (`TopCat.Presheaf.isSheaf_on_punit_of_isTerminal`).  So
`SheafOfModules.forget` is an equivalence with a strict quasi-inverse, and the unit and counit of
`coefficientPointForgetEquivalence` are identities.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u v

namespace Stacks.AssociatedSheaf

/-! ### Presheaves of modules on the point are sheaves -/

section Sheafhood

variable {Rc : CommRingCat.{u}}

/-- A presheaf of modules on the one-point ringed space is a sheaf: its sections off the point are
zero, since the structure sheaf there is the zero ring, and on a one-point space vanishing on the
empty open is the whole of the sheaf condition. -/
theorem isSheaf_of_presheafOfModules_coefficientPoint
    (N : PresheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)).obj) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (coefficientPoint Rc).carrier) N.presheaf := by
  have h : Subsingleton (N.presheaf.obj (op (⊥ : Opens (TopCat.of PUnit.{u + 1})))) :=
    subsingleton_obj_of_notMem N (by simp)
  exact TopCat.Presheaf.isSheaf_on_punit_of_isTerminal N.presheaf
    (@AddCommGrpCat.isZero_of_subsingleton (N.presheaf.obj (op ⊥)) h).isTerminal

/-- A presheaf of modules on the one-point ringed space, regarded as a sheaf of modules. -/
def coefficientPointSheafOfModules :
    PresheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)).obj ⥤
      SheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)) where
  obj N := ⟨N, isSheaf_of_presheafOfModules_coefficientPoint N⟩
  map f := ⟨f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of modules of `coefficientPointSheafOfModules.obj N` is `N`. -/
@[simp]
theorem coefficientPointSheafOfModules_obj_val
    (N : PresheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)).obj) :
    (coefficientPointSheafOfModules.obj N).val = N := rfl

/-- On the one-point ringed space, forgetting the sheaf condition is an equivalence between
sheaves of modules and presheaves of modules; its unit and counit are identities. -/
def coefficientPointForgetEquivalence :
    SheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)) ≌
      PresheafOfModules.{v} (structureSheafRing (coefficientPoint Rc)).obj where
  functor := SheafOfModules.forget _
  inverse := coefficientPointSheafOfModules
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Sheafhood

/-! ### Tensoring with a ring isomorphism -/

section Tensor

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- Multiplication by `e⁻¹ s`, as an `R`-linear map in `s`, for a ring isomorphism `e : R ≃+* S`
whose underlying map is the structure map of the `R`-algebra `S`. -/
def invScalarAction (e : R ≃+* S) (he : ∀ r, algebraMap R S r = e r) : S →ₗ[R] M →ₗ[R] M where
  toFun s := (e.symm s) • (LinearMap.id : M →ₗ[R] M)
  map_add' s t := by simp [add_smul]
  map_smul' r s := by
    have h : r • s = e r * s := by rw [Algebra.smul_def, he]
    simp only [h, map_mul, RingEquiv.symm_apply_apply, RingHom.id_apply, mul_smul]

/-- If the structure map of an `R`-algebra `S` is a ring isomorphism `e`, then `m ↦ 1 ⊗ m` is a
bijection from `M` onto `S ⊗_R M`, with inverse `s ⊗ m ↦ e⁻¹(s) • m`. -/
theorem bijective_one_tmul (e : R ≃+* S) (he : ∀ r, algebraMap R S r = e r) :
    Function.Bijective (fun m : M ↦ (1 : S) ⊗ₜ[R] m) := by
  set g : S ⊗[R] M →ₗ[R] M := TensorProduct.lift (invScalarAction e he) with hg
  have hgt : ∀ (s : S) (m : M), g (s ⊗ₜ[R] m) = e.symm s • m := fun s m ↦ by
    simp [hg, invScalarAction]
  have hleft : ∀ m : M, g ((1 : S) ⊗ₜ[R] m) = m := fun m ↦ by rw [hgt, map_one, one_smul]
  have hright : ∀ x : S ⊗[R] M, (1 : S) ⊗ₜ[R] (g x) = x := by
    intro x
    induction x with
    | zero => simp
    | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb]
    | tmul s m =>
      rw [hgt, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, he,
        RingEquiv.apply_symm_apply, mul_one]
  refine ⟨fun a b h ↦ ?_, fun x ↦ ⟨g x, hright x⟩⟩
  have h2 : g ((1 : S) ⊗ₜ[R] a) = g ((1 : S) ⊗ₜ[R] b) := congrArg g h
  rwa [hleft, hleft] at h2

end Tensor

/-! ### The one-point identification -/

section OnePoint

variable (R : Type u) [CommRing R]

/-- Sections on the whole space of a presheaf of modules on the coefficient point, regarded as an
`R`-module along a given ring map from `R` to the sections of the structure sheaf. -/
abbrev pointSectionsAlong
    (g : R →+* (structureSheafRing (coefficientPoint (CommRingCat.of R))).obj.obj (op ⊤)) :
    PresheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R))).obj ⥤
      ModuleCat.{u} R :=
  PresheafOfModules.evaluation _ (op ⊤) ⋙ ModuleCat.restrictScalars g

/-- On the coefficient point the scalar map of construction (3) of Stacks 01BH is the canonical
identification of `R` with the sections of the structure sheaf on the whole space. -/
theorem globalSectionsMap_point_app_top :
    ((globalSectionsMap (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))).app
      (op ⊤)).hom = (coefficientRingEquiv (R := R)).toRingHom := by
  refine RingHom.ext fun r ↦ ?_
  rw [globalSectionsMap_app_top_apply]
  rfl

/-- On the coefficient point, global sections with scalars restricted along the canonical ring map
is sections on the whole space read through `R ≅ 𝒪_{pt}({*})`.  The two functors are *equal*: they
differ only in the ring map along which scalars are restricted, and those are equal by
`globalSectionsMap_point_app_top`. -/
theorem presheafGlobalSections_eq_pointSections :
    presheafGlobalSections.{u, u} (coefficientPoint (CommRingCat.of R))
        (pointRing (R := R)) = pointSections.{u, u} (R := R) :=
  congrArg (pointSectionsAlong R) (globalSectionsMap_point_app_top R)

/-- On the coefficient point, the global-sections functor on presheaves of modules is full. -/
instance presheafGlobalSections_point_full :
    (presheafGlobalSections.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).Full := by
  rw [presheafGlobalSections_eq_pointSections]
  exact (pointSectionsFullyFaithful (R := R)).full

/-- On the coefficient point, the global-sections functor on presheaves of modules is faithful. -/
instance presheafGlobalSections_point_faithful :
    (presheafGlobalSections.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).Faithful := by
  rw [presheafGlobalSections_eq_pointSections]
  exact (pointSectionsFullyFaithful (R := R)).faithful

/-- On the coefficient point the counit of `presheafGlobalSectionsAdjunction` is invertible,
global sections being fully faithful there. -/
instance isIso_pointAdjunction_counit :
    IsIso ((presheafGlobalSectionsAdjunction.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).counit) :=
  Adjunction.counit_isIso_of_R_fully_faithful
    (R := presheafGlobalSections.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R)))
    (presheafGlobalSectionsAdjunction.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R)))

/-- On the coefficient point each component of the counit of
`presheafGlobalSectionsAdjunction` is invertible. -/
instance isIso_pointAdjunction_counit_app
    (Y : PresheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R))).obj) :
    IsIso ((presheafGlobalSectionsAdjunction.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).counit.app Y) :=
  NatIso.isIso_app_of_isIso ((presheafGlobalSectionsAdjunction.{u, u}
    (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))).counit) Y

/-- The unit `M ⟶ 𝒪_{pt}({*}) ⊗_R M` of construction (3) on the coefficient point is invertible:
it is `m ↦ 1 ⊗ m`, and the structure map `R → 𝒪_{pt}({*})` is a ring isomorphism. -/
instance isIso_pointAdjunction_unit_app (M : ModuleCat.{u} R) :
    IsIso ((presheafGlobalSectionsAdjunction.{u, u} (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).unit.app M) := by
  let := ((globalSectionsMap (coefficientPoint (CommRingCat.of R))
    (pointRing (R := R))).app (op ⊤)).hom.toAlgebra
  have he : ∀ r, algebraMap ((constantRingPresheaf (coefficientPoint (CommRingCat.of R)) R).obj
      (op ⊤)) ((coefficientPoint (CommRingCat.of R)).presheaf.obj (op ⊤)) r =
      (coefficientRingEquiv (R := R)) r := fun r ↦
    DFunLike.congr_fun (globalSectionsMap_point_app_top R) r
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : (fun m : M ↦ ((presheafGlobalSectionsAdjunction.{u, u}
        (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))).unit.app M).hom m) =
      (fun m : M ↦ (1 : (coefficientPoint (CommRingCat.of R)).presheaf.obj (op ⊤)) ⊗ₜ[
        (constantRingPresheaf (coefficientPoint (CommRingCat.of R)) R).obj (op ⊤)] m) :=
    funext fun m ↦ presheafGlobalSectionsAdjunction_unit_app_apply _ _ M m
  change Function.Bijective (fun m : M ↦ ((presheafGlobalSectionsAdjunction.{u, u}
      (coefficientPoint (CommRingCat.of R)) (pointRing (R := R))).unit.app M).hom m)
  rw [hfun]
  exact bijective_one_tmul (coefficientRingEquiv (R := R)) he

/-- **The one-point identification, at the presheaf level.** An `R`-module `M` is the same thing
as a presheaf of modules on the one-point ringed space `({*}, R)`: the two functors are
construction (3) of Stacks 01BH and sections on the whole space. -/
def onePointPresheafEquivalence :
    ModuleCat.{u} R ≌
      PresheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R))).obj :=
  (presheafGlobalSectionsAdjunction.{u, u} (coefficientPoint (CommRingCat.of R))
    (pointRing (R := R))).toEquivalence

/-- The quasi-inverse of the presheaf-level one-point identification is sections on the whole
space. -/
theorem onePointPresheafEquivalence_inverse :
    (onePointPresheafEquivalence R).inverse = pointSections.{u, u} (R := R) :=
  presheafGlobalSections_eq_pointSections R

/-- **The unit of the one-point identification is `m ↦ 1 ⊗ m`.** -/
theorem onePointPresheafEquivalence_unit_app_apply (M : ModuleCat.{u} R) (m : M) :
    letI := ((globalSectionsMap (coefficientPoint (CommRingCat.of R))
      (pointRing (R := R))).app (op ⊤)).hom.toAlgebra
    ((onePointPresheafEquivalence R).unitIso.hom.app M).hom m =
      (1 : (coefficientPoint (CommRingCat.of R)).presheaf.obj (op ⊤)) ⊗ₜ[
        (constantRingPresheaf (coefficientPoint (CommRingCat.of R)) R).obj (op ⊤)] m :=
  presheafGlobalSectionsAdjunction_unit_app_apply _ _ M m

/-- **The one-point identification** `Mod(R) ≌ Mod(𝒪_{({*}, R)})`: an `R`-module is the same thing
as a sheaf of modules on the one-point ringed space with ring `R`. -/
def onePointEquivalence :
    ModuleCat.{u} R ≌
      SheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R))) :=
  (onePointPresheafEquivalence R).trans coefficientPointForgetEquivalence.symm

/-- **The quasi-inverse of the one-point identification is sections on the whole space.** -/
theorem onePointEquivalence_inverse :
    (onePointEquivalence R).inverse =
      SheafOfModules.forget _ ⋙ pointSections.{u, u} (R := R) :=
  congrArg (fun F ↦ SheafOfModules.forget _ ⋙ F) (presheafGlobalSections_eq_pointSections R)

/-- **The sheaf of modules attached to `M` by the one-point identification is construction (3) of
Stacks 01BH**: its sections on `U` are `𝒪(U) ⊗_R M`. -/
theorem onePointEquivalence_functor_obj_val (M : ModuleCat.{u} R) :
    ((onePointEquivalence R).functor.obj M).val =
      associatedPresheaf (coefficientPoint (CommRingCat.of R)) (pointRing (R := R)) M :=
  rfl

/-- The one-point identification sends a sheaf of modules to its sections on the whole space. -/
theorem onePointEquivalence_inverse_obj
    (F : SheafOfModules.{u} (structureSheafRing (coefficientPoint (CommRingCat.of R)))) :
    (onePointEquivalence R).inverse.obj F =
      (ModuleCat.restrictScalars (coefficientRingEquiv (R := R)).toRingHom).obj
        (F.val.obj (op ⊤)) :=
  congrFun (congrArg Functor.obj (onePointEquivalence_inverse R)) F

end OnePoint

end Stacks.AssociatedSheaf

end
