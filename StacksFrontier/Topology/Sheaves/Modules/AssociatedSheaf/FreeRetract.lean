module

public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.FlatFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.FreeMatrix
import StacksCore.Tactic.StacksAttribute

/-!
# A retract of a finite free sheaf of modules is the associated sheaf of a finite projective
module

Let `(X, 𝒪_X)` be a ringed space and let `F` be a sheaf of `𝒪_X`-modules which, on an open `U`,
is a retract of `𝒪_U^{⊕n}`. Stacks 08BL supplies exactly such a `U` around every point of a flat
sheaf of modules of finite presentation. This file identifies `F` on `U` with construction (3) of
Stacks 01BH applied to a finite projective module over `𝒪_X(U)`, namely to `Γ(U, F)` itself.

The argument is the one that makes the adjunction of Stacks 01BH(4) do the work. Write `ℱ_•` for
construction (3) and `Γ` for global sections with scalars restricted along `α`, so that
`ℱ_• ⊣ Γ`. The unit of that adjunction is an isomorphism at a finite free module, because the
free sheaf of modules on a finite index type has tuples for its sections
(`Stacks.SheafOfModules.freeSectionsIso`) and is the associated sheaf of the free module
(`Stacks.AssociatedSheaf.freeIsoAssociatedSheaf`). By the triangle identity the counit is then an
isomorphism at `ℱ_{R^n}`, hence at the free sheaf `𝒪^{⊕n}`, and the counit-isomorphism property
passes to retracts: a retract of an isomorphism in the arrow category is an isomorphism, with the
inverse read off the retraction. The counit at `F` *is* the comparison `ℱ_{Γ(F)} ≅ F`, and
applying `Γ` to the retraction exhibits `Γ(F)` as a direct summand of a finite free module, so it
is finite and projective.

## Main results

* `Stacks.AssociatedSheaf.unit_free_apply` and `Stacks.AssociatedSheaf.isIso_unit_free`: the unit
  of the adjunction of Stacks 01BH(4) at a finite free module, computed on sections and shown to
  be an isomorphism.
* `Stacks.AssociatedSheaf.isIso_counit_of_retract`, `isIso_counit_of_iso`, `isIso_counit_map`: the
  counit of an arbitrary adjunction is an isomorphism at a retract of, or at an object isomorphic
  to, an object where it is one, and it is one at the image of the left adjoint wherever the unit
  is.
* `Stacks.AssociatedSheaf.globalSectionsFreeIso`: the global sections of `𝒪^{⊕I}` for a finite `I`
  are the free module on `I`.
* `Stacks.AssociatedSheaf.associatedSheafGlobalSectionsIso`, together with
  `moduleFinite_globalSections` and `moduleProjective_globalSections`: for `F` a retract of a
  finite free sheaf of modules, `ℱ_{Γ(X, F)} ≅ F` and `Γ(X, F)` is finite projective.
* `Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_retract_free` and its slice-site form
  `exists_associatedSheaf_iso_of_retract_free_over`: the same statement on an open `U`.
* `Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso_of_isFlat`: Stacks 08BL in that form —
  a flat sheaf of modules of finite presentation is, near every point, `ℱ_M` for a finite
  projective `M`.
* `Stacks.AssociatedSheaf.isSplitMono_associatedSheafFunctor_map` and
  `mono_associatedSheafFunctor_map`: construction (3) carries a direct summand of a module to a
  subsheaf. Its docstring records why the inclusion has to split, and that construction (3) does
  not carry an arbitrary injection to a monomorphism.

## Implementation notes

*Which ambient category.* The statement on an open `U` is given on the restricted ringed space
`U`, not on the slice site over `U`. That is forced rather than chosen: construction (3) is
defined only for a ringed space, since its input is a ring map `R → Γ(X, 𝒪_X)` into the sections
over a terminal object, so `ℱ_M` cannot be written on the slice site at all without being carried
back along an equivalence. The spelling chosen is also the one Stacks 01BK already uses
(`Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso`), so no transport is needed to compare
the two. Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOver` is the equivalence between
the two ambient categories; `restrictOverFreeIso` and `restrictOverRetract` carry 08BL's retract
across it, and `exists_associatedSheaf_iso_of_retract_free_over` carries the conclusion back for
consumers phrased on the slice, such as the descent of invertibility along a covering
(`Stacks.InvertibleLocallyFree.InvertibleIsLocal`, which is stated at `M.over (X i)`).

*Which spelling of the structure sheaf.* The free sheaves of modules and the retract supplied by
Stacks 08BL are stated over `structureSheafRing X`, whereas construction (3) and its adjunction are
stated over `structureSheafRing X`. The two agree definitionally, but only at default transparency:
`structureSheafRing` is semireducible, so typeclass inference, which unfolds neither it nor
`sheafCompose`, does not see through it. So wherever a step needs an *instance* rather than a type
ascription — the evaluation of `freeIsoAssociatedSheaf` in `isIso_unit_free`, the counit at the
free sheaf in `isIso_counit_of_retract_free`, the `change` in `freeSection_val_top` — the ring
sheaf is written the way the term being searched for writes it, and the conversion between the two
spellings is left to the ascribed type, where default transparency is available.

*No matrix description is needed.* The argument never names the idempotent of `End (𝒪^{⊕n})`
cutting out `F`: the only input beyond the adjunction is the sections of a finite free sheaf of
modules, and no presentation of `F` is used, so
`Stacks.AssociatedSheaf.exists_associatedSheaf_iso_of_unit_matrix` is not needed.

*No Stacks attribute.* These are steps inside the proof of Stacks 0FJN, not a tagged statement of
their own; the module over which the sheaf is associated is produced, not assumed, so none of
these carries a hypothesis the source does not.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01BK](https://stacks.math.columbia.edu/tag/01BK)
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u})

/-- Global sections acts on morphisms by taking the component on the whole space. -/
lemma globalSectionsFunctor_map_apply {R : Type u} [CommRing R]
    (α : R →+* X.presheaf.obj (op ⊤))
    {Y Z : SheafOfModules.{u} (structureSheafRing X)} (φ : Y ⟶ Z) (y : Y.val.obj (op ⊤)) :
    (globalSectionsFunctor.{u, u} X α).map φ y = φ.val.app (op ⊤) y := rfl

variable (I : Type u)

/-- The tautological section of a free sheaf of modules on the whole space is the image of `1`
under the corresponding inclusion. -/
lemma freeSection_val_top (i : I) :
    (SheafOfModules.freeSection (R := structureSheafRing X) (I := I) i).val (op ⊤) =
      freeUnitTop X i := by
  show (SheafOfModules.ιFree (R := structureSheafRing X) (I := I) i ≫
      𝟙 (SheafOfModules.free I)).val.app (op ⊤)
      (1 : (structureSheafRing X).obj.obj (op ⊤)) = _
  rw [Category.comp_id]

section Fintype

variable {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤)) [Fintype I] [DecidableEq I]

/-- The unit of the tensor-sheafification adjunction at a finite free module, read through the
comparison of the free sheaf of modules with the associated sheaf of a free module: a finitely
supported family is sent to the tuple of its values, pushed along `α`. -/
lemma unit_free_apply (f : I →₀ R) :
    (associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I) f =
      (freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤)
        ((Stacks.SheafOfModules.freeSectionsIso (R := structureSheafRing X) I (op ⊤)).hom
          (fun i ↦ α (f i))) := by
  have step : ∀ i : I,
      (associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I)
          (Finsupp.single i (f i)) =
        (freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤)
          (smulTop X (SheafOfModules.free (R := structureSheafRing X) I) (α (f i))
            (freeUnitTop X i)) := by
    intro i
    refine Eq.trans (congrArg (fun x : (ModuleCat.free R).obj I ↦
      (associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I) x)
      (show Finsupp.single i (f i) = (f i) • Finsupp.single i (1 : R) by simp)) ?_
    refine Eq.trans (((associatedSheafAdjunction.{u, u} X α).unit.app
      ((ModuleCat.free R).obj I)).hom.map_smul (f i) (Finsupp.single i (1 : R))) ?_
    refine Eq.trans (smul_globalSections X α
      ((associatedSheafFunctor.{u, u} X α).obj ((ModuleCat.free R).obj I)) (f i) _) ?_
    refine Eq.trans (congrArg (fun y ↦ smulTop X ((associatedSheafFunctor.{u, u} X α).obj
      ((ModuleCat.free R).obj I)) (α (f i)) y)
      (freeIsoAssociatedSheaf_hom_app_top X α I i).symm) ?_
    exact (((freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤)).hom.map_smul _ _).symm
  refine Eq.trans (congrArg (fun x : (ModuleCat.free R).obj I ↦
    (associatedSheafAdjunction.{u, u} X α).unit.app ((ModuleCat.free R).obj I) x)
    (Finsupp.univ_sum_single f).symm) ?_
  refine Eq.trans (map_sum ((associatedSheafAdjunction.{u, u} X α).unit.app
    ((ModuleCat.free R).obj I)).hom _ _) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ step i) ?_
  refine Eq.trans (map_sum ((freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤)).hom _ _).symm ?_
  refine congrArg (fun y ↦ (freeIsoAssociatedSheaf X α I).hom.val.app (op ⊤) y) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦
    congrArg (smulTop X (SheafOfModules.free (R := structureSheafRing X) I) (α (f i)))
      (freeSection_val_top X I i).symm) ?_
  exact (Stacks.SheafOfModules.freeSectionsIso_hom_apply
    (R := structureSheafRing X) I (op ⊤) (fun i ↦ α (f i))).symm

end Fintype

/-- **The unit of the tensor-sheafification adjunction is an isomorphism at a finite free
module.** -/
lemma isIso_unit_free [Finite I] :
    IsIso ((associatedSheafAdjunction.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
      ((ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I)) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype I
  rw [ConcreteCategory.isIso_iff_bijective]
  have hc : Function.Bijective
      ((freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I).hom.val.app (op ⊤)) :=
    ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I).hom)
  have hs : Function.Bijective
      ((Stacks.SheafOfModules.freeSectionsIso (R := structureSheafRing X) I (op ⊤)).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have h := (hc.comp hs).comp
    (Finsupp.equivFunOnFinite (α := I) (M := (X.presheaf.obj (op ⊤) : Type u))).bijective
  have key := unit_free_apply X I (RingHom.id (X.presheaf.obj (op ⊤)))
  refine ⟨fun {a b} hab ↦ h.1 ((key a).symm.trans (hab.trans (key b))), fun y ↦ ?_⟩
  obtain ⟨a, ha⟩ := h.2 y
  exact ⟨a, (key a).trans ha⟩

section Counit

variable {C : Type*} [Category C] {D : Type*} [Category D] {Lf : C ⥤ D} {Gf : D ⥤ C}

/-- **The counit of an adjunction is an isomorphism at every retract of an object where it is
one.** The inverse is read off the retraction. -/
lemma isIso_counit_of_retract (adj : Lf ⊣ Gf) {A B : D} (ρ : Retract A B)
    [IsIso (adj.counit.app B)] : IsIso (adj.counit.app A) := by
  have hnat : ∀ {A' B' : D} (g : A' ⟶ B'),
      Lf.map (Gf.map g) ≫ adj.counit.app B' = adj.counit.app A' ≫ g :=
    fun g ↦ adj.counit.naturality g
  refine ⟨ρ.i ≫ inv (adj.counit.app B) ≫ Lf.map (Gf.map ρ.r), ?_, ?_⟩
  · rw [← Category.assoc, ← hnat ρ.i, Category.assoc, IsIso.hom_inv_id_assoc,
      ← Functor.map_comp, ← Functor.map_comp, ρ.retract, Gf.map_id, Lf.map_id]
    rfl
  · rw [Category.assoc, Category.assoc, hnat ρ.r, IsIso.inv_hom_id_assoc]
    exact ρ.retract

/-- The counit of an adjunction is an isomorphism at an object isomorphic to one where it is
one. -/
lemma isIso_counit_of_iso (adj : Lf ⊣ Gf) {A B : D} (e : A ≅ B)
    [IsIso (adj.counit.app B)] : IsIso (adj.counit.app A) :=
  isIso_counit_of_retract adj ⟨e.hom, e.inv, e.hom_inv_id⟩

/-- Where the unit of an adjunction is an isomorphism, so is the counit at the image of the left
adjoint: the two are inverse to each other by the triangle identity. -/
lemma isIso_counit_map (adj : Lf ⊣ Gf) (A : C) [IsIso (adj.unit.app A)] :
    IsIso (adj.counit.app (Lf.obj A)) := by
  have h : Lf.map (adj.unit.app A) ≫ adj.counit.app (Lf.obj A) = 𝟙 (Lf.obj A) :=
    adj.left_triangle_components A
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  infer_instance

end Counit

section ModuleRetract

variable {R : Type u} [CommRing R]

/-- A retract of a finite projective module is finite projective. -/
lemma module_finite_of_retract {M N : ModuleCat.{u} R} (ρ : Retract M N)
    [Module.Finite R N] : Module.Finite R M :=
  Module.Finite.of_surjective ρ.r.hom fun m ↦
    ⟨ρ.i m, ConcreteCategory.congr_hom ρ.retract m⟩

/-- A retract of a projective module is projective. -/
lemma module_projective_of_retract {M N : ModuleCat.{u} R} (ρ : Retract M N)
    [Module.Projective R N] : Module.Projective R M :=
  Module.Projective.of_split ρ.i.hom ρ.r.hom
    (LinearMap.ext fun m ↦ ConcreteCategory.congr_hom ρ.retract m)

end ModuleRetract

section Global

variable [Finite I] (F : SheafOfModules.{u} (structureSheafRing X))

/-- The free module on a finite type is a finite module. -/
instance moduleFinite_free :
    Module.Finite (X.presheaf.obj (op ⊤))
      ((ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I) :=
  inferInstanceAs (Module.Finite (X.presheaf.obj (op ⊤))
    (I →₀ (X.presheaf.obj (op ⊤) : Type u)))

/-- The free module on a type is a projective module. -/
instance moduleProjective_free :
    Module.Projective (X.presheaf.obj (op ⊤))
      ((ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I) :=
  inferInstanceAs (Module.Projective (X.presheaf.obj (op ⊤))
    (I →₀ (X.presheaf.obj (op ⊤) : Type u)))

/-- **The global sections of a free sheaf of modules on a finite type form the free module on
that type.** This is the unit of the tensor-sheafification adjunction, which is an isomorphism
there, read through the comparison `freeIsoAssociatedSheaf`. -/
def globalSectionsFreeIso :
    (globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).obj
        (SheafOfModules.free (R := structureSheafRing X) I) ≅
      (ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I :=
  haveI := isIso_unit_free X I
  (globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).mapIso
      (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I) ≪≫
    (asIso ((associatedSheafAdjunction.{u, u} X
      (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
        ((ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I))).symm

/-- The global sections of a retract of a finite free sheaf of modules are a retract of a finite
free module. -/
def globalSectionsRetract (ρ : Retract F (SheafOfModules.free I)) :
    Retract ((globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).obj F)
      ((ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I) :=
  (ρ.map (globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤))))).trans
    ⟨(globalSectionsFreeIso X I).hom, (globalSectionsFreeIso X I).inv,
      (globalSectionsFreeIso X I).hom_inv_id⟩

/-- **The global sections of a retract of a finite free sheaf of modules are a finite module.** -/
lemma moduleFinite_globalSections (ρ : Retract F (SheafOfModules.free I)) :
    Module.Finite (X.presheaf.obj (op ⊤))
      ((globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).obj F) :=
  module_finite_of_retract (globalSectionsRetract X I F ρ)

/-- **The global sections of a retract of a finite free sheaf of modules are a projective
module.** -/
lemma moduleProjective_globalSections (ρ : Retract F (SheafOfModules.free I)) :
    Module.Projective (X.presheaf.obj (op ⊤))
      ((globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).obj F) :=
  module_projective_of_retract (globalSectionsRetract X I F ρ)

/-- The counit of the tensor-sheafification adjunction is an isomorphism at a retract of a finite
free sheaf of modules. -/
lemma isIso_counit_of_retract_free (ρ : Retract F (SheafOfModules.free I)) :
    IsIso ((associatedSheafAdjunction.{u, u} X
      (RingHom.id (X.presheaf.obj (op ⊤)))).counit.app F) := by
  have := isIso_unit_free X I
  have := isIso_counit_map (associatedSheafAdjunction.{u, u} X
    (RingHom.id (X.presheaf.obj (op ⊤))))
      ((ModuleCat.free (X.presheaf.obj (op ⊤) : Type u)).obj I)
  have : IsIso ((associatedSheafAdjunction.{u, u} X
      (RingHom.id (X.presheaf.obj (op ⊤)))).counit.app
        (SheafOfModules.free (R := structureSheafRing X) I)) :=
    isIso_counit_of_iso (associatedSheafAdjunction.{u, u} X
      (RingHom.id (X.presheaf.obj (op ⊤))))
        (freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I)
  exact isIso_counit_of_retract _ ρ

/-- **A sheaf of modules which is a retract of a finite free sheaf of modules is the sheaf
associated to its module of global sections.** The isomorphism is the counit of the
tensor-sheafification adjunction of Stacks 01BH(4). -/
def associatedSheafGlobalSectionsIso (ρ : Retract F (SheafOfModules.free I)) :
    associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤)))
        ((globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).obj F) ≅ F :=
  @asIso _ _ _ _ ((associatedSheafAdjunction.{u, u} X
    (RingHom.id (X.presheaf.obj (op ⊤)))).counit.app F) (isIso_counit_of_retract_free X I F ρ)

end Global

section Open

variable {X}

/-- The equivalence between sheaves of modules on the slice site over `U` and sheaves of modules
on the restricted ringed space carries the free sheaf of modules on `I` to the free sheaf of
modules on `I`. -/
def restrictOverFreeIso (U : Opens X.carrier) (I : Type u) :
    SheafOfModules.free (R := structureSheafRing (X.restrict U.isOpenEmbedding)) I ≅
      (U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj
        (SheafOfModules.free (R := (structureSheafRing X).over U) I) :=
  SheafOfModules.mapFreeIso (U.sheafOfModulesEquivOver (structureSheafRing X)).functor I
    (U.sheafOfModulesEquivOverUnit (structureSheafRing X))

/-- 08BL's retract on the slice site over `U`, transported to the restricted ringed space. -/
def restrictOverRetract (U : Opens X.carrier)
    (F : SheafOfModules.{u} (structureSheafRing X)) (I : Type u)
    (ρ : Retract (F.over U) (SheafOfModules.free (R := (structureSheafRing X).over U) I)) :
    Retract ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U))
      (SheafOfModules.free (R := structureSheafRing (X.restrict U.isOpenEmbedding)) I) :=
  (ρ.map (U.sheafOfModulesEquivOver (structureSheafRing X)).functor).trans
    ⟨(restrictOverFreeIso U I).inv, (restrictOverFreeIso U I).hom,
      (restrictOverFreeIso U I).inv_hom_id⟩

variable (U : Opens X.carrier) (F : SheafOfModules.{u} (structureSheafRing X)) (I : Type u)
  [Finite I]

/-- **A sheaf of modules which restricts on `U` to a retract of a finite free sheaf of modules
is, on the ringed space `U`, the sheaf associated to a finite projective module over
`𝒪_X(U)`.** This is the hypothesis Stacks 08BL supplies and the conclusion the determinant
argument of Stacks 0FJN consumes.

The statement is on the *restricted ringed space* `U`, not on the slice site over `U`:
construction (3) of Stacks 01BH is defined only for a ringed space, so `ℱ_M` cannot be written
on the slice site at all without transporting it back. This is also the spelling of Stacks 01BK,
`Stacks.AssociatedSheaf.exists_open_associatedSheaf_iso`. The slice-site form is
`exists_associatedSheaf_iso_of_retract_free_over`. -/
theorem exists_associatedSheaf_iso_of_retract_free
    (ρ : Retract (F.over U) (SheafOfModules.free (R := (structureSheafRing X).over U) I)) :
    ∃ M : ModuleCat.{u} ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
      Module.Finite ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
      Module.Projective ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
      Nonempty ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U) ≅
        associatedSheaf (X.restrict U.isOpenEmbedding)
          (RingHom.id ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M) :=
  ⟨(globalSectionsFunctor.{u, u} (X.restrict U.isOpenEmbedding)
      (RingHom.id ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)))).obj
      ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U)),
    moduleFinite_globalSections (X.restrict U.isOpenEmbedding) I
      ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U))
      (restrictOverRetract U F I ρ),
    moduleProjective_globalSections (X.restrict U.isOpenEmbedding) I
      ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U))
      (restrictOverRetract U F I ρ),
    ⟨(associatedSheafGlobalSectionsIso (X.restrict U.isOpenEmbedding) I
      ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U))
      (restrictOverRetract U F I ρ)).symm⟩⟩

/-- **The slice-site form of `exists_associatedSheaf_iso_of_retract_free`**: the restriction of
`F` to the slice site over `U` is the sheaf associated to a finite projective `𝒪_X(U)`-module,
carried back along the equivalence of Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver`. This is the form the descent of invertibility
along a covering consumes, since `Stacks.InvertibleLocallyFree.InvertibleIsLocal` is stated at
`M.over (X i)`. -/
theorem exists_associatedSheaf_iso_of_retract_free_over
    (ρ : Retract (F.over U) (SheafOfModules.free (R := (structureSheafRing X).over U) I)) :
    ∃ M : ModuleCat.{u} ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
      Module.Finite ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
      Module.Projective ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
      Nonempty (F.over U ≅ (U.sheafOfModulesEquivOver (structureSheafRing X)).inverse.obj
        (associatedSheaf (X.restrict U.isOpenEmbedding)
          (RingHom.id ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M)) := by
  obtain ⟨M, hfin, hproj, ⟨e⟩⟩ := exists_associatedSheaf_iso_of_retract_free U F I ρ
  exact ⟨M, hfin, hproj, ⟨(U.sheafOfModulesEquivOver (structureSheafRing X)).unitIso.app _ ≪≫
    (U.sheafOfModulesEquivOver (structureSheafRing X)).inverse.mapIso e⟩⟩

/-- **A sheaf of modules which is locally a direct summand of a finite free module is, near every
point, the sheaf associated to a finite projective module.** -/
theorem exists_open_associatedSheaf_iso_of_isLocallyFiniteFreeSummand
    (hF : Stacks.SheafOfModules.IsLocallyFiniteFreeSummand X F) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat.{u} ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
        Module.Finite ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
        Module.Projective ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
        Nonempty ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U) ≅
          associatedSheaf (X.restrict U.isOpenEmbedding)
            (RingHom.id ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M) := by
  obtain ⟨U, hxU, n, ⟨ρ⟩⟩ := hF x
  exact ⟨U, hxU, exists_associatedSheaf_iso_of_retract_free U F (ULift.{u} (Fin n)) ρ⟩

/-- **Stacks 08BL in the form the determinant argument of Stacks 0FJN consumes it.** A flat sheaf
of modules of finite presentation on a ringed space is, on a neighbourhood `U` of every point,
the sheaf associated to a finite projective module over `𝒪_X(U)`. -/
theorem exists_open_associatedSheaf_iso_of_isFlat [F.IsFinitePresentation]
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F)
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ M : ModuleCat.{u} ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)),
        Module.Finite ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
        Module.Projective ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)) M ∧
        Nonempty ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (F.over U) ≅
          associatedSheaf (X.restrict U.isOpenEmbedding)
            (RingHom.id ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))) M) :=
  exists_open_associatedSheaf_iso_of_isLocallyFiniteFreeSummand F
    (Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation F hF) x

end Open

section SplitMono

variable {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- **Construction (3) of Stacks 01BH carries a direct summand to a subsheaf.** The comparison
of the associated sheaves of a split inclusion of modules is a split monomorphism, hence a
monomorphism.

Splitness is not a convenience here, and construction (3) does *not* carry an arbitrary
injection of modules to a monomorphism of sheaves. `ℱ_M` is base change `M ↦ 𝒪_X(V) ⊗_R M`
followed by sheafification; sheafification is exact, but base change along `R → 𝒪_X(V)` carries
an injection to an injection only when the injection splits or `𝒪_X(V)` is flat over `R`. On
stalks, where monomorphy of a morphism of sheaves of modules is detected, the map in question is
`𝒪_x ⊗_R M' → 𝒪_x ⊗_R M` by `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`, and there
is no reason for that to be injective. So a consumer wanting `ℱ_{M'}` to be a subsheaf of `ℱ_M`
must exhibit `M'` as a direct summand of `M`, which is what this lemma consumes. -/
lemma isSplitMono_associatedSheafFunctor_map {M N : ModuleCat.{u} R} (ρ : Retract M N) :
    IsSplitMono ((associatedSheafFunctor.{u, u} X α).map ρ.i) :=
  IsSplitMono.mk' ⟨(associatedSheafFunctor.{u, u} X α).map ρ.r,
    (ρ.map (associatedSheafFunctor.{u, u} X α)).retract⟩

/-- Construction (3) carries a split inclusion of modules to a monomorphism of sheaves of
modules. See `isSplitMono_associatedSheafFunctor_map` for why the inclusion must split. -/
lemma mono_associatedSheafFunctor_map {M N : ModuleCat.{u} R} (ρ : Retract M N) :
    Mono ((associatedSheafFunctor.{u, u} X α).map ρ.i) :=
  have := isSplitMono_associatedSheafFunctor_map X α ρ
  inferInstance

end SplitMono

end Stacks.AssociatedSheaf

end
