module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The extensions by zero of the structure sheaves generate

Let `C` be a small site, `J` a topology on it and `O` a sheaf of rings on `C`. Every sheaf
of `O`-modules `M` is a quotient of a direct sum of the modules `j_{U!}O_U`, one summand for
each section of `M` over each object `U` of the site. This is part (3) of Stacks Tag 03EW;
part (1), the presheaf-level statement, is
`Stacks.SheafOfModules.FlatResolution.exists_epi_from_coproduct_extension`.

## Main definitions

* `SheafOfModules.overSections`: the section of `M` over the slice site over `U` obtained by
  restricting a section of `M` over `U` along the structure maps.
* `SheafOfModules.extensionByZeroGen`: the tautological generating section of `j_{U!}O_U`
  over `U`.
* `SheafOfModules.fromExtensionByZero`: the map `j_{U!}O_U ⟶ M` attached to a section of `M`
  over `U`, namely the one sending the tautological section to it.
* `SheafOfModules.fromGenerators`: the map onto `M` from the direct sum of its generators.

## Main results

* `SheafOfModules.fromExtensionByZero_val_app_gen`: `fromExtensionByZero` really does send
  the tautological generating section to the prescribed section. This is the whole content
  of the construction, and the reason `fromGenerators` is an epimorphism.
* `SheafOfModules.exists_epi_from_coproduct_extensionByZero`: every sheaf of `O`-modules is a
  quotient of a direct sum of modules `j_{U!}O_U`.
* `SheafOfModules.extensionByZeroIsoSheafifiedFreeYoneda`: `j_{U!}O_U` **is** the sheafification
  of the free presheaf of modules on the representable at `U`. The Stacks 03EV development
  asserts this identification in its module docstring and does not state it, supplying
  `Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_of_iso_freeYoneda` as an escape hatch
  instead; here it is stated, which turns 03EV part (1) plus 03ET into flatness of `j_{U!}O_U`
  as a sheaf of modules.

## Implementation notes

A map `j_{U!}O_U ⟶ M` is, by the adjunction `extensionByZeroAdjunction`, the same as a map
`O_U ⟶ j_U^*M` of sheaves of `O.over U`-modules, and such a map is by
`SheafOfModules.unitHomEquiv` the same as a global section of `j_U^*M`, that is a section of
`M` over the whole slice site. The slice `Over U` has a terminal object `Over.mk (𝟙 U)`, so a
section of `M` over `U` determines one, by restricting along the structure map of each object
of the slice; that is `overSections`. Running this chain backwards and evaluating at the
terminal object is `fromExtensionByZero_val_app_gen`, and it is proved by evaluating the
adjunction identity `homEquiv f = unit ≫ j_U^* f` rather than by unfolding either equivalence:
the restriction `(j_U^*f).val.app (op W)` is `f.val.app (op W.left)` definitionally, so at the
terminal object it is `f.val.app (op U)` with no rewriting.

Surjectivity is checked on the underlying presheaves of modules, where it is the statement
that the summand at a section hits that section, and then transported to the sheaf level by
`epi_of_epi_val`. Faithfulness of `SheafOfModules.forget` is enough for that transport,
because the cancellation is on the target side; no local surjectivity is needed.

Everything is stated at a single universe `u` for site, ring and modules, as forced by
`ExtensionByZero.lean` — see its implementation notes.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

section Unit

variable {D : Type u} [SmallCategory.{u} D] {K : GrothendieckTopology D}
  {R : Sheaf K RingCat.{u}}

/-- A morphism out of `unit R` is recovered from the image of `1` in each degree. -/
lemma unitHomEquiv_symm_val_app_one (N : SheafOfModules.{u} R) (t : N.sections) (X : Dᵒᵖ) :
    ((unitHomEquiv N).symm t).val.app X (1 : R.obj.obj X) = t.val X :=
  (unitHomEquiv_apply_coe N ((unitHomEquiv N).symm t) X).symm.trans
    (congrArg (fun (r : N.sections) ↦ r.val X) ((unitHomEquiv N).apply_symm_apply t))

end Unit

section Restriction

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{u})

/-- **The section of `M` over the slice site over `U` determined by a section of `M` over
`U`**: restrict along the structure map of each object of `Over U`. -/
noncomputable def overSections (M : SheafOfModules.{u} O) (U : C) (s : M.val.obj (op U)) :
    (M.over U).sections :=
  PresheafOfModules.sectionsMk (fun V ↦ M.val.map V.unop.hom.op s) (fun V W f ↦ by
    change M.val.map f.unop.left.op (M.val.map V.unop.hom.op s) = M.val.map W.unop.hom.op s
    rw [← PresheafOfModules.map_comp_apply]
    exact M.val.congr_map_apply
      (by simpa only [op_comp] using congrArg Quiver.Hom.op f.unop.w) s)

/-- At the terminal object of the slice, `overSections` gives back the section it came
from. -/
lemma overSections_eval_id (M : SheafOfModules.{u} O) (U : C) (s : M.val.obj (op U)) :
    (overSections O M U s).val (op (Over.mk (𝟙 U))) = s := by
  change M.val.map (𝟙 U).op s = s
  exact (M.val.congr_map_apply op_id s).trans
    (CategoryTheory.congr_fun (M.val.map_id (op U)) s)

/-- **A section of `M` over the slice site over `U` is the same thing as a section of `M`
over `U`**: the slice has a terminal object `Over.mk (𝟙 U)`, and a compatible family is
determined by its value there. -/
noncomputable def overSectionsEquiv (M : SheafOfModules.{u} O) (U : C) :
    M.val.obj (op U) ≃ (M.over U).sections where
  toFun := overSections O M U
  invFun t := t.val (op (Over.mk (𝟙 U)))
  left_inv := overSections_eval_id O M U
  right_inv t := by
    apply Subtype.ext
    funext V
    have h := t.property (Over.homMk V.unop.hom (by simp) :
      V.unop ⟶ Over.mk (𝟙 U)).op
    change M.val.map V.unop.hom.op (t.val (op (Over.mk (𝟙 U)))) = t.val V at h
    exact h

/-- A morphism of sheaves of modules whose underlying morphism of presheaves of modules is
an epimorphism is itself an epimorphism: `forget` is faithful, which suffices because the
cancellation is on the target side. -/
lemma epi_of_epi_val {M N : SheafOfModules.{u} O} (p : M ⟶ N) [Epi p.val] : Epi p where
  left_cancellation {_} _ _ hfg := (forget O).map_injective
    ((cancel_epi p.val).1 (congrArg Hom.val hfg))

end Restriction

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u})

/-- **The tautological generating section of `j_{U!}O_U` over `U`**: the image of `1` under
the unit of the adjunction `j_{U!} ⊣ j_U^*`, read at the terminal object of the slice. -/
noncomputable def extensionByZeroGen (U : C) :
    ((extensionByZero.{u, u, u, u} O U).obj (unit (O.over U))).val.obj (op U) :=
  (((extensionByZeroAdjunction.{u, u, u, u} O U).unit.app (unit (O.over U))).val.app
    (op (Over.mk (𝟙 U)))) (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U))))

/-- **The map `j_{U!}O_U ⟶ M` attached to a section of `M` over `U`.** -/
noncomputable def fromExtensionByZero (M : SheafOfModules.{u} O) (U : C)
    (s : M.val.obj (op U)) : (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ⟶ M :=
  ((extensionByZeroAdjunction.{u, u, u, u} O U).homEquiv _ _).symm
    ((unitHomEquiv _).symm (overSections O M U s))

/-- **`fromExtensionByZero` sends the tautological generating section to the prescribed
one.** -/
lemma fromExtensionByZero_val_app_gen (M : SheafOfModules.{u} O) (U : C)
    (s : M.val.obj (op U)) :
    (fromExtensionByZero O M U s).val.app (op U) (extensionByZeroGen O U) = s := by
  have h0 : (extensionByZeroAdjunction.{u, u, u, u} O U).homEquiv _ _
      (fromExtensionByZero O M U s) =
      (unitHomEquiv (M.over U)).symm (overSections O M U s) :=
    ((extensionByZeroAdjunction.{u, u, u, u} O U).homEquiv _ _).apply_symm_apply _
  rw [Adjunction.homEquiv_unit] at h0
  have h' := congrArg
    (fun (φ : unit (O.over U) ⟶ (overFunctor O U).obj M) ↦
      φ.val.app (op (Over.mk (𝟙 U)))
        (1 : (O.over U).obj.obj (op (Over.mk (𝟙 U))))) h0
  dsimp only at h'
  rw [unitHomEquiv_symm_val_app_one, overSections_eval_id] at h'
  exact h'

/-- **`j_{U!}O_U` corepresents `M ↦ M(U)`.** Composing the adjunction `j_{U!} ⊣ j_U^*`,
`unitHomEquiv` and `overSectionsEquiv`, a map `j_{U!}O_U ⟶ M` is the same thing as a section
of `M` over `U`; `fromExtensionByZero` is this bijection read in one direction. -/
noncomputable def fromExtensionByZeroEquiv (M : SheafOfModules.{u} O) (U : C) :
    M.val.obj (op U) ≃ ((extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ⟶ M) :=
  (overSectionsEquiv O M U).trans ((unitHomEquiv (M.over U)).symm.trans
    (((extensionByZeroAdjunction.{u, u, u, u} O U).homEquiv _ _).symm))

/-- The bijection `fromExtensionByZeroEquiv` sends a section `s` to `fromExtensionByZero O M U s`.
-/
lemma fromExtensionByZeroEquiv_apply (M : SheafOfModules.{u} O) (U : C)
    (s : M.val.obj (op U)) :
    fromExtensionByZeroEquiv O M U s = fromExtensionByZero O M U s := rfl

/-- **Evaluating at the tautological generating section is a bijection
`(j_{U!}O_U ⟶ M) ≃ M(U)`.** It is the inverse of `fromExtensionByZeroEquiv`, by
`fromExtensionByZero_val_app_gen`. -/
lemma bijective_val_app_gen (M : SheafOfModules.{u} O) (U : C) :
    Function.Bijective (fun φ : (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ⟶ M ↦
      φ.val.app (op U) (extensionByZeroGen O U)) := by
  have h : (fun φ : (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ⟶ M ↦
      φ.val.app (op U) (extensionByZeroGen O U))
      = (fromExtensionByZeroEquiv O M U).symm := by
    funext φ
    conv_lhs => rw [← (fromExtensionByZeroEquiv O M U).apply_symm_apply φ]
    exact fromExtensionByZero_val_app_gen O M U _
  exact h ▸ (fromExtensionByZeroEquiv O M U).symm.bijective

section SheafifiedFree

/-- The identity morphism of the underlying presheaf of rings of `O` is locally injective. -/
instance isLocallyInjective_id : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
  Presheaf.isLocallyInjective_of_injective J _ (fun _ _ _ h ↦ h)

/-- The identity morphism of the underlying presheaf of rings of `O` is locally surjective. -/
instance isLocallySurjective_id : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
  Presheaf.isLocallySurjective_of_surjective J _ (fun _ x ↦ ⟨x, rfl⟩)

/-- The sheafification of the free presheaf of modules on the representable at `U`. -/
@[sga "4 II 6.8"]
noncomputable def sheafifiedFreeYoneda (U : C) : SheafOfModules.{u} O :=
  (PresheafOfModules.sheafification (𝟙 O.obj)).obj
    ((PresheafOfModules.free O.obj).obj (yoneda.obj U))

/-- The sheafified free presheaf on the representable at `U` also corepresents `M ↦ M(U)`:
sheafification is a left adjoint and the free presheaf on a representable corepresents
evaluation. -/
@[sga "3 I 3.1.2.1" "more general"]
noncomputable def sheafifiedFreeYonedaEquiv (M : SheafOfModules.{u} O) (U : C) :
    (sheafifiedFreeYoneda O U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 O.obj)).trans
    PresheafOfModules.freeYonedaEquiv

/-- Reading off the generating section is natural in the target. Both bijections in play are
exactly that, so this is `rfl`. -/
lemma sheafifiedFreeYonedaEquiv_comp {M N : SheafOfModules.{u} O} {U : C}
    (ψ : sheafifiedFreeYoneda O U ⟶ M) (φ : M ⟶ N) :
    sheafifiedFreeYonedaEquiv O N U (ψ ≫ φ)
      = φ.val.app (op U) (sheafifiedFreeYonedaEquiv O M U ψ) := rfl

/-- The comparison map from the sheafified free presheaf on the representable at `U` to
`j_{U!}O_U`: the one carrying the canonical generator to the tautological one. -/
noncomputable def freeYonedaToExtensionByZero (U : C) :
    sheafifiedFreeYoneda O U ⟶ (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) :=
  (sheafifiedFreeYonedaEquiv O _ U).symm (extensionByZeroGen O U)

/-- **`j_{U!}O_U` is the sheafification of the free presheaf of modules on the representable
at `U`.** Both corepresent `M ↦ M(U)` and the comparison matches the two generators, so it
is an isomorphism by Yoneda. -/
@[sga "4 IV 11.3.3" "special case"]
instance isIso_freeYonedaToExtensionByZero (U : C) :
    IsIso (freeYonedaToExtensionByZero O U) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  have key : ∀ φ : (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ⟶ M,
      sheafifiedFreeYonedaEquiv O M U (freeYonedaToExtensionByZero O U ≫ φ)
        = φ.val.app (op U) (extensionByZeroGen O U) := by
    intro φ
    rw [sheafifiedFreeYonedaEquiv_comp,
      show sheafifiedFreeYonedaEquiv O _ U (freeYonedaToExtensionByZero O U)
        = extensionByZeroGen O U from
          (sheafifiedFreeYonedaEquiv O _ U).apply_symm_apply _]
  have h : (fun φ : (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ⟶ M ↦
        freeYonedaToExtensionByZero O U ≫ φ)
      = (sheafifiedFreeYonedaEquiv O M U).symm ∘
        fun φ ↦ φ.val.app (op U) (extensionByZeroGen O U) :=
    funext fun φ ↦ (sheafifiedFreeYonedaEquiv O M U).eq_symm_apply.2 (key φ)
  rw [h]
  exact (sheafifiedFreeYonedaEquiv O M U).symm.bijective.comp (bijective_val_app_gen O M U)

/-- **`j_{U!}O_U` is the sheafification of the free presheaf of modules on the representable
at `U`.** -/
@[sga "4 IV 11.3.3" "special case"]
noncomputable def extensionByZeroIsoSheafifiedFreeYoneda (U : C) :
    (extensionByZero.{u, u, u, u} O U).obj (unit (O.over U)) ≅ sheafifiedFreeYoneda O U :=
  (asIso (freeYonedaToExtensionByZero O U)).symm

end SheafifiedFree

/-- The sections of `M`, indexing one copy of `j_{U!}O_U` for each section over each `U`. -/
abbrev Elements (M : SheafOfModules.{u} O) : Type u := Σ X : C, M.val.obj (op X)

/-- The family of generators `j_{U!}O_U`, one for each section of `M`. -/
noncomputable def generatorFamily (M : SheafOfModules.{u} O) :
    Elements O M → SheafOfModules.{u} O :=
  fun i ↦ (extensionByZero.{u, u, u, u} O i.1).obj (unit (O.over i.1))

/-- The canonical map onto `M` from the direct sum of its generators. -/
noncomputable def fromGenerators (M : SheafOfModules.{u} O) :
    (∐ generatorFamily O M) ⟶ M :=
  Sigma.desc (fun i ↦ fromExtensionByZero O M i.1 i.2)

/-- `fromGenerators` is surjective on sections: the summand at a section hits it. -/
lemma epi_fromGenerators_val (M : SheafOfModules.{u} O) : Epi (fromGenerators O M).val := by
  refine PresheafOfModules.epi_of_surjective ?_
  rintro ⟨V⟩ x
  refine ⟨(Sigma.ι (generatorFamily O M) ⟨V, x⟩).val.app (op V)
    (extensionByZeroGen O V), ?_⟩
  change ((Sigma.ι (generatorFamily O M) ⟨V, x⟩ ≫ fromGenerators O M).val.app (op V))
    (extensionByZeroGen O V) = x
  rw [show Sigma.ι (generatorFamily O M) ⟨V, x⟩ ≫ fromGenerators O M =
    fromExtensionByZero O M V x from Sigma.ι_comp_desc _ _]
  exact fromExtensionByZero_val_app_gen O M V x

/-- The canonical map `fromGenerators O M` onto `M` from the direct sum of its generators is an
epimorphism. -/
instance epi_fromGenerators (M : SheafOfModules.{u} O) : Epi (fromGenerators O M) :=
  have := epi_fromGenerators_val O M
  epi_of_epi_val O _

/-- **Every sheaf of `O`-modules is a quotient of a direct sum of extensions by zero
`j_{U!}O_U` of the structure sheaves of slices.** The sum is indexed by the sections of `M`,
the summand attached to a section over `U` being `j_{U!}O_U`, and the map sends the
tautological generating section of that summand to the section. -/
@[stacks 03EW "part (3)"]
theorem exists_epi_from_coproduct_extensionByZero (M : SheafOfModules.{u} O) :
    ∃ (ι : Type u) (U : ι → C)
      (π : (∐ fun i ↦ (extensionByZero.{u, u, u, u} O (U i)).obj (unit (O.over (U i)))) ⟶ M),
        Epi π :=
  ⟨Elements O M, fun i ↦ i.1, fromGenerators O M, epi_fromGenerators O M⟩

end SheafOfModules

end
