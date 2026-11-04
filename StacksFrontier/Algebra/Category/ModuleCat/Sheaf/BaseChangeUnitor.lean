module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsAdjunction

/-!
# The base-change unitor

Let `α : R ⟶ R'` be a morphism of (pre)sheaves of rings and let `L` be a left adjoint of
restriction of scalars along `α`. Informally `L` is `R' ⊗_R -`, and the *base-change unitor* is the
canonical isomorphism `L (unit R) ≅ unit R'`, that is, `R' ⊗_R R ≅ R'` read on the free rank-one
module `unit`. It is constructed for an arbitrary left adjoint of restriction of scalars, with no
hypothesis on the site, no commutativity and no smallness.

## Main definitions

* `Stacks.PresheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit α`: the canonical morphism
  `unit R ⟶ (restrictScalars α).obj (unit R')` of presheaves of modules, namely `α` itself read
  as a map of modules. It is the unique morphism sending the unit section to the unit section.
* `Stacks.PresheafOfModules.ChangeOfRings.unitComparison α adj`: its adjoint transpose
  `L (unit R) ⟶ unit R'`, and `baseChangeUnitor α adj` the same morphism as an isomorphism.
* `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit`, `unitComparison`,
  `baseChangeUnitor`: the same constructions for sheaves of modules.
* `Stacks.SheafOfModules.ChangeOfRings.extendScalarsBaseChangeUnitor` and
  `Stacks.NoncommChangeOfRings.Presheaf.extendScalarsBaseChangeUnitor`: the unitor at the
  extension of scalars of `ExtendScalarsAdjunction.lean`, respectively at the objectwise
  noncommutative extension of scalars of `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/NoncommBaseChange.lean`.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.isIso_unitComparison` and
  `Stacks.SheafOfModules.ChangeOfRings.isIso_unitComparison`: the comparison morphism is an
  isomorphism, for any left adjoint `L` of restriction of scalars.
* `Stacks.SheafOfModules.ChangeOfRings.extendScalarsFreeIso`: extension of scalars carries the
  free sheaf of modules on a type `I` to the free sheaf of modules on `I`, for an arbitrary `I`.
* `Stacks.SheafOfModules.ChangeOfRings.extendScalarsGeneratingSections`: a family of generating
  sections of `M` indexed by `I` gives a family of generating sections of `R' ⊗_R M` indexed by
  the *same* `I`; in particular finiteness of the family is preserved.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
-/

@[expose] public section

open CategoryTheory

universe v u v' u'

namespace Stacks.PresheafOfModules.ChangeOfRings

open _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')

/-- The unit section of the restriction of scalars of `unit R'`: the global section of `R'`
given by `1` over every object. -/
noncomputable def restrictScalarsUnitSection :
    ((restrictScalars.{u} α).obj (unit R')).sections :=
  sectionsMk (fun X ↦ (1 : R'.obj X)) (fun {_ _} f ↦ (R'.map f).hom.map_one)

/-- The canonical morphism `unit R ⟶ (restrictScalars α).obj (unit R')` of presheaves of
modules: it is `α` itself, read as a map of modules, and is characterised as the unique
morphism carrying the unit section to the unit section. -/
noncomputable def unitToRestrictScalarsUnit :
    unit R ⟶ (restrictScalars.{u} α).obj (unit R') :=
  (unitHomEquiv _).symm (restrictScalarsUnitSection α)

/-- `unitToRestrictScalarsUnit α` sends the unit of `R.obj X` to the unit of `R'.obj X`. -/
lemma unitToRestrictScalarsUnit_app_one (X : Cᵒᵖ) :
    Hom.app (unitToRestrictScalarsUnit α) X (1 : R.obj X) = (1 : R'.obj X) :=
  congrArg (fun s ↦ sections.eval s X)
    ((unitHomEquiv ((restrictScalars.{u} α).obj (unit R'))).apply_symm_apply
      (restrictScalarsUnitSection α))

/-- Restriction of scalars does not change the global sections of a presheaf of modules, since it
does not change its underlying presheaf of abelian groups: the identity equivalence between the
global sections of `M` and those of its restriction of scalars. -/
def restrictScalarsSectionsEquiv (M : PresheafOfModules.{u} R') :
    M.sections ≃ ((restrictScalars.{u} α).obj M).sections := Equiv.refl _

/-- The image of a section `s` under `restrictScalarsSectionsEquiv α M` has the same value as `s`
at every object. -/
lemma restrictScalarsSectionsEquiv_val (M : PresheafOfModules.{u} R') (s : M.sections)
    (X : Cᵒᵖ) : (restrictScalarsSectionsEquiv α M s).val X = s.val X := rfl

variable {L : PresheafOfModules.{u} R ⥤ PresheafOfModules.{u} R'}
  (adj : L ⊣ restrictScalars.{u} α)

/-- The base-change comparison morphism `L (unit R) ⟶ unit R'`, for any left adjoint `L` of
restriction of scalars along `α`: the adjoint transpose of `unitToRestrictScalarsUnit α`.
Informally it is the map `R' ⊗_R R ⟶ R'`, `b ⊗ a ↦ b · α a`. -/
noncomputable def unitComparison : L.obj (unit R) ⟶ unit R' :=
  (adj.homEquiv _ _).symm (unitToRestrictScalarsUnit α)

/-- The adjoint transpose of `unitComparison α adj` is `unitToRestrictScalarsUnit α`. -/
lemma homEquiv_unitComparison :
    adj.homEquiv (unit R) (unit R') (unitComparison α adj) = unitToRestrictScalarsUnit α :=
  (adj.homEquiv _ _).apply_symm_apply _

/-- Composing with the comparison morphism is, under the adjunction bijection and
corepresentability of global sections, the identity of `M.sections`. -/
lemma unitComparison_comp (M : PresheafOfModules.{u} R') (g : unit R' ⟶ M) :
    unitComparison α adj ≫ g =
      (adj.homEquiv _ M).symm
        (((restrictScalars.{u} α).obj M).unitHomEquiv.symm
          (restrictScalarsSectionsEquiv α M (M.unitHomEquiv g))) := by
  apply (adj.homEquiv _ M).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right, homEquiv_unitComparison]
  apply (((restrictScalars.{u} α).obj M).unitHomEquiv).injective
  rw [Equiv.apply_symm_apply]
  apply sections_ext
  intro X
  rw [restrictScalarsSectionsEquiv_val]
  show Hom.app ((restrictScalars.{u} α).map g) X
      (Hom.app (unitToRestrictScalarsUnit α) X (1 : R.obj X)) = Hom.app g X (1 : R'.obj X)
  rw [unitToRestrictScalarsUnit_app_one]
  rfl

/-- For any left adjoint `L` of restriction of scalars along a morphism `α : R ⟶ R'` of presheaves
of rings, the base-change comparison morphism is an isomorphism: `L` carries the free rank-one
module over `R` to the free rank-one module over `R'`. -/
instance isIso_unitComparison : IsIso (unitComparison α adj) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  have h : (fun (x : unit R' ⟶ M) ↦ unitComparison α adj ≫ x) =
      (adj.homEquiv _ M).symm ∘ ((restrictScalars.{u} α).obj M).unitHomEquiv.symm ∘
        restrictScalarsSectionsEquiv α M ∘ M.unitHomEquiv :=
    funext (unitComparison_comp α adj M)
  rw [h]
  exact (adj.homEquiv _ M).symm.bijective.comp
    ((((restrictScalars.{u} α).obj M).unitHomEquiv.symm.bijective).comp
      ((restrictScalarsSectionsEquiv α M).bijective.comp M.unitHomEquiv.bijective))

/-- The base-change unitor for presheaves of modules: `R' ⊗_R R ≅ R'`. -/
noncomputable def baseChangeUnitor : L.obj (unit R) ≅ unit R' := asIso (unitComparison α adj)

/-- The underlying morphism of `baseChangeUnitor α adj` is `unitComparison α adj`. -/
@[simp]
lemma baseChangeUnitor_hom : (baseChangeUnitor α adj).hom = unitComparison α adj := rfl

end Stacks.PresheafOfModules.ChangeOfRings

namespace Stacks.NoncommChangeOfRings.Presheaf

open _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')

/-- The base-change unitor for the objectwise noncommutative extension of scalars: the
canonical map `R'(X) ⊗_{R(X)} R(X) ⟶ R'(X)` is an isomorphism of presheaves of modules. -/
noncomputable def extendScalarsBaseChangeUnitor :
    (extendScalars.{u} α).obj (unit R) ≅ unit R' :=
  Stacks.PresheafOfModules.ChangeOfRings.baseChangeUnitor α (extendScalarsAdjunction.{u} α)

end Stacks.NoncommChangeOfRings.Presheaf

namespace Stacks.SheafOfModules.ChangeOfRings

open _root_.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- The unit section of the restriction of scalars of `unit R'`: the global section of `R'`
given by `1` over every object. -/
noncomputable def restrictScalarsUnitSection :
    ((restrictScalars.{u} α).obj (unit R')).sections :=
  PresheafOfModules.sectionsMk (fun X ↦ (1 : R'.obj.obj X))
    (fun {_ _} f ↦ (R'.obj.map f).hom.map_one)

/-- The canonical morphism `unit R ⟶ (restrictScalars α).obj (unit R')` of sheaves of modules:
it is `α` itself, read as a map of modules, and is characterised as the unique morphism
carrying the unit section to the unit section. -/
noncomputable def unitToRestrictScalarsUnit :
    unit R ⟶ (restrictScalars.{u} α).obj (unit R') :=
  (unitHomEquiv _).symm (restrictScalarsUnitSection α)

/-- `unitToRestrictScalarsUnit α` sends the unit of `R.obj.obj X` to the unit of `R'.obj.obj X`. -/
lemma unitToRestrictScalarsUnit_val_app_one (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (unitToRestrictScalarsUnit α).val X (1 : R.obj.obj X) =
      (1 : R'.obj.obj X) :=
  Stacks.PresheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_app_one α.hom X

/-- Restriction of scalars does not change the global sections of a sheaf of modules: the identity
equivalence between the global sections of `M` and those of its restriction of scalars. -/
def restrictScalarsSectionsEquiv (M : SheafOfModules.{u} R') :
    M.sections ≃ ((restrictScalars.{u} α).obj M).sections := Equiv.refl _

/-- The image of a section `s` under `restrictScalarsSectionsEquiv α M` has the same value as `s`
at every object. -/
lemma restrictScalarsSectionsEquiv_val (M : SheafOfModules.{u} R') (s : M.sections) (X : Cᵒᵖ) :
    (restrictScalarsSectionsEquiv α M s).val X = s.val X := rfl

variable {L : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R'}
  (adj : L ⊣ restrictScalars.{u} α)

/-- The base-change comparison morphism `L (unit R) ⟶ unit R'`, for any left adjoint `L` of
restriction of scalars along a morphism `α : R ⟶ R'` of sheaves of rings: the adjoint transpose
of `unitToRestrictScalarsUnit α`. Informally it is `R' ⊗_R R ⟶ R'`. -/
noncomputable def unitComparison : L.obj (unit R) ⟶ unit R' :=
  (adj.homEquiv _ _).symm (unitToRestrictScalarsUnit α)

/-- The adjoint transpose of `unitComparison α adj` is `unitToRestrictScalarsUnit α`. -/
lemma homEquiv_unitComparison :
    adj.homEquiv (unit R) (unit R') (unitComparison α adj) = unitToRestrictScalarsUnit α :=
  (adj.homEquiv _ _).apply_symm_apply _

/-- Composing with the comparison morphism is, under the adjunction bijection and
corepresentability of global sections, the identity of `M.sections`. -/
lemma unitComparison_comp (M : SheafOfModules.{u} R') (g : unit R' ⟶ M) :
    unitComparison α adj ≫ g =
      (adj.homEquiv _ M).symm
        (((restrictScalars.{u} α).obj M).unitHomEquiv.symm
          (restrictScalarsSectionsEquiv α M (M.unitHomEquiv g))) := by
  apply (adj.homEquiv _ M).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right, homEquiv_unitComparison]
  apply (((restrictScalars.{u} α).obj M).unitHomEquiv).injective
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro X
  rw [restrictScalarsSectionsEquiv_val]
  show PresheafOfModules.Hom.app ((restrictScalars.{u} α).map g).val X
      (PresheafOfModules.Hom.app (unitToRestrictScalarsUnit α).val X (1 : R.obj.obj X)) =
    PresheafOfModules.Hom.app g.val X (1 : R'.obj.obj X)
  rw [unitToRestrictScalarsUnit_val_app_one]
  rfl

/-- For any left adjoint `L` of restriction of scalars along a morphism `α : R ⟶ R'` of sheaves
of rings, the base-change comparison morphism is an isomorphism: `L` carries the free rank-one
sheaf of modules over `R` to the free rank-one sheaf of modules over `R'`. -/
instance isIso_unitComparison : IsIso (unitComparison α adj) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  have h : (fun (x : unit R' ⟶ M) ↦ unitComparison α adj ≫ x) =
      (adj.homEquiv _ M).symm ∘ ((restrictScalars.{u} α).obj M).unitHomEquiv.symm ∘
        restrictScalarsSectionsEquiv α M ∘ M.unitHomEquiv :=
    funext (unitComparison_comp α adj M)
  rw [h]
  exact (adj.homEquiv _ M).symm.bijective.comp
    ((((restrictScalars.{u} α).obj M).unitHomEquiv.symm.bijective).comp
      ((restrictScalarsSectionsEquiv α M).bijective.comp M.unitHomEquiv.bijective))

/-- The base-change unitor for sheaves of modules: `R' ⊗_R R ≅ R'`. -/
noncomputable def baseChangeUnitor : L.obj (unit R) ≅ unit R' := asIso (unitComparison α adj)

/-- The underlying morphism of `baseChangeUnitor α adj` is `unitComparison α adj`. -/
@[simp]
lemma baseChangeUnitor_hom : (baseChangeUnitor α adj).hom = unitComparison α adj := rfl

/-! ### The unitor at the extension of scalars of `ExtendScalarsAdjunction.lean` -/

section ExtendScalars

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(PresheafOfModules.restrictScalars.{u} α.hom).IsRightAdjoint]

/-- The base-change unitor for the extension of scalars of `ExtendScalarsAdjunction.lean`:
`R' ⊗_R R ≅ R'`. -/
noncomputable def extendScalarsBaseChangeUnitor :
    (extendScalars.{u} α).obj (unit R) ≅ unit R' :=
  baseChangeUnitor α (extendRestrictScalarsAdjunction.{u} α)

section Free

variable [HasSheafify J AddCommGrpCat.{u}]

/-- Extension of scalars carries free sheaves of modules to free sheaves of modules,
`R' ⊗_R R^{(I)} ≅ R'^{(I)}`, for an arbitrary index type `I` in the universe of the sections of
the sheaves of rings. -/
noncomputable def extendScalarsFreeIso (I : Type u) :
    free (R := R') I ≅ (extendScalars.{u} α).obj (free I) :=
  mapFreeIso _ I (extendScalarsBaseChangeUnitor α).symm

/-- A family of sections of `M` indexed by `I` which generates `M` gives a family of sections of
`R' ⊗_R M` indexed by the same `I` which generates `R' ⊗_R M`. -/
noncomputable def extendScalarsGeneratingSections {M : SheafOfModules.{u} R}
    (G : M.GeneratingSections) : ((extendScalars.{u} α).obj M).GeneratingSections :=
  G.map _ (extendScalarsBaseChangeUnitor α).symm

/-- The generating sections `extendScalarsGeneratingSections α G` are of finite type if `G` is. -/
instance {M : SheafOfModules.{u} R} (G : M.GeneratingSections) [G.IsFiniteType] :
    (extendScalarsGeneratingSections α G).IsFiniteType :=
  inferInstanceAs (GeneratingSections.IsFiniteType (G.map _ _))

end Free

end ExtendScalars

end Stacks.SheafOfModules.ChangeOfRings

end
