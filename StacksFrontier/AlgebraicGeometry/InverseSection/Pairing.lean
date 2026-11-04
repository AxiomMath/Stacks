module

public import StacksFrontier.AlgebraicGeometry.InverseSection.Reindex
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic

/-!
# Pairing a global section of an invertible module against its inverse power

Let `(X, 𝒪_X)` be a ringed space, `L` an invertible `𝒪_X`-module and `s` a global section of
`L`. Stacks Tag 01CY, in its "inverse section" clause, asks for a section `t` of `L ^⊗ (-1)`
over the nonvanishing open of `s` whose canonical pairing with `s` is `1`. This file builds the
map being asked about -- pairing against `s` -- as a single morphism of sheaves of modules
`L ^⊗ (-1) ⟶ 𝒪_X`, and proves the one elementary fact about it that the tag's proof needs:
**over every open inside the nonvanishing locus of `s`, the presheaf-level half of the pairing
is bijective.**

Everything is at the **ringed-space** spelling of Stacks Tag 01CY, the one at which the openness
and trivialization clauses are already proved, as
`Stacks.NonvanishingTrivialize.isOpen_nonvanishingLocus` and
`Stacks.NonvanishingTrivialize.isIso_over_nonvanishingOpen`.

## Main definitions

* `Stacks.InverseSection.powPre`: the `n`-th tensor power of `L`, as a presheaf of modules over
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`. This is a spelling device:
  Mathlib's monoidal structure on presheaves of modules is stated over
  `𝒪 ⋙ forget₂ CommRingCat RingCat`, and instance search will not unfold
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf` to find it.
* `Stacks.InverseSection.sectionHom`: the morphism `𝒪_X ⟶ L ^⊗ 1` determined by `s`, namely the
  morphism `SheafOfModules.unitHomEquiv.symm s` of the tag's statement followed by the
  identification of `L` with its first tensor power.
* `Stacks.InverseSection.tensorLeftSection`: **tensoring with `s` on the left**, the morphism of
  presheaves of modules `L ^⊗ (-1) ⟶ L ^⊗ 1 ⊗ L ^⊗ (-1)` sending `t` to `s ⊗ t`. It is built as
  the inverse of the left unitor followed by right whiskering with `sectionHom`, so that its
  naturality in the open set is the naturality of those two and needs no proof.
* `Stacks.InverseSection.pairingHom`: **pairing against `s`**, the morphism of sheaves of
  modules `L ^⊗ (-1) ⟶ 𝒪_X` sending `t` to the canonical pairing of `s` with `t`. It is
  `Stacks.InverseSection.tensorLeftSectionSheaf` -- that is, `tensorLeftSection` followed by the
  sheafification unit -- followed by `Stacks.InverseSection.tensorPowPairingIso`.
* `Stacks.InverseSection.valPre`: the underlying presheaf of modules of a sheaf of modules, at
  the spelling of the indexing presheaf of rings at which `⊗` is available. The same spelling
  device as `powPre`.
* `Stacks.InverseSection.tensorRightSection`: **tensoring with `s` on the right, for an
  arbitrary module in the first factor**, the morphism of presheaves of modules
  `M ⟶ M ⊗ L ^⊗ 1` sending `t` to `t ⊗ s`. Built from the right unitor and left whiskering, so
  that its naturality in the open set costs nothing.

## Main results

* `Stacks.InverseSection.bijective_tensorLeftSection_app`: **over every open `W` inside the
  nonvanishing open of `s`, the map `t ↦ s|_W ⊗ t` is a bijection from the sections of
  `L ^⊗ (-1)` over `W` to the sections of the presheaf tensor product.** This is the elementary
  content of the inverse-section clause, and the reason it is true is that over such a `W` the
  morphism `sectionHom` is bijective on sections -- multiplication by `s` is bijective there by
  `Stacks.NonvanishingTrivialize.bijective_smul` -- so that tensoring it with the identity is an
  isomorphism of modules, which the left unitor then identifies with the sections of
  `L ^⊗ (-1)`.
* `Stacks.InverseSection.pairingHom_val_app`: pairing against `s` is, on sections, exactly the
  composite that Stacks Tag 01CY's statement writes out.
* `Stacks.InverseSection.app_presheaf_map`: a morphism of presheaves of modules commutes with
  restriction of sections, at the spelling of restriction that lands in the sections.
* `Stacks.InverseSection.bijective_hom_app`: a component of an isomorphism of sheaves of modules
  is bijective on sections. Used for the three isomorphisms occurring in the pairing.
* `Stacks.InverseSection.bijective_tensorRightSection_app`: **for an arbitrary module `M`, the
  map `t ↦ t ⊗ s|_W` is a bijection from the sections of `M` over `W` to the sections of the
  objectwise tensor product `M ⊗ L ^⊗ 1`, for every open `W` inside the nonvanishing locus of
  `s`.** Same proof as `bijective_tensorLeftSection_app` with the factors in the other order:
  through the right unitor the map is the identity of `M` tensored with `sectionHom`, and over
  such a `W` that is an isomorphism of modules of sections.

## Implementation notes

The map `t ↦ s ⊗ t` is built as a morphism rather than as a bare function on sections, because
the whole proof of the tag needs its compatibility with restriction, and obtaining that from
`MonoidalCategory.whiskerRight` and `MonoidalCategory.leftUnitor` costs nothing while proving it
by hand costs a naturality square for the presheaf tensor product. Its sectionwise description
`tensorLeftSection_app` then holds by `rfl`, both of Mathlib's relevant component lemmas
(`PresheafOfModules.Monoidal.leftUnitor_inv_app` and
`PresheafOfModules.Monoidal.whiskerRight_app`) being `rfl`.

`Stacks.InverseSection.moduleSections` is the module structure on the sections of a presheaf of
modules over the sections of the structure sheaf, at the spelling `X.presheaf.obj (op U)` of the
latter and with the scalar presheaf spelled
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`. The analogous instance over
`structureSheaf X.sheaf` is `Stacks.NonvanishingTrivialize.moduleSections`; it is not usable
here, because the tensor powers are indexed by
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, which instance search does not
unfold. Without one of the two, the statement of the inverse-section clause does not elaborate at
all: the scalar ring of its tensor product has no `Module` instance on the sections of the first
tensor power.

No sectionwise description of `tensorPowOneIso`, of the addition isomorphism or of
`tensorPowZeroIso` is used anywhere. Only the fact that they are isomorphisms is used, through
`bijective_hom_app`. This is deliberate: those isomorphisms come from
`Stacks.SheafInternalHom.monoidalCategory`, which is a `LocalizedMonoidal` structure whose
unitors have no sectionwise formula.

## Generalization

`bijective_tensorRightSection_app` is the case `n = 1`, at the **objectwise** tensor product, of
the statement that `Γ(W, M) → Γ(W, M ⊗ L ^⊗ n)`, `t ↦ t ⊗ (sⁿ)|_W`, is bijective for an
arbitrary `M`. That statement holds for arbitrary `M` and arbitrary `n` at the *sheafified*
tensor product, as `Stacks.InverseSection.bijective_sectionPowerAction_app`: the `n`-th power of
`s` is `Stacks.SheafOfModules.sectionPowerHom`, and multiplication by it restricts to an
isomorphism of sheaves of modules on the open subspace `W` because the trivialization of
`Stacks.NonvanishingTrivialize.bijective_smul` does and because restriction commutes with the
tensor product naturally, by
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality_right`. Nothing in that route
uses a formula on sections, so the objectwise statement below is not what it is built from, and
no inclusion of nonvanishing loci `X_s ≤ X_{sⁿ}` is needed.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v₁ u₁ w₁ u

open CategoryTheory TopologicalSpace Opposite TensorProduct MonoidalCategory
open AlgebraicGeometry Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry.SheafOfModules (IsInvertible)

namespace Stacks.InverseSection

section Helper

/-- Applying a composite of morphisms of presheaves of modules to a section is applying the two
factors in turn. Stated for a general site because `PresheafOfModules.comp_app` has to be
combined with `ConcreteCategory.comp_apply` at explicit arguments: left to unification, the
middle object of the composite has to be guessed from the right-hand side, which is a
higher-order problem that does not terminate on the composites of this file. -/
theorem comp_app_apply {D : Type u₁} [Category.{v₁} D] {R : Dᵒᵖ ⥤ RingCat.{w₁}}
    {P Q S : PresheafOfModules.{w₁} R} (f : P ⟶ Q) (g : Q ⟶ S) (W : Dᵒᵖ) (x : P.obj W) :
    (f ≫ g).app W x = g.app W (f.app W x) :=
  (ConcreteCategory.congr_hom (PresheafOfModules.comp_app f g W) x).trans
    (ConcreteCategory.comp_apply (f.app W) (g.app W) x)

/-- A morphism of presheaves of modules commutes with restriction of sections. Stated at the
spelling `P.presheaf.map` of restriction, which lands in the sections themselves rather than in
the restricted-scalars wrapper that `PresheafOfModules.map` produces. -/
theorem app_presheaf_map {D : Type u₁} [Category.{v₁} D] {R : Dᵒᵖ ⥤ RingCat.{w₁}}
    {P Q : PresheafOfModules.{w₁} R} (f : P ⟶ Q) {W W' : Dᵒᵖ} (h : W ⟶ W') (x : P.obj W) :
    f.app W' (P.presheaf.map h x) = Q.presheaf.map h (f.app W x) :=
  NatTrans.naturality_apply ((PresheafOfModules.toPresheaf R).map f) h x

end Helper

section Sections

variable {X : RingedSpace.{u}}

/-- The module structure of the sections of a presheaf of modules over the sections of the
structure sheaf of a ringed space, at the spelling `X.presheaf.obj (op U)` of the latter and
with the scalar presheaf spelled `Stacks.SheafOfModules.TensorSheafification.structureSheaf`.
This is the instance the inverse-section clause of Stacks Tag 01CY needs in order to
elaborate. -/
noncomputable scoped instance moduleSections
    (P : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.sheaf.obj
      (structureSheaf X.sheaf).property).obj) (U : Opens X) :
    Module (X.presheaf.obj (op U)) (P.obj (op U)) := (P.obj (op U)).isModule

/-- A component of an isomorphism of sheaves of modules on a ringed space is bijective on
sections: evaluation at an open is a functor, and isomorphisms in `ModuleCat` are bijective. -/
theorem bijective_hom_app {M N : SheafOfModules.{u} (structureSheaf X.sheaf)} (i : M ≅ N)
    (W : Opens X) : Function.Bijective fun m : M.val.obj (op W) => i.hom.val.app (op W) m :=
  (ConcreteCategory.isIso_iff_bijective
    ((SheafOfModules.evaluation (structureSheaf X.sheaf) (op W)).map i.hom)).mp inferInstance

/-- Restriction of sections of the structure sheaf, read through `SheafOfModules.unit`, is
restriction in `X.presheaf`. -/
theorem unit_val_map {W W' : Opens X} (h : W' ⟶ W)
    (a : (SheafOfModules.unit (structureSheaf X.sheaf)).val.obj (op W)) :
    (SheafOfModules.unit (structureSheaf X.sheaf)).val.map h.op a = X.presheaf.map h.op a := rfl

/-- The unit section of the structure sheaf restricts to the unit section. -/
theorem unit_val_map_one {W W' : Opens X} (h : W' ⟶ W) :
    (SheafOfModules.unit (structureSheaf X.sheaf)).val.map h.op (1 : X.presheaf.obj (op W)) =
      (1 : X.presheaf.obj (op W')) :=
  PresheafOfModules.unit_map_one _ h.op

end Sections

section Pairing

open scoped Stacks.NonvanishingTrivialize
open AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u}} (L : SheafOfModules.{u} (structureSheaf X.sheaf))
  [IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L]

/-- The `n`-th tensor power of `L`, with its type spelled over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`. Mathlib's monoidal structure
on presheaves of modules is stated over a composite with `forget₂ CommRingCat RingCat`, and
instance search does not unfold `Stacks.SheafOfModules.TensorSheafification.structureSheaf` to
that shape; this reducible wrapper puts the tensor powers in the category where `⊗`, `▷` and `λ_`
are available. -/
@[reducible] noncomputable def powPre (n : ℤ) :
    PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj) :=
  (tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L n).val

/-- The morphism from the structure sheaf to the first tensor power of `L` determined by a
global section `s`: the morphism `SheafOfModules.unitHomEquiv.symm s` named in the statement of
Stacks Tag 01CY, followed by the identification of `L` with `L ^⊗ 1`. -/
noncomputable def sectionHom (s : L.sections) :
    SheafOfModules.unit (structureSheaf X.sheaf) ⟶
      tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1 :=
  L.unitHomEquiv.symm s ≫ (tensorPowOneIso X.sheaf.obj (structureSheaf X.sheaf).property L).inv

/-- The value of `sectionHom` at `1` is the section `s` itself, read in the first tensor power.
This is the element that the statement of Stacks Tag 01CY pairs against. -/
theorem sectionHom_one (s : L.sections) (W : Opens X) :
    (sectionHom L s).val.app (op W) (1 : X.presheaf.obj (op W)) =
      (tensorPowOneIso X.sheaf.obj (structureSheaf X.sheaf).property L).inv.val.app (op W)
        (s.eval (op W)) := by
  have h : (sectionHom L s).val.app (op W) (1 : X.presheaf.obj (op W)) =
      (tensorPowOneIso X.sheaf.obj (structureSheaf X.sheaf).property L).inv.val.app (op W)
        ((L.unitHomEquiv.symm s).val.app (op W) (1 : X.presheaf.obj (op W))) := rfl
  rw [h, Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app, one_smul]

/-- **Tensoring with `s` on the left**: the morphism of presheaves of modules
`L ^⊗ (-1) ⟶ L ^⊗ 1 ⊗ L ^⊗ (-1)` sending a section `t` to `s ⊗ t`. Built from the left unitor
and right whiskering so that compatibility with restriction is inherited rather than proved. -/
noncomputable def tensorLeftSection (s : L.sections) :
    powPre L (-1) ⟶
      (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1)) ((powPre L (-1)))) :=
  (λ_ (powPre L (-1))).inv ≫
    whiskerRight (C := PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj))
      (sectionHom L s).val (powPre L (-1))

/-- Tensoring with `s` on the left does send `t` to `s ⊗ t`. -/
theorem tensorLeftSection_app (s : L.sections) (W : Opens X) (t : (powPre L (-1)).obj (op W)) :
    (tensorLeftSection L s).app (op W) t =
      (sectionHom L s).val.app (op W) (1 : X.presheaf.obj (op W)) ⊗ₜ[X.presheaf.obj (op W)] t :=
  rfl

/-- **Tensoring with `s` on the left, at the sheaf level**: the morphism of sheaves of modules
`L ^⊗ (-1) ⟶ L ^⊗ 1 ⊗ L ^⊗ (-1)` into the *sheafified* tensor product, obtained from
`tensorLeftSection` by following it with the sheafification unit. A morphism of sheaves of
modules is nothing but a morphism of the underlying presheaves, so no sheaf condition is used
here. -/
noncomputable def tensorLeftSectionSheaf (s : L.sections) :
    tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
            (forget₂ CommRingCat RingCat) ((structureSheaf X.sheaf).property)⟩).obj
          ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L 1))).obj
        ((tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1)))) :=
  ⟨tensorLeftSection L s ≫
    toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
      ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1)) ((powPre L (-1)))))⟩

/-- The underlying morphism of presheaves of `tensorLeftSectionSheaf` is the composite it is
built from. Recorded separately because the two sides are definitionally but not syntactically
equal: the restriction of scalars along an identity morphism of rings has to be inserted, and
elaboration puts it in a different place on the two sides. -/
theorem tensorLeftSectionSheaf_val (s : L.sections) :
    (tensorLeftSectionSheaf L s).val =
      tensorLeftSection L s ≫
        toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
          ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1)) ((powPre L (-1))))) := rfl

/-- On sections, `tensorLeftSectionSheaf` forms the elementary tensor `s|_W ⊗ t` and pushes it
into the sheafified tensor product. -/
theorem tensorLeftSectionSheaf_val_app (s : L.sections) (W : Opens X)
    (t : (powPre L (-1)).obj (op W)) :
    (tensorLeftSectionSheaf L s).val.app (op W) t =
      (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
          ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
            ((powPre L (-1)))))).app (op W)
        ((sectionHom L s).val.app (op W) (1 : X.presheaf.obj (op W))
          ⊗ₜ[X.presheaf.obj (op W)] t) := by
  rw [tensorLeftSectionSheaf_val]
  exact comp_app_apply (tensorLeftSection L s)
    (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
      ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1)) ((powPre L (-1)))))) (op W) t

/-- On sections, `tensorLeftSectionSheaf` is `tensorLeftSection` followed by the sheafification
unit. -/
theorem tensorLeftSectionSheaf_val_app' (s : L.sections) (W : Opens X)
    (t : (powPre L (-1)).obj (op W)) :
    (tensorLeftSectionSheaf L s).val.app (op W) t =
      (toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
          ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
            ((powPre L (-1)))))).app (op W)
        ((tensorLeftSection L s).app (op W) t) := by
  rw [tensorLeftSectionSheaf_val_app, tensorLeftSection_app]

/-- **Pairing against `s`**: the morphism of sheaves of modules `L ^⊗ (-1) ⟶ 𝒪_X` that sends a
section `t` to the canonical pairing of `s` with `t`. It is `tensorLeftSectionSheaf` followed by
the canonical pairing `tensorPowPairingIso`. -/
noncomputable def pairingHom (s : L.sections) :
    tensorPow X.sheaf.obj (structureSheaf X.sheaf).property L (-1) ⟶
      SheafOfModules.unit (structureSheaf X.sheaf) :=
  tensorLeftSectionSheaf L s ≫
    (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom

/-- Pairing against `s` is, on the sections over an open `W`, exactly the composite written out
in the statement of the inverse-section clause of Stacks Tag 01CY: form the elementary tensor of
`s|_W` with `t`, push it into the sheafified tensor product, and apply the canonical pairing. -/
theorem pairingHom_val (s : L.sections) :
    (pairingHom L s).val = (tensorLeftSectionSheaf L s).val ≫
      (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val := rfl

/-- Pairing against `s` is, on the sections over an open `W`, exactly the composite written out
in the statement of the inverse-section clause of Stacks Tag 01CY. -/
theorem pairingHom_val_app (s : L.sections) (W : Opens X) (t : (powPre L (-1)).obj (op W)) :
    (pairingHom L s).val.app (op W) t =
      (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app (op W)
        ((toSheafify X.sheaf.obj (structureSheaf X.sheaf).property
            ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((powPre L 1))
              ((powPre L (-1)))))).app (op W)
          ((sectionHom L s).val.app (op W) (1 : X.presheaf.obj (op W))
            ⊗ₜ[X.presheaf.obj (op W)] t)) := by
  rw [← tensorLeftSectionSheaf_val_app, pairingHom_val]
  exact comp_app_apply (tensorLeftSectionSheaf L s).val
    (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val (op W) t

/-- Pairing against `s`, in two steps: form `s ⊗ t` in the sheafified tensor product, then
apply the canonical pairing. -/
theorem pairingHom_val_app' (s : L.sections) (W : Opens X) (t : (powPre L (-1)).obj (op W)) :
    (pairingHom L s).val.app (op W) t =
      (tensorPowPairingIso X.sheaf.obj (structureSheaf X.sheaf).property L).hom.val.app (op W)
        ((tensorLeftSectionSheaf L s).val.app (op W) t) := by
  rw [pairingHom_val_app, tensorLeftSectionSheaf_val_app]

/-! ### Tensoring an arbitrary module with a nonvanishing section -/

/-- The underlying presheaf of modules of a sheaf of modules, with its type spelled over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`. The same spelling device as
`Stacks.InverseSection.powPre`: it puts the module in the category where `⊗`, `◁` and `ρ_` are
available. -/
@[reducible] noncomputable def valPre (M : SheafOfModules.{u} (structureSheaf X.sheaf)) :
    PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj) :=
  M.val

/-- **Tensoring with `s` on the right**: the morphism of presheaves of modules
`M ⟶ M ⊗ L ^⊗ 1` sending a section `t` to `t ⊗ s`, for an *arbitrary* module `M` in the first
factor. It is built as the inverse of the right unitor followed by left whiskering with
`Stacks.InverseSection.sectionHom`, so that its naturality in the open set is the naturality of
those two and needs no proof. -/
noncomputable def tensorRightSection (M : SheafOfModules.{u} (structureSheaf X.sheaf))
    (s : L.sections) :
    valPre M ⟶ (PresheafOfModules.tensorObj (O := X.sheaf.obj) ((valPre M)) ((powPre L 1))) :=
  (ρ_ (valPre M)).inv ≫
    whiskerLeft (C := PresheafOfModules.{u} (structureRingPresheaf X.sheaf.obj))
      (valPre M) (sectionHom L s).val

/-- Tensoring with `s` on the right does send `t` to `t ⊗ s`. -/
theorem tensorRightSection_app (M : SheafOfModules.{u} (structureSheaf X.sheaf))
    (s : L.sections) (W : Opens X) (t : (valPre M).obj (op W)) :
    (tensorRightSection L M s).app (op W) t =
      t ⊗ₜ[X.presheaf.obj (op W)]
        (sectionHom L s).val.app (op W) (1 : X.presheaf.obj (op W)) :=
  rfl

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **Over every open inside the nonvanishing locus of `s`, the morphism determined by `s` is
bijective on sections.** This is `Stacks.NonvanishingTrivialize.bijective_smul` -- the
elementary content of the trivialization clause of Stacks Tag 01CY -- composed with the
identification of `L` with its first tensor power. -/
theorem bijective_sectionHom (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    Function.Bijective fun a : X.presheaf.obj (op W) => (sectionHom L s).val.app (op W) a := by
  have h1 : Function.Bijective
      fun a : X.presheaf.obj (op W) => (L.unitHomEquiv.symm s).val.app (op W) a := by
    have hfun : (fun a : X.presheaf.obj (op W) => (L.unitHomEquiv.symm s).val.app (op W) a) =
        fun a : X.presheaf.obj (op W) => a • s.eval (op W) :=
      funext fun a => Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app s W a
    rw [hfun]
    exact Stacks.NonvanishingTrivialize.bijective_smul s hW
  exact (bijective_hom_app
    (tensorPowOneIso X.sheaf.obj (structureSheaf X.sheaf).property L).symm W).comp h1

/-- Tensoring on the left with the image of `1` under a bijective linear map `f : R → N` is a
bijection `M → N ⊗ M`. -/
private theorem bijective_tmul_left {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : R →ₗ[R] N) (hf : Function.Bijective f) :
    Function.Bijective fun t : M => f 1 ⊗ₜ[R] t :=
  ((TensorProduct.lid R M).symm.trans
    (TensorProduct.congr (LinearEquiv.ofBijective f hf) (LinearEquiv.refl R M))).bijective

/-- Tensoring on the right with the image of `1` under a bijective linear map `f : R → N` is a
bijection `M → M ⊗ N`. -/
private theorem bijective_tmul_right {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : R →ₗ[R] N) (hf : Function.Bijective f) :
    Function.Bijective fun t : M => t ⊗ₜ[R] f 1 :=
  ((TensorProduct.rid R M).symm.trans
    (TensorProduct.congr (LinearEquiv.refl R M) (LinearEquiv.ofBijective f hf))).bijective

/-- **The map `t ↦ s ⊗ t` is bijective over every open inside the nonvanishing locus.** Read
through the left unitor it is `sectionHom` tensored with the identity, and over such an open
`sectionHom` is an isomorphism of modules of sections by `bijective_sectionHom`. -/
theorem bijective_tensorLeftSection_app (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    Function.Bijective fun t : (powPre L (-1)).obj (op W) =>
      (tensorLeftSection L s).app (op W) t := by
  exact bijective_tmul_left (R := X.presheaf.obj (op W)) ((sectionHom L s).val.app (op W)).hom
    (bijective_sectionHom L s hW)

/-- **For an arbitrary module `M`, the map `t ↦ t ⊗ s` is bijective on the sections over every
open inside the nonvanishing locus of `s`.** Read through the right unitor it is the identity of
`M` tensored with `Stacks.InverseSection.sectionHom`, and over such an open `sectionHom` is an
isomorphism of modules of sections by `Stacks.InverseSection.bijective_sectionHom`, so the
tensor product of the two is an isomorphism of modules. This is the case `n = 1` of the
statement that `Γ(W, M) → Γ(W, M ⊗ L ^⊗ n)`, `t ↦ t ⊗ (sⁿ)|_W`, is bijective, at the
*objectwise* tensor product; `Stacks.InverseSection.bijective_tensorLeftSection_app` is the case
`M = L ^⊗ (-1)` with the factors in the other order. -/
theorem bijective_tensorRightSection_app (M : SheafOfModules.{u} (structureSheaf X.sheaf))
    (s : L.sections) {W : Opens X}
    (hW : W ≤ Stacks.NonvanishingTrivialize.nonvanishingOpen X L s) :
    Function.Bijective fun t : (valPre M).obj (op W) =>
      (tensorRightSection L M s).app (op W) t := by
  exact bijective_tmul_right (R := X.presheaf.obj (op W)) ((sectionHom L s).val.app (op W)).hom
    (bijective_sectionHom L s hW)

end Pairing

end Stacks.InverseSection

end
