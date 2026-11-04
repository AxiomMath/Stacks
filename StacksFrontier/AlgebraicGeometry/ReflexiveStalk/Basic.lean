module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk

/-!
# Reflexivity is reflexivity of the stalks

Let `X` be a scheme and let `F` be an `𝒪_X`-module such that `F` and its dual `F^∨` are of
finite presentation.  At a point `x`, Tag 01CP identifies the stalk of `F^∨` with the
`𝒪_{X,x}`-dual of `M = F_x` and the stalk of `F^∨∨` with its double dual, and under those two
identifications the stalk of the canonical map `F ⟶ F^∨∨` **is** the algebraic evaluation map
`M ⟶ M^**`.  Consequently `F` is reflexive if and only if every stalk of `F` is a reflexive
module over the local ring at that point.  That is the equivalence of the first two conditions
of [Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3).

## Main results

* `dualStalkEquiv_germAt`: the germ formula for `dualStalkEquiv`, namely that it sends the germ
  of a local functional and the germ of a local section to the germ of the value.
* `dualStalkEquiv_stalkHom_toDoubleDual`: **the compatibility square.**  The stalk of
  `toDoubleDual F`, read through `dualStalkEquiv` at `F^∨` and at `F`, is evaluation.
* `dualEvalEquiv_stalkHom_toDoubleDual`: the same statement with the two identifications
  packaged into a single equivalence onto the double dual of the stalk, so that the stalk map is
  literally `Module.Dual.eval` conjugated by equivalences.
* `bijective_stalkHom_toDoubleDual_iff`: the stalk of the canonical map is bijective exactly
  when the stalk is a reflexive module.
* `isReflexive_iff_forall_modStalk`: **Tag 0AY3, conditions (1) and (2)**, for a module whose
  dual is of finite presentation.

## Implementation notes

The compatibility square is the one piece of Tag 0AY3 that the library did not already have:
`Stacks.AlgebraicGeometry.ReflexiveModules.dualStalkEquiv` is used elsewhere only through a
counting argument, and
`Stacks.AlgebraicGeometry.ReflexiveModules.modStalkEquivDualOfIsReflexive`
deliberately avoids the square by exhibiting the stalk as *some* dual rather than as its own
double dual.  It is proved here by a germ chase: both sides of the square are computed on germs
over a common open neighbourhood, where `dualStalkEquiv_germAt` turns each into a germ of a
value, and the two values agree by `toDoubleDual_val_app_apply`, which is the defining formula
for the canonical map.

`dualSheafHom_sectionsEquiv_app` records the small compatibility behind the `germ_apply` field
of Tag 01CP at the dual: a section of `F^∨` *is* a morphism of the restricted modules, and
`SheafHom.sectionsEquiv` recovers it unchanged.

The hypotheses are finite presentation of `F` and of `F^∨`, which is what Tag 01CP needs at the
two places it is applied; neither coherence nor local Noetherianity nor integrality is used
here.  `Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_tfae` supplies them from
coherence on a locally Noetherian scheme and adds the third condition of the tag.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-! ### Sections of the dual, as morphisms -/

/-- A local section of `F^∨` over `U` is a morphism `F|_U ⟶ 𝒪_U`, and the identification
`SheafHom.sectionsEquiv` of `dualSheafHom F` recovers it unchanged: its component at the
terminal object of the slice site over `U` is the section's own component there. -/
public theorem dualSheafHom_sectionsEquiv_app (F : X.Modules) (U : X.Opens)
    (s : Γ(dualSheaf F, U)) (m : Γ(F, U)) :
    (((dualSheafHom F).sectionsEquiv U s).val.app (op (Over.mk (𝟙 U)))).hom m
      = (s.app (op (Over.mk (𝟙 U)))).hom m := by
  have he : (SheafOfModules.fullyFaithfulForget ((structureSheaf X.sheaf).over U)).homEquiv
      (X := F.over U) (Y := (unitModule X).over U)
      ((dualSheafHom F).sectionsEquiv U s) = s :=
    Equiv.apply_symm_apply _ s
  exact congrArg (fun q => (q.app (op (Over.mk (𝟙 U)))).hom m) he

/-! ### The germ formula for the stalk of a dual -/

/-- **The germ formula for `dualStalkEquiv`.**  The identification of the stalk of `F^∨` with
the dual of the stalk of `F` sends the germ of a local functional, evaluated at the germ of a
local section, to the germ of the value `Stacks.AlgebraicGeometry.ReflexiveModules.evalAt` of
the functional at the section. -/
public theorem dualStalkEquiv_germAt (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (U : X.Opens) (hxU : x ∈ U) (s : Γ(dualSheaf F, U)) (m : Γ(F, U)) :
    dualStalkEquiv F x (germAt (dualSheaf F) U x hxU s) (germAt F U x hxU m)
      = ringGermAt X U x hxU (evalAt F s m) :=
  dualStalkEquiv_germ F x U hxU s m

/-! ### The compatibility square -/

/-- **The stalk of the canonical map to the double dual is evaluation.**  Read through the
identifications of Tag 01CP at `F^∨` and at `F`, the stalk at `x` of `toDoubleDual F` sends the
germ `m` to the functional `λ ↦ λ m` on the dual of the stalk.

This is the compatibility square underlying
[Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3). -/
public theorem dualStalkEquiv_stalkHom_toDoubleDual (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) (m : modStalk F x)
    (lam : modStalk (dualSheaf F) x) :
    dualStalkEquiv (dualSheaf F) x (stalkHom (toDoubleDual F) x m) lam
      = dualStalkEquiv F x lam m := by
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq F m
  obtain ⟨V, hxV, l, rfl⟩ := exists_germ_eq (dualSheaf F) lam
  have hxZ : x ∈ W ⊓ V := ⟨hxW, hxV⟩
  rw [← germAt_resLE F (inf_le_left (a := W) (b := V)) hxZ t,
    ← germAt_resLE (dualSheaf F) (inf_le_right (a := W) (b := V)) hxZ l]
  set Z : X.Opens := W ⊓ V with hZ
  set tZ := resLE F (inf_le_left (a := W) (b := V)) t with htZ
  set lZ := resLE (dualSheaf F) (inf_le_right (a := W) (b := V)) l with hlZ
  rw [stalkHom_germAt (toDoubleDual F) x Z hxZ tZ,
    dualStalkEquiv_germAt (dualSheaf F) x Z hxZ _ lZ,
    dualStalkEquiv_germAt F x Z hxZ lZ tZ]
  exact congrArg (ringGermAt X Z x hxZ) (toDoubleDual_val_app_apply F Z tZ lZ)

/-! ### Reflexivity of the stalk -/

/-- Tag 01CP's identification `dualStalkEquiv`, with its scalar ring and its two modules spelled
by `ringStalk` and `modStalk` rather than by `X.presheaf.stalk` and `F.presheaf.stalk`.  The two
spellings are definitionally equal but carry separately declared `Semiring` and `Module`
instances, so composing identifications across them needs the crossing to be made explicitly;
it is made here once, by ascription, and the statements below use this form throughout. -/
public noncomputable def dualModStalkEquiv (F : X.Modules) [F.IsFinitePresentation] (x : X) :
    modStalk (dualSheaf F) x ≃ₗ[ringStalk X.sheaf x]
      Module.Dual (ringStalk X.sheaf x) (modStalk F x) :=
  dualStalkEquiv F x

/-- `dualStalkEquiv_stalkHom_toDoubleDual` in the `ringStalk`/`modStalk` spelling. -/
public theorem dualModStalkEquiv_stalkHom_toDoubleDual (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) (m : modStalk F x)
    (lam : modStalk (dualSheaf F) x) :
    dualModStalkEquiv (dualSheaf F) x (stalkHom (toDoubleDual F) x m) lam
      = dualModStalkEquiv F x lam m :=
  dualStalkEquiv_stalkHom_toDoubleDual F x m lam

/-- The identification of the stalk of `F^∨∨` with the double `𝒪_{X,x}`-dual of the stalk of
`F`, obtained by applying Tag 01CP twice. -/
public noncomputable def dualEvalEquiv (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) :
    modStalk (dualSheaf (dualSheaf F)) x ≃ₗ[ringStalk X.sheaf x]
      Module.Dual (ringStalk X.sheaf x) (Module.Dual (ringStalk X.sheaf x) (modStalk F x)) :=
  (dualModStalkEquiv (dualSheaf F) x).trans (dualModStalkEquiv F x).symm.dualMap

/-- **Tag 0AY3's compatibility square, packaged.**  Composing the stalk of `toDoubleDual F`
with `dualEvalEquiv` gives the algebraic evaluation map of the stalk. -/
public theorem dualEvalEquiv_stalkHom_toDoubleDual (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) (m : modStalk F x) :
    dualEvalEquiv F x (stalkHom (toDoubleDual F) x m)
      = Module.Dual.eval (ringStalk X.sheaf x) (modStalk F x) m := by
  refine LinearMap.ext fun phi => ?_
  have h := dualModStalkEquiv_stalkHom_toDoubleDual F x m ((dualModStalkEquiv F x).symm phi)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

/-- **The stalk of the canonical map is bijective exactly when the stalk is reflexive.** -/
public theorem bijective_stalkHom_toDoubleDual_iff (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) :
    Function.Bijective (stalkHom (toDoubleDual F) x) ↔
      Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x) := by
  have hcomp : (dualEvalEquiv F x) ∘ (stalkHom (toDoubleDual F) x)
      = Module.Dual.eval (ringStalk X.sheaf x) (modStalk F x) :=
    funext (dualEvalEquiv_stalkHom_toDoubleDual F x)
  rw [← (dualEvalEquiv F x).bijective.of_comp_iff', hcomp]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.bijective_dual_eval'⟩

/-- The stalk of a reflexive module is a reflexive module over the local ring.  This is the
implication (1) ⟹ (2) of [Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3). -/
public theorem module_isReflexive_modStalk (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F) (x : X) :
    Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x) := by
  have hiso : IsIso (toDoubleDual F) := hF
  refine (bijective_stalkHom_toDoubleDual_iff F x).mp ?_
  refine Function.bijective_iff_has_inverse.mpr ⟨stalkHom (inv (toDoubleDual F)) x, fun a ↦ ?_,
    fun a ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← stalkHom_comp, IsIso.hom_inv_id, stalkHom_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← stalkHom_comp, IsIso.inv_hom_id, stalkHom_id, LinearMap.id_apply]

/-- A module whose every stalk is a reflexive module is reflexive.  This is the implication
(2) ⟹ (1) of [Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3), and needs no
hypothesis on `X` beyond the finite presentation that Tag 01CP uses. -/
public theorem isReflexive_of_forall_modStalk (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation]
    (h : ∀ x : X, Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x)) :
    IsReflexive F :=
  isIso_of_bijective_stalkHom _ fun x =>
    (bijective_stalkHom_toDoubleDual_iff F x).mpr (h x)

/-- **Stacks, Tag 0AY3, conditions (1) and (2).**  A module whose dual is of finite
presentation is reflexive if and only if all of its stalks are reflexive modules over the local
rings. -/
public theorem isReflexive_iff_forall_modStalk (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] :
    IsReflexive F ↔ ∀ x : X, Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x) :=
  ⟨fun hF => module_isReflexive_modStalk F hF, isReflexive_of_forall_modStalk F⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
