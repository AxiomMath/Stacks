module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.CategoryTheory.Abelian.Basic
public import StacksCore.CategoryTheory.Subobject.Basic
public import StacksCore.CategoryTheory.Subobject.Lattice
public import StacksCore.CategoryTheory.Subobject.Limits
import StacksCore.Tactic.StacksAttribute

/-! ## Subobjects in abelian categories: covering pairs, and the correspondence theorem.

For subobjects `A ≤ B` of an object `X` of an abelian category, the first part of this file
relates `B` covering `A` in `Subobject X` to simplicity of the quotient `B/A`. The second part
(`Ported from mathlib#41769`) is the calculus of `Subobject.exists f` and `Subobject.pullback f`
along an epimorphism `f`, ending in the correspondence theorem `cokernelOrderIso`.

## Relation to mathlib

**Everything in this file except the section `Own lemmas` at the end is temporary and is
expected to be deleted.** Upstream, this
material is being developed by mckoen in two pull requests:

* mathlib#41769 (`feat(CategoryTheory/Abelian/Subobject): correspondence theorem for
  subobjects in abelian categories`, open as of 2026-09-11) constructs
  `Abelian.Subobject.cokernelOrderIso (Y : Subobject X) : Subobject (cokernel Y.arrow) ≃o Set.Ici Y`
  from the image/preimage calculus along epimorphisms: `f(f⁻¹(Y')) = Y'`,
  `f⁻¹(f(X')) = X' ⊔ Ker f`, and `f(f⁻¹(Y')) = Y' ⊓ Im f` for arbitrary `f`. The section
  `Ported from mathlib#41769` below is a port of that pull request with the upstream names,
  statements and proofs, on top of the ports of mathlib#42757 and mathlib#42759 in
  `Stacks.CategoryTheory.Subobject.{MonoOver, Basic, Lattice, Limits}` and of the `Abelian/Basic`
  part of #41769 in `StacksCore.CategoryTheory.Abelian.Basic`. It is used for the strict morphisms
  of filtered objects of Stacks §12.19 (`StacksCore.CategoryTheory.Filtration.Strict`).
* mathlib#41424 (`feat(CategoryTheory/Abelian): subobjects in an abelian category form a
  modular lattice`, open as of 2026-09-15), which is stacked on #41769, derives from it
  `covBy_iff_cokernel_is_simple (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleSubobject (cokernel (A.ofLE B hAB))`,
  where `IsSimpleSubobject X` is a new class extending `IsSimpleOrder (Subobject X)`, and
  `IsModularLattice (Subobject A)`, after showing that abelian categories are regular
  (`Abelian.abelianRegular`). Of this, only the two instances `Abelian.abelianRegular` (in
  `StacksCore.CategoryTheory.Abelian.Basic`) and `IsModularLattice (Subobject A)` (the section
  `Ported from mathlib#41424` below) are ported, with the upstream statements and proofs; they
  are used for Stacks 0129 (`StacksCore.CategoryTheory.Filtration.Subquotient`).
  `IsSimpleSubobject`, `covBy_iff_cokernel_is_simple` and `cokernelSupIsoCokernelInf` are not
  ported.

`isSimpleOrder_subobject_cokernel_ofLE` below predates the port and proves only the
implication that Stacks 0FCJ needs, by a direct pullback argument: a subobject of `B/A` pulls
back to a subobject of `B` containing `A`, and `A ⋖ B` leaves it no room.

### What to do once the pull requests land

* Delete the section `Ported from mathlib#41769`; every name in it then resolves to the
  mathlib declaration. Do the same for the port sections of #42757 and #42759 in
  `Stacks.CategoryTheory.Subobject.{MonoOver, Basic, Lattice, Limits}` and for the
  `Ported from mathlib#41769` section of `StacksCore.CategoryTheory.Abelian.Basic`.
* Delete the section `Ported from mathlib#41424` below and `Abelian.abelianRegular` in
  `StacksCore.CategoryTheory.Abelian.Basic` (together with its import of
  `Mathlib.CategoryTheory.RegularCategory.Basic` if nothing else needs it); both names then
  resolve to the mathlib declarations.
* Delete `isSimpleOrder_subobject_cokernel_ofLE` and `simple_cokernel_ofLE`, and replace
  their uses in `StacksCore.CategoryTheory.Abelian.JordanHolder` by the forward direction of
  `covBy_iff_cokernel_is_simple`, converting `IsSimpleSubobject` to `Simple` with
  `simple_iff_subobject_isSimpleOrder`.
* The converse implication (`Simple (B/A) → A ⋖ B`) is deliberately **not** proved here,
  since 0FCJ does not use it; it arrives with #41424.

Note that mathlib#41445 (already merged, but not in our pinned revision) is *not* needed
for any of this. It is needed for Stacks 0FCK: it supplies
`instance [IsModularLattice X] : JordanHolderLattice X`, which together with the
`IsModularLattice (Subobject A)` instance of #41424 (now ported below) makes
`CompositionSeries.jordan_holder` applicable to subobject lattices.
-/

@[expose] public section

namespace CategoryTheory.Subobject

open Limits

variable {C : Type*} [Category* C] [Abelian C] {X : C}

/-- If `B` covers `A` in `Subobject X`, then the quotient `B/A` has exactly two subobjects.

Superseded by the forward direction of `covBy_iff_cokernel_is_simple` (mathlib#41424);
delete when that lands. -/
lemma isSimpleOrder_subobject_cokernel_ofLE {A B : Subobject X} (h : A ≤ B) (hcov : A ⋖ B) :
    IsSimpleOrder (Subobject (cokernel (Subobject.ofLE A B h))) := by
  set u := Subobject.ofLE A B h with hu
  set q := cokernel.π u with hq
  have huq : u ≫ q = 0 := cokernel.condition _
  have : Nontrivial (Subobject (cokernel u)) := by
    refine Subobject.nontrivial_of_not_isZero fun hz => hcov.lt.ne ?_
    have : Epi u := Abelian.epi_of_cokernel_π_eq_zero u (hz.eq_zero_of_tgt (cokernel.π u))
    have : IsIso u := isIso_of_mono_of_epi _
    calc A = (Subobject.map B.arrow).obj (Subobject.mk u) := (map_arrow_mk_ofLE h).symm
      _ = (Subobject.map B.arrow).obj ⊤ := by rw [Subobject.mk_eq_top_of_isIso]
      _ = B := map_arrow_top B
  refine ⟨fun Z => ?_⟩
  have : Epi (pullback.fst Z.arrow q) := Abelian.epi_pullback_of_epi_g Z.arrow q
  have hcond : pullback.fst Z.arrow q ≫ Z.arrow = pullback.snd Z.arrow q ≫ q :=
    pullback.condition
  have hle : Subobject.mk u ≤ Subobject.mk (pullback.snd Z.arrow q) :=
    Subobject.mk_le_mk_of_comm (pullback.lift 0 u (by simp [huq])) (pullback.lift_snd _ _ _)
  have h1 : A ≤ (Subobject.map B.arrow).obj (Subobject.mk (pullback.snd Z.arrow q)) :=
    calc A = (Subobject.map B.arrow).obj (Subobject.mk u) := (map_arrow_mk_ofLE h).symm
      _ ≤ _ := (Subobject.map B.arrow).monotone hle
  have h2 : (Subobject.map B.arrow).obj (Subobject.mk (pullback.snd Z.arrow q)) ≤ B :=
    calc (Subobject.map B.arrow).obj (Subobject.mk (pullback.snd Z.arrow q))
        ≤ (Subobject.map B.arrow).obj ⊤ := (Subobject.map B.arrow).monotone le_top
      _ = B := map_arrow_top B
  rcases hcov.eq_or_eq h1 h2 with hc | hc
  · -- the pullback is exactly `A`, so `Z` is zero
    left
    have hmk : Subobject.mk (pullback.snd Z.arrow q) = Subobject.mk u :=
      Subobject.map_obj_injective B.arrow (by rw [hc]; exact (map_arrow_mk_ofLE h).symm)
    have : IsIso (Subobject.ofMkLEMk u (pullback.snd Z.arrow q) hmk.ge) :=
      (Subobject.isoOfMkEqMk _ _ hmk.symm).isIso_hom
    have hfac : Subobject.ofMkLEMk u (pullback.snd Z.arrow q) hmk.ge ≫ pullback.snd Z.arrow q = u :=
      Subobject.ofMkLEMk_comp _
    have h0 : pullback.fst Z.arrow q ≫ Z.arrow = 0 := by
      rw [← cancel_epi (Subobject.ofMkLEMk u (pullback.snd Z.arrow q) hmk.ge), comp_zero,
        hcond, ← Category.assoc, hfac, huq]
    rw [← Subobject.mk_arrow Z, Subobject.mk_eq_bot_iff_zero]
    exact zero_of_epi_comp _ h0
  · -- the pullback is all of `B`, so `Z` is everything
    right
    have hmk : Subobject.mk (pullback.snd Z.arrow q) = ⊤ :=
      Subobject.map_obj_injective B.arrow (by rw [hc]; exact (map_arrow_top B).symm)
    have : IsIso (pullback.snd Z.arrow q) := (Subobject.isIso_iff_mk_eq_top _).mpr hmk
    have : Epi ((inv (pullback.snd Z.arrow q) ≫ pullback.fst Z.arrow q) ≫ Z.arrow) := by
      rw [Category.assoc, hcond, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp, hq]
      infer_instance
    have : Epi Z.arrow := epi_of_epi (inv (pullback.snd Z.arrow q) ≫ pullback.fst Z.arrow q) _
    have : IsIso Z.arrow := isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow Z

/-- If `B` covers `A` in `Subobject X`, then the quotient `B/A` is simple.

Superseded by the forward direction of `covBy_iff_cokernel_is_simple` (mathlib#41424),
modulo `simple_iff_subobject_isSimpleOrder`; delete when that lands. -/
lemma simple_cokernel_ofLE {A B : Subobject X} (h : A ≤ B) (hcov : A ⋖ B) :
    Simple (cokernel (Subobject.ofLE A B h)) :=
  haveI := isSimpleOrder_subobject_cokernel_ofLE h hcov
  simple_of_isSimpleOrder_subobject _

end CategoryTheory.Subobject

/-! ### Ported from mathlib#41769

**Everything below is temporary and is expected to be deleted**; see the file header. -/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace MonoOver

instance {X Y : C} (f : X ⟶ Y) [Epi f] (Y' : MonoOver Y) :
    IsIso ((existsPullbackAdj f).counit.app Y') := by
  let : Epi ((existsPullbackAdj f).counit.app Y').hom.left :=
    epi_of_epi_fac (factorThruImage_comp_existsPullbackAdj_counit_app_hom_left f Y')
  let : Mono ((existsPullbackAdj f).counit.app Y').hom.left := mono_of_mono_fac (MonoOver.w _)
  rw [isIso_iff_isIso_hom_left]
  apply isIso_of_mono_of_epi

/-- Pullback along an epimorphism in an abelian category is fully faithful.
Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def fullyFaithfulPullbackOfEpi {X Y : C} (f : X ⟶ Y) [Epi f] :
    (pullback f).FullyFaithful :=
  letI := NatIso.isIso_of_isIso_app (existsPullbackAdj f).counit
  (existsPullbackAdj f).fullyFaithfulROfIsIsoCounit

end MonoOver

namespace Abelian.Subobject

open CategoryTheory.Subobject

section

variable {X Y : C} (f : X ⟶ Y)

lemma imageSubobject_eq_kernelSubobject :
    imageSubobject f = kernelSubobject (cokernel.π f) :=
  mk_eq_mk_of_comm (Limits.image.ι f) (kernel.ι (cokernel.π f)) (imageIsoImage f).symm
    (by rw [Iso.symm_hom, imageIsoImage_inv, kernel.lift_ι])

lemma exists_eq_kernelSubobject (X' : Subobject X) :
    («exists» f).obj X' = kernelSubobject (cokernel.π (X'.arrow ≫ f)) := by
  rw [exists_eq_imageSubobject, ← imageSubobject_eq_kernelSubobject]

lemma pullback_eq_kernelSubobject (Y' : Subobject Y) :
    (Subobject.pullback f).obj Y' = kernelSubobject (f ≫ cokernel.π Y'.arrow) := by
  slice_lhs 0 1 => rw [← mk_arrow Y', ← imageSubobject_mono Y'.arrow,
    imageSubobject_eq_kernelSubobject, pullback_kernelSubobject]

lemma pullback_mk_eq_kernelSubobject {A : C} (g : A ⟶ Y) [Mono g] :
    (Subobject.pullback f).obj (Subobject.mk g) = kernelSubobject (f ≫ cokernel.π g) := by
  rw [← imageSubobject_mono, imageSubobject_eq_kernelSubobject, pullback_kernelSubobject]

theorem exists_pullback_eq_self_of_epi [Epi f] (Y' : Subobject Y) :
    («exists» f).obj ((Subobject.pullback f).obj Y') = Y' :=
  Quotient.inductionOn' Y' (fun _ ↦
    Quotient.sound ⟨asIso ((MonoOver.existsPullbackAdj f).counit.app _)⟩)

theorem pullback_le_pullback_iff_of_epi (Y₁ Y₂ : Subobject Y) [Epi f] :
    (Subobject.pullback f).obj Y₁ ≤ (Subobject.pullback f).obj Y₂ ↔ Y₁ ≤ Y₂ := by
  constructor
  · intro h
    rw [← exists_pullback_eq_self_of_epi f Y₁, ← exists_pullback_eq_self_of_epi f Y₂]
    exact («exists» f).monotone h
  · intro h
    exact (Subobject.pullback f).monotone h

lemma pullback_exists_eq_self_of_epi [Epi f] (X' : Subobject X) (h : kernelSubobject f ≤ X') :
    (Subobject.pullback f).obj ((«exists» f).obj X') = X' := by
  let d := epiDesc f (cokernel.π X'.arrow) (by
    rw [← kernelSubobject_arrow' f, ← ofLE_arrow h, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero])
  have : Epi d := epi_of_epi_fac (comp_epiDesc f (cokernel.π X'.arrow) _)
  have hX' : (Subobject.pullback f).obj (kernelSubobject d) = X' := by
    rw [pullback_mk_eq_kernelSubobject, ← comp_inv_factorThruCoimage d]
    simp only [← Category.assoc, d, comp_epiDesc, kernelSubobject_comp_mono]
    rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono, mk_arrow]
  rw [← hX', exists_pullback_eq_self_of_epi]

theorem pullback_exists_eq_sup (X' : Subobject X) :
    (Subobject.pullback f).obj ((«exists» f).obj X') = X' ⊔ kernelSubobject f := by
  rw [← imageSubobject_arrow_comp f, exists_comp, pullback_comp, exists_iso_map, pullback_map_self,
    kernelSubobject_comp_mono]
  let f' := (factorThruImageSubobject f)
  apply le_antisymm
  · rw [← pullback_exists_eq_self_of_epi f' (X' ⊔ kernelSubobject f') le_sup_right]
    exact (Subobject.pullback f').monotone ((«exists» f').monotone le_sup_left)
  · apply sup_le
    · exact (existsPullbackAdj f').gc.le_u_l X'
    · exact kernelSubobject_le_pullback f' _

theorem exists_pullback_eq_inf (Y' : Subobject Y) :
    («exists» f).obj ((Subobject.pullback f).obj Y') = Y' ⊓ imageSubobject f := by
  rw [← imageSubobject_arrow_comp f, exists_comp, Subobject.pullback_comp,
    exists_pullback_eq_self_of_epi, exists_pullback_eq_inf_of_mono, mk_arrow,
    imageSubobject_arrow_comp]

end

/-- For an epimorphism `f : X ⟶ Y`, there is an order-isomorphism between subobjects of `Y`
and subobjects of `X` containing `kernelSubobject f`.
Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def epiOrderIso {X Y : C} (f : X ⟶ Y) [Epi f] :
    Subobject Y ≃o Set.Ici (kernelSubobject f) where
  toFun p := ⟨(Subobject.pullback f).obj p, by
    rw [pullback_eq_kernelSubobject]
    exact kernelSubobject_comp_le f _⟩
  invFun q := («exists» f).obj q
  left_inv p := exists_pullback_eq_self_of_epi f p
  right_inv := fun ⟨q, hq⟩ ↦ SetCoe.ext (pullback_exists_eq_self_of_epi f q hq)
  map_rel_iff' := pullback_le_pullback_iff_of_epi ..

/-- The correspondence theorem for subobjects in an abelian category.
Ported from mathlib#41769; delete when the pin includes it. -/
noncomputable def cokernelOrderIso {X : C} (Y : Subobject X) :
    Subobject (cokernel Y.arrow) ≃o Set.Ici Y :=
  (epiOrderIso (cokernel.π Y.arrow)).trans (Set.orderIsoOfEq _ _
    (by rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono, mk_arrow]))

end Abelian.Subobject

/-! ### Ported from mathlib#41424

**Everything in this section is temporary and is expected to be deleted**; see the file header.
Upstream this instance lives in the new file `Mathlib/CategoryTheory/Abelian/JordanHolder.lean`
of mathlib#41424, anonymous and in `namespace CategoryTheory`; it is kept so here. -/

open Subobject Abelian.Subobject in
/-- The lattice of subobjects of an object in an abelian category is modular.
Ported from mathlib#41424; delete when the pin includes it. -/
instance (A : C) : IsModularLattice (Subobject A) where
  sup_inf_le_assoc_of_le := by
    intro X Y Z hXZ
    suffices (⟨(X ⊔ Y) ⊓ Z, Set.mem_Ici.2 (le_inf le_sup_left hXZ)⟩ : Set.Ici X) =
      ⟨X ⊔ Y ⊓ Z, Set.mem_Ici.2 le_sup_left⟩ from (congrArg Subtype.val this).le
    apply (cokernelOrderIso X).symm.injective
    have hs (W : Subobject A) (hW : W ∈ Set.Ici X) :
        (cokernelOrderIso X).symm ⟨W, hW⟩ = («exists» (cokernel.π X.arrow)).obj W :=
      rfl
    rw [hs, hs]
    have hZ : (Subobject.pullback _).obj ((«exists» _).obj Z) = Z :=
      congrArg Subtype.val ((cokernelOrderIso X).apply_symm_apply ⟨Z, hXZ⟩)
    have hqX : («exists» _).obj X = ⊥ := (cokernelOrderIso X).symm.map_bot
    slice_lhs 0 1 =>
      rw [← hZ, Regular.exists_inf_pullback_eq_exists_inf,
      (existsPullbackAdj (cokernel.π X.arrow)).gc.l_sup, hqX, bot_sup_eq,
      ← Regular.exists_inf_pullback_eq_exists_inf, hZ,
      ← bot_sup_eq ((«exists» (cokernel.π X.arrow)).obj (Y ⊓ Z)),
      ← (cokernelOrderIso X).symm.map_bot]
    exact (existsPullbackAdj _).gc.l_sup.symm

/-! ### Own lemmas -/

namespace Abelian.Subobject

open CategoryTheory.Subobject

/-- Pulling back subobjects along an epimorphism is injective, the dual of
`Subobject.map_obj_injective`: `f(f⁻¹(Y')) = Y'` for an epimorphism `f`. -/
theorem pullback_obj_injective_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    Function.Injective (Subobject.pullback f).obj :=
  Function.LeftInverse.injective (g := (Subobject.exists f).obj)
    (exists_pullback_eq_self_of_epi f)

/-- The modular law of `Subobject A` read through a morphism `n : Y ⟶ A`: for a subobject `F` of
`A` and a subobject `X'` of `Y`, `n⁻¹(F + n(X')) = n⁻¹(F) + X'`. Apply `n` to both sides: both
become `(F ⊓ Im n) ⊔ n(X')` by the modular law `sup_inf_assoc_of_le`, as `n(X') ≤ Im n`; pull
back again and absorb `Ker n ≤ n⁻¹(F)`. No hypothesis on `n`. -/
theorem pullback_sup_exists {Y A : C} (n : Y ⟶ A) (F : Subobject A) (X' : Subobject Y) :
    (Subobject.pullback n).obj (F ⊔ («exists» n).obj X') =
      (Subobject.pullback n).obj F ⊔ X' := by
  have hk : kernelSubobject n ≤ (Subobject.pullback n).obj F := kernelSubobject_le_pullback n F
  have key : («exists» n).obj ((Subobject.pullback n).obj (F ⊔ («exists» n).obj X')) =
      («exists» n).obj ((Subobject.pullback n).obj F ⊔ X') := by
    rw [exists_pullback_eq_inf, (existsPullbackAdj n).gc.l_sup, exists_pullback_eq_inf, sup_comm F,
      sup_inf_assoc_of_le _
        (((existsPullbackAdj n).gc.monotone_l le_top).trans (exists_obj_top n).le),
      sup_comm]
  have := congrArg (Subobject.pullback n).obj key
  rwa [pullback_exists_eq_sup, pullback_exists_eq_sup,
    sup_eq_left.2 (hk.trans ((Subobject.pullback n).monotone le_sup_left)),
    sup_eq_left.2 (hk.trans le_sup_left)] at this

/-- The modular law of `Subobject A` for a chain `X ⟶ Y ⟶ A` of monomorphisms `k`, `n`: for a
subobject `F` of `A`, `n⁻¹(F + X) = n⁻¹(F) + X` as subobjects of `Y`. This is the identity
`Y ∩ (F^pA + X) = (Y ∩ F^pA) + X` of the proof of Stacks 0129. -/
theorem pullback_sup_mk_comp_of_mono {X Y A : C} (k : X ⟶ Y) (n : Y ⟶ A) [Mono k] [Mono n]
    (F : Subobject A) :
    (Subobject.pullback n).obj (F ⊔ Subobject.mk (k ≫ n)) =
      (Subobject.pullback n).obj F ⊔ Subobject.mk k := by
  rw [← map_mk k n, ← exists_iso_map n, pullback_sup_exists]

/-- The lattice identity behind Stacks 0129: for `k : X ⟶ Y` and any `n : Y ⟶ A`, the image in
`Y/X = Coker k` of the preimage `n⁻¹(F)` of a subobject `F` of `A` is the preimage under
`Y/X ⟶ A/X` of the image of `F` in `A/X = Coker (k ≫ n)`. Pulling back along the epimorphism
`Y ⟶ Y/X` turns the two sides into `n⁻¹(F) + X` and `n⁻¹(F + X)`, which agree by
`pullback_sup_exists`. (For a monomorphism `n` the square `Y → A → A/X = Y → Y/X → A/X` is a
fibre product and this is also the Beck–Chevalley identity `IsPullback.exists_pullback` of
`StacksCore.CategoryTheory.Abelian.Images`; in general the square is not a fibre product, but the
identity persists.) -/
theorem exists_pullback_eq_pullback_exists {X Y A : C} (k : X ⟶ Y) (n : Y ⟶ A)
    (F : Subobject A) :
    («exists» (cokernel.π k)).obj ((Subobject.pullback n).obj F) =
      (Subobject.pullback (cokernel.map k (k ≫ n) (𝟙 X) n (by simp))).obj
        ((«exists» (cokernel.π (k ≫ n))).obj F) := by
  apply pullback_obj_injective_of_epi (cokernel.π k)
  rw [pullback_exists_eq_sup, ← imageSubobject_eq_kernelSubobject, ← pullback_comp,
    cokernel.π_desc, pullback_comp, pullback_exists_eq_sup, ← imageSubobject_eq_kernelSubobject,
    imageSubobject_comp_eq_exists, pullback_sup_exists]

/-! #### Transport of subquotients along an epimorphism and along a monomorphism

For an epimorphism `q : Y ⟶ E` and subobjects `X' ≤ Y'` of `E`, the composite
`q⁻¹(Y') ⟶ Y' ⟶ Y'/X'` is a cokernel of `q⁻¹(X') ⊆ q⁻¹(Y')`
(`isColimitPullbackπCokernelCofork`), so `q⁻¹(Y')/q⁻¹(X') ≅ Y'/X'`
(`cokernelOfLEPullbackIso`, induced by the restriction of `q`, itself an epimorphism:
`epi_pullbackπ`); for a monomorphism `n : Y ⟶ A` and `X₁ ≤ X₂` in `Y`, `n(X₂)/n(X₁) ≅ X₂/X₁`
(`cokernelOfLEMapIso`); `q⁻¹(⊥) = Ker q` is `Subobject.pullback_bot` (needs no abelianness,
so it lives in `StacksCore.CategoryTheory.Subobject.Limits`). These are the two transports
of the recursion step `E_{r+1} = Z_{r+1}/B_{r+1}` of Stacks 011N
(`StacksCore.Algebra.Homology.SpectralSequence.Tower`). -/

section Pullback

variable {Y E : C} (q : Y ⟶ E)

variable [Epi q]

/-- The restriction `q⁻¹(Y') ⟶ Y'` of an epimorphism `q` is an epimorphism. -/
instance epi_pullbackπ (Y' : Subobject E) : Epi (pullbackπ q Y') :=
  Abelian.epi_fst_of_isLimit _ _ (isPullback q Y').isLimit

/-- For an epimorphism `q : Y ⟶ E` and subobjects `X' ≤ Y'` of `E`, the composite
`q⁻¹(Y') ⟶ Y' ⟶ Y'/X'` is a cokernel of `q⁻¹(X') ⟶ q⁻¹(Y')`. -/
noncomputable def isColimitPullbackπCokernelCofork {X' Y' : Subobject E} (h : X' ≤ Y') :
    IsColimit (CokernelCofork.ofπ (f := ofLE _ _ ((Subobject.pullback q).monotone.imp h))
      (pullbackπ q Y' ≫ cokernel.π (ofLE X' Y' h))
      (by rw [ofLE_pullback_comp_pullbackπ_assoc q h, cokernel.condition, comp_zero])) := by
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {T} ψ hψ => ?_
  have hκ : kernel.ι (pullbackπ q Y') ≫ ψ = 0 := by
    have hF : ((Subobject.pullback q).obj X').Factors
        (kernel.ι (pullbackπ q Y') ≫ ((Subobject.pullback q).obj Y').arrow) :=
      pullback_factors q X' _ (by
        rw [Category.assoc, ← (isPullback q Y').w, kernel.condition_assoc, zero_comp]
        exact factors_zero)
    have hv : factorThru _ _ hF ≫ ofLE _ _ ((Subobject.pullback q).monotone.imp h) =
        kernel.ι (pullbackπ q Y') := by
      rw [← cancel_mono ((Subobject.pullback q).obj Y').arrow, Category.assoc, ofLE_arrow,
        factorThru_arrow]
    rw [← hv, Category.assoc, hψ, comp_zero]
  have hψ' : ofLE X' Y' h ≫ Abelian.epiDesc (pullbackπ q Y') ψ hκ = 0 := by
    rw [← cancel_epi (pullbackπ q X'), ← ofLE_pullback_comp_pullbackπ_assoc,
      Abelian.comp_epiDesc, hψ, comp_zero]
  exact ⟨cokernel.desc _ _ hψ', by simp⟩

/-- Transport of a subquotient along an epimorphism `q : Y ⟶ E`: for subobjects `X' ≤ Y'` of
`E`, `q⁻¹(Y')/q⁻¹(X') ≅ Y'/X'`. -/
noncomputable def cokernelOfLEPullbackIso {X' Y' : Subobject E} (h : X' ≤ Y') :
    cokernel (ofLE _ _ ((Subobject.pullback q).monotone.imp h)) ≅ cokernel (ofLE X' Y' h) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (isColimitPullbackπCokernelCofork q h)

/-- The transport `q⁻¹(Y')/q⁻¹(X') ≅ Y'/X'` is induced by the restriction of `q`. -/
@[reassoc (attr := simp)]
lemma π_cokernelOfLEPullbackIso_hom {X' Y' : Subobject E} (h : X' ≤ Y') :
    cokernel.π _ ≫ (cokernelOfLEPullbackIso q h).hom =
      pullbackπ q Y' ≫ cokernel.π (ofLE X' Y' h) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (isColimitPullbackπCokernelCofork q h) WalkingParallelPair.one

end Pullback

section Map

variable {Y A : C} (n : Y ⟶ A) [Mono n]

/-- Transport of a subquotient along a monomorphism `n : Y ⟶ A`: for subobjects `X₁ ≤ X₂` of
`Y`, `n(X₂)/n(X₁) ≅ X₂/X₁`. -/
noncomputable def cokernelOfLEMapIso {X₁ X₂ : Subobject Y} (h : X₁ ≤ X₂) :
    cokernel (ofLE _ _ ((map n).monotone.imp h)) ≅ cokernel (ofLE X₁ X₂ h) :=
  cokernel.mapIso _ _ (mapObjIso n X₁) (mapObjIso n X₂) (by
    rw [← cancel_mono (X₂.arrow ≫ n), Category.assoc, Category.assoc, ofLE_arrow_assoc,
      mapObjIso_hom_arrow, mapObjIso_hom_arrow, ofLE_arrow])

/-- The transport `n(X₂)/n(X₁) ≅ X₂/X₁` is induced by the identification `n(X₂) ≅ X₂`. -/
@[reassoc (attr := simp)]
lemma π_cokernelOfLEMapIso_hom {X₁ X₂ : Subobject Y} (h : X₁ ≤ X₂) :
    cokernel.π _ ≫ (cokernelOfLEMapIso n h).hom =
      (mapObjIso n X₂).hom ≫ cokernel.π (ofLE X₁ X₂ h) := by
  simp [cokernelOfLEMapIso]

end Map

end Abelian.Subobject

end CategoryTheory
