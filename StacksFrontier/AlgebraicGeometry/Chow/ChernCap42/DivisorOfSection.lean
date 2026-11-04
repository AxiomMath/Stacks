module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.PicardGroup
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk

/-!
# Nonzero sections of an invertible module on an integral scheme

Let `X` be an integral scheme and let `L` be an invertible `𝒪_X`-module. The Stacks Project
computes the Weil divisor of a nonzero global section `s ∈ Γ(X, L)` as the cycle of the zero
scheme of `s` (Tag 02SK), and the first step of that computation is that the canonical
meromorphic image of `s` is a *regular* meromorphic section. This file establishes the
pointwise input to that step: on an integral scheme a nonzero global section of an invertible
module has a nonzero germ at every point, and those germs survive the passage to the sheaf
`𝒦(L)` of meromorphic sections.

The arguments here deliberately avoid Stacks 0B8M — that an invertible module is finite locally
free of rank one — which is not available in this repository (see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne.lean`: the unconditional
direction needs an internal hom for sheaves of modules, which the pinned Mathlib does not have).
What is used instead is the *stalkwise* shadow of 0B8M, which Tag 0B8K and the stalk pairing of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationStalk.lean` already supply: a
trivialization `L ⊗ N ≅ 𝒪_X` has a stalk at every point, exhibiting `L_x` as an invertible
module over the local ring `𝒪_{X,x}`, hence — the Picard group of a local ring being trivial —
free of rank one. That is enough for every statement below; no trivializing open cover is ever
produced.

## Main results

* `Stacks.ChernCap42.nonempty_stalkLinearEquiv_of_isInvertible` — the stalk of an invertible
  module on a ringed space with local stalks is free of rank one.
* `Stacks.ChernCap42.eq_zero_of_germ_eq_zero` — on an integral scheme a global section of an
  invertible module with one vanishing germ vanishes identically.
* `Stacks.ChernCap42.injective_toMeromorphicSectionStalk` — the stalk of `L` embeds in the
  stalk of `𝒦(L)`.
* `Stacks.ChernCap42.meromorphicSectionOfSection` — the canonical meromorphic image of an
  ordinary global section, with its germ formula
  `Stacks.ChernCap42.germ_meromorphicSectionOfSection` and the nonvanishing
  `Stacks.ChernCap42.germ_meromorphicSectionOfSection_ne_zero`.

## Implementation notes

Three different encodings of "the stalk of a sheaf of modules on a scheme" meet here, and the
statements are phrased to keep them apart. `Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk`
  with
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` is the one the stalk pairing of Tag 0B8K
  is stated in;
`Stacks.ModuleStalk.presheafOn` with `Stacks.ModuleStalk.moduleStalk` is the one the stalk of
the sheaf of meromorphic sections is stated in; and Mathlib's own instance on
`AlgebraicGeometry.Scheme.Modules` is what instance search finds. The underlying abelian groups
and germ maps agree definitionally, and the two module structures are *equal* by
`Stacks.SheafOfModules.stalkModule_eq`, which `moduleInvertible_stalk` uses to move between
them. Where instance search cannot bridge the spellings the instances are passed explicitly;
`Stacks.ModuleStalk.moduleStalk` exists for exactly that purpose.

No declaration here carries a `@[stacks]` attribute. The covering set of Tag 02SK is its two
displayed equalities — `div_L(s) = [Z(s)]_{n-1}` in `Z_{n-1}(X)` and `c₁(L) ∩ [X] =
[Z(s)]_{n-1}` in `CH_{n-1}(X)` — and neither can even be stated here, because the divisor cycle
and the first Chern class of Tag 02SJ are not formalized in this repository. Tagging the
auxiliary results below would over-claim the tag.

## References

* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk grpGerm ringGerm)
open Stacks.SheafOfModules (tensorPairing stalkPairing)

universe u

namespace Stacks.ChernCap42

/-! ### Stalkwise rank one -/

/-- The stalk of an invertible module on a ringed space is an invertible module over the stalk of
the structure sheaf. -/
private theorem moduleInvertible_grpStalk (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheafRing X))
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L]
    (x : X.carrier) : Module.Invertible ↑(ringStalk X x) ↑(grpStalk X L.val x) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  exact Module.Invertible.left (stalkPairing ψ x)

/-- **The stalkwise shadow of Stacks 0B8M.** On a ringed space whose structure sheaf has local
stalks, every stalk of an invertible module is free of rank one. Unlike Stacks 0B8M this says
nothing about a *neighbourhood* of the point, and correspondingly needs none of the internal-hom
machinery that 0B8M does: a trivialization `L ⊗ N ≅ 𝒪` exists by Stacks 0B8K, and its stalk at
`x` exhibits `L_x` as an invertible module over the local ring `𝒪_x`, whose Picard group is
trivial. -/
@[ega "0 5.4.3" "more general"]
theorem nonempty_stalkLinearEquiv_of_isInvertible (X : RingedSpace.{u, u})
    [∀ x : X.carrier, IsLocalRing ↑(ringStalk X x)]
    (L : SheafOfModules.{u} (structureSheafRing X))
    [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L]
    (x : X.carrier) :
    Nonempty (↑(grpStalk X L.val x) ≃ₗ[↑(ringStalk X x)] ↑(ringStalk X x)) := by
  have := moduleInvertible_grpStalk X L x
  exact Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible _ _

/-! ### Sections of an invertible module on an integral scheme -/

variable {X : Scheme.{u}}

/-- The section pairing of a trivialization `L ⊗ N ≅ 𝒪` vanishes when its first argument
does. -/
theorem tensorPairing_zero_left
    {L N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
        SheafOfModules.unit _)
    (W : Opens X) (b : N.val.obj (op W)) :
    tensorPairing ψ W (0 : L.val.obj (op W)) b = 0 := by
  have hz : Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace L N
    (op W) 0 = 0 :=
    ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (L.val) (N.val)))).app
        (op W)).hom.map_zero
  unfold tensorPairing
  rw [TensorProduct.zero_tmul, hz]
  exact (ψ.hom.val.app (op W)).hom.map_zero

/-- **A nonzero global section of an invertible module on an integral scheme has nonzero germs.**
If the germ of `s` vanishes at a single point then `s` vanishes identically.

This is the sheaf-theoretic companion of `nonempty_stalkLinearEquiv_of_isInvertible`, and it is
what makes `s ≠ 0` usable pointwise. Note that it is proved without a *trivializing cover* for
`L` — which is the content of Stacks 0B8M and is not available — by pairing `s` against sections
of the dual `N` and transporting the vanishing through the structure sheaf, where injectivity of
restriction to a nonempty open is `AlgebraicGeometry.map_injective_of_isIntegral`. Irreducibility
of `X` enters exactly once, to know that the open set on which `s` vanishes meets every other
nonempty open. -/
theorem eq_zero_of_germ_eq_zero [IsIntegral X]
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.val.obj (op (⊤ : Opens X))) {x : X}
    (hx : grpGerm X.toRingedSpace L.val x ⊤ trivial s = 0) :
    s = 0 := by
  obtain ⟨N, ⟨ψ⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf)
    (hO := (structureSheafRing X.toRingedSpace).property) L).mp ‹_›
  -- `s` vanishes on some neighbourhood `W` of `x`.
  obtain ⟨W, hxW, iW, iW', hW⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    (U := (⊤ : Opens X)) (V := (⊤ : Opens X)) L.val.presheaf x trivial trivial s 0
    (hx.trans (map_zero _).symm)
  have hWs : (L.val.map (homOfLE (le_top (a := W))).op).hom s = 0 := by
    have h : (L.val.map iW.op).hom s = (L.val.map iW'.op).hom (0 : L.val.obj (op ⊤)) := hW
    rw [map_zero] at h
    have : iW = homOfLE (le_top (a := W)) := Subsingleton.elim _ _
    rwa [this] at h
  -- every germ of `s` vanishes
  have key : ∀ z : X, grpGerm X.toRingedSpace L.val z ⊤ trivial s = 0 := by
    intro z
    -- the dual stalk is free of rank one, so it has a generator
    let _ : Module ↑(ringStalk X.toRingedSpace z) ↑(grpStalk X.toRingedSpace N.val z) :=
      Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace N.val z
    let _ : Module ↑(ringStalk X.toRingedSpace z) ↑(grpStalk X.toRingedSpace L.val z) :=
      Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val z
    have hNinv : Module.Invertible ↑(ringStalk X.toRingedSpace z)
        ↑(grpStalk X.toRingedSpace N.val z) :=
      Module.Invertible.right (stalkPairing ψ z)
    obtain ⟨e⟩ := Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible
      ↑(ringStalk X.toRingedSpace z) ↑(grpStalk X.toRingedSpace N.val z)
    -- realise the generator as a germ
    obtain ⟨V, hzV, b, hb⟩ := Stacks.SheafOfModules.exists_grpGerm_eq X.toRingedSpace N.val z
      (e.symm 1)
    -- the two opens meet
    have hWne : ((W : Opens X) : Set X).Nonempty := ⟨x, hxW⟩
    have hVne : ((V : Opens X) : Set X).Nonempty := ⟨z, hzV⟩
    have hmeet : (((W ⊓ V : Opens X)) : Set X).Nonempty :=
      nonempty_preirreducible_inter W.isOpen V.isOpen hWne hVne
    have : Nonempty ((W ⊓ V : Opens X)) := hmeet.to_subtype
    -- the pairing of `s` with `b` vanishes on `W ⊓ V`, hence on `V`
    have h2 : (L.val.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op).hom
        ((L.val.map (homOfLE (le_top (a := V))).op).hom s) = 0 := by
      rw [← L.val.map_comp_apply]
      have hcomp : (homOfLE (le_top (a := V))).op ≫ (homOfLE (inf_le_right : W ⊓ V ≤ V)).op =
          (homOfLE (le_top (a := W))).op ≫ (homOfLE (inf_le_left : W ⊓ V ≤ W)).op :=
        Subsingleton.elim _ _
      rw [hcomp, L.val.map_comp_apply, hWs]
      exact (L.val.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom.map_zero
    have hres : ((SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val.map
          (homOfLE (inf_le_right : W ⊓ V ≤ V)).op).hom
        (tensorPairing ψ V ((L.val.map (homOfLE (le_top (a := V))).op).hom s) b) = 0 := by
      rw [Stacks.SheafOfModules.tensorPairing_res ψ
        (homOfLE (inf_le_right : W ⊓ V ≤ V))
        ((L.val.map (homOfLE (le_top (a := V))).op).hom s) b, h2]
      exact tensorPairing_zero_left ψ (W ⊓ V) _
    have hzero : tensorPairing ψ V ((L.val.map (homOfLE (le_top (a := V))).op).hom s) b = 0 := by
      refine AlgebraicGeometry.map_injective_of_isIntegral (X := X)
        (homOfLE (inf_le_right : W ⊓ V ≤ V)) ?_
      exact hres.trans
        (((SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val.map
          (homOfLE (inf_le_right : W ⊓ V ≤ V)).op).hom.map_zero).symm
    -- read that on the stalk at `z`
    have hst : stalkPairing ψ z
        (grpGerm X.toRingedSpace L.val z ⊤ trivial s ⊗ₜ[↑(ringStalk X.toRingedSpace z)]
          e.symm 1) = 0 := by
      have hgerm : grpGerm X.toRingedSpace L.val z V hzV
          ((L.val.map (homOfLE (le_top (a := V))).op).hom s) =
          grpGerm X.toRingedSpace L.val z ⊤ trivial s :=
        TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
          (homOfLE (le_top (a := V))) z hzV s
      rw [← hgerm, ← hb]
      refine (Stacks.SheafOfModules.stalkPairing_germ ψ z V hzV _ b).trans ?_
      rw [hzero]
      exact (ringGerm X.toRingedSpace z V hzV).map_zero
    have htens : grpGerm X.toRingedSpace L.val z ⊤ trivial s ⊗ₜ[↑(ringStalk X.toRingedSpace z)]
        e.symm 1 = 0 := by
      refine (stalkPairing ψ z).injective ?_
      rw [hst]
      exact ((stalkPairing ψ z).toLinearMap.map_zero).symm
    -- cancel the generator
    have hcancel : ((TensorProduct.congr (LinearEquiv.refl _ _) e).trans
        (TensorProduct.rid ↑(ringStalk X.toRingedSpace z)
          ↑(grpStalk X.toRingedSpace L.val z)))
        (grpGerm X.toRingedSpace L.val z ⊤ trivial s ⊗ₜ e.symm 1) =
        grpGerm X.toRingedSpace L.val z ⊤ trivial s := by
      simp
    rw [htens, map_zero] at hcancel
    exact hcancel.symm
  -- a section all of whose germs vanish is zero
  refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj L) ⊤ s 0 ?_
  intro z _
  rw [map_zero]
  exact key z

/-! ### Torsion-freeness of the stalks -/

/-- The invertibility hypothesis of the Stacks Project's chapter 42 statements, in the spelling that
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne` proves Tag 0B8K for. The two
predicates are the same by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem isInvertible_stacks_of_algebraicGeometry (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›

/-- The stalk of an invertible module is an invertible module over the local ring at the point,
stated for the `Module` instance that instance search uses on a scheme. This is
`nonempty_stalkLinearEquiv_of_isInvertible` with the two (equal) stalk module structures aligned
by `Stacks.SheafOfModules.stalkModule_eq`. -/
theorem moduleInvertible_stalk
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (x : X) :
    @Module.Invertible ↑(X.sheaf.presheaf.stalk x)
      ↑((Stacks.ModuleStalk.presheafOn (O := X.sheaf.presheaf) L.val).stalk x) _ _
      (Stacks.ModuleStalk.moduleStalk L.val x) := by
  have hinvT := moduleInvertible_grpStalk X.toRingedSpace L x
  rw [Stacks.SheafOfModules.stalkModule_eq] at hinvT
  exact hinvT

/-- A nonzerodivisor of a local ring acts regularly on an invertible module over it: such a
module is free of rank one, so multiplication by a nonzerodivisor is injective on it. -/
theorem isSMulRegular_of_invertible {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M]
    {c : R} (hc : c ∈ nonZeroDivisors R) : IsSMulRegular M c := by
  obtain ⟨e⟩ := Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible R M
  intro a b hab
  refine e.injective ?_
  have h : c • e a = c • e b := by
    rw [← map_smul, ← map_smul]; exact congrArg e hab
  have h0 : (e a - e b) * c = 0 := by
    rw [mul_comm, ← smul_eq_mul, smul_sub, h, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hc).2 _ h0)

/-- **The stalk of an invertible module embeds in the stalk of its sheaf of meromorphic
sections.** The latter is the localization of the former at the germs of regular sections
(`Stacks.Divisors.isLocalizedModule_toMeromorphicSectionStalk`), and those germs are
nonzerodivisors of the local ring, which act regularly because the stalk is free of rank one. -/
theorem injective_toMeromorphicSectionStalk (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) :
    Function.Injective (Stacks.Divisors.toMeromorphicSectionStalk X.sheaf L x) := by
  have _ := isInvertible_stacks_of_algebraicGeometry L
  have _ := Stacks.Divisors.isLocalizedModule_toMeromorphicSectionStalk X.sheaf L x
  have hinv := moduleInvertible_stalk (X := X) (L := L) x
  have _ : IsLocalRing ↑(X.sheaf.presheaf.stalk x) :=
    inferInstanceAs (IsLocalRing ↑(X.presheaf.stalk x))
  refine (@IsLocalizedModule.injective_iff_isRegular _ _
    (Stacks.Divisors.regularGerms X.sheaf x) _ _ _ _
    (Stacks.ModuleStalk.moduleStalk L.val x)
    (Stacks.Divisors.moduleStalkMeromorphicSectionSheaf X.sheaf L x)
    (Stacks.Divisors.toMeromorphicSectionStalk X.sheaf L x) _).mpr ?_
  intro c
  exact @isSMulRegular_of_invertible ↑(X.sheaf.presheaf.stalk x)
    ↑((Stacks.ModuleStalk.presheafOn (O := X.sheaf.presheaf) L.val).stalk x) _ _ _
    (Stacks.ModuleStalk.moduleStalk L.val x) hinv _
    (Stacks.Divisors.regularGerms_le_nonZeroDivisors X.sheaf x c.2)

/-! ### The canonical meromorphic image of an ordinary section -/

/-- **The canonical meromorphic image of an ordinary global section.** A global section `s` of
`L` is sent to the global meromorphic section whose value on every open set is the restriction of
the image of `s` under the canonical morphism `L ⟶ 𝒦(L)`. -/
def meromorphicSectionOfSection (L : X.Modules) (s : Γ(L, ⊤)) :
    AlgebraicGeometry.MeromorphicSection X.sheaf L :=
  let M := AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L
  let a : M.val.obj (.op ⊤) :=
    ((Stacks.Divisors.toMeromorphicSectionSheaf X.sheaf L).app (op ⊤)).hom s
  M.val.sectionsMk (fun _ => M.val.map (homOfLE le_top).op a)
    (by
      intro U V f
      have h : (homOfLE le_top).op ≫ f = (homOfLE le_top).op := Subsingleton.elim _ _
      rw [← M.val.map_comp_apply, h])

/-- The germ of the canonical meromorphic image of `s` is the image of the germ of `s` under the
map of stalks `L_x → 𝒦(L)_x`. -/
theorem germ_meromorphicSectionOfSection (L : X.Modules) (s : Γ(L, ⊤))
    (x : X) (U : Opens X) (hx : x ∈ U) :
    Stacks.ModuleStalk.germ (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val U x hx
        ((meromorphicSectionOfSection L s).val (op U)) =
      Stacks.Divisors.toMeromorphicSectionStalk X.sheaf L x
        (Stacks.ModuleStalk.germ L.val ⊤ x trivial s) :=
  (Stacks.ModuleStalk.germ_res
      (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val le_top hx _).trans
    (Stacks.ModuleStalk.stalkMap_germ
      (Stacks.Divisors.toMeromorphicSectionSheaf X.sheaf L) x ⊤ trivial s).symm

/-- **The canonical meromorphic image of a nonzero section is nowhere zero.** On an integral
scheme a nonzero global section of an invertible module has a nonzero germ at every point
(`eq_zero_of_germ_eq_zero`), and the map from the stalk of `L` to the stalk of its sheaf of
meromorphic sections is injective (`injective_toMeromorphicSectionStalk`). -/
theorem germ_meromorphicSectionOfSection_ne_zero [AlgebraicGeometry.IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (x : X) (U : Opens X) (hx : x ∈ U) :
    Stacks.ModuleStalk.germ (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val U x hx
      ((meromorphicSectionOfSection L s).val (op U)) ≠ 0 := by
  have _ := isInvertible_stacks_of_algebraicGeometry L
  intro hzero
  have h := (germ_meromorphicSectionOfSection L s x U hx).symm.trans hzero
  have h0 : Stacks.ModuleStalk.germ L.val ⊤ x trivial s = 0 := by
    refine injective_toMeromorphicSectionStalk L x ?_
    rw [h, map_zero]
  exact hs (eq_zero_of_germ_eq_zero L s h0)

end Stacks.ChernCap42

end
