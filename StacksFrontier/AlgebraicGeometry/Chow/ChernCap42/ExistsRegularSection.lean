module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.RegularMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.GenericValue

/-!
# Existence of a regular meromorphic section on an integral scheme

Let `X` be an integral scheme and let `L` be an invertible `𝒪_X`-module. This file proves
[Stacks, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ) part (1): `L` has a regular
meromorphic section, that is, a global section of the sheaf `𝒦_X(L)` which is regular in the
sense of [Stacks, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX).

`Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible` supplies a nonzero element of the
generic stalk `L_η`, and `Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk` — Stacks 01X5
(2) — turns it back into a section of `𝒦_X(L)` over `X`; the restriction maps of `𝒦_X(L)` between
nonempty opens being isomorphisms, that single section extends to a compatible family, which is a
global meromorphic section. It is regular by
`Stacks.ChernCap42.isRegularMeromorphicSection_of_germ_ne_zero`: a nonzero generic germ is
nonzero at every point, because the generization map carries the germ at `x` to the germ at `η`.

The existence statement is proved in the strengthened form which also records that the generic
value of the section is nonzero, the hypothesis that
`Stacks.Chow.mk_divisorOfMeromorphicSectionCycle_eq` takes.

## Main results

* `Stacks.ChernCap42.germ_ne_zero_of_germ_genericPoint_ne_zero` — on an irreducible space a germ
  with nonzero generic germ is nonzero at every point.
* `Stacks.ChernCap42.isRegularMeromorphicSection_of_genericValue_ne_zero` — a meromorphic section
  of an invertible module on an integral scheme with nonzero generic value is regular.
* `Stacks.ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral` — **Stacks 02OZ (1)**, in
  the strengthened form which also gives nonvanishing of the generic value.

## Implementation notes

The compatible family is built by the same device as
`Stacks.ChernCap42.meromorphicSectionOfSection`: restrict the section over `⊤` to each open set.
Compatibility is `Subsingleton.elim` on morphisms into `⊤`, and the component over `⊤` is
recovered because the restriction along `⊤ ≤ ⊤` is the identity.

No `@[stacks]` attribute is attached to the existence statement; the covering set of Tag 02OZ has
three parts, of which only part (1) is here.

## References

* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.ModuleStalk

universe u

namespace Stacks.ChernCap42

/-- **A germ which is nonzero at the generic point is nonzero everywhere.** On an irreducible
space the generic point specializes to every point, and the generization map
`F_x ⟶ F_η` carries the germ of a global section at `x` to its germ at `η`; so a section whose
germ at some point vanishes has vanishing generic germ. -/
theorem germ_ne_zero_of_germ_genericPoint_ne_zero {X : Scheme.{u}} [IrreducibleSpace X]
    (F : (X : TopCat.{u}).Presheaf AddCommGrpCat.{u}) (m : ↑(F.obj (op ⊤))) (x : X)
    (h : F.germ ⊤ (genericPoint X) trivial m ≠ 0) :
    F.germ ⊤ x trivial m ≠ 0 := by
  intro h0
  refine h ?_
  have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hcomp := ConcreteCategory.congr_hom
    (F.germ_stalkSpecializes (U := ⊤) (trivial : x ∈ (⊤ : Opens X)) hsp) m
  rw [ConcreteCategory.comp_apply, h0, map_zero] at hcomp
  exact hcomp.symm

/-- **A meromorphic section with nonzero generic value is regular.** The generic value of a
meromorphic section is its germ at `η`, read through the canonical bijection
`L_η → 𝒦_X(L)_η`; that bijection is injective, so a nonzero generic value gives a nonzero germ
at `η`, which is nonzero at every point by
`Stacks.ChernCap42.germ_ne_zero_of_germ_genericPoint_ne_zero`. -/
theorem isRegularMeromorphicSection_of_genericValue_ne_zero (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (σ : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hσ : Stacks.Divisors.genericValue L σ ≠ 0) :
    AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L σ := by
  refine isRegularMeromorphicSection_of_germ_ne_zero X L σ fun x => ?_
  refine germ_ne_zero_of_germ_genericPoint_ne_zero _ _ x fun h0 => ?_
  have _ : Module ↑(X.sheaf.presheaf.stalk (genericPoint X))
      ↑((presheafOn L.val).stalk (genericPoint X)) := moduleStalk L.val (genericPoint X)
  refine hσ (injective_toMeromorphicSectionStalk L (genericPoint X) ?_)
  exact (Stacks.Divisors.toMeromorphicSectionStalk_genericValue L σ).trans
    (h0.trans (map_zero _).symm)

/-- **Stacks 02OZ (1): an invertible module on an integral scheme has a regular meromorphic
section**, together with the nonvanishing of its generic value.

A nonzero element of the generic stalk exists
(`Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible`); Stacks 01X5 (2) turns it into a
section of `𝒦_X(L)` over `X`, which extends to a compatible family by restriction; and a
meromorphic section with nonzero generic value is regular.

No `@[stacks]` attribute is attached; see the module documentation. -/
theorem exists_isRegularMeromorphicSection_of_isIntegral (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ∃ σ : AlgebraicGeometry.MeromorphicSection X.sheaf L,
      AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L σ ∧
        Stacks.Divisors.genericValue L σ ≠ 0 := by
  have _ := Stacks.ChernCap42.isInvertible_stacks_of_algebraicGeometry L
  have _ := Stacks.Divisors.isInvertible_presheaf L
  obtain ⟨v, hv⟩ := Stacks.Divisors.exists_ne_zero_genericStalk_of_isInvertible L
  let M := AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L
  let a : ↑(M.val.obj (op ⊤)) :=
    (Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk L ⊤ trivial).symm v
  have hcompat : ∀ ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V),
      M.val.map f (M.val.map (homOfLE le_top).op a) = M.val.map (homOfLE le_top).op a := by
    intro U V f
    have h : (homOfLE le_top).op ≫ f = (homOfLE le_top).op := Subsingleton.elim _ _
    rw [← M.val.map_comp_apply, h]
  have htop : M.val.map (homOfLE (le_top (a := (⊤ : Opens X)))).op a = a := by
    have h : (homOfLE (le_top (a := (⊤ : Opens X)))).op = 𝟙 (op (⊤ : Opens X)) :=
      Subsingleton.elim _ _
    rw [h]
    simp
    rfl
  have hval : Stacks.Divisors.genericValue L
      (M.val.sectionsMk (fun _ => M.val.map (homOfLE le_top).op a) hcompat) = v := by
    show (Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk L ⊤ trivial)
      (M.val.map (homOfLE le_top).op a) = v
    rw [htop]
    exact (Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk L ⊤ trivial).apply_symm_apply v
  exact ⟨M.val.sectionsMk (fun _ => M.val.map (homOfLE le_top).op a) hcompat,
    isRegularMeromorphicSection_of_genericValue_ne_zero X L _ (hval.trans_ne hv),
    hval.trans_ne hv⟩

end Stacks.ChernCap42

end
