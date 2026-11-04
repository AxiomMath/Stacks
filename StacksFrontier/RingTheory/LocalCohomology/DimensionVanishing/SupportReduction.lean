module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.Localization
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules
public import StacksFrontier.RingTheory.LocalCohomology.RestrictScalars

/-!
# Reducing the vanishing above the support dimension to the case of a local ring

Stacks 0DXC asserts two things: that `H^i_{V(I)}(M) = 0` for `i > dim(Supp M)` when `M` is a
finite module over a commutative ring `A` and `I ⊆ A` is finitely generated, and that the
cohomological dimension satisfies `cd(A, I) ≤ dim A`. The source derives the first from the
second, and proves the second by reducing to a local ring. This file performs both reductions, so
that what remains of the tag is exactly its local case.

The first reduction is Stacks 0DXB,
`Stacks.LocalCohomology.cohomologicalDimension_eq_sSup_localizations`: the cohomological
dimension of `I` is the supremum of the cohomological dimensions of its extensions to the local
rings `A_𝔭`, and the dimension of `A_𝔭` is the height of `𝔭`, which is at most `dim A`.

The second reduction is Stacks 0BJB,
`Stacks.LocalCohomology.localCohomologyRestrictScalarsIso`: writing `B = A / ann(M)` and
`J = IB`, the module `M` is a `B`-module and local cohomology commutes with restriction of
scalars along `A ⟶ B`, so `H^i_{V(I)}(M) = H^i_{V(J)}(M)`. Since `dim B = dim(Supp M)`
(`Module.supportDim_eq_ringKrullDim_quotient_annihilator`), the bound `cd(B, J) ≤ dim B` together
with (1) ⟹ (2) of Stacks 0DX7
(`Stacks.LocalCohomology.isZero_homology_localCohomology_of_isLocalCohomologyBound`) gives the
vanishing for `M`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyModuleRestrictScalarsIso` — Stacks 0BJB degreewise:
  `H^i_{V(I)}(M_A) ≅ H^i_{V(IB)}(M)_A` for a `B`-module `M`.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_supportDim_lt_of_bound` — the vanishing
  above the support dimension follows from the bound `cd(B, J) ≤ dim B` for arbitrary rings.

## Implementation notes

No `@[stacks 0DXC]` attribute is placed, and neither statement of that tag is proved here. Both
results below carry as a hypothesis the very bound `cd(·, ·) ≤ dim(·)` that Stacks 0DXC asserts,
so they are reductions of the tag and not instances of it: what they establish is that the whole
tag follows from its local case.

The local case is carried out in
`StacksFrontier/RingTheory/LocalCohomology/CohomologicalDimension/KrullDimension.lean`, which is
where Stacks 0DXC itself is proved. It combines the ingredients named here —
`Stacks.LocalCohomology.specOpenComplement_toScheme_dim_lt` for the dimension drop on the
punctured spectrum and
`Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology` for the passage from
abelian-sheaf cohomology to cohomology in `Mod(𝒪_X)` — with clause (1) of Stacks 0A3G on a
spectral space and the implication (3) ⟹ (1) of Stacks 0DX7.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DXB](https://stacks.math.columbia.edu/tag/0DXB)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0BJB](https://stacks.math.columbia.edu/tag/0BJB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

/-- **Stacks 0BJB, degreewise.** For a ring map `f : A →+* B` and a finitely generated ideal
`I ⊆ A`, the degree-`i` local cohomology with support in `V(I)` of a `B`-module restricted to `A`
is the restriction to `A` of its degree-`i` local cohomology with support in `V(IB)`. -/
def localCohomologyModuleRestrictScalarsIso {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} B) (i : ℤ) :
    localCohomologyModule A I hI ((ModuleCat.restrictScalars f).obj M) i ≅
      (ModuleCat.restrictScalars f).obj
        (localCohomologyModule B (I.map f) (hI.map f) M i) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      ((Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
            ((Dualizing.localCohomologyFunctor A I hI).mapIso
              (((ModuleCat.restrictScalars.{max u v} f).mapDerivedCategorySingleFunctor 0).app
                M).symm) ≪≫
          (Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
            ((localCohomologyRestrictScalarsIso.{u, u, v} f I hI).app
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj M)) ≪≫
          (powerTorsionRestrictScalarsCompInclusionIso.{u, u, v} f I hI).app
            ((Dualizing.localCohomologyFunctor B (I.map f) (hI.map f)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj M))) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
        (ModuleCat.restrictScalars.{max u v} f) i).app
      ((Dualizing.derivedPowerTorsionProperty B (I.map f) (hI.map f)).ι.obj
        ((Dualizing.localCohomologyFunctor B (I.map f) (hI.map f)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj M)))

/-- **The second reduction of Stacks 0DXC.** If the bound `cd(B, J) ≤ dim B` holds for every ring
`B` in the universe of `A`, then the local cohomology of a finite `A`-module vanishes above the
dimension of its support.

Write `B = A / ann(M)` and `J = IB`. The module `M` is a `B`-module, local cohomology commutes
with restriction of scalars along `A ⟶ B` (Stacks 0BJB), and `dim B = dim(Supp M)`, so the bound
over `B` together with (1) ⟹ (2) of Stacks 0DX7 gives the vanishing. -/
theorem isZero_localCohomologyModule_of_supportDim_lt_of_bound
    (hcd : ∀ (B : Type u) [CommRing B] (J : Ideal B) (hJ : J.FG) (e : ℕ),
      ringKrullDim B ≤ (e : WithBot ℕ∞) → cohomologicalDimension B J hJ ≤ (e : ℤ))
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) [Module.Finite A M] (i : ℤ)
    (hi : Module.supportDim A M < ((i.toNat : ℕ) : WithBot ℕ∞)) :
    IsZero (localCohomologyModule A I hI M i) := by
  classical
  by_cases hzero : Subsingleton M
  · have := hzero
    exact isZero_homology_localCohomology_of_subsingleton.{u, v} A I hI M i
  have hi0 : 0 < i := by
    by_contra hi0
    refine hzero ((Module.supportDim_eq_bot_iff_subsingleton A M).mp ?_)
    refine (WithBot.lt_zero_iff_eq_bot _).mp ?_
    simpa [Int.toNat_of_nonpos (by omega : i ≤ 0)] using hi
  set J := Module.annihilator A M with hJdef
  set B := A ⧸ J with hBdef
  set f : A →+* B := Ideal.Quotient.mk J with hfdef
  have hTor := Module.isTorsionBySet_annihilator A M
  let _ : Module B M := hTor.module
  have hJne : J ≠ ⊤ := fun htop ↦ hzero (Module.annihilator_eq_top_iff.mp htop)
  have hBnt : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hJne
  have hdimBlt : ringKrullDim B < ((i.toNat : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt
      (le_of_eq (Module.supportDim_eq_ringKrullDim_quotient_annihilator A M).symm) hi
  have hdimBle : ringKrullDim B ≤ ((i.toNat - 1 : ℕ) : WithBot ℕ∞) := by
    have hdimNe : ringKrullDim B ≠ ⊥ := fun hbot ↦
      (not_subsingleton_iff_nontrivial.mpr hBnt) (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
    obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hdimNe
    rw [← hr] at hdimBlt ⊢
    have hltInner : r < ((i.toNat : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp hdimBlt
    cases r with
    | top => simp at hltInner
    | coe m =>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (Nat.le_sub_one_of_lt (WithTop.coe_lt_coe.mp hltInner)))
  have hcdB : cohomologicalDimension B (I.map f) (hI.map f) ≤ (i.toNat : ℤ) - 1 := by
    have h := hcd B (I.map f) (hI.map f) (i.toNat - 1) hdimBle
    have hcast : ((i.toNat - 1 : ℕ) : ℤ) = (i.toNat : ℤ) - 1 := by omega
    rwa [hcast] at h
  have hbound : IsLocalCohomologyBound B (I.map f) (hI.map f) ((i.toNat : ℤ) - 1) :=
    ⟨by omega, fun j hj ↦
      (isLocalCohomologyBound_cohomologicalDimension B (I.map f) (hI.map f)).2 j
        (lt_of_le_of_lt hcdB hj)⟩
  have hMB : IsZero (localCohomologyModule B (I.map f) (hI.map f) (ModuleCat.of B M) i) :=
    isZero_homology_localCohomology_of_isLocalCohomologyBound (I.map f) (hI.map f)
      ((i.toNat : ℤ) - 1) hbound (ModuleCat.of B M) i (by omega)
  have hRestr : IsZero ((ModuleCat.restrictScalars f).obj
      (localCohomologyModule B (I.map f) (hI.map f) (ModuleCat.of B M) i)) := by
    rw [ModuleCat.isZero_iff_subsingleton] at hMB ⊢
    exact hMB
  have hA : IsZero (localCohomologyModule A I hI
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B M)) i) :=
    hRestr.of_iso (localCohomologyModuleRestrictScalarsIso f I hI (ModuleCat.of B M) i)
  have eLin : ((ModuleCat.restrictScalars f).obj (ModuleCat.of B M)) ≃ₗ[A] M :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a m ↦ hTor.mk_smul a m }
  have eM : (ModuleCat.restrictScalars f).obj (ModuleCat.of B M) ≅ M :=
    { hom := ModuleCat.ofHom eLin.toLinearMap
      inv := ModuleCat.ofHom eLin.symm.toLinearMap
      hom_inv_id := by ext m; exact eLin.symm_apply_apply m
      inv_hom_id := by ext m; exact eLin.apply_symm_apply m }
  exact hA.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    ((localCohomologyOnModules A I hI).mapIso eM)).symm

end Stacks.LocalCohomology

end
