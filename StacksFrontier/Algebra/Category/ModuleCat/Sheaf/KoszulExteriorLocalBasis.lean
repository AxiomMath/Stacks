module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulQuotientIdentification

/-!
# A section of an exterior power of a finite free sheaf is locally a combination of basis products

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `(O♯)ʳ` the free
sheaf of `O♯`-modules on `r` generators. The sections of the degree-`n` exterior power
`⋀ⁿ((O♯)ʳ)` over an open set are *not* combinations of the ordered exterior products of the
tautological generators: the exterior power is a sheafification, so such a description holds
only locally. This file proves that it does hold locally, in the form a local computation needs:
every section of `⋀ⁿ((O♯)ʳ)` over an open set `V` restricts, on a neighbourhood of each point of
`V`, to a combination of the `binom(r, n)` ordered products
`Stacks.RegularSequence.exteriorBasisSection`.

The proof is by passing to the stalk, where Tag 01CH identifies `(⋀ⁿ((O♯)ʳ))_x` with
`⋀ⁿ_{O_x}((O_x)ʳ)` and where the ordered products become the canonical basis
`Stacks.RegularSequence.wedgeBasis` of that module. Expanding the germ of the section in that
basis gives the coefficients as germs; representing them by sections on a common neighbourhood
and shrinking once more so that two sections with the same germ agree produces the asserted
equality of sections.

## Main results

* `Stacks.RegularSequence.exteriorKoszulStalkEquiv_germ_sum`: the germ of a combination of
  ordered exterior products is the corresponding combination of the canonical basis vectors.
* `Stacks.RegularSequence.exists_restrict_eq_sum_smul_exteriorBasisSection`: **a section of an
  exterior power of `(O♯)ʳ` is, near every point, a combination of the ordered exterior
  products of the tautological generators.**

## Implementation notes

The index type of the canonical basis is `Set.powersetCard (Fin r) n`, the `n`-element finite
subsets of `Fin r`, and the ordered products are indexed by functions `Fin n → Fin r`; the
translation between the two is `Set.powersetCard.ofFinEmbEquiv`, whose inverse enumerates a
subset by an embedding of `Fin n`. That enumeration is named here rather than written out at
each use, because it appears in the statement of the main result.

The two shrinkings of the neighbourhood are of different kinds and cannot be merged. The first,
`Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_common_germ_presheaf`, makes finitely many
germs simultaneously representable; the second,
`TopCat.Presheaf.germ_eq`, turns an equality of germs into an equality of sections. Both are
needed, and the second has to come last.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open scoped ExteriorAlgebra

universe u

namespace Stacks.RegularSequence

open Stacks.SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Osharp r))

/-- **The germ of a combination of ordered exterior products is the corresponding combination of
the canonical basis vectors**, with each coefficient replaced by its germ. -/
theorem exteriorKoszulStalkEquiv_germ_sum (n : ℕ) {x : ↥X} (W : Opens ↥X) (hxW : x ∈ W)
    (a : ↑(Set.powersetCard (Fin r) n) → Osharp.obj.obj (op W)) :
    exteriorKoszulStalkEquiv A n x
        (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf W x hxW
          (∑ t, a t • exteriorBasisSection A W n (wedgeIndex n t)))
      = ∑ t, TopCat.Presheaf.germ Osharp.obj W x hxW (a t) •
          wedgeBasis ↑(TopCat.Presheaf.stalk Osharp.obj x) r n t := by
  have hg : ∀ s, TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf W x hxW s
      = germAddHom (A.exteriorPower n).val W hxW s := fun _ => rfl
  rw [hg]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  erw [← hg, exteriorKoszulStalkEquiv_germ_smul_exteriorBasisSection A n W hxW (a t)
    (wedgeIndex n t), wedgeBasis_apply]

/-- **A section of an exterior power of `(O♯)ʳ` is, near every point, a combination of the
ordered exterior products of the tautological generators.** -/
theorem exists_restrict_eq_sum_smul_exteriorBasisSection (n : ℕ) {x : ↥X} (V : Opens ↥X)
    (hx : x ∈ V) (y : (A.exteriorPower n).val.obj (op V)) :
    ∃ (W : Opens ↥X) (hWV : W ≤ V) (_ : x ∈ W)
      (a : ↑(Set.powersetCard (Fin r) n) → Osharp.obj.obj (op W)),
      (A.exteriorPower n).val.map (homOfLE hWV).op y =
        ∑ t, a t • exteriorBasisSection A W n (wedgeIndex n t) := by
  classical
  obtain ⟨U₀, hx₀, σ, hσ⟩ := Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_common_germ_presheaf
    Osharp.obj x (fun t => (wedgeBasis ↑(TopCat.Presheaf.stalk Osharp.obj x) r n).repr
      (exteriorKoszulStalkEquiv A n x
        (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf V x hx y)) t)
    (Finset.univ : Finset ↑(Set.powersetCard (Fin r) n))
  have hxW₁ : x ∈ U₀ ⊓ V := ⟨hx₀, hx⟩
  have hgerm : TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf (U₀ ⊓ V) x hxW₁
        (∑ t, Osharp.obj.map (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op (σ t) •
          exteriorBasisSection A (U₀ ⊓ V) n (wedgeIndex n t))
      = TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf V x hx y := by
    refine (exteriorKoszulStalkEquiv A n x).injective ?_
    rw [exteriorKoszulStalkEquiv_germ_sum]
    have hc : ∀ t : ↑(Set.powersetCard (Fin r) n),
        TopCat.Presheaf.germ Osharp.obj (U₀ ⊓ V) x hxW₁
            (Osharp.obj.map (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op (σ t))
          = (wedgeBasis ↑(TopCat.Presheaf.stalk Osharp.obj x) r n).repr
            (exteriorKoszulStalkEquiv A n x
              (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf V x hx y)) t :=
      fun t => (TopCat.Presheaf.germ_res_apply Osharp.obj _ x hxW₁ (σ t)).trans
        (hσ t (Finset.mem_univ t))
    simp_rw [hc]
    exact Module.Basis.sum_repr _ _
  obtain ⟨W, hxW, iW₁, iV, hWeq⟩ := TopCat.Presheaf.germ_eq
    (A.exteriorPower n).val.presheaf x hxW₁ hx _ y hgerm
  refine ⟨W, leOfHom iV, hxW, fun t => Osharp.obj.map iW₁.op
    (Osharp.obj.map (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op (σ t)), ?_⟩
  have hsum : (A.exteriorPower n).val.map iW₁.op
        (∑ t, Osharp.obj.map (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op (σ t) •
          exteriorBasisSection A (U₀ ⊓ V) n (wedgeIndex n t))
      = ∑ t, Osharp.obj.map iW₁.op
          (Osharp.obj.map (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀)).op (σ t)) •
        exteriorBasisSection A W n (wedgeIndex n t) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [PresheafOfModules.map_smul, map_exteriorBasisSection]
    rfl
  exact Eq.trans hWeq.symm hsum

end Stacks.RegularSequence

end
