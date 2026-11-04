module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Sections of a torsion free module vanishing on a nonempty open

Let `X` be an integral scheme and let `F` be a quasi-coherent torsion free `𝒪_X`-module. A section
of `F` over an open `W` which vanishes on a nonempty open `V ⊆ W` is zero. This is the form in
which [Stacks, Tag 0G5E] uses torsion freeness: "this sheaf has no nonzero sections vanishing on a
nonempty open of `X` (those would be torsion sections)".

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree.eq_zero_of_map_eq_zero`: a section of a
  torsion free quasi-coherent module on an integral scheme vanishing on a nonempty open is zero.

## Implementation notes

The proof is affine-local. Around a point `x ∈ W` choose an affine open `A ⊆ W`; since `X` is
irreducible, `A ∩ V` is nonempty and contains a nonempty basic open `D(f)` of `A`. A section of a
quasi-coherent module on `A` vanishing on `D(f)` is killed by a power of `f`
(`AlgebraicGeometry.Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact`), and `f ≠ 0` in the
domain `Γ(X, A)`, over which `Γ(F, A)` is torsion free
(`AlgebraicGeometry.isTorsionFree_iff_forall_isAffineOpen`).

## References

* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
* [Stacks Project, Tag 0AXS](https://stacks.math.columbia.edu/tag/0AXS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open _root_.AlgebraicGeometry

/-- On an integral scheme, a section of a quasi-coherent torsion free module which vanishes on a
nonempty open subset of its domain is zero. -/
theorem IsTorsionFree.eq_zero_of_map_eq_zero {X : Scheme.{u}} [IsIntegral X] {F : X.Modules}
    [F.IsQuasicoherent] (hF : IsTorsionFree F) {V W : X.Opens} (hVW : V ≤ W)
    (hV : (V : Set X).Nonempty) (s : Γ(F, W)) (hs : F.presheaf.map (homOfLE hVW).op s = 0) :
    s = 0 := by
  have hFaff := (isTorsionFree_iff_forall_isAffineOpen F).1 hF
  refine TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ W s 0 fun x hx => ?_
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hAW : A ≤ W := hAW
  obtain ⟨y, hyV, hyA⟩ : ((V : Set X) ∩ (A : Set X)).Nonempty := by
    have hV' : (Set.univ ∩ (V : Set X)).Nonempty := by simpa using hV
    have hA' : (Set.univ ∩ (A : Set X)).Nonempty := ⟨x, Set.mem_univ x, hxA⟩
    simpa using (IrreducibleSpace.isIrreducible_univ X).2 _ _ V.isOpen A.isOpen hV' hA'
  obtain ⟨f, hfV, hyf⟩ := hA.exists_basicOpen_le (V := V) ⟨y, hyV⟩ hyA
  let sA : Γ(F, A) := F.presheaf.map (homOfLE hAW).op s
  have hsA : F.presheaf.map (homOfLE (inf_le_left : A ⊓ X.basicOpen f ≤ A)).op sA = 0 := by
    have hle : A ⊓ X.basicOpen f ≤ V := inf_le_right.trans hfV
    dsimp only [sA]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    have : (homOfLE (inf_le_left : A ⊓ X.basicOpen f ≤ A) ≫ homOfLE hAW) =
        homOfLE hle ≫ homOfLE hVW := rfl
    rw [this, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  obtain ⟨n, hn⟩ := Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact F f A
    hA.isCompact le_rfl sA hsA
  have hres : X.presheaf.map (homOfLE (le_refl A)).op f = f := by
    rw [show homOfLE (le_refl A) = 𝟙 A from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hres] at hn
  have : Nonempty A := ⟨⟨x, hxA⟩⟩
  have : IsDomain Γ(X, A) := IsIntegral.component_integral A
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  have hsA0 : sA = 0 := by
    apply (hFaff A hA).isSMulRegular ((isRegular_iff_ne_zero).2 (pow_ne_zero n hf))
    simpa using hn
  have hgerm : F.presheaf.germ W x hx s = F.presheaf.germ A x hxA sA :=
    (F.presheaf.germ_res_apply (homOfLE hAW) x hxA s).symm
  rw [hgerm, hsA0, map_zero]
  exact (map_zero _).symm

end Stacks.AlgebraicGeometry.ReflexiveModules

end
