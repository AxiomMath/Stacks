module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneratingSystem
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator

/-!
# The nonvanishing locus of a section is the complement of its zero scheme

Let `X` be a scheme, `𝓛` an invertible `𝒪_X`-module and `s` a global section of `𝓛`. A point `x`
lies in the nonvanishing locus of `s` (Stacks 01CY) exactly when it lies outside the support of
the zero scheme `Z(s)` of Stacks 02OQ. No integrality or regularity of `s` is needed: on an affine
open `D(g)` trivializing `𝓛` by a generator `e`, `s = a · e`, the zero scheme is cut out by `a`,
and the germ of `e` generates the stalk (`𝓛` is quasi-coherent), so the germ of `s` lies in
`𝔪_x 𝓛_x` exactly when `a` is not a unit at `x`.

## Main results

* `AlgebraicGeometry.mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **The nonvanishing locus of a global section of an invertible module is the complement of the
support of its zero scheme.** -/
theorem mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus L s ↔ x ∉ (zeroScheme X L s).supportSet := by
  refine ⟨fun hx => notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen L s hx, fun hx => ?_⟩
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  obtain ⟨g, hxg, -, ⟨e⟩⟩ := exists_basicOpen_linearEquiv L U x hxU
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem
      (U := ⟨X.basicOpen g, U.2.basicOpen g⟩) hxg,
    zeroScheme_ideal_of_trivialization X L s ⟨X.basicOpen g, U.2.basicOpen g⟩ e _ rfl,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hx
  set a : Γ(X, X.basicOpen g) := e (L.presheaf.map (homOfLE le_top).op s) with ha
  have hunit := (X.mem_basicOpen a x hxg).mp hx
  have hsmul (r : Γ(X, X.basicOpen g)) : r • e.symm 1 = e.symm r := by
    rw [← map_smul e.symm r 1, smul_eq_mul, mul_one]
  have hsW : L.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op s = a • e.symm 1 := by
    rw [hsmul, ha, e.symm_apply_apply]
  have hgerm : (L.presheaf.Γgerm x).hom s =
      (X.presheaf.germ (X.basicOpen g) x hxg).hom a •
        (L.presheaf.germ (X.basicOpen g) x hxg).hom (e.symm 1) := by
    rw [← TopCat.Presheaf.Γgerm_res_apply
      (i := homOfLE (le_top : X.basicOpen g ≤ ⊤)) L.presheaf x hxg s, hsW,
      Stacks.ModuleStalk.germ_smul]
  have hgen := Stacks.PicSurjectiveOpen.notMem_maximalIdeal_smul_top_germ_of_bijective_smul L
    (U.2.basicOpen g) (e.symm 1) (by
      rw [funext hsmul]; exact e.symm.bijective) hxg
  show x ∈ Stacks.NonvanishingOpen.nonvanishingOpen X L s
  rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, hgerm,
    Stacks.ModuleStalk.smul_mem_maximalSmul_iff]
  rintro (h | h)
  · exact h hunit
  · exact hgen h

end AlgebraicGeometry

end
