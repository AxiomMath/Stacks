module

public import StacksFrontier.Algebra.Homology.FlatComplexTopDegreeFibres

/-!
# Vanishing on top cohomology of flat complexes is stable under base change

Let `φ : K ⟶ L` be a morphism of cochain complexes of `R`-modules, where `K` is a complex of flat
modules vanishing in large degrees whose cohomology vanishes above degree `d = q + 1`. If `φ`
induces zero on `Hᵈ`, then so does `φ ⊗_R S` for every ring map `R ⟶ S`: the cycles of `S ⊗ K`
in degree `d` are `S ⊗ Zᵈ(K)` (`Stacks.FlatComplexTopDegree.range_lTensor_ker_subtype`), and
`φ` carries every cycle of `K` to a boundary of `L`.

## Main results

* `Stacks.FlatComplexTopDegree.homologyMap_extendScalars_eq_zero_of_homologyMap_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleCat
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.FlatComplexTopDegree

variable {R : Type u} [CommRing R]

/-- **Vanishing on top cohomology of a flat complex is stable under base change.** Let
`φ : K ⟶ L` be a morphism of complexes of `R`-modules with `K` a complex of flat modules
vanishing in degrees `≥ n` whose cohomology vanishes above degree `q + 1`. If `φ` is zero on
`H^{q+1}`, then so is `φ ⊗_R S` for every ring map `ι : R →+* S`. -/
theorem homologyMap_extendScalars_eq_zero_of_homologyMap_eq_zero
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (q n : ℕ)
    [∀ i, Module.Flat R (K.X i)] (hKn : ∀ i, n ≤ i → Subsingleton (K.X i))
    (hK : ∀ i, q + 1 < i → IsZero (K.homology i))
    (h : HomologicalComplex.homologyMap φ (q + 1) = 0)
    {S : Type u} [CommRing S] (ι : R →+* S) :
    HomologicalComplex.homologyMap
      (((extendScalars ι).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (q + 1) = 0 := by
  classical
  have hexK : ∀ i, q + 1 ≤ i →
      Function.Exact (K.d i (i + 1)).hom (K.d (i + 1) (i + 1 + 1)).hom :=
    fun i hi => exact_of_isZero_homology K i (hK (i + 1) (by omega))
  have key : ∀ z : K.X (q + 1), K.d (q + 1) (q + 1 + 1) z = 0 →
      ∃ y : (extendScalars ι).obj (L.X q),
        (extendScalars ι).map (L.d q (q + 1)) y = (show (extendScalars ι).obj (L.X (q + 1)) from
          toRingModule ι 1 ⊗ₜ[R] φ.f (q + 1) z) := by
    intro z hz
    obtain ⟨v, hv⟩ := (CochainComplex.moduleCat_homologyMap_succ_eq_zero_iff φ q).1 h z hz
    exact ⟨toRingModule ι 1 ⊗ₜ[R] v, (extendScalars_map_tmul ι _ _ v).trans (congrArg _ hv)⟩
  rw [CochainComplex.moduleCat_homologyMap_succ_eq_zero_iff]
  intro x hx
  change (extendScalars ι).map (K.d (q + 1) (q + 1 + 1)) x = 0 at hx
  change ∃ y : (extendScalars ι).obj (L.X q),
    (extendScalars ι).map (L.d q (q + 1)) y = (extendScalars ι).map (φ.f (q + 1)) x
  rw [extendScalars_map_apply] at hx
  have hxr := (congrArg (fun P => x ∈ P) (range_lTensor_ker_subtype (C := fun i => K.X i)
    (fun i => (K.d i (i + 1)).hom) (q + 1) n hKn hexK (ringModule ι))).mpr hx
  obtain ⟨w, rfl⟩ := hxr
  clear hx
  induction w using TensorProduct.inductionOn with
  | tmul s z =>
    obtain ⟨y, hy⟩ := key z.1 z.2
    refine ⟨(show S from s) • y, ?_⟩
    refine (((extendScalars ι).map (L.d q (q + 1))).hom.map_smul (show S from s) y).trans ?_
    refine (congrArg _ hy).trans ?_
    refine (extendScalars_smul_tmul ι (show S from s) 1 _).trans ?_
    change toRingModule ι ((show S from s) * 1) ⊗ₜ[R] φ.f (q + 1) z.1 =
      toRingModule ι (show S from s) ⊗ₜ[R] φ.f (q + 1) z.1
    rw [mul_one]
  | add a b ha hb =>
    obtain ⟨ya, hya⟩ := ha
    obtain ⟨yb, hyb⟩ := hb
    exact ⟨ya + yb, (map_add _ _ _).trans ((congrArg₂ (· + ·) hya hyb).trans
      (((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm))⟩

end Stacks.FlatComplexTopDegree
