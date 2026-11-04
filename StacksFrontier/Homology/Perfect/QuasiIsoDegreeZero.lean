module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# A quasi-isomorphism is surjective on degree-zero cocycles up to coboundaries

`StacksDraft.QuasiIsoDegreeZero.exists_cocycle_of_quasiIso`: for a quasi-isomorphism
`u : P ⟶ L` of `ℤ`-indexed cochain complexes of `R`-modules, every degree-zero cocycle of `L` is
the image of a degree-zero cocycle of `P` up to a coboundary. It is proved by lifting the map
`R[0] ⟶ L` defined by the cocycle through `u` up to homotopy, which is possible because `R[0]` is
K-projective ([Stacks, Tag 0649](https://stacks.math.columbia.edu/tag/0649)).

This is the elementwise form of surjectivity on `H⁰` that the proof of the theorem of the cube
uses to transport sections of an invertible module, computed by a Čech complex, to a perfect
model of that complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open scoped ChangeOfRings TensorProduct

universe u

namespace StacksDraft.QuasiIsoDegreeZero

variable {R : Type u} [CommRing R]

/-- The test complex `R[0]`: the module `R` placed in degree `0`. -/
private noncomputable abbrev testComplex (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj (ModuleCat.of R R)

/-- The generator `1` of `R[0]` in degree `0`. -/
private noncomputable abbrev testGenerator (R : Type u) [CommRing R] :
    (testComplex R).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).inv.hom 1

/-- A degree-zero cocycle `x` of `X` is the image of the generator under a map `R[0] ⟶ X`. -/
private theorem exists_hom_testComplex_apply {X : CochainComplex (ModuleCat.{u} R) ℤ} (x : X.X 0)
    (hx : (X.d 0 1).hom x = 0) : ∃ γ : testComplex R ⟶ X, (γ.f 0).hom (testGenerator R) = x := by
  let φ : ModuleCat.of R R ⟶ X.X 0 := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
  have hφ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → φ ≫ X.d 0 k = 0 := by
    intro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    ext
    simp [φ, hx]
  refine ⟨HomologicalComplex.mkHomFromSingle φ hφ, ?_⟩
  simp only [HomologicalComplex.mkHomFromSingle_f, φ, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  simp [testGenerator]

/-- A homotopy `f ≃ g` of maps out of `R[0]` gives `f e = g e + d (h e)` in degree `0`. -/
private theorem apply_eq_add_d_of_homotopy {X : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : testComplex R ⟶ X} (h : Homotopy f g) (e : (testComplex R).X 0) :
    (f.f 0).hom e = (g.f 0).hom e + (X.d (-1) 0).hom ((h.hom 0 (-1)).hom e) := by
  have hc := h.comm 0
  have hE : (testComplex R).d 0 1 = 0 := by simp
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp), hE, zero_comp, zero_add,
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
  have := congrArg (fun m => m.hom e) hc
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply, add_comm] using this

/-- **A quasi-isomorphism is surjective on degree-zero cohomology, elementwise.** A cocycle `z`
of degree `0` of the target is cohomologous to the image of a cocycle of the source. The test
complex `R[0]` is K-projective, so the map `R[0] ⟶ L` defined by `z` lifts through `u` up to
homotopy, and the homotopy is the required coboundary. -/
theorem exists_cocycle_of_quasiIso {P L : CochainComplex (ModuleCat.{u} R) ℤ} (u : P ⟶ L)
    [QuasiIso u] (z : L.X 0) (hz : (L.d 0 1).hom z = 0) :
    ∃ q : P.X 0, (P.d 0 1).hom q = 0 ∧ ∃ w : L.X (-1), (u.f 0).hom q = z + (L.d (-1) 0).hom w := by
  have : CochainComplex.IsKProjective (testComplex R) :=
    StacksDraft.Perfect.isKProjective_single (ModuleCat.of R R) 0
  obtain ⟨γ, hγ⟩ := exists_hom_testComplex_apply z hz
  obtain ⟨β, ⟨h⟩⟩ := (CochainComplex.IsKProjective.exists_lift_of_quasiIso u γ).1
  refine ⟨(β.f 0).hom (testGenerator R), ?_, (h.hom 0 (-1)).hom (testGenerator R), ?_⟩
  · have hE : (testComplex R).d 0 1 = 0 := by simp
    have hc : β.f 0 ≫ P.d 0 1 = 0 := by rw [β.comm 0 1, hE, zero_comp]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun m => m.hom (testGenerator R)) hc
  · simpa [hγ, add_comm] using apply_eq_add_d_of_homotopy h (testGenerator R)

/-- **A quasi-isomorphism is injective on degree-zero cohomology, elementwise.** A degree-zero
cocycle `q` of the source whose image is a coboundary is itself a coboundary. The map
`R[0] ⟶ P` defined by `q` becomes null-homotopic after composing with `u`, and since `R[0]` is
K-projective it was null-homotopic already ([Stacks, Tag 064A]). -/
theorem exists_eq_d_of_quasiIso {P L : CochainComplex (ModuleCat.{u} R) ℤ} (u : P ⟶ L)
    [QuasiIso u] (q : P.X 0) (hq : (P.d 0 1).hom q = 0) (w : L.X (-1))
    (hw : (u.f 0).hom q = (L.d (-1) 0).hom w) :
    ∃ v : P.X (-1), q = (P.d (-1) 0).hom v := by
  have : CochainComplex.IsKProjective (testComplex R) :=
    StacksDraft.Perfect.isKProjective_single (ModuleCat.of R R) 0
  obtain ⟨β, hβ⟩ := exists_hom_testComplex_apply q hq
  let ι := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)
  let ψ : (testComplex R).X 0 ⟶ L.X (-1) :=
    ι.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R _ w)
  have hE : (testComplex R).d (-1) 0 = 0 := by simp
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((testComplex R).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hcoch : CochainComplex.HomComplex.Cochain.ofHom (β ≫ u) =
      CochainComplex.HomComplex.δ (-1) 0 (CochainComplex.HomComplex.Cochain.single ψ (-1)) +
        CochainComplex.HomComplex.Cochain.ofHom 0 := by
    rw [CochainComplex.HomComplex.Cochain.δ_single ψ (-1) 0 (by norm_num) (-1) 0 (by norm_num)
      (by norm_num), hE, zero_comp, CochainComplex.HomComplex.Cochain.single_zero, smul_zero,
      add_zero, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]
    refine CochainComplex.HomComplex.Cochain.ext₀ _ _ (fun p => ?_)
    by_cases hp : p = 0
    · subst hp
      rw [CochainComplex.HomComplex.Cochain.ofHom_v,
        CochainComplex.HomComplex.Cochain.single_v, ← cancel_epi ι.inv]
      ext
      simp only [ψ, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_ofHom]
      change (u.f 0).hom ((β.f 0).hom (testGenerator R)) = _
      rw [hβ, hw]
      simp
    · exact (hz p hp).eq_of_src _ _
  let H : Homotopy (β ≫ u) 0 :=
    (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
      ⟨CochainComplex.HomComplex.Cochain.single ψ (-1), hcoch⟩
  obtain ⟨h⟩ := CochainComplex.IsKProjective.nonempty_homotopy_of_comp_quasiIso u
    (β₁ := β) (β₂ := 0) (H.trans (Homotopy.ofEq (zero_comp).symm))
  refine ⟨(h.hom 0 (-1)).hom (testGenerator R), ?_⟩
  rw [← hβ, apply_eq_add_d_of_homotopy h]
  simp

end StacksDraft.QuasiIsoDegreeZero

end
