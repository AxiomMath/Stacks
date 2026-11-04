module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Tactic.Abel

/-!
# The degree-zero cohomology of a mapping cone over a complex concentrated in one degree

Let `φ : K ⟶ L` be a morphism of cochain complexes in an abelian category and let `n` be an
integer. Mathlib's mapping cone has `(mappingCone φ).X n ≅ K.X (n + 1) ⊞ L.X n`, with
differential `(k, l) ↦ (-d k, φ k + d l)`; this is the convention recorded by
`CochainComplex.mappingCone.d_fst_v` and `CochainComplex.mappingCone.d_snd_v`. So the degree-`n`
cohomology of the cone is computed from

`K.X n ⊞ L.X (n-1) ⟶ K.X (n+1) ⊞ L.X n ⟶ K.X (n+2) ⊞ L.X (n+1)`,

and when `L` is concentrated in degree `n` — that is, `L.X (n-1)` and `L.X (n+1)` vanish — and
`φ` is invertible in degree `n`, the two outer `L`-summands disappear and the differentials become
`k ↦ (-d k, φ k)` and `(k, l) ↦ (-d k, 0)`. The second map has kernel `Z^{n+1}(K) ⊞ L.X n` and the
first is the graph of `φ ∘ d`, so the quotient is `Z^{n+1}(K)`:

`H^n(mappingCone φ) ≅ K.cycles (n + 1)`.

This is `Stacks.MappingCone.homologyIsoCycles`. Note the index shift: the degree-`n` cohomology of
the cone is the *degree-`n+1`* cycles of `K`, i.e. the kernel of `K.d (n+1) (n+2)`, because the
cone places `K.X (n+1)` in degree `n`. All three hypotheses are needed: for `φ = 0` and `K = 0` the
cone is `L` and the conclusion fails.

The proof is a splitting, carried out entirely with morphisms. The composite
`K.cycles (n+1) ⟶ (mappingCone φ).cycles n ⟶ K.cycles (n+1)` of
`Stacks.MappingCone.coneCyclesLift` and `Stacks.MappingCone.coneCyclesProj` is the identity, while
the composite in the other order differs from the identity by the boundary
`Stacks.MappingCone.coneCyclesCorrection ≫ toCycles`. Hence `coneCyclesProj` becomes an inverse of
`coneCyclesLift` after passing to the cokernel of `toCycles`, which is the cohomology.

## Main definitions

* `Stacks.MappingCone.coneCyclesLift` — `Z^{n+1}(K) ⟶ Z^n(mappingCone φ)`, induced by the
  inclusion `K.X (n+1) ⟶ (mappingCone φ).X n` of the first summand.
* `Stacks.MappingCone.coneCyclesProj` — the retraction `Z^n(mappingCone φ) ⟶ Z^{n+1}(K)`, the
  first projection corrected by `d ∘ φ⁻¹ ∘ snd`.
* `Stacks.MappingCone.homologyIsoCycles` — **`H^n(mappingCone φ) ≅ K.cycles (n + 1)`**.

## Main results

* `Stacks.MappingCone.coneCyclesLift_comp_coneCyclesProj` — the retraction identity.
* `Stacks.MappingCone.coneCyclesProj_comp_coneCyclesLift` — the other composite is the identity up
  to a boundary.
* `Stacks.MappingCone.toCycles_comp_coneCyclesProj` — the retraction kills the boundaries.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex HomComplex

universe v u

namespace Stacks.MappingCone

variable {C : Type u} [Category.{v} C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)

/-- The first projection off the mapping cone anticommutes with the differential of the source:
this is `CochainComplex.mappingCone.d_fst_v` solved for the differential of `K`. -/
theorem fst_v_comp_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone.fst φ).1.v i j hij ≫ K.d j k =
      -((mappingCone φ).d i j ≫ (mappingCone.fst φ).1.v j k hjk) := by
  rw [mappingCone.d_fst_v φ i j k hij hjk]; simp

/-- The cycles of `K` in degree `n + 1`, viewed inside the cycles of the mapping cone in degree
`n` through the inclusion of the first summand. The inclusion of a cycle is a cycle because the
`L`-component of the cone differential on it is `φ.f (n + 1)`, which vanishes as `L.X (n + 1)`
does. -/
def coneCyclesLift (hL : IsZero (L.X (n + 1))) :
    K.cycles (n + 1) ⟶ (mappingCone φ).cycles n :=
  (mappingCone φ).liftCycles
    (K.iCycles (n + 1) ≫ (mappingCone.inl φ).v (n + 1) n (by omega)) (n + 1) (by simp)
    (by
      rw [Category.assoc, mappingCone.inl_v_d φ (n + 1) n (n + 2) (by omega) (by omega),
        hL.eq_of_tgt (φ.f (n + 1)) 0]
      simp)

/-- The retraction of `Stacks.MappingCone.coneCyclesLift`: on a cycle of the cone it is the first
projection, corrected by the differential of `K` applied to the preimage under `φ.f n` of the
second projection. The correction is what makes the retraction kill the boundaries. -/
def coneCyclesProj [IsIso (φ.f n)] :
    (mappingCone φ).cycles n ⟶ K.cycles (n + 1) :=
  K.liftCycles ((mappingCone φ).iCycles n ≫ (mappingCone.fst φ).1.v n (n + 1) rfl) (n + 2)
    (by simp; omega)
    (by
      rw [Category.assoc, fst_v_comp_d φ n (n + 1) (n + 2) rfl (by omega), comp_neg,
        ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp, neg_zero]) +
  (mappingCone φ).iCycles n ≫ (mappingCone.snd φ).v n n (add_zero n) ≫ inv (φ.f n) ≫
    K.toCycles n (n + 1)

variable [IsIso (φ.f n)]

/-- The retraction, read inside `K.X (n + 1)`. -/
theorem coneCyclesProj_comp_iCycles :
    coneCyclesProj φ n ≫ K.iCycles (n + 1) =
      (mappingCone φ).iCycles n ≫ (mappingCone.fst φ).1.v n (n + 1) rfl +
        (mappingCone φ).iCycles n ≫ (mappingCone.snd φ).v n n (add_zero n) ≫ inv (φ.f n) ≫
          K.d n (n + 1) := by
  rw [coneCyclesProj, add_comp, HomologicalComplex.liftCycles_i]
  simp

/-- **The retraction identity.** Including a cycle of `K` into the cone and projecting back
recovers it: the first projection undoes the inclusion and the correction term vanishes on it,
the second projection of the inclusion being zero. -/
theorem coneCyclesLift_comp_coneCyclesProj (hL : IsZero (L.X (n + 1))) :
    coneCyclesLift φ n hL ≫ coneCyclesProj φ n = 𝟙 _ := by
  rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, coneCyclesProj_comp_iCycles,
    comp_add, Category.id_comp, coneCyclesLift, HomologicalComplex.liftCycles_i_assoc,
    HomologicalComplex.liftCycles_i_assoc, Category.assoc,
    mappingCone.inl_v_fst_v φ (n + 1) n (by omega)]
  simp

/-- **The retraction kills the boundaries.** On the image of the cone differential the first
projection and the correction term cancel: the second projection of a boundary is `φ.f n` of its
first projection, because `L.X (n - 1)` vanishes. -/
theorem toCycles_comp_coneCyclesProj (hL : IsZero (L.X (n - 1))) :
    (mappingCone φ).toCycles (n - 1) n ≫ coneCyclesProj φ n = 0 := by
  rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, coneCyclesProj_comp_iCycles,
    comp_add, zero_comp]
  rw [← Category.assoc, ← Category.assoc ((mappingCone φ).toCycles (n - 1) n),
    HomologicalComplex.toCycles_i]
  rw [mappingCone.d_fst_v φ (n - 1) n (n + 1) (by omega) rfl]
  rw [mappingCone.d_snd_v_assoc φ (n - 1) n (by omega),
    hL.eq_of_tgt ((mappingCone.snd φ).v (n - 1) (n - 1) (add_zero _)) 0]
  simp

/-- The null-homotopy witnessing that `Stacks.MappingCone.coneCyclesProj` is inverse to
`Stacks.MappingCone.coneCyclesLift` modulo boundaries: a cycle of the cone differs from the
inclusion of its corrected first projection by the boundary of the preimage under `φ.f n` of its
second projection. -/
def coneCyclesCorrection :
    (mappingCone φ).cycles n ⟶ (mappingCone φ).X (n - 1) :=
  (mappingCone φ).iCycles n ≫ (mappingCone.snd φ).v n n (add_zero n) ≫ inv (φ.f n) ≫
    (mappingCone.inl φ).v n (n - 1) (by omega)

/-- **The other composite is the identity up to a boundary.** -/
theorem coneCyclesProj_comp_coneCyclesLift (hL : IsZero (L.X (n + 1))) :
    coneCyclesProj φ n ≫ coneCyclesLift φ n hL +
      coneCyclesCorrection φ n ≫ (mappingCone φ).toCycles (n - 1) n = 𝟙 _ := by
  have hid : (mappingCone φ).iCycles n =
      (mappingCone φ).iCycles n ≫ (mappingCone.fst φ).1.v n (n + 1) rfl ≫
          (mappingCone.inl φ).v (n + 1) n (by omega) +
        (mappingCone φ).iCycles n ≫ (mappingCone.snd φ).v n n (add_zero n) ≫
          (mappingCone.inr φ).f n := by
    rw [← comp_add, mappingCone.id_X φ n (n + 1) rfl, Category.comp_id]
  rw [← cancel_mono ((mappingCone φ).iCycles n), add_comp, Category.id_comp, Category.assoc,
    Category.assoc, HomologicalComplex.toCycles_i, coneCyclesLift,
    HomologicalComplex.liftCycles_i, coneCyclesCorrection, ← Category.assoc,
    coneCyclesProj_comp_iCycles]
  rw [Category.assoc, Category.assoc, Category.assoc,
    mappingCone.inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega)]
  simp only [add_comp, comp_sub, Category.assoc, IsIso.inv_hom_id_assoc]
  conv_rhs => rw [hid]
  abel

variable (hL₁ : IsZero (L.X (n - 1))) (hL₂ : IsZero (L.X (n + 1)))

/-- The retraction `Stacks.MappingCone.coneCyclesProj`, descended to the degree-`n` cohomology of
the cone: the cohomology is the cokernel of the boundary map, and the retraction kills the
boundaries. -/
def homologyCyclesProj : (mappingCone φ).homology n ⟶ K.cycles (n + 1) :=
  (CokernelCofork.IsColimit.desc'
    ((mappingCone φ).homologyIsCokernel (n - 1) n (by simp))
    (coneCyclesProj φ n) (toCycles_comp_coneCyclesProj φ n hL₁)).1

/-- The descended retraction is the retraction on cycles. -/
theorem homologyπ_comp_homologyCyclesProj :
    (mappingCone φ).homologyπ n ≫ homologyCyclesProj φ n hL₁ = coneCyclesProj φ n :=
  (CokernelCofork.IsColimit.desc' ((mappingCone φ).homologyIsCokernel (n - 1) n (by simp)) _
    (toCycles_comp_coneCyclesProj φ n hL₁)).2

/-- **The degree-`n` cohomology of a mapping cone over a complex concentrated in degree `n`.**
If `φ : K ⟶ L` is a morphism of cochain complexes which is invertible in degree `n` and `L`
vanishes in degrees `n - 1` and `n + 1`, then the degree-`n` cohomology of the mapping cone of `φ`
is the module of cycles of `K` in degree `n + 1`, i.e. the kernel of `K.d (n+1) (n+2)`. The index
shift is the one built into the mapping cone, whose degree-`n` term has `K.X (n + 1)` as its first
summand. -/
def homologyIsoCycles : (mappingCone φ).homology n ≅ K.cycles (n + 1) where
  hom := homologyCyclesProj φ n hL₁
  inv := coneCyclesLift φ n hL₂ ≫ (mappingCone φ).homologyπ n
  hom_inv_id := by
    have h : coneCyclesProj φ n ≫ coneCyclesLift φ n hL₂ =
        𝟙 _ - coneCyclesCorrection φ n ≫ (mappingCone φ).toCycles (n - 1) n :=
      eq_sub_of_add_eq (coneCyclesProj_comp_coneCyclesLift φ n hL₂)
    rw [← cancel_epi ((mappingCone φ).homologyπ n), Category.comp_id, ← Category.assoc,
      homologyπ_comp_homologyCyclesProj, ← Category.assoc, h, sub_comp, Category.id_comp,
      Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero, sub_zero]
  inv_hom_id := by
    rw [Category.assoc, homologyπ_comp_homologyCyclesProj,
      coneCyclesLift_comp_coneCyclesProj]

end Stacks.MappingCone

end
