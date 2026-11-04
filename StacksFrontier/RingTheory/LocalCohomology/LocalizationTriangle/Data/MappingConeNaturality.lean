module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Basic

/-!
# Functoriality of the degree-`n` cohomology of a mapping cone

Let `φ₁ : K₁ ⟶ L₁` and `φ₂ : K₂ ⟶ L₂` be morphisms of cochain complexes in an abelian category,
both invertible in degree `n`, with `L₁` and `L₂` vanishing in degree `n - 1`. A commutative square
`φ₁ ≫ b = a ≫ φ₂` induces a morphism of mapping cones, and
`StacksFrontier/RingTheory/LocalCohomology/MappingConeH0/Basic.lean` identifies the degree-`n`
cohomology of each cone with the degree-`n+1` cycles of its source. This file proves that those two
identifications are compatible: the square

```
H^n(mappingCone φ₁) ⟶ Z^{n+1}(K₁)
      ↓                    ↓
H^n(mappingCone φ₂) ⟶ Z^{n+1}(K₂)
```

commutes, the vertical maps being induced by `a` and by the morphism of cones.

The retraction `Stacks.MappingCone.coneCyclesProj` is the first projection off the cone corrected
by `d ∘ (φ.f n)⁻¹ ∘ snd`, so the proof is two compatibilities of the induced map of cones with the
biproduct projections — `Stacks.MappingCone.map_comp_fst_v` and
`Stacks.MappingCone.map_comp_snd_v`, each a two-case check against the inclusions — together with
the degree-`n` square read as `b ≫ (φ₂.f n)⁻¹ = (φ₁.f n)⁻¹ ≫ a`. The correction term is where the
square enters; the first projection alone would be natural for any pair of maps.

The same computation of `Stacks.MappingCone.coneCyclesProj` on the second biproduct summand gives
its value on the image of `Stacks.MappingCone.inr`: a cycle of `L` placed in the cone by the
canonical inclusion is carried to the boundary of its preimage under `φ.f n`, which is
`Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles`. On the Čech cone of the
localization triangle that is the statement that the restriction map sends `m` to the family of
constant fractions `m / 1`.

## Main results

* `Stacks.MappingCone.coneCyclesProj_naturality`,
  `Stacks.MappingCone.homologyCyclesProj_naturality` — the retraction onto the cycles of the
  source, and its descent to cohomology, commute with the morphism induced by a commutative
  square.
* `Stacks.MappingCone.homologyIsoCycles_hom_naturality` — **the identification
  `H^n(mappingCone φ) ≅ Z^{n+1}(K)` is natural in the square.**
* `Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles` — the retraction sends the
  image of a cycle of `L` under the canonical inclusion to the boundary of its preimage under
  `φ.f n`.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive CochainComplex

universe v u

namespace Stacks.MappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### The induced map of cones against the biproduct projections -/

section Map

variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (comm : φ₁ ≫ b = a ≫ φ₂) (n : ℤ)

/-- The morphism of mapping cones induced by a commutative square commutes with the first
projection, which it covers by `a`. Both sides are checked against the two inclusions of the
source cone: on the first summand the projections are identities, and on the second both
composites vanish. -/
@[reassoc]
theorem map_comp_fst_v :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.fst φ₂).1.v n (n + 1) rfl =
      (mappingCone.fst φ₁).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  rw [mappingCone.ext_from_iff _ (n + 1) n rfl]
  exact ⟨by simp [mappingCone.map], by simp [mappingCone.map]⟩

/-- The morphism of mapping cones induced by a commutative square commutes with the second
projection, which it covers by `b`. -/
@[reassoc]
theorem map_comp_snd_v :
    (mappingCone.map φ₁ φ₂ a b comm).f n ≫ (mappingCone.snd φ₂).v n n (add_zero n) =
      (mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  rw [mappingCone.ext_from_iff _ (n + 1) n rfl]
  exact ⟨by simp [mappingCone.map], by simp [mappingCone.map]⟩

/-- **The retraction onto the cycles of the source is natural in the square.** The first projection
is natural for the trivial reason that the induced map of cones covers `a` on the first summand;
the correction term `d ∘ (φ.f n)⁻¹ ∘ snd` is natural because the induced map covers `b` on the
second summand, `b` and `a` are exchanged by the square read with its horizontal maps inverted,
and `a` is a morphism of complexes. -/
theorem coneCyclesProj_naturality [IsIso (φ₁.f n)] [IsIso (φ₂.f n)] :
    HomologicalComplex.cyclesMap (mappingCone.map φ₁ φ₂ a b comm) n ≫ coneCyclesProj φ₂ n =
      coneCyclesProj φ₁ n ≫ HomologicalComplex.cyclesMap a (n + 1) := by
  have hc := congrArg (fun ψ => HomologicalComplex.Hom.f ψ n) comm
  simp only [HomologicalComplex.comp_f] at hc
  have hinv : b.f n ≫ inv (φ₂.f n) = inv (φ₁.f n) ≫ a.f n := by
    rw [← cancel_epi (φ₁.f n), IsIso.hom_inv_id_assoc, ← Category.assoc, hc, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [← cancel_mono (K₂.iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i, comp_add, add_comp,
    coneCyclesProj_comp_iCycles, reassoc_of% (coneCyclesProj_comp_iCycles φ₁ n),
    HomologicalComplex.cyclesMap_i_assoc, map_comp_fst_v, map_comp_snd_v_assoc,
    reassoc_of% hinv, a.comm n (n + 1)]

/-- **The descended retraction is natural in the square.** The cohomology of the cone is the
cokernel of the boundary map, so this follows from
`Stacks.MappingCone.coneCyclesProj_naturality` by cancelling the projection onto it. -/
theorem homologyCyclesProj_naturality [IsIso (φ₁.f n)] [IsIso (φ₂.f n)]
    (hL₁ : IsZero (L₁.X (n - 1))) (hL₂ : IsZero (L₂.X (n - 1))) :
    HomologicalComplex.homologyMap (mappingCone.map φ₁ φ₂ a b comm) n ≫
        homologyCyclesProj φ₂ n hL₂ =
      homologyCyclesProj φ₁ n hL₁ ≫ HomologicalComplex.cyclesMap a (n + 1) := by
  rw [← cancel_epi ((mappingCone φ₁).homologyπ n), ← Category.assoc,
    HomologicalComplex.homologyπ_naturality, Category.assoc, homologyπ_comp_homologyCyclesProj,
    ← Category.assoc, homologyπ_comp_homologyCyclesProj, coneCyclesProj_naturality]

/-- **The identification `H^n(mappingCone φ) ≅ Z^{n+1}(K)` is natural in the square.** For a
commutative square `φ₁ ≫ b = a ≫ φ₂` whose horizontal maps are invertible in degree `n`, with
`L₁` and `L₂` vanishing in degrees `n - 1` and `n + 1`, the degree-`n` cohomology of the induced
map of cones corresponds to the map induced by `a` on degree-`n+1` cycles. -/
theorem homologyIsoCycles_hom_naturality [IsIso (φ₁.f n)] [IsIso (φ₂.f n)]
    (hL₁ : IsZero (L₁.X (n - 1))) (hL₁' : IsZero (L₁.X (n + 1)))
    (hL₂ : IsZero (L₂.X (n - 1))) (hL₂' : IsZero (L₂.X (n + 1))) :
    HomologicalComplex.homologyMap (mappingCone.map φ₁ φ₂ a b comm) n ≫
        (homologyIsoCycles φ₂ n hL₂ hL₂').hom =
      (homologyIsoCycles φ₁ n hL₁ hL₁').hom ≫ HomologicalComplex.cyclesMap a (n + 1) :=
  homologyCyclesProj_naturality comm n hL₁ hL₂

end Map

/-! ### The retraction on the image of the canonical inclusion -/

section Inr

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)

/-- **The retraction sends the image of a cycle of `L` to the boundary of its preimage.** The
canonical inclusion `L ⟶ mappingCone φ` hits the second biproduct summand, on which the first
projection vanishes and the second is the identity, so only the correction term of
`Stacks.MappingCone.coneCyclesProj` survives: a cycle `l` of `L` in degree `n` is carried to
`d ((φ.f n)⁻¹ l)` in `Z^{n+1}(K)`.

On the Čech cone of the affine localization triangle, with `φ` the Čech augmentation and `n = 0`,
this is the formula `m ↦ (m / 1)ᵢ` for the restriction map of Stacks 0DWR. -/
theorem coneCyclesProj_comp_cyclesMap_inr_comp_iCycles [IsIso (φ.f n)] :
    HomologicalComplex.cyclesMap (mappingCone.inr φ) n ≫ coneCyclesProj φ n ≫
        K.iCycles (n + 1) =
      L.iCycles n ≫ inv (φ.f n) ≫ K.d n (n + 1) := by
  rw [coneCyclesProj_comp_iCycles, comp_add, HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.cyclesMap_i_assoc, mappingCone.inr_f_fst_v,
    mappingCone.inr_f_snd_v_assoc]
  simp

/-- **The identification `H^n(mappingCone φ) ≅ Z^{n+1}(K)` on a class coming from the target.**
The class of an `n`-cycle `l` of `L`, pushed into the cone along the canonical inclusion, is
carried to the boundary `d ((φ.f n)⁻¹ l)`. This is
`Stacks.MappingCone.coneCyclesProj_comp_cyclesMap_inr_comp_iCycles` read after the projection onto
cohomology, which turns the descended retraction back into the retraction itself. -/
theorem homologyπ_homologyMap_inr_comp_homologyCyclesProj [IsIso (φ.f n)]
    (hL : IsZero (L.X (n - 1))) :
    L.homologyπ n ≫ HomologicalComplex.homologyMap (mappingCone.inr φ) n ≫
        homologyCyclesProj φ n hL ≫ K.iCycles (n + 1) =
      L.iCycles n ≫ inv (φ.f n) ≫ K.d n (n + 1) := by
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    reassoc_of% (homologyπ_comp_homologyCyclesProj φ n hL),
    coneCyclesProj_comp_cyclesMap_inr_comp_iCycles]

end Inr

end Stacks.MappingCone

end
