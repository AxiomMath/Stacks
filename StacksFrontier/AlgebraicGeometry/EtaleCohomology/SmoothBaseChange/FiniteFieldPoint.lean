module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen

/-!
# Points of a finite scheme over a field are defined over a finite extension

Let `W` be finite over `Spec E`, `L/E` a field extension, and `s : Spec L ⟶ W` a morphism over
`Spec E`. Then `s` factors through `Spec E'` for an intermediate field `E ⊆ E' ⊆ L` of finite
degree over `E`: writing `W = Spec B` with `B` a finite `E`-algebra, `s` is an `E`-algebra map
`B ⟶ L`, and its image `E'` is a domain finite over `E`, hence a field. This is how, in the proof
of [Stacks, Tag 0EYT], a point of a finite étale cover over a rational point of the base is
defined over a finite extension of the ground field.

## Main results

* `Stacks.EtaleCohomology.exists_finiteDimensional_factorization_of_isFinite`.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **A point of a finite scheme over a field is defined over a finite subextension.** Let
`h : W ⟶ Spec E` be finite, `L/E` a field extension and `s : Spec L ⟶ W` a morphism over
`Spec E`. Then there are an intermediate field `E ⊆ E' ⊆ L` of finite degree over `E` and a
morphism `t : Spec E' ⟶ W` over `Spec E` through which `s` factors. -/
theorem exists_finiteDimensional_factorization_of_isFinite {E L : Type u} [Field E] [Field L]
    [Algebra E L] {W : Scheme.{u}} (h : W ⟶ Spec (.of E)) [IsFinite h]
    (s : Spec (.of L) ⟶ W) (hs : s ≫ h = spectrumMap E L) :
    ∃ (E' : IntermediateField E L) (_ : FiniteDimensional E E') (t : Spec (.of E') ⟶ W),
      t ≫ h = spectrumMap E E' ∧ spectrumMap E' L ≫ t = s := by
  have : IsAffine W := isAffine_of_isAffineHom h
  let φh : CommRingCat.of E ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ h)
  let φs : Γ(W, ⊤) ⟶ CommRingCat.of L := Spec.preimage (s ≫ W.isoSpec.hom)
  have hφh : Spec.map φh = W.isoSpec.inv ≫ h := Spec.map_preimage _
  have hφs : Spec.map φs = s ≫ W.isoSpec.hom := Spec.map_preimage _
  have hcomp : φh ≫ φs = CommRingCat.ofHom (algebraMap E L) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφh, hφs, Category.assoc, Iso.hom_inv_id_assoc, hs]
  have hfin : φh.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφh]
    infer_instance
  let : Algebra E Γ(W, ⊤) := φh.hom.toAlgebra
  have : Module.Finite E Γ(W, ⊤) := hfin
  let ψ : Γ(W, ⊤) →ₐ[E] L :=
    { φs.hom with
      commutes' := fun e => congrArg (fun f => f.hom e) hcomp }
  have : Module.Finite E ψ.range :=
    Module.Finite.of_surjective ψ.rangeRestrict.toLinearMap ψ.rangeRestrict_surjective
  have hS : IsField ψ.range :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap E ψ.range).injective).1
      (Field.toIsField E)
  let E' : IntermediateField E L := ψ.range.toIntermediateField' hS
  let ψ' : Γ(W, ⊤) →+* E' := ψ.rangeRestrict.toRingHom
  refine ⟨E', this, Spec.map (CommRingCat.ofHom ψ') ≫ W.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφh, ← Spec.map_comp]
    congr 1
    ext e
    exact ψ.commutes e
  · rw [← Category.assoc, ← Spec.map_comp,
      show CommRingCat.ofHom ψ' ≫ CommRingCat.ofHom (algebraMap E' L) = φs from rfl, hφs,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Stacks.EtaleCohomology

end
