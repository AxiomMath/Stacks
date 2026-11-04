module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplex

/-!
# Ideal powers of a split sheaf and of a mapping cone

Let `I` be a quasi-coherent sheaf of ideals on a scheme `X`. The subsheaf `I ^ n • C` of a sheaf
of modules `C` is defined by a universal property over the affine opens, so its sections cannot
be computed directly. This file shows that it nevertheless splits along any direct sum
decomposition of `C`: if `C` carries maps `A ⟶ C ⟶ A` and `B ⟶ C ⟶ B` whose two composites with
the projections add up to the identity of `C`, then a section of `C` lies in `I ^ n • C` exactly
when each of its two components lies in `I ^ n • A` and `I ^ n • B`. In short

`I ^ n • (A ⊕ B) = I ^ n • A ⊕ I ^ n • B`.

Only the completeness relation `fst ≫ inl + snd ≫ inr = 𝟙 C` is used; neither the idempotent
relations nor quasi-coherence of `A`, `B`, `C` is needed. Both halves come from the one
observation that a morphism of sheaves of modules carries `I ^ n` of its source into `I ^ n` of
its target: applied to the projections it gives the forward implication, applied to the
inclusions and combined with the completeness relation it gives the converse.

The mapping cone of a morphism `α : F ⟶ G` of cochain complexes is split in every degree, with
`C(α)^p` decomposing as `F^(p+1) ⊕ G^p`. So the splitting above computes the ideal powers of a
mapping cone degreewise:

`I ^ n • C(α)^p = I ^ n • F^(p+1) ⊕ I ^ n • G^p`

which is the term-by-term form of the identity `C(α_n)^• = I ^ n • C(α)^•` used by
[Stacks, Tag 0G4M], for the morphism `α_n` of ideal-power subcomplexes that `α` restricts to.

## Main results

* `AlgebraicGeometry.mem_idealPowerMultiple_iff_of_total`: the splitting of `I ^ n • C` along a
  direct sum decomposition of `C`.
* `AlgebraicGeometry.mem_idealPowerMultiple_biprod_iff`: the splitting for a binary biproduct.
* `AlgebraicGeometry.mem_idealPowerMultiple_mappingCone_iff`: the splitting in each degree of a
  mapping cone.

## References

* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

namespace AlgebraicGeometry

/-! ### Ideal powers of a split sheaf of modules -/

/-- **The ideal powers of a sheaf of modules split along a direct sum decomposition.** Let `C` be
a sheaf of modules presented as a direct sum of `A` and `B`, by morphisms `inl : A ⟶ C`,
`inr : B ⟶ C`, `fst : C ⟶ A` and `snd : C ⟶ B` satisfying the completeness relation
`fst ≫ inl + snd ≫ inr = 𝟙 C`. Then a section of `C` lies in `I ^ n • C` precisely when its
`A`-component lies in `I ^ n • A` and its `B`-component lies in `I ^ n • B`; that is,
`I ^ n • C = I ^ n • A ⊕ I ^ n • B`.

The forward implication is the general fact that a morphism of sheaves of modules carries
`I ^ n` of its source into `I ^ n` of its target, applied to `fst` and to `snd`. For the converse
that same fact, applied to `inl` and to `inr`, puts both summands of `fst ≫ inl + snd ≫ inr`
applied to the section inside `I ^ n • C`, and the completeness relation says their sum is the
section itself. The idempotent relations of a direct sum decomposition are not used, and no
quasi-coherence hypothesis is needed. -/
public lemma mem_idealPowerMultiple_iff_of_total {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {A B C : X.Modules} (inl : A ⟶ C) (inr : B ⟶ C) (fst : C ⟶ A) (snd : C ⟶ B)
    (htotal : fst ≫ inl + snd ≫ inr = 𝟙 C) (U : X.Opens) (x : Γ(C, U)) :
    x ∈ (idealPowerMultiple I n C).toSubmodule.obj (op U) ↔
      ((fst.val.app (op U)).hom x ∈ (idealPowerMultiple I n A).toSubmodule.obj (op U) ∧
        (snd.val.app (op U)).hom x ∈ (idealPowerMultiple I n B).toSubmodule.obj (op U)) := by
  refine ⟨fun hx => ⟨idealPowerMultiple_le_comap I n fst _ le_rfl (op U) hx,
    idealPowerMultiple_le_comap I n snd _ le_rfl (op U) hx⟩, fun ⟨ha, hb⟩ => ?_⟩
  have hid : ((fst ≫ inl + snd ≫ inr).val.app (op U)).hom x = x := by
    rw [htotal]
    rfl
  have hsplit : ((fst ≫ inl + snd ≫ inr).val.app (op U)).hom x =
      (inl.val.app (op U)).hom ((fst.val.app (op U)).hom x) +
        (inr.val.app (op U)).hom ((snd.val.app (op U)).hom x) := rfl
  rw [← hid, hsplit]
  exact Submodule.add_mem _ (idealPowerMultiple_le_comap I n inl _ le_rfl (op U) ha)
    (idealPowerMultiple_le_comap I n inr _ le_rfl (op U) hb)

/-- **The ideal powers of a binary biproduct split.** A section of `M ⊞ N` lies in
`I ^ n • (M ⊞ N)` exactly when its two biproduct components lie in `I ^ n • M` and `I ^ n • N`.

This is `AlgebraicGeometry.mem_idealPowerMultiple_iff_of_total` for the completeness relation
`CategoryTheory.Limits.biprod.total` of a binary biproduct. -/
public lemma mem_idealPowerMultiple_biprod_iff {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M N : X.Modules) (U : X.Opens) (x : Γ(M ⊞ N, U)) :
    x ∈ (idealPowerMultiple I n (M ⊞ N)).toSubmodule.obj (op U) ↔
      (((biprod.fst : M ⊞ N ⟶ M).val.app (op U)).hom x ∈
          (idealPowerMultiple I n M).toSubmodule.obj (op U) ∧
        ((biprod.snd : M ⊞ N ⟶ N).val.app (op U)).hom x ∈
          (idealPowerMultiple I n N).toSubmodule.obj (op U)) :=
  mem_idealPowerMultiple_iff_of_total I n biprod.inl biprod.inr biprod.fst biprod.snd
    biprod.total U x

/-! ### Ideal powers of a mapping cone -/

/-- **The ideal powers of a mapping cone split degreewise**, which is the term-by-term form of
the identity `C(α_n)^• = I ^ n • C(α)^•` of [Stacks, Tag 0G4M].

In degree `p` the mapping cone of `α : F ⟶ G` is the direct sum of `F^(p + 1)` and `G^p`, the
inclusions and projections being `CochainComplex.mappingCone.inl`, `.inr`, `.fst` and `.snd`. So
a section of `C(α)^p` lies in `I ^ n • C(α)^p` exactly when its `F^(p + 1)`-component lies in
`I ^ n • F^(p + 1)` and its `G^p`-component lies in `I ^ n • G^p`. Equivalently, the degree `p`
term of the ideal-power subcomplex of the cone is the direct sum of the degree `p + 1` term of
`I ^ n • F^•` and the degree `p` term of `I ^ n • G^•`, which is the degree `p` term of the cone
of the morphism of ideal-power subcomplexes that `α` restricts to. -/
public lemma mem_idealPowerMultiple_mappingCone_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) {F G : CochainComplex X.Modules ℤ} (α : F ⟶ G) (p q : ℤ) (hpq : p + 1 = q)
    (U : X.Opens) (x : Γ((CochainComplex.mappingCone α).X p, U)) :
    x ∈ (idealPowerMultiple I n ((CochainComplex.mappingCone α).X p)).toSubmodule.obj (op U) ↔
      ((((CochainComplex.mappingCone.fst α).1.v p q hpq).val.app (op U)).hom x ∈
          (idealPowerMultiple I n (F.X q)).toSubmodule.obj (op U) ∧
        (((CochainComplex.mappingCone.snd α).v p p (add_zero p)).val.app (op U)).hom x ∈
          (idealPowerMultiple I n (G.X p)).toSubmodule.obj (op U)) :=
  mem_idealPowerMultiple_iff_of_total I n
    ((CochainComplex.mappingCone.inl α).v q p (by lia))
    ((CochainComplex.mappingCone.inr α).f p)
    ((CochainComplex.mappingCone.fst α).1.v p q hpq)
    ((CochainComplex.mappingCone.snd α).v p p (add_zero p))
    (CochainComplex.mappingCone.id_X α p q hpq) U x

end AlgebraicGeometry

end
