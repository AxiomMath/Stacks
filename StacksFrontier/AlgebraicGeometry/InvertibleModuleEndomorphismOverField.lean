module

import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear

/-!
# Endomorphisms of an invertible module over a field are the scalars

Let `f : X ⟶ Spec k` be a scheme over a field whose global functions are the constants, that is,
`k → Γ(X, 𝒪_X)` is an isomorphism. For the `k`-linear structure
`AlgebraicGeometry.modulesLinearOverField` on `𝒪_X`-modules, this file proves that the
endomorphisms of an invertible `𝒪_X`-module `ℒ` are exactly the scalars: `c ↦ c • 𝟙 ℒ` is a
`k`-linear isomorphism `k ≃ End(ℒ)`, so `dim_k End(ℒ) = 1`.

The argument has three steps.

* On the structure sheaf an endomorphism is multiplication by the global function it sends `1`
  to (`AlgebraicGeometry.IntegralTransformQcoh.sectionScalar_unit_surjective`), and
  multiplication by the image of `c ∈ k` is `c • 𝟙`
  (`AlgebraicGeometry.IntegralTransformQcoh.sectionScalar_base`); as every global function is
  the image of a constant, every endomorphism of `𝒪_X` is a scalar.
* Tensoring on the left by `ℒ` is a `k`-linear functor
  (`AlgebraicGeometry.tensorLeft_linear`) and an autoequivalence ([Stacks, Tag 01CS]) carrying
  `𝒪_X` to `ℒ` (the first tensor power of [Stacks, Tag 01CU]). Conjugating an endomorphism `φ`
  of `ℒ` back to `𝒪_X` along it, `φ` is the image of a scalar, hence a scalar.
* `𝟙 ℒ ≠ 0`: it corresponds to `𝟙 𝒪_X` under that conjugation, which is not zero because it
  sends the global function `1` to `1` and `Γ(X, 𝒪_X) = k` is not the zero ring. So
  `c • 𝟙 ℒ = 0` forces `c = 0`.

## Main results

* `AlgebraicGeometry.exists_eq_smul_id_unit`: an endomorphism of `𝒪_X` is a scalar.
* `AlgebraicGeometry.exists_eq_smul_id_of_isInvertible`: an endomorphism of an invertible
  module is a scalar.
* `AlgebraicGeometry.endLinearEquivOfIsInvertible`: `k ≃ₗ[k] End(ℒ)`, `c ↦ c • 𝟙 ℒ`.
* `AlgebraicGeometry.finrank_end_eq_one_of_isInvertible`: `dim_k End(ℒ) = 1`.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

include f

/-- **An endomorphism of `𝒪_X` is a scalar** on a scheme over `k` whose global functions are
the constants: it is multiplication by the global function it sends `1` to, and that function
is the image of a scalar `c ∈ k`, multiplication by which is `c • 𝟙`. -/
theorem exists_eq_smul_id_unit
    (χ : structureSheafModule X ⟶ structureSheafModule X) :
    letI := modulesLinearOverField k f
    ∃ c : k, χ = c • 𝟙 (structureSheafModule X) := by
  let := modulesLinearOverField k f
  obtain ⟨a, rfl⟩ := IntegralTransformQcoh.sectionScalar_unit_surjective X χ
  set g := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  refine ⟨(inv g).hom a, ?_⟩
  have ha : f.appTop ((Scheme.ΓSpecIso (.of k)).inv ((inv g).hom a)) = a :=
    congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(X, ⊤) => φ.hom a) (IsIso.inv_hom_id g)
  have hb := IntegralTransformQcoh.sectionScalar_base k (Over.mk f) ((inv g).hom a)
    (structureSheafModule X)
  rw [← hb]
  exact congrArg (fun b => IntegralTransformQcoh.sectionScalar X b _) ha.symm

/-- On a scheme over `k` whose global functions are the constants, the identity of `𝒪_X` is not
zero: it sends the global section `1` to `1`, and `Γ(X, 𝒪_X) ≅ k` is not the zero ring. -/
theorem id_structureSheafModule_ne_zero : 𝟙 (structureSheafModule X) ≠ 0 := by
  intro h0
  have h := congrArg (fun χ : structureSheafModule X ⟶ structureSheafModule X =>
    (χ.val.app (op ⊤)).hom (1 : X.ringCatSheaf.obj.obj (op ⊤))) h0
  change (1 : Γ(X, ⊤)) = 0 at h
  have h1 := congrArg (inv ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)).hom h
  rw [map_one, map_zero] at h1
  exact one_ne_zero h1

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] in
/-- Tensoring on the left by an invertible module `ℒ` and conjugating by `ℒ ⊗ 𝒪_X ≅ ℒ` is a
`k`-linear bijection `End(𝒪_X) → End(ℒ)` sending the identity to the identity: the tensor
functor is `k`-linear and an autoequivalence ([Stacks, Tag 01CS]). -/
private theorem exists_linearMap_end_unit (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI := modulesLinearOverField k f
    ∃ E : (structureSheafModule X ⟶ structureSheafModule X) →ₗ[k] (L ⟶ L),
      Function.Bijective E ∧ E (𝟙 _) = 𝟙 L := by
  let := modulesLinearOverField k f
  let T : X.Modules ⥤ X.Modules :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (ringSheafCond X)⟩).obj L
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹_›
  have : T.Linear k := tensorLeft_linear k (Over.mk f) L
  have : T.IsEquivalence :=
    Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L
  have : T.Additive := Functor.additive_of_preserves_binary_products T
  have := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.presheaf
    X.ringCatSheaf.2 L
  let e : T.obj (structureSheafModule X) ≅ L :=
    (Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight X.presheaf X.ringCatSheaf.2
      L).app _ ≪≫ Stacks.SheafOfModules.TensorPower.tensorPowerOneIso X.presheaf
        X.ringCatSheaf.2 L
  refine ⟨(Linear.homCongr k e e).toLinearMap ∘ₗ T.mapLinearMap k,
    (Linear.homCongr k e e).bijective.comp ⟨T.map_injective, T.map_surjective⟩, ?_⟩
  simp [Linear.homCongr_apply]

variable (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- **An endomorphism of an invertible module is a scalar** on a scheme over `k` whose global
functions are the constants. Tensoring on the left by `ℒ` is a `k`-linear autoequivalence
carrying `𝒪_X` to `ℒ`; it carries the scalar endomorphisms of `𝒪_X`, which are all of them, to
the scalar endomorphisms of `ℒ`, and it is full. -/
theorem exists_eq_smul_id_of_isInvertible (φ : L ⟶ L) :
    letI := modulesLinearOverField k f
    ∃ c : k, φ = c • 𝟙 L := by
  let := modulesLinearOverField k f
  obtain ⟨E, hE, hE1⟩ := exists_linearMap_end_unit k f L
  obtain ⟨χ, rfl⟩ := hE.2 φ
  obtain ⟨c, rfl⟩ := exists_eq_smul_id_unit k f χ
  exact ⟨c, by rw [map_smul, hE1]⟩

/-- An invertible module on a scheme over `k` whose global functions are the constants is not
zero: its identity is the image of the identity of `𝒪_X` under an injective map. -/
theorem id_ne_zero_of_isInvertible : 𝟙 L ≠ 0 := by
  let := modulesLinearOverField k f
  obtain ⟨E, hE, hE1⟩ := exists_linearMap_end_unit k f L
  rw [← hE1, ← map_zero E]
  exact fun h => id_structureSheafModule_ne_zero k f (hE.1 h)

/-- **The endomorphisms of an invertible module are the scalars**, `k`-linearly: on a scheme over
a field `k` whose global functions are the constants, `c ↦ c • 𝟙 ℒ` is a `k`-linear isomorphism
from `k` onto `End(ℒ)`, for the `k`-linear structure `AlgebraicGeometry.modulesLinearOverField`.
It is onto by `AlgebraicGeometry.exists_eq_smul_id_of_isInvertible` and one-to-one because
`𝟙 ℒ ≠ 0`. -/
def endLinearEquivOfIsInvertible :
    letI := modulesLinearOverField k f
    k ≃ₗ[k] (L ⟶ L) :=
  letI := modulesLinearOverField k f
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton k (L ⟶ L) (𝟙 L))
    ⟨fun _ _ h => smul_left_injective k (id_ne_zero_of_isInvertible k f L) h,
      fun φ => (exists_eq_smul_id_of_isInvertible k f L φ).imp fun _ h => h.symm⟩

/-- The isomorphism `k ≃ End(ℒ)` sends a scalar `c` to `c • 𝟙 ℒ`. -/
@[simp]
theorem endLinearEquivOfIsInvertible_apply (c : k) :
    letI := modulesLinearOverField k f
    endLinearEquivOfIsInvertible k f L c = c • 𝟙 L :=
  rfl

/-- **`dim_k End(ℒ) = 1`** for an invertible module `ℒ` on a scheme over a field `k` whose global
functions are the constants, for the `k`-linear structure
`AlgebraicGeometry.modulesLinearOverField`. -/
theorem finrank_end_eq_one_of_isInvertible :
    letI := modulesLinearOverField k f
    Module.finrank k (L ⟶ L) = 1 :=
  let := modulesLinearOverField k f
  (endLinearEquivOfIsInvertible k f L).finrank_eq.symm.trans (Module.finrank_self k)

end AlgebraicGeometry

end
