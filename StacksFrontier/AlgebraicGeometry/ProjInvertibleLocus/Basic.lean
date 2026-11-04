module

public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Trivialization
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor

/-!
# The locus on `Proj S` where the `d`-divisible twists are invertible

Let `S` be a graded ring, `X = Proj(S)` and `d ≥ 1`. Tag 01MU identifies two opens of `X`:

1. the largest open `W_d` on which every `𝒪_X(dn)` is invertible and every multiplication map
   `𝒪_X(nd)|_W ⊗ 𝒪_X(md)|_W → 𝒪_X(nd + md)|_W` is an isomorphism; and
2. the union of the standard opens `D₊(fg)` with `f`, `g` homogeneous and
   `deg f = deg g + d`.

This file carries Tag 01MU's vocabulary — the goodness condition, the open `W_d`, and the
multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` — together with the part of the identity that is
provable from what this repository has.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`: the canonical
  multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` of Tag 01MO.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.IsGoodOpen`: Tag 01MU's condition (1) on a
  single open.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible`: the open `W_d`, as the
  supremum of the good opens.

## Main results

* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.le_whereInvertible_of_isGoodOpen`: a good open
  lies in `W_d`. This is the easy half of Tag 01MU's maximality assertion.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.iSup_basicOpen_mul_eq_ratioLocus`: Tag 01MU's
  open (2) is `Stacks.AlgebraicGeometry.ProjShared.ratioLocus`, by `Iff.rfl`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_pullback_twistingSheaf_basicOpen_mul`:
  **the first half of goodness of `D₊(pq)`** — every `𝒪(dn)` is invertible after restriction to
  `D₊(pq)` when `deg p = deg q + d`. This is the sheaf-theoretic content of Tag 01MU's first
  inclusion and it is proved here in full, for every `n : ℤ` and with no hypothesis on `d`.
* `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isGoodOpen_basicOpen_mul_of_isIso_mul` and
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioLocus_le_whereInvertible_of_isIso_mul`:
  Tag 01MU's inclusion `W_d ⊇ ⋃ D₊(fg)`, **reduced to the single remaining gap** — that the
  multiplication maps become isomorphisms on `D₊(pq)`.

## Implementation notes

Tag 01MU's assertions are *not* proved here, and the only `stacks` attribute this file carries is
for Tag 01MO, the construction of the multiplication map itself. The two assertions of
Tag 01MU are

* `IsGoodOpen 𝒮 d U ↔ U ≤ whereInvertible 𝒮 d`, and
* `whereInvertible 𝒮 d = ⨆ (e) (f : 𝒮 (e+d)) (g : 𝒮 e), Proj.basicOpen 𝒮 (f * g)`,

and three of the four inclusions they comprise need mathematics that is absent from this
repository, namely Tag 0B8M (invertible ⟺ locally free of rank 1, and its descent):

* the `←` direction of the first needs `IsGoodOpen` to be closed under passing to a smaller
  open and under arbitrary suprema. Invertibility is defined here, following Tag 01CS, as "the
  tensor functor is an equivalence", a property with no visible locality; recovering locality is
  exactly the descent step that `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Invertible.lean`
  states in its own implementation notes is deliberately not formalized.
* `whereInvertible 𝒮 d ≤ ratioLocus 𝒮 d` needs, from invertibility on a neighbourhood of `x`,
  a *generating section* of `𝒪(d)` near `x` — i.e. freeness of rank one, which is the other
  unformalized direction of Tag 0B8M. The purely algebraic remainder of that argument, from the
  relation `g^{d+e+deg g} = a f^{deg g}` to `x ∈ D₊(f)`, is
  `Stacks.AlgebraicGeometry.ProjShared.basicOpen_le_ratioLocus_of_pow_eq_mul_pow`.
* `ratioLocus 𝒮 d ≤ whereInvertible 𝒮 d` needs goodness of each `D₊(pq)`. Its invertibility
  half is proved here; its multiplication half is the hypothesis of
  `ratioLocus_le_whereInvertible_of_isIso_mul`.

The hypothesis of `ratioLocus_le_whereInvertible_of_isIso_mul` is phrased on the restricted
site (`SheafOfModules.Hom.over`) rather than on the open subscheme, because that is where it is
provable: `twistMultiplicationMap` is a morphism out of a *sheafified* tensor product, so its
sections are reached only through the sheafification adjunction, whose unit lives on the same
site as the sheaves. `isIso_restrictFunctor_map_of_isIso_over` converts.

Tag 01MU's third assertion, that `M̃ ⊗ 𝒪(nd) → M(nd)̃` is an isomorphism on `W_d`, is not stated
in this file. Its target `associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 a)` needs
`DirectSum.Decomposition` and `SetLike.GradedSMul` for the shifted grading, which are
`Stacks.GradedModule.shiftedGradingDecomposition` and `.shiftedGradingGradedSMul` in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwistGlobalSections.lean`; the map
`moduleTwistMap` itself is stated in `StacksFrontier/AlgebraicGeometry/ProjShifted/Basic.lean`, its
degree-preservation input being `Stacks.GradedModule.rid_mem_shiftedGrading`.

The `VAdd ℕ ℤ` instance is local, as in `StacksFrontier/AlgebraicGeometry/ProjTwists/Basic.lean`:
Mathlib has none, and it is the one with respect to which
`SetLike.GradedSMul 𝒮 𝒨` says that a nonnegatively graded ring acts on an integer-graded
module.

Tag 01MU writes its twists as `d * n`, while the trivialization of
`StacksFrontier/AlgebraicGeometry/ProjInvertibleLocus/Trivialization.lean` is indexed by
`n * d`; the two are equal only propositionally in `ℤ`, which is why that file takes the twist
index as a variable with an equation rather than as a literal product.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The action of `ℕ` on `ℤ` by addition, which lets a nonnegatively graded ring act on an
integer-graded module. -/
local instance instVAddNatInt : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-! ### The multiplication maps between twists -/

/-- Multiplication takes the graded tensor product of two twists of the regular module into the
twist by the sum of the indices. This is Tag 01MU's degree-preservation clause, in the spelling
of `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading`; it is
`Stacks.GradedModule.lid_mem_twistGrading`, the two gradings being definitionally equal. -/
theorem twistMultiplication_preserves_grading (a b i : ℤ) (z : S ⊗[S] S)
    (hz : z ∈ Stacks.GradedModule.tensorGrading
      (twistGrading (S := S) 𝒮 a) (twistGrading (S := S) 𝒮 b) i) :
    (TensorProduct.lid S S).toLinearMap z ∈ twistGrading (S := S) 𝒮 (a + b) i :=
  Stacks.GradedModule.lid_mem_twistGrading 𝒮 a b i z hz

/-- The canonical multiplication map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` on `Proj S`: the associated-sheaf
tensor map followed by the sheaf map induced by multiplication `S(a) ⊗ S(b) → S(a+b)`. -/
noncomputable def twistMultiplicationMap (a b : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((AlgebraicGeometry.Proj
      𝒮).toRingedSpace)).presheaf, (((AlgebraicGeometry.Proj
      𝒮).toRingedSpace)).IsSheaf⟩).obj ((twistingSheaf 𝒮 a))).obj ((twistingSheaf 𝒮 b))) ⟶
        twistingSheaf 𝒮 (a + b) := by
  letI := tensorGrading_decomposition (S := S) 𝒮
    (twistGrading (S := S) 𝒮 a) (twistGrading (S := S) 𝒮 b)
  letI := tensorGrading_gradedSMul (S := S) 𝒮
    (twistGrading (S := S) 𝒮 a) (twistGrading (S := S) 𝒮 b)
  exact associatedModuleSheafTensorMap 𝒮
      (twistGrading (S := S) 𝒮 a) (twistGrading (S := S) 𝒮 b) ≫
    associatedModuleSheafMap 𝒮
      (Stacks.GradedModule.tensorGrading
        (twistGrading (S := S) 𝒮 a) (twistGrading (S := S) 𝒮 b))
      (twistGrading (S := S) 𝒮 (a + b))
      (TensorProduct.lid S S).toLinearMap
      (twistMultiplication_preserves_grading 𝒮 a b)

add_to_stacks 01MO twistMultiplicationMap

/-! ### The goodness condition and the invertible locus -/

/-- Tag 01MU's condition on an open `U`: the restrictions of all `d`-divisible twists are
invertible, and the canonical multiplication maps between them restrict to isomorphisms. -/
def IsGoodOpen (d : ℕ) (U : (AlgebraicGeometry.Proj 𝒮).Opens) : Prop :=
  (∀ n : ℤ,
    SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback U.ι).obj (twistingSheaf 𝒮 ((d : ℤ) * n)))) ∧
  (∀ n m : ℤ,
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m))))

/-- The largest open on which the `d`-divisible twists and their multiplication maps have the
required invertibility property: Tag 01MU's `W_d`. -/
def whereInvertible (d : ℕ) : (AlgebraicGeometry.Proj 𝒮).Opens :=
  sSup {U | IsGoodOpen 𝒮 d U}

/-- A good open lies in the invertible locus. This is the easy half of Tag 01MU's maximality
assertion, and the only half that does not need Tag 0B8M. -/
theorem le_whereInvertible_of_isGoodOpen {d : ℕ} {U : (AlgebraicGeometry.Proj 𝒮).Opens}
    (hU : IsGoodOpen 𝒮 d U) : U ≤ whereInvertible 𝒮 d :=
  le_sSup hU

/-- Tag 01MU's second open subset is `ratioLocus`, definitionally. -/
theorem iSup_basicOpen_mul_eq_ratioLocus (d : ℕ) :
    (⨆ (e : ℕ) (f : 𝒮 (e + d)) (g : 𝒮 e),
      AlgebraicGeometry.Proj.basicOpen 𝒮 ((f : S) * (g : S))) = ProjShared.ratioLocus 𝒮 d :=
  rfl

/-! ### The invertibility half of goodness of `D₊(pq)` -/

variable {p q : S} {e d : ℕ}

/-- **The sheaf-theoretic content of Tag 01MU's first inclusion.** For `p` homogeneous of degree
`e + d` and `q` homogeneous of degree `e`, every twist `𝒪(dn)` becomes invertible after
restriction to the standard open `D₊(pq)`: it is trivialized there by `(p/q)^n`. No hypothesis
on `d` is needed. -/
theorem isInvertible_pullback_twistingSheaf_basicOpen_mul (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e)
    (n : ℤ) :
    SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)).toScheme.presheaf
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)).toScheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)).ι).obj
        (twistingSheaf 𝒮 ((d : ℤ) * n))) :=
  isInvertible_pullback_of_iso_unit _ _
    (ratioOverIsoUnit 𝒮 hp hq (mul_comm (n : ℤ) (d : ℤ)))

/-- Tag 01MU's first inclusion, reduced to its one remaining gap: `D₊(pq)` is a good open as
soon as the multiplication maps between the `d`-divisible twists restrict to isomorphisms on
the restricted site of `D₊(pq)`. -/
theorem isGoodOpen_basicOpen_mul_of_isIso_mul (hp : p ∈ 𝒮 (e + d)) (hq : q ∈ 𝒮 e)
    (hmul : ∀ n m : ℤ, IsIso ((twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m)).over
      (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)))) :
    IsGoodOpen 𝒮 d (AlgebraicGeometry.Proj.basicOpen 𝒮 (p * q)) :=
  ⟨isInvertible_pullback_twistingSheaf_basicOpen_mul 𝒮 hp hq,
    fun n m => isIso_restrictFunctor_map_of_isIso_over _ _ (hmul n m)⟩

/-- Tag 01MU's inclusion `⋃ D₊(fg) ⊆ W_d`, reduced to the same single gap. -/
theorem ratioLocus_le_whereInvertible_of_isIso_mul (d : ℕ)
    (hmul : ∀ (e : ℕ) (f : 𝒮 (e + d)) (g : 𝒮 e) (n m : ℤ),
      IsIso ((twistMultiplicationMap 𝒮 ((d : ℤ) * n) ((d : ℤ) * m)).over
        (AlgebraicGeometry.Proj.basicOpen 𝒮 ((f : S) * (g : S))))) :
    ProjShared.ratioLocus 𝒮 d ≤ whereInvertible 𝒮 d := by
  rw [← iSup_basicOpen_mul_eq_ratioLocus 𝒮 d]
  refine iSup_le fun e => iSup_le fun f => iSup_le fun g => ?_
  exact le_whereInvertible_of_isGoodOpen 𝒮
    (isGoodOpen_basicOpen_mul_of_isIso_mul 𝒮 f.2 g.2 (hmul e f g))

end Stacks.AlgebraicGeometry.ProjInvertibleLocus

end
