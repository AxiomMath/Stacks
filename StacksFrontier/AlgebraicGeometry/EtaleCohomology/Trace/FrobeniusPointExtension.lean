module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageStalkEnd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf

/-!
# The geometric Frobenius at a point above a point

Let `g : X' ⟶ X` be a morphism of schemes and `y` a point of `X'` with finite residue field,
lying over `x = g(y)`, with `#κ(y) = #κ(x) ^ e`.  Then the geometric Frobenius at `y`, pushed to
`X` along `g`, is related by a morphism of geometric points to the `e`-th power of the geometric
Frobenius at `x`: an embedding `κ(x)‾ ⟶ κ(y)‾` of algebraic closures over `κ(x) ⟶ κ(y)` commutes
with raising to the power `#κ(y) = #κ(x) ^ e`.  Consequently, for an ℓ-adic sheaf `F` on `X`,

`Tr(π_y | (g⁻¹F)_ȳ) = Tr(π_x ^ e | F_x̄)`.

This is the point side of the reduction, in the proof of [Stacks, Tag 03V0], of the trace formula
for `π_X^m` to Tag 03V2 for `X ×_k k_m`: a point of `X ×_k k_m` of degree one over `k_m` over a
closed point `x` of degree `d ∣ m` has residue field `k_m`, of cardinality `#κ(x) ^ (m / d)`.

## Main results

* `Stacks.Frobenius.frobeniusPointHom_iterate_comm`: the morphism of geometric points.
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_inverseImage`: the trace
  identity.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Morphisms of geometric points are determined by their underlying morphisms of schemes. -/
lemma GeometricPoint.Hom.ext' {S : Scheme.{u}} {s t : GeometricPoint S}
    {a b : GeometricPoint.Hom s t}
    (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

end AlgebraicGeometry

namespace Stacks.Frobenius

section Iterate

variable {k : Type u} [Field k] {X : Scheme.{u}} (K : Type u) [Field K] [IsAlgClosed K]
  [Algebra k K]

/-- The iterates of `Spec σ` are `Spec` of the powers of `σ`. -/
lemma galoisPointHom_iterate_hom (σ : K ≃ₐ[k] K) (x : Spec (.of k) ⟶ X) (e : ℕ) :
    ((galoisPointHom K σ x).iterate e).hom =
      Spec.map (CommRingCat.ofHom (σ ^ (e + 1)).toAlgHom.toRingHom) := by
  induction e with
  | zero => rw [zero_add, pow_one]; rfl
  | succ e ih =>
      change ((galoisPointHom K σ x).iterate e).hom ≫ (galoisPointHom K σ x).hom = _
      rw [ih, galoisPointHom_hom, ← Spec.map_comp, pow_succ σ (e + 1)]
      rfl

end Iterate

section PointAbove

variable {X' X : Scheme.{u}} (g : X' ⟶ X) (y : X')

/-- `κ(y)‾` as an algebra over `κ(g(y))`, through `κ(g(y)) ⟶ κ(y)`. -/
abbrev residueClosureAlgebra :
    Algebra (X.residueField (g.base y)) (AlgebraicClosure (X'.residueField y)) :=
  ((algebraMap (X'.residueField y) (AlgebraicClosure (X'.residueField y))).comp
    (g.residueFieldMap y).hom).toAlgebra

/-- An embedding `κ(g(y))‾ ⟶ κ(y)‾` of algebraic closures over `κ(g(y)) ⟶ κ(y)`. -/
def residueClosureEmbedding :
    AlgebraicClosure (X.residueField (g.base y)) →+* AlgebraicClosure (X'.residueField y) :=
  let := residueClosureAlgebra g y
  (IsAlgClosed.lift (M := AlgebraicClosure (X'.residueField y))
    (R := X.residueField (g.base y)) (S := AlgebraicClosure (X.residueField (g.base y)))).toRingHom

/-- The embedding extends `κ(g(y)) ⟶ κ(y)`. -/
lemma residueClosureEmbedding_algebraMap (z : X.residueField (g.base y)) :
    residueClosureEmbedding g y (algebraMap _ _ z) =
      algebraMap (X'.residueField y) (AlgebraicClosure (X'.residueField y))
        ((g.residueFieldMap y).hom z) := by
  let := residueClosureAlgebra g y
  exact (IsAlgClosed.lift (M := AlgebraicClosure (X'.residueField y))
    (R := X.residueField (g.base y))
    (S := AlgebraicClosure (X.residueField (g.base y)))).commutes z

/-- **The morphism of geometric points** from the geometric point at `y`, pushed to `X`, to the
geometric point at `g(y)`: `Spec` of the embedding of algebraic closures. -/
def residueClosurePointHom :
    GeometricPoint.Hom ((geometricPointAt X' y).map g) (geometricPointAt X (g.base y)) where
  hom := Spec.map (CommRingCat.ofHom (residueClosureEmbedding g y))
  comm := by
    change Spec.map (CommRingCat.ofHom (residueClosureEmbedding g y)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (g.base y))
          (AlgebraicClosure (X.residueField (g.base y))))) ≫ X.fromSpecResidueField (g.base y) =
      (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField y)
        (AlgebraicClosure (X'.residueField y)))) ≫ X'.fromSpecResidueField y) ≫ g
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext z
    change residueClosureEmbedding g y (algebraMap _ _ z) =
      algebraMap (X'.residueField y) (AlgebraicClosure (X'.residueField y))
        ((g.residueFieldMap y).hom z)
    exact residueClosureEmbedding_algebraMap g y z

variable [Finite (X'.residueField y)] [Finite (X.residueField (g.base y))]

/-- **The geometric Frobenius at `y` is carried to the `(e + 1)`-st power of the geometric
Frobenius at `g(y)`** when `#κ(y) = #κ(g(y)) ^ (e + 1)`. -/
theorem frobeniusPointHom_iterate_comm (e : ℕ)
    (he : Nat.card (X'.residueField y) = Nat.card (X.residueField (g.base y)) ^ (e + 1)) :
    (residueClosurePointHom g y).comp ((frobeniusPointHom X (g.base y)).iterate e) =
      ((frobeniusPointHom X' y).mapHom g).comp (residueClosurePointHom g y) := by
  refine GeometricPoint.Hom.ext' ?_
  change Spec.map (CommRingCat.ofHom (residueClosureEmbedding g y)) ≫
      ((frobeniusPointHom X (g.base y)).iterate e).hom =
    Spec.map (CommRingCat.ofHom (residueGeometricFrobenius X' y).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (residueClosureEmbedding g y))
  rw [frobeniusPointHom, galoisPointHom_iterate_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  change residueClosureEmbedding g y (((residueGeometricFrobenius X (g.base y)) ^ (e + 1)) z) =
    residueGeometricFrobenius X' y (residueClosureEmbedding g y z)
  apply (residueGeometricFrobenius X' y).symm.injective
  rw [AlgEquiv.symm_apply_apply, residueGeometricFrobenius_symm_apply, ← map_pow, he]
  congr 1
  have key : ∀ (n : ℕ) (w : AlgebraicClosure (X.residueField (g.base y))),
      (((residueGeometricFrobenius X (g.base y)) ^ n) w) ^
        Nat.card (X.residueField (g.base y)) ^ n = w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
        intro w
        rw [pow_succ' (residueGeometricFrobenius X (g.base y)) n, AlgEquiv.mul_apply,
          pow_succ' (Nat.card (X.residueField (g.base y))) n, pow_mul,
          ← residueGeometricFrobenius_symm_apply, AlgEquiv.symm_apply_apply]
        exact ih w
  exact key (e + 1) z

end PointAbove

end Stacks.Frobenius

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.SmallEtale Stacks.Frobenius

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} (g : X' ⟶ X) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian X'.obj]

/-- **The trace of the geometric Frobenius at a point above a point.**  If `y` is a point of `X'`
with finite residue field over `x = g(y)`, with `#κ(y) = #κ(x) ^ (e + 1)`, then
`Tr(π_y | (g⁻¹F)_ȳ ⊗ ℚ_ℓ) = Tr(π_x ^ (e + 1) | F_x̄ ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.trace_rationalStalkFrobenius_inverseImage (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (y : X'.1) (hy : Finite (X'.1.residueField y))
    (hx : Finite (X.1.residueField ((B.inclusion.map g).base y))) (e : ℕ)
    (he : Nat.card (X'.1.residueField y) =
      Nat.card (X.1.residueField ((B.inclusion.map g).base y)) ^ (e + 1)) :
    LinearMap.trace (Padic ℓ) _
        (LAdicSheaf.rationalStalkFrobenius B X' ℓ (LAdicSheaf.inverseImage g F) y hy) =
      LinearMap.trace (Padic ℓ) _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F ((B.inclusion.map g).base y) hx ^ (e + 1)) := by
  have := hy
  have := hx
  have : Finite ((B.inclusion.obj X').residueField y) := hy
  have : Finite ((B.inclusion.obj X).residueField ((B.inclusion.map g).base y)) := hx
  change LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X' ℓ
      (LAdicSheaf.inverseImage g F) (frobeniusPointHom X'.1 y)) =
    LinearMap.trace (Padic ℓ) _ (LAdicSheaf.rationalStalkEnd B X ℓ F
      (frobeniusPointHom X.1 ((B.inclusion.map g).base y)) ^ (e + 1))
  rw [trace_inverseImage_rationalStalkEnd, ← LAdicSheaf.rationalStalkEnd_iterate]
  exact LAdicSheaf.trace_rationalStalkEnd_eq_of_comm B X ℓ F
    (residueClosurePointHom (B.inclusion.map g) y) _ _
    (frobeniusPointHom_iterate_comm (B.inclusion.map g) y e he)

end Stacks.EtaleCohomology

end
