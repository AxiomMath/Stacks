module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Blowup

/-!
# Weil cohomology theories, III: the axioms (A5) and (A7)

Section 45.14 of the Stacks Project (Tag 0FID) works with data (D0), (D1), (D2') —
`Stacks.WeilCohomology.FirstChernClassData` — over the category of smooth projective schemes over
`k`, here `Stacks.WeilCohomology.(SmoothProjectiveScheme k).FullSubcategory`, the full subcategory
of schemes over `k` cut out by `Stacks.WeilCohomology.SmoothProjectiveScheme k`. Axioms (A1)–(A4)
are in `StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassData`. This file states two
more, as the source words them:

* (A5) `H^*` is compatible with finite products: `H^*(Spec k) = F`, and for `X`, `Y` smooth
  projective over `k` the map `H^*(X) ⊗_F H^*(Y) ⟶ H^*(X × Y)`, `a ⊗ b ↦ p^*a ∪ q^*b`, is an
  isomorphism, `p` and `q` being the projections;
* (A7) if `b : X' ⟶ X` is the blowing up of a smooth projective scheme `X` over `k` in a smooth
  centre, then `b^* : H^*(X) ⟶ H^*(X')` is injective. The smooth centre is a closed immersion
  `i : Z ⟶ X` of smooth projective schemes over `k`.

Axiom (A6) involves the class `γ([Δ])` of the diagonal, which needs the cycle class map of Tag
0FIF, and is stated with it.

## The centre in (A7)

The centre of (A7) is a closed subscheme `Z` of `X`, smooth over `k` (given as a closed immersion
`i : Z ⟶ X` of smooth projective schemes over `k`), which is nowhere dense in `X`. The source does
not say "nowhere dense", but it cannot mean otherwise: blowing up `X` in a centre containing a
connected component `C` of `X` removes `C` (the Rees algebra of the zero ideal on `C` has no
positive degrees, so its `Proj` is empty over `C`), so `b^*` would have to inject `H^*(C)` into
`0`, and with (A5) and (A1) no nonempty `C` would be allowed. (A7) is applied in the source (Lemma
0FII) to blowups `b` that are isomorphisms over a dense open, which is what nowhere density of the
centre gives. Requiring it makes the axiom weaker, so everything proved from it holds a fortiori
for the literal reading.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.kunnethMap`: `a ⊗ b ↦ p^*a ∪ q^*b`.
* `Stacks.WeilCohomology.FirstChernClassData.KunnethAxiom`: axiom (A5).
* `Stacks.WeilCohomology.FirstChernClassData.BlowupAxiom`: axiom (A7).

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u w

namespace Stacks.WeilCohomology.FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- **The Künneth map** `H^*(X) ⊗_F H^*(Y) ⟶ H^*(X × Y)`, `a ⊗ b ↦ p^*a ∪ q^*b`, with `p`, `q`
the two projections of `X × Y = X ×_k Y`. -/
def kunnethMap (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔇.H X ⊗[F] 𝔇.H Y →ₗ[F] 𝔇.H (SmoothProjectiveScheme.prod X Y) :=
  TensorProduct.lift ((LinearMap.mul F _).compl₁₂
    (𝔇.pull (SmoothProjectiveScheme.fst X Y)).toLinearMap
    (𝔇.pull (SmoothProjectiveScheme.snd X Y)).toLinearMap)

/-- The Künneth map sends `a ⊗ b` to `p^*a ∪ q^*b`. -/
@[simp]
theorem kunnethMap_tmul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) (b : 𝔇.H Y) :
    𝔇.kunnethMap X Y (a ⊗ₜ b) =
      𝔇.pull (SmoothProjectiveScheme.fst X Y) a * 𝔇.pull (SmoothProjectiveScheme.snd X Y) b :=
  rfl

/-- **Axiom (A5)**: `H^*` is compatible with finite products. `H^*(Spec k) = F`, that is, the
structure map `F ⟶ H^*(Spec k)` is bijective, and for all `X`, `Y` the Künneth map
`H^*(X) ⊗_F H^*(Y) ⟶ H^*(X × Y)`, `a ⊗ b ↦ p^*a ∪ q^*b`, is bijective. -/
def KunnethAxiom : Prop :=
  Function.Bijective (Algebra.linearMap F (𝔇.H (SmoothProjectiveScheme.point k))) ∧
    ∀ X Y : (SmoothProjectiveScheme k).FullSubcategory, Function.Bijective (𝔇.kunnethMap X Y)

/-- **Axiom (A7)**: if `b : X' ⟶ X` is the blowing up of a smooth projective scheme `X` over `k`
in a smooth centre `i : Z ⟶ X` (a closed immersion of smooth projective schemes over `k`, with
`Z` nowhere dense in `X`, see the module documentation), then `b^* : H^*(X) ⟶ H^*(X')` is
injective. -/
def BlowupAxiom : Prop :=
  ∀ (Z X : (SmoothProjectiveScheme k).FullSubcategory) (i : Z ⟶ X) [IsClosedImmersion i.hom.left],
    IsNowhereDense (Set.range i.hom.left.base) →
      Function.Injective (𝔇.pull (SmoothProjectiveScheme.blowupHom i))

end Stacks.WeilCohomology.FirstChernClassData

end
