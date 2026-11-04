module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Sections defining a good elementary fibration through a point

In the pointwise form of Artin's good neighbourhoods (SGA 4, Exposé XI, Proposition 3.3) a
neighbourhood of a closed point `x` of a smooth variety is fibred over `𝔸^{d-1}` by a projection
`t = (v₁/w₀, …, v_{d-1}/w₀)` given by sections `v₁, …, v_{d-1}, w₀` of an invertible module `L` on
a normal projective compactification `X̄`. Every property of the resulting family that the
construction has to control is a property of the one fibre through `x`, namely the curve
`C = V(v₁, …, v_{d-1}) ⊂ X̄` (the `vᵢ` vanish at `x`), and all of it is over the base field. This
file records those properties as the proposition
`AlgebraicGeometry.GoodNeighbourhood.GoodSections`, and the existence statement that the Bertini
theorems are to supply as `AlgebraicGeometry.GoodNeighbourhood.ExistsGoodSections`.

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.partialIdeal`: the ideal of `V(v₁, …, v_m)`.
* `AlgebraicGeometry.GoodNeighbourhood.SubschemeSmoothAt`: a closed subscheme is smooth of a given
  relative dimension at a point.
* `AlgebraicGeometry.GoodNeighbourhood.GoodSections`: the properties of the curve `C` through `x`.
* `AlgebraicGeometry.GoodNeighbourhood.ExistsGoodSections`: good sections exist for every normal
  projective variety with a smooth open and a closed point in it.

## The conditions

With `W ⊆ X̄` the smooth open (the part of the variety that is compactified), `Y = X̄ ∖ W` with its
reduced structure and `x ∈ W`:

1. `x ∈ C` and `w₀(x) ≠ 0`;
2. at every point `z ∈ C`, each partial intersection `V(v₁, …, v_m)` (`m ≤ d - 1`) is smooth of
   relative dimension `d - m` over `k` — in particular `C` misses the singular locus of `X̄`;
3. at every point `z ∈ C ∖ W`, each `Y ∩ V(v₁, …, v_m)` is smooth of relative dimension
   `d - 1 - m` — `C` meets the boundary transversally, at smooth points of `Y`;
4. every point `z ∈ C` with `w₀(z) = 0` lies in `W`, and `V(v₁, …, v_{d-1}, w₀)` is smooth of
   relative dimension `0` at `z` — the base locus `E = C ∩ V(w₀)` is reduced and inside `W`;
5. `E` is nonempty.

The partial intersections are what the fibrewise smoothness criterion consumes (Tag 062Y one
equation at a time), conditions 2 and 4 give smoothness of the family and étaleness of the
boundary at `E`, condition 3 étaleness of the boundary at `C ∖ W`, and a point of `E` is the
section of the family.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **The ideal of `V(v₁, …, v_m)`**: the supremum of the zero schemes of the first `m` of the
sections `v`. For `m = 0` it is `⊥`, cutting out the whole scheme. -/
noncomputable def partialIdeal {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {c : ℕ}
    (v : Fin c → Γ(L, ⊤)) (m : ℕ) : X.IdealSheafData :=
  ⨆ (j : Fin c) (_ : j.val < m), zeroScheme X L (v j)

/-- **A closed subscheme is smooth of relative dimension `n` at a point `z` of the ambient
scheme**: `z` lies on the subscheme cut out by `I`, and the subscheme is smooth of relative
dimension `n` over the base on an open neighbourhood of `z`. -/
def SubschemeSmoothAt {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (n : ℕ) (z : X) :
    Prop :=
  ∃ y : I.subscheme, I.subschemeι y = z ∧
    ∃ U : I.subscheme.Opens, y ∈ U ∧ SmoothOfRelativeDimension n (U.ι ≫ I.subschemeι ≫ f)

/-- **Good sections through a point** (SGA 4, Exposé XI, Proposition 3.3, the genericity of the
projection). Let `p̄ : X̄ ⟶ Spec k`, `W ⊆ X̄` open, `x ∈ W`, and let `v₁, …, v_{d-1}, w₀` be
sections of an invertible module `L`. Write `C = V(v₁, …, v_{d-1})` and `Y` for the reduced
closed subscheme on `X̄ ∖ W`. The sections are good if `x ∈ C`, `w₀(x) ≠ 0`, every partial
intersection `V(v₁, …, v_m)` is smooth of relative dimension `d - m` along `C`, every
`Y ∩ V(v₁, …, v_m)` is smooth of relative dimension `d - 1 - m` along `C ∖ W`, the points of `C`
where `w₀` vanishes lie in `W` and `V(v₁, …, v_{d-1}, w₀)` is smooth of relative dimension `0`
there, and there is such a point. -/
def GoodSections (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (d : ℕ)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (W : X.Opens) (x : X) (v : Fin (d - 1) → Γ(L, ⊤)) (w₀ : Γ(L, ⊤)) : Prop :=
  x ∈ (partialIdeal L v (d - 1)).support ∧ x ∉ (zeroScheme X L w₀).support ∧
  (∀ z ∈ (partialIdeal L v (d - 1)).support, ∀ m ≤ d - 1,
    SubschemeSmoothAt p (partialIdeal L v m) (d - m) z) ∧
  (∀ z ∈ (partialIdeal L v (d - 1)).support, z ∉ W → ∀ m ≤ d - 1,
    SubschemeSmoothAt p
      (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ ⊔
        partialIdeal L v m) (d - 1 - m) z) ∧
  (∀ z ∈ (partialIdeal L v (d - 1)).support, z ∈ (zeroScheme X L w₀).support →
    z ∈ W ∧ SubschemeSmoothAt p (partialIdeal L v (d - 1) ⊔ zeroScheme X L w₀) 0 z) ∧
  ∃ z ∈ (partialIdeal L v (d - 1)).support, z ∈ (zeroScheme X L w₀).support

/-- **Good sections exist** (the Bertini input of SGA 4, Exposé XI, Proposition 3.3). For every
normal integral projective `X̄` over `k`, every open `W ⊆ X̄` smooth of relative dimension `d ≥ 1`
over `k` and every closed point `x ∈ W`, some invertible module on `X̄` has good sections through
`x` (`AlgebraicGeometry.GoodNeighbourhood.GoodSections`). This holds for `k` algebraically closed:
the `vᵢ` are general members of a very ample system vanishing at `x`, and `w₀` a general member
not vanishing at `x`. -/
def ExistsGoodSections (k : Type u) [Field k] : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (d : ℕ), IsProjectiveMorphism p → IsIntegral X →
    IsNormal X → ∀ W : X.Opens, SmoothOfRelativeDimension d (W.ι ≫ p) → 1 ≤ d →
    ∀ x ∈ W, IsClosed ({x} : Set X) →
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
      (v : Fin (d - 1) → Γ(L, ⊤)) (w₀ : Γ(L, ⊤)), GoodSections k p d L W x v w₀

end AlgebraicGeometry.GoodNeighbourhood

end
