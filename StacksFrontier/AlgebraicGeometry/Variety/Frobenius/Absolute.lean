module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.AlgebraicGeometry.Scheme
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Frobenius

/-!
# Naturality of the absolute Frobenius

A morphism of schemes in characteristic `p` commutes with their absolute Frobenius
endomorphisms, which raise sections to their `p`-th powers.

## Main results

* `Stacks.Frobenius.absoluteFrobenius_naturality`: the absolute Frobenius commutes with every
  morphism of schemes in characteristic `p`.

## References

* [Stacks Project, Tag 0CC7](https://stacks.math.columbia.edu/tag/0CC7)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Stacks.Frobenius

/-- The absolute Frobenius is natural with respect to morphisms of schemes in characteristic
`p`. -/
@[stacks 0CC7,
  ega "0 21.2.6" "more general",
  sga "3 VIIA 4.1",
  sga "4½ Rapport 1.3" "special case",
  sga "7 IX 4.3.2" "partial"]
public lemma absoluteFrobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    absoluteFrobenius X p hX ≫ f = f ≫ absoluteFrobenius Y p hY := by
  let hb : (absoluteFrobenius X p hX ≫ f).base = (f ≫ absoluteFrobenius Y p hY).base := by simp
  apply Scheme.Hom.ext hb
  intro U
  cases hb
  ext g
  change (X.presheaf.map _).hom ((absoluteFrobenius X p hX).app _ (f.app U g)) =
    f.app U ((absoluteFrobenius Y p hY).app U g)
  rw [absoluteFrobenius_app_apply, absoluteFrobenius_app_apply]
  change (X.presheaf.map (eqToHom rfl).op) ((f.app U g) ^ p) = f.app U (g ^ p)
  simp

end Stacks.Frobenius

end
