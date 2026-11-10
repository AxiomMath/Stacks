module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Direct images over an open the morphism misses

Let `f : X ⟶ Y` be a morphism of schemes and `V` an open of `Y` disjoint from the set-theoretic
image of `f`. Then `f ⁻¹ V` is empty, so the direct image `f_* M` of an `𝒪_X`-module has only
the zero section over `V`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.preimage_eq_bot_of_disjoint_range`: the preimage of such an open
  is the empty open.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_pushforward_sections_of_disjoint_range`: the
  direct image has a single section over such an open.
* `AlgebraicGeometry.Scheme.Modules.pushforward_app_eq_zero_of_disjoint_range`: every morphism
  into the direct image vanishes on sections over such an open.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- The preimage of an open disjoint from the set-theoretic image of a morphism of schemes is
the empty open. -/
public theorem Scheme.Hom.preimage_eq_bot_of_disjoint_range (f : X ⟶ Y) (V : Y.Opens)
    (hV : (V : Set Y) ∩ Set.range f.base = ∅) : f ⁻¹ᵁ V = ⊥ := by
  ext x
  exact ⟨fun hx => False.elim (hV.subset ⟨hx, x, rfl⟩), fun hx => hx.elim⟩

/-- Over an open of the target disjoint from the set-theoretic image of `f`, the direct image of
an `𝒪_X`-module has a single section: its sections there are those over the empty open, where
the ring of functions is the zero ring. -/
public theorem Scheme.Modules.subsingleton_pushforward_sections_of_disjoint_range (f : X ⟶ Y)
    (M : X.Modules) (V : Y.Opens) (hV : (V : Set Y) ∩ Set.range f.base = ∅) :
    Subsingleton Γ((Scheme.Modules.pushforward f).obj M, V) := by
  change Subsingleton Γ(M, f ⁻¹ᵁ V)
  rw [Scheme.Hom.preimage_eq_bot_of_disjoint_range f V hV]
  exact Module.subsingleton Γ(X, ⊥) _

/-- A morphism of `𝒪_Y`-modules into a direct image along `f` kills every section over an open
disjoint from the set-theoretic image of `f`. -/
public theorem Scheme.Modules.pushforward_app_eq_zero_of_disjoint_range (f : X ⟶ Y)
    {M : X.Modules} {N : Y.Modules} (φ : N ⟶ (Scheme.Modules.pushforward f).obj M)
    (V : Y.Opens) (hV : (V : Set Y) ∩ Set.range f.base = ∅) (a : Γ(N, V)) : φ.app V a = 0 :=
  @Subsingleton.elim _
    (Scheme.Modules.subsingleton_pushforward_sections_of_disjoint_range f M V hV) _ _

end AlgebraicGeometry

end
