module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Sheaf subfunctors are determined by their preimages along a locally surjective morphism

Let `J` be a Grothendieck topology on `C`, `F` a presheaf of sets and `c : W ⟶ F` a locally
surjective morphism of presheaves. A subfunctor `Z₁ ⊆ F` whose preimage under `c` lies in that of
`Z₂` lies in the sheafification of `Z₂`: every section of `Z₁` lifts locally through `c`, and the
lifts land in `Z₂`. So two subfunctors which are sheaves, of a sheaf `F`, are equal as soon as
their preimages under `c` are.

This is the form in which closed subspaces of an algebraic space are compared on a surjective
étale chart.

## Main results

* `CategoryTheory.Subfunctor.le_sheafify_of_preimage_le`.
* `CategoryTheory.Subfunctor.eq_of_preimage_eq_of_isLocallySurjective`.
* `CategoryTheory.Subfunctor.isSheaf_range_of_mono`: the range of a monomorphism out of a sheaf is
  a sheaf.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {F W : Cᵒᵖ ⥤ Type w}

/-- **A subfunctor whose preimage under a locally surjective morphism lies in that of another
lies in the sheafification of the other.** -/
theorem le_sheafify_of_preimage_le {Z₁ Z₂ : Subfunctor F} (c : W ⟶ F)
    (hc : Presheaf.IsLocallySurjective J c) (h : Z₁.preimage c ≤ Z₂.preimage c) :
    Z₁ ≤ Z₂.sheafify J := by
  intro U x hx
  refine J.superset_covering ?_ (hc.imageSieve_mem x)
  rintro V f ⟨y, hy⟩
  show F.map f.op x ∈ Z₂.obj (Opposite.op V)
  have hy' : c.app (Opposite.op V) y = F.map f.op x := hy
  rw [← hy']
  exact h _ (show c.app _ y ∈ Z₁.obj _ from hy' ▸ Z₁.map f.op hx)

/-- **Two sheaf subfunctors of a sheaf with the same preimage under a locally surjective morphism
are equal.** -/
theorem eq_of_preimage_eq_of_isLocallySurjective (hF : Presieve.IsSheaf J F)
    {Z₁ Z₂ : Subfunctor F} (h₁ : Presieve.IsSheaf J Z₁.toFunctor)
    (h₂ : Presieve.IsSheaf J Z₂.toFunctor) (c : W ⟶ F) (hc : Presheaf.IsLocallySurjective J c)
    (h : Z₁.preimage c = Z₂.preimage c) : Z₁ = Z₂ := by
  refine le_antisymm ?_ ?_
  · rw [Z₂.eq_sheafify hF h₂]
    exact le_sheafify_of_preimage_le J c hc h.le
  · rw [Z₁.eq_sheafify hF h₁]
    exact le_sheafify_of_preimage_le J c hc h.ge

variable {J}

/-- The comparison of a monomorphism with its range is an isomorphism. -/
theorem isIso_toRange_of_mono (p : W ⟶ F) [Mono p] : IsIso (toRange p) := by
  have : ∀ U, IsIso ((toRange p).app U) := fun U => by
    rw [isIso_iff_bijective]
    refine ⟨fun a b hab => ?_, fun ⟨x, ⟨a, ha⟩⟩ => ⟨a, Subtype.ext ha⟩⟩
    have hinj := (NatTrans.mono_iff_mono_app p).1 inferInstance U
    rw [mono_iff_injective] at hinj
    exact hinj (congrArg Subtype.val hab)
  exact NatIso.isIso_of_isIso_app _

/-- **The range of a monomorphism out of a sheaf is a sheaf.** -/
theorem isSheaf_range_of_mono (p : W ⟶ F) [Mono p] (hW : Presieve.IsSheaf J W) :
    Presieve.IsSheaf J (range p).toFunctor :=
  have := isIso_toRange_of_mono p
  Presieve.isSheaf_iso J (asIso (toRange p)) hW

end CategoryTheory.Subfunctor
