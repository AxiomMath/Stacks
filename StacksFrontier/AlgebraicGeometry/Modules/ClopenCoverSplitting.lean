module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands

/-!
# Morphisms of modules split along a clopen decomposition

A clopen subset `U` of a scheme `X` splits `X` into the two disjoint opens `U` and `Uᶜ`. This
file records that two-member covering and the fact that a morphism of sheaves of modules on `X`
is *freely and uniquely* determined by a pair of morphisms over those two pieces: free because
the covering has no overlaps, so there is no compatibility condition to satisfy, and unique
because a morphism is determined by its restrictions to any covering.

## Main definitions

* `AlgebraicGeometry.clopenPart`: the two opens `U` and `Uᶜ` of the decomposition, indexed by
  `Bool`.
* `AlgebraicGeometry.clopenCover`: the two-member open covering of `X` by them.

## Main results

* `AlgebraicGeometry.noOverlap_clopenCover`: the covering has no overlaps — only a scheme with no
  points maps compatibly into both pieces, since its points would lie in `U ∩ Uᶜ = ∅`.
* `AlgebraicGeometry.exists_hom_of_clopenHoms`: **an arbitrary pair of morphisms over the two
  pieces comes from a morphism on `X`**, with no compatibility condition.
* `AlgebraicGeometry.injective_map_clopenCover`: and the morphism on `X` is determined by that
  pair.

## Implementation notes

Both results are `AlgebraicGeometry.exists_hom_of_disjointCoverHoms` and
`AlgebraicGeometry.injective_map_openCover`, whose hypothesis is exactly
`AlgebraicGeometry.NoOverlap`; neither carries a quasi-coherence hypothesis, so the splitting here
applies to arbitrary sheaves of modules.

Indexing the two pieces by `Bool` through a single function `clopenPart` keeps the two members of
the covering uniform in the index, so the covering is an ordinary `Scheme.Cover.mkOfCovers` and
its member maps are all of the form `(clopenPart U hU b).ι`; a `Sum`- or `if`-shaped definition
would make the member *type* depend on the index and force a transport at every use.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The two opens of a clopen decomposition of `X`**, indexed by `Bool`: `U` itself at `true`
and its complement at `false`, which is open because `U` is closed. -/
def clopenPart (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) : Bool → X.Opens
  | true => U
  | false => ⟨(U : Set X)ᶜ, hU⟩

/-- The member of `clopenPart U hU` at `true` is `U`. -/
@[simp] theorem clopenPart_true (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) :
    clopenPart U hU true = U := rfl

/-- The member of `clopenPart U hU` at `false` is the complement of `U`. -/
@[simp] theorem clopenPart_false (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) :
    (clopenPart U hU false : Set X) = (U : Set X)ᶜ := rfl

/-- **The two-member open covering of `X` by a clopen `U` and its complement.** -/
def clopenCover (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) : Scheme.OpenCover.{0} X :=
  Scheme.Cover.mkOfCovers Bool (fun b => (clopenPart U hU b).toScheme)
    (fun b => (clopenPart U hU b).ι) fun x => by
      by_cases hx : x ∈ U
      · exact ⟨true, ⟨x, hx⟩, rfl⟩
      · exact ⟨false, ⟨x, hx⟩, rfl⟩

/-- A point of a member of the clopen covering lies in that member. -/
theorem clopenCover_f_mem (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) (b : Bool)
    (y : (clopenCover U hU).X b) :
    (clopenCover U hU).f b y ∈ (clopenPart U hU b : Set X) := by
  show (clopenPart U hU b).ι y ∈ (clopenPart U hU b : Set X)
  rw [← Scheme.Opens.range_ι]
  exact ⟨y, rfl⟩

/-- **The clopen covering has no overlaps**: a scheme mapping compatibly into two distinct members
has no points. -/
theorem noOverlap_clopenCover (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) :
    NoOverlap (clopenCover U hU) := by
  intro k l hkl V a b hab
  refine ⟨fun v => ?_⟩
  have h0 : (clopenCover U hU).f k (a v) = (clopenCover U hU).f l (b v) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
  have hk := clopenCover_f_mem U hU k (a v)
  have hl := clopenCover_f_mem U hU l (b v)
  rw [h0] at hk
  revert hk hl
  match k, l with
  | true, true => exact absurd rfl hkl
  | false, false => exact absurd rfl hkl
  | true, false => exact fun h1 h2 => h2 h1
  | false, true => exact fun h1 h2 => h1 h2

/-- **An arbitrary pair of morphisms of modules over a clopen piece and its complement comes
from a morphism on the whole scheme**, with no compatibility condition on the pair. This is
`AlgebraicGeometry.exists_hom_of_disjointCoverHoms` for `AlgebraicGeometry.clopenCover`. -/
theorem exists_hom_of_clopenHoms (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ)) (A B : X.Modules)
    (φ : ∀ b, (Scheme.Modules.pullback (clopenPart U hU b).ι).obj A ⟶
      (Scheme.Modules.pullback (clopenPart U hU b).ι).obj B) :
    ∃ ψ : A ⟶ B, ∀ b, (Scheme.Modules.pullback (clopenPart U hU b).ι).map ψ = φ b :=
  exists_hom_of_disjointCoverHoms (clopenCover U hU) (noOverlap_clopenCover U hU) A B φ

/-- **A morphism of modules is determined by its restrictions to a clopen piece and its
complement.** This is `AlgebraicGeometry.injective_map_openCover` for
`AlgebraicGeometry.clopenCover`. -/
theorem injective_map_clopenCover (U : X.Opens) (hU : IsOpen ((U : Set X)ᶜ))
    (A B : X.Modules) :
    Function.Injective (fun (ψ : A ⟶ B) b =>
      (Scheme.Modules.pullback (clopenPart U hU b).ι).map ψ) :=
  injective_map_openCover (clopenCover U hU) A B

end AlgebraicGeometry

end
