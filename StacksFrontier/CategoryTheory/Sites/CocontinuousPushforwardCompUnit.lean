module

public import StacksFrontier.CategoryTheory.Sites.CocontinuousPushforwardCounits

/-!
# The comparison of a composite direct image, read against a chain of counits

A direct image along a composite `X₂ ⟶ X₁ ⟶ X₀` of morphisms of sites, written as the composite of
the two stages, acquires one extra occurrence of "push to the big site, restrict to the small one"
in the middle; the canonical comparison between the two readings is therefore built from two
pieces, the comparison of the two cocontinuous pushforwards attached to a factorization
`L₁ ⋙ L₂ ≅ L` and the unit of the adjunction that inserts the middle restriction.

This file carries out, once and in the generality of right Kan extensions alone, the computation
that reads such a comparison against the counits: following it with the chain of counits of the
finer decomposition recovers the chain of counits of the coarser one, at the morphism of the
coarse index obtained by composing the two fine ones across the factorization.

## Main results

* `CategoryTheory.Functor.ran_comp_unit_ranCounit_chain` — **the computation.**  Both of its
  hypotheses are statements about counits alone: `hkap` says of the comparison
  `Ran_L P ⟶ Ran_{L₂}(Ran_{L₁} P)` exactly what
  `CategoryTheory.Functor`
  `.rightAdjointUniq_sheafAdjunctionCocontinuous_inv_app_hom_app_comp_ranCounit`
  proves of the comparison of the two cocontinuous pushforwards, and `heta` says of the unit
  `Ran_{L₁}P ⟶ Ran_T(T ⋙ Ran_{L₁}P)` exactly what
  `CategoryTheory.Functor.sheafAdjunctionCocontinuous_unit_app_hom_app_comp_ranCounit` proves of
  the unit of the adjunction along `T`.  The proof is naturality of the three counits and of the
  comparison, with the triangle identity of the unit collapsing the middle of the chain.

## References

* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe w w' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  {H : Type w} [Category.{w'} H]
  (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (L : C₁ ⥤ C₃) (ε : L₁ ⋙ L₂ ≅ L) (T : C₄ ⥤ C₂) (P : C₁ ⥤ H)
  [∀ Q : C₁ ⥤ H, L₁.HasRightKanExtension Q] [∀ Q : C₂ ⥤ H, L₂.HasRightKanExtension Q]
  [∀ Q : C₁ ⥤ H, L.HasRightKanExtension Q] [∀ Q : C₄ ⥤ H, T.HasRightKanExtension Q]

/-- **The comparison of a composite right Kan extension with its two-stage reading, read against
the chain of counits of the finer decomposition.**

The comparison is made of two pieces: a map `kap : Ran_L P ⟶ Ran_{L₂}(Ran_{L₁}P)` compatible with
the counits across the factorization `ε : L₁ ⋙ L₂ ≅ L` (`hkap`), and a unit
`eta : Ran_{L₁}P ⟶ Ran_T(T ⋙ Ran_{L₁}P)` split by the counit of `Ran_T` (`heta`), pushed forward
along `Ran_{L₂}`.

Composing it with the four-step chain of counits attached to a pair of morphisms
`k₂ : Z ⟶ L₂(T b)` and `k₁ : T b ⟶ L₁ c` gives the two-step chain of counits of `Ran_L P` at any
morphism `k : Z ⟶ L c` which, read across `ε`, is their composite. -/
theorem ran_comp_unit_ranCounit_chain
    {kap : L.ran.obj P ⟶ L₂.ran.obj (L₁.ran.obj P)}
    (hkap : ∀ c : C₁, kap.app (L.obj c) ≫
        (L₂.ran.obj (L₁.ran.obj P)).map (ε.inv.app c) ≫
          (L₂.ranCounit.app (L₁.ran.obj P)).app (L₁.obj c) ≫ (L₁.ranCounit.app P).app c =
      (L.ranCounit.app P).app c)
    {eta : L₁.ran.obj P ⟶ T.ran.obj (T ⋙ L₁.ran.obj P)}
    (heta : ∀ b : C₄, eta.app (T.obj b) ≫
        (T.ranCounit.app (T ⋙ L₁.ran.obj P)).app b = 𝟙 ((L₁.ran.obj P).obj (T.obj b)))
    (Z : C₃) (b : C₄) (c : C₁) (k₂ : Z ⟶ L₂.obj (T.obj b)) (k₁ : T.obj b ⟶ L₁.obj c)
    (k : Z ⟶ L.obj c) (hk : k ≫ ε.inv.app c = k₂ ≫ L₂.map k₁) :
    kap.app Z ≫ (L₂.ran.map eta).app Z ≫
        (L₂.ran.obj (T.ran.obj (T ⋙ L₁.ran.obj P))).map k₂ ≫
          (L₂.ranCounit.app (T.ran.obj (T ⋙ L₁.ran.obj P))).app (T.obj b) ≫
            (T.ranCounit.app (T ⋙ L₁.ran.obj P)).app b ≫
              (L₁.ran.obj P).map k₁ ≫ (L₁.ranCounit.app P).app c =
      (L.ran.obj P).map k ≫ (L.ranCounit.app P).app c := by
  have h3 : (L₂.ran.map eta).app (L₂.obj (T.obj b)) ≫
        (L₂.ranCounit.app (T.ran.obj (T ⋙ L₁.ran.obj P))).app (T.obj b) =
      (L₂.ranCounit.app (L₁.ran.obj P)).app (T.obj b) ≫ eta.app (T.obj b) :=
    NatTrans.congr_app (L₂.ranCounit.naturality eta) (T.obj b)
  have h5 : (L₂.ranCounit.app (L₁.ran.obj P)).app (T.obj b) ≫ (L₁.ran.obj P).map k₁ =
      (L₂.ran.obj (L₁.ran.obj P)).map (L₂.map k₁) ≫
        (L₂.ranCounit.app (L₁.ran.obj P)).app (L₁.obj c) :=
    ((L₂.ranCounit.app (L₁.ran.obj P)).naturality k₁).symm
  rw [← hkap c]
  slice_rhs 1 2 => rw [kap.naturality]
  slice_rhs 2 3 => rw [← Functor.map_comp, hk]
  slice_lhs 2 3 => rw [← (L₂.ran.map eta).naturality k₂]
  slice_lhs 3 4 => rw [h3]
  slice_lhs 4 6 => rw [reassoc_of% (heta b)]
  slice_lhs 3 4 => rw [h5]
  slice_lhs 2 3 => rw [← Functor.map_comp]

end Functor

end CategoryTheory

end
