module

public import StacksFrontier.RingTheory.AugmentationIdealPowTorVanishing
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# [Stacks, Tag 08RE] with the **first** variable resolved

Let `T = MvPolynomial σ B`, let `g : σ → B` and let `K` be the augmentation ideal of `T` at `g`.
[Stacks, Tag 08RE], `MvPolynomial.tor_map_augmentationIdeal_pow_eq_zero_of_lt`, says that for a
`T`-module `M` killed by `K` the inclusion `K ^ m ⊆ K ^ n` induces the zero map on
`Tor_i^T(M, -)` in every degree, for `n < m`.  It is stated for `CategoryTheory.Tor`, which
derives the **second** variable — so it is computed from a resolution of the ideal.

The consumer is the second claim in the proof of [Stacks, Tag 08RF]: there the local complexes
are `W_m = Q_• ⊗_T K ^ m` for a fixed projective resolution `Q_•` of `M`, which resolve the
**first** variable, so their homology is `CategoryTheory.Tor'`.  This file restates the vanishing
there.

The bridge is the balancing of `Tor` ([Stacks, Tag 00M1], `Tor_iso_Tor'`): it is an isomorphism
of bifunctors, so its naturality in the second variable carries the vanishing of a map from one
side to the other.  Nothing else is needed, and the statement is not weakened — the hypotheses
and the degree range are those of [Stacks, Tag 08RE].

## Main results

* `StacksDraft.AugmentationTor.tor'_map_eq_zero_of_tor_map_eq_zero`: a morphism inducing the zero
  map on `Tor_i(M, -)` induces the zero map on `Tor'_i(M, -)`.
* `MvPolynomial.tor'_map_augmentationIdeal_pow_succ_eq_zero` and
  `MvPolynomial.tor'_map_augmentationIdeal_pow_eq_zero_of_lt`: [Stacks, Tag 08RE] and its
  `k`-fold form, with the first variable resolved.

## References

* [Stacks Project, Tag 08RE](https://stacks.math.columbia.edu/tag/08RE)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace StacksDraft.AugmentationTor

/-- A morphism that is zero transfers across a commuting square whose sides `α`, `β` are
isomorphisms. -/
private theorem eq_zero_of_comp_eq_comp_of_isIso {C : Type*} [Category C] [Preadditive C]
    {A B A' B' : C} {u : A ⟶ B} {v : A' ⟶ B'} (α : A ≅ A') (β : B ≅ B')
    (hnat : u ≫ β.hom = α.hom ≫ v) (hu : u = 0) : v = 0 := by
  rw [hu, zero_comp] at hnat
  exact zero_of_epi_comp _ hnat.symm

/-- **Vanishing on `Tor` transfers to `Tor'`.** If a morphism `f` induces the zero map on
`Tor_i^R(M, -)`, computed by resolving the second variable, then it induces the zero map on
`Tor'_i^R(M, -)`, computed by resolving the first.

The balancing `Tor_iso_Tor'` of [Stacks, Tag 00M1] is an isomorphism of bifunctors; its
component at `M` is an isomorphism of functors of the second variable, whose naturality square
at `f` identifies the two maps up to isomorphisms. -/
theorem tor'_map_eq_zero_of_tor_map_eq_zero {R : Type w} [CommRing R] (i : ℕ)
    (M : ModuleCat.{w} R) {N N' : ModuleCat.{w} R} (f : N ⟶ N')
    (h : ((Tor (ModuleCat.{w} R) i).obj M).map f = 0) :
    ((Tor' (ModuleCat.{w} R) i).obj M).map f = 0 := by
  exact eq_zero_of_comp_eq_comp_of_isIso (((Tor_iso_Tor' R i).app M).app N)
    (((Tor_iso_Tor' R i).app M).app N') (((Tor_iso_Tor' R i).app M).hom.naturality f) h

/-- **`Tor'` is symmetric**, as an isomorphism of bifunctors `Tor'_i(Y, X) ≅ Tor'_i(X, Y)`.

Both the balancing `Tor_iso_Tor'` of [Stacks, Tag 00M1] and the braiding comparison
`torFlip_iso_Tor'` of [Stacks, Tag 00M3] are isomorphisms of bifunctors, so flipping the first
and composing with the second exchanges the two variables of `Tor'`. -/
def tor'FlipIso (R : Type w) [CommRing R] (i : ℕ) :
    (Tor' (ModuleCat.{w} R) i).flip ≅ Tor' (ModuleCat.{w} R) i :=
  ((flipFunctor _ _ _).mapIso (Tor_iso_Tor' R i)).symm ≪≫ torFlip_iso_Tor' R i

/-- **Vanishing in the second variable of `Tor'` transfers to the first.** If a morphism `f`
induces the zero map on `Tor'_i^R(M, -)` — the variable which is *not* resolved — then it induces
the zero map on `Tor'_i^R(-, M)`, the variable which *is*.

The two are exchanged by `StacksDraft.AugmentationTor.tor'FlipIso`, whose naturality square at
`f`, read at `M`, identifies them up to isomorphisms.

This is the step that turns the local claim of [Stacks, Tag 08RF] — whose complexes
`Q_• ⊗ Kᵐ` resolve the *fixed* module `M` and are functorial in the ideal — into the form a
projective resolution *of the ideal* computes, which is what the derived tensor product with a
new coefficient ring produces. -/
theorem tor'_map_app_eq_zero_of_obj_map_eq_zero {R : Type w} [CommRing R] (i : ℕ)
    (M : ModuleCat.{w} R) {N N' : ModuleCat.{w} R} (f : N ⟶ N')
    (h : ((Tor' (ModuleCat.{w} R) i).obj M).map f = 0) :
    ((Tor' (ModuleCat.{w} R) i).map f).app M = 0 := by
  have hnat := NatTrans.congr_app ((tor'FlipIso R i).hom.naturality f) M
  simp only [NatTrans.comp_app] at hnat
  exact eq_zero_of_comp_eq_comp_of_isIso (((tor'FlipIso R i).app N).app M)
    (((tor'FlipIso R i).app N').app M) hnat h

end StacksDraft.AugmentationTor

namespace MvPolynomial

/-- **[Stacks, Tag 08RE] with the first variable resolved.** Let `T = MvPolynomial σ B`, let
`g : σ → B` and let `K` be the augmentation ideal of `T` at `g`.  For any `T`-module on which `K`
acts as zero the inclusion `K ^ (n + 1) ⊆ K ^ n` induces the zero map on `Tor'_i^T` in every
degree.

This is `MvPolynomial.tor_map_augmentationIdeal_pow_succ_eq_zero` read through the balancing
`StacksDraft.AugmentationTor.tor'_map_eq_zero_of_tor_map_eq_zero`. -/
theorem tor'_map_augmentationIdeal_pow_succ_eq_zero
    (B : Type u) [CommRing B] (σ : Type v) (g : σ → B) (i n : ℕ)
    (M : ModuleCat.{max u v} (MvPolynomial σ B))
    (hM : ∀ r ∈ RingHom.ker (eval₂Hom (RingHom.id B) g), ∀ m : M, r • m = 0) :
    ((Tor' (ModuleCat.{max u v} (MvPolynomial σ B)) i).obj M).map
      (ModuleCat.ofHom (Submodule.inclusion
        (Ideal.pow_le_pow_right (Nat.le_succ n) :
          RingHom.ker (eval₂Hom (RingHom.id B) g) ^ (n + 1) ≤
            RingHom.ker (eval₂Hom (RingHom.id B) g) ^ n))) = 0 :=
  StacksDraft.AugmentationTor.tor'_map_eq_zero_of_tor_map_eq_zero i M _
    (tor_map_augmentationIdeal_pow_succ_eq_zero B σ g i n M hM)

/-- **The `k`-fold form of [Stacks, Tag 08RE] with the first variable resolved.** With `K` the
augmentation ideal of `MvPolynomial σ B` at `g`, the inclusion `K ^ m ⊆ K ^ n` induces the zero
map on `Tor'_i^T` in every degree whenever `n < m`, for any module on which `K` acts as zero.

This is the form in which the second claim in the proof of [Stacks, Tag 08RF] feeds
[Stacks, Tag 08Q2]: the local complexes `W_m = Q_• ⊗_T K ^ m` resolve the first variable, and
`H^{-j}` of the transition map `W_m ⟶ W_n` is this one — zero in **every** degree `j`, not only
for `j` below a bound, which is why `k` single steps suffice in [Stacks, Tag 08Q2]. -/
theorem tor'_map_augmentationIdeal_pow_eq_zero_of_lt
    (B : Type u) [CommRing B] (σ : Type v) (g : σ → B) (i n m : ℕ) (hnm : n < m)
    (M : ModuleCat.{max u v} (MvPolynomial σ B))
    (hM : ∀ r ∈ RingHom.ker (eval₂Hom (RingHom.id B) g), ∀ x : M, r • x = 0) :
    ((Tor' (ModuleCat.{max u v} (MvPolynomial σ B)) i).obj M).map
      (ModuleCat.ofHom (Submodule.inclusion
        (Ideal.pow_le_pow_right hnm.le :
          RingHom.ker (eval₂Hom (RingHom.id B) g) ^ m ≤
            RingHom.ker (eval₂Hom (RingHom.id B) g) ^ n))) = 0 :=
  StacksDraft.AugmentationTor.tor'_map_eq_zero_of_tor_map_eq_zero i M _
    (tor_map_augmentationIdeal_pow_eq_zero_of_lt B σ g i n m hnm M hM)

end MvPolynomial

end
