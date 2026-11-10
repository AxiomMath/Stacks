module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullback

/-!
# Approximate splittings of presentations of an `(A, n, c)`-module

Let `M` be an `(A, n, c)`-module ([Stacks, Tag 0GA6]) and `a ∈ I^c`. By
`IsANCModule.exists_finFree_factorization` ([Stacks, Tag 0GAB]) multiplication by `a` on `M`
factors through a finite free `A/Iⁿ`-module. This file records the two consequences of that
factorization which the proofs of [Stacks, Tags 0GA8 and 0GAB] use, in the form of identities
between module maps, so that any additive `A/Iⁿ`-linear functor carries them along:

* for a surjection `g : L ⟶ M` from a projective module there is `s : M ⟶ L` with
  `s ≫ g = a • 𝟙 M` (`IsANCModule.exists_comp_eq_smul`), an *`a`-section* of `g`;
* for a short exact sequence `0 → K → L → M → 0` with `L` projective there is `r : L ⟶ K` with
  `i ≫ r = a • 𝟙 K` (`IsANCModule.exists_comp_eq_smul_of_exact`), an *`a`-retraction* of `i`.

The second is what makes the kernel of `p^*K → p^*L` annihilated by `a` (Tag 0GA8): applying an
additive linear functor `F` gives `F i ≫ F r = a • 𝟙`, which kills the kernel of `F i`. For the
canonical map of Tag 0GAB the first is applied to the surjection `R^r → M` of a presentation
`R^s → R^r → M → 0`, together with `IsANCModule.exists_comp_eq_smul_sub`, an `a`-section of the
inclusion of the relations.

## Main results

* `Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_comp_eq_smul`
* `Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_comp_eq_smul_of_exact`
* `Stacks.LocalCohomology.UniformityIII.IsANCModule.exists_comp_eq_smul_sub`

## References

* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
* [Stacks Project, Tag 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] {I : Ideal A} {n c : ℕ}

/-- **An `a`-section of a surjection onto an `(A, n, c)`-module.** For `a ∈ I^c` and a surjection
`g : L ⟶ M` from a projective `A/Iⁿ`-module, there is `s : M ⟶ L` with `s ≫ g = a • 𝟙 M`:
multiplication by `a` factors through a finite free module `F` (Tag 0GAB), and the map
`F ⟶ M` lifts through `g` because `F` is free. -/
theorem IsANCModule.exists_comp_eq_smul {M L : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) [Module.Projective (A ⧸ I ^ n) L] (g : L ⟶ M)
    (hg : Function.Surjective g) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    ∃ s : M ⟶ L, s ≫ g = a • 𝟙 M := by
  obtain ⟨r, α, β, hαβ⟩ := hM.exists_finFree_factorization ha
  obtain ⟨β', hβ'⟩ := Module.projective_lifting_property g.hom β.hom hg
  refine ⟨α ≫ ModuleCat.ofHom β', ?_⟩
  rw [Category.assoc, ← hαβ]
  congr 1
  exact ModuleCat.hom_ext hβ'

/-- A map `t` with `t ≫ u = a • 𝟙 L - v ≫ s`, for `s` an `a`-section of `v` and `ker v = im u`. -/
private theorem exists_comp_eq_smul_sub_aux {N L M : ModuleCat.{u} (A ⧸ I ^ n)}
    [Module.Projective (A ⧸ I ^ n) L] (u : N ⟶ L) (v : L ⟶ M)
    (hex : LinearMap.range u.hom = LinearMap.ker v.hom) {a : A ⧸ I ^ n} (s : M ⟶ L)
    (hs : s ≫ v = a • 𝟙 M) :
    ∃ t : L ⟶ N, t ≫ u = a • 𝟙 L - v ≫ s := by
  have hsv : ∀ y : M, v.hom (s.hom y) = a • y := fun y => by
    simpa using congrArg (fun φ : M ⟶ M => φ.hom y) hs
  have hmem : ∀ x : L, (a • x - s.hom (v.hom x)) ∈ LinearMap.range u.hom := by
    intro x
    rw [hex, LinearMap.mem_ker, map_sub, map_smul, hsv, sub_self]
  let w : L →ₗ[A ⧸ I ^ n] LinearMap.range u.hom :=
    { toFun := fun x => ⟨a • x - s.hom (v.hom x), hmem x⟩
      map_add' := fun x y => Subtype.ext (by
        simp only [Submodule.coe_add, map_add, smul_add]
        abel)
      map_smul' := fun b x => Subtype.ext (by
        simp only [map_smul, SetLike.val_smul, smul_sub, RingHom.id_apply]
        rw [smul_comm]) }
  obtain ⟨t, ht⟩ := Module.projective_lifting_property u.hom.rangeRestrict w
    u.hom.surjective_rangeRestrict
  refine ⟨ModuleCat.ofHom t, ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
  change u (t x) = (a • 𝟙 L - v ≫ s).hom x
  rw [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_smul, ModuleCat.hom_id]
  exact congrArg Subtype.val (LinearMap.congr_fun ht x)

/-- **An `a`-retraction of the kernel of a projective presentation.** For a short exact sequence
`0 → K → L → M → 0` of `A/Iⁿ`-modules with `M` an `(A, n, c)`-module and `L` projective, and for
`a ∈ I^c`, there is `r : L ⟶ K` with `i ≫ r = a • 𝟙 K`.

With `s` an `a`-section of `g` (`exists_comp_eq_smul`), `a • 𝟙 L - g ≫ s` is killed by `g`, so it
factors as `r ≫ i`; then `i ≫ r ≫ i = a • i - i ≫ g ≫ s = a • i`, and `i` is injective. -/
theorem IsANCModule.exists_comp_eq_smul_of_exact {K L M : ModuleCat.{u} (A ⧸ I ^ n)}
    (hM : IsANCModule I n c M) [Module.Projective (A ⧸ I ^ n) L] (i : K ⟶ L) (g : L ⟶ M)
    (hi : Function.Injective i) (hg : Function.Surjective g)
    (hex : LinearMap.range i.hom = LinearMap.ker g.hom) {a : A ⧸ I ^ n}
    (ha : a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) :
    ∃ r : L ⟶ K, i ≫ r = a • 𝟙 K := by
  obtain ⟨s, hs⟩ := hM.exists_comp_eq_smul g hg ha
  obtain ⟨t, ht⟩ := exists_comp_eq_smul_sub_aux i g hex s hs
  have : Mono i := (ModuleCat.mono_iff_injective i).2 hi
  have hig : i ≫ g = 0 := ModuleCat.hom_ext (LinearMap.ext fun k => by
    have : i.hom k ∈ LinearMap.ker g.hom := hex ▸ ⟨k, rfl⟩
    exact this)
  refine ⟨t, (cancel_mono i).1 ?_⟩
  rw [Category.assoc, ht, Preadditive.comp_sub, Linear.comp_smul, ← Category.assoc, hig,
    Limits.zero_comp, sub_zero, Category.comp_id, Linear.smul_comp, Category.id_comp]

/-- **An `a`-section of the relations of a projective presentation.** For an exact sequence
`R^s --u--> L --v--> M → 0` of `A/Iⁿ`-modules with `L` projective, `M` an `(A, n, c)`-module,
`a ∈ I^c` and `s` an `a`-section of `v`, there is `t : L ⟶ N` with
`t ≫ u = a • 𝟙 L - v ≫ s`: the right hand side is killed by `v`, so it lands in the image of `u`,
through which it lifts because `L` is projective. -/
theorem IsANCModule.exists_comp_eq_smul_sub {N L M : ModuleCat.{u} (A ⧸ I ^ n)}
    [Module.Projective (A ⧸ I ^ n) L] (u : N ⟶ L) (v : L ⟶ M)
    (hex : LinearMap.range u.hom = LinearMap.ker v.hom) {a : A ⧸ I ^ n} (s : M ⟶ L)
    (hs : s ≫ v = a • 𝟙 M) :
    ∃ t : L ⟶ N, t ≫ u = a • 𝟙 L - v ≫ s :=
  exists_comp_eq_smul_sub_aux u v hex s hs

end Stacks.LocalCohomology.UniformityIII
