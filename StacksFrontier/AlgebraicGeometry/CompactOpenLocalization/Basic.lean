module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic

/-!
# Localizations of a quasi-compact open of an affine open

Let `A` be an affine open of a scheme `X`, so that `A = Spec B` for `B = Γ(X, A)`, and let
`W ≤ A` be a quasi-compact open.  Write `s : B →+* R` for the restriction map onto
`R = Γ(X, W)`.  For a section `g : B` whose basic open `D(g)` is contained in `W`, the two
localizations `B_g` and `R_{s g}` are the same ring: both are the sections over `D(g)`, the
first because `A` is affine, the second because `W` is quasi-compact and quasi-separated and
`D(s g) = W ⊓ D(g) = D(g)`.  Consequently the canonical map `B_g → R_{s g}` is bijective.

Since the basic opens of `A` form a basis of the opens contained in `A`, the quasi-compact open
`W` is covered by finitely many such `D(g)`, and so comes with a finite family of sections of
`A` whose localizations it computes.

## Main results

* `AlgebraicGeometry.IsAffineOpen.bijective_awayMap_res`: for `g : Γ(X, A)` with
  `X.basicOpen g ≤ W`, the canonical map from `Γ(X, A)_g` to `Γ(X, W)_{g|_W}` is bijective.
* `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_cover_bijective_awayMap`: the finite family
  of sections of `A` whose basic opens cover `W` and each of which has the previous property.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The localizations of an affine open and of a quasi-compact open agree on a basic open
contained in both.**  For an affine open `A` of `X`, a quasi-compact open `W ≤ A` and a section
`g : Γ(X, A)` whose basic open is contained in `W`, the canonical map from `Γ(X, A)_g` to
`Γ(X, W)` localized at the restriction of `g` is bijective. -/
theorem IsAffineOpen.bijective_awayMap_res {A W : X.Opens} (hA : IsAffineOpen A)
    (hW : IsCompact (W : Set X)) (hWA : W ≤ A) {g : Γ(X, A)} (hg : X.basicOpen g ≤ W) :
    Function.Bijective (Localization.awayMap (X.presheaf.map (homOfLE hWA).op).hom g) := by
  have hWqs : IsQuasiSeparated (W : Set X) := hA.isQuasiSeparated.of_subset hWA
  have hlocg := hA.isLocalization_basicOpen g
  set s := (X.presheaf.map (homOfLE hWA).op).hom with hs
  have hbo : X.basicOpen (s g) = X.basicOpen g := by
    rw [hs, Scheme.basicOpen_res, inf_eq_right.mpr hg]
  have hres : ∀ {V : X.Opens} (e : V ≤ W) (c : Γ(X, A)),
      (X.presheaf.map (homOfLE e).op).hom (s c) =
        (X.presheaf.map (homOfLE (e.trans hWA)).op).hom c :=
    fun e c => TopCat.Presheaf.restrict_restrict e hWA c
  constructor
  · rw [Localization.awayMap_injective_iff]
    intro a ha
    refine exists_of_res_zero_of_qcqs hA.isCompact hA.isQuasiSeparated (f := a) (s := g) ?_
    calc a |_ X.basicOpen g = s a |_ X.basicOpen g :=
          (hres hg a).symm
      _ = 0 := by rw [ha]; simp
  · rw [Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨⟨b, gn, n, hn⟩, hb⟩ := IsLocalization.surj (M := Submonoid.powers g)
      (S := Γ(X, X.basicOpen g)) (a |_ X.basicOpen g)
    simp only [← hn, RingHom.algebraMap_toAlgebra] at hb
    have key : ∀ V : X.Opens, V = X.basicOpen g → ∀ e : V ≤ W,
        (X.presheaf.map (homOfLE e).op).hom (s g ^ n * a) =
          (X.presheaf.map (homOfLE e).op).hom (s b) := by
      intro V hV e
      subst hV
      rwa [map_mul, map_pow, hres, hres, ← map_pow, mul_comm]
    obtain ⟨k, hk⟩ := exists_of_res_eq_of_qcqs hW hWqs (s := s g)
      (key (X.basicOpen (s g)) hbo (hbo ▸ hg))
    refine ⟨g ^ k * b, k + n, ?_⟩
    rw [map_mul, map_pow, ← hk]
    ring

/-- **The sections of an affine open whose basic opens cover a quasi-compact open.**  A
quasi-compact open `W` of an affine open `A` is covered by the basic opens of finitely many
sections of `A`, each contained in `W`, and each of them computes the localization of
`Γ(X, W)` at its own restriction. -/
theorem IsAffineOpen.exists_basicOpen_cover_bijective_awayMap {A W : X.Opens}
    (hA : IsAffineOpen A) (hW : IsCompact (W : Set X)) (hWA : W ≤ A) :
    ∃ (n : ℕ) (g : Fin n → Γ(X, A)),
      (∀ l, X.basicOpen (g l) ≤ W) ∧ W = ⨆ l, X.basicOpen (g l) ∧
        ∀ l, Function.Bijective
          (Localization.awayMap (X.presheaf.map (homOfLE hWA).op).hom (g l)) := by
  classical
  obtain ⟨t, ht⟩ :=
    Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact hA hW hWA
  have hmem : ∀ l : Fin t.card, X.basicOpen ((t.equivFin.symm l).1 : Γ(X, A)) ≤ W := by
    intro l
    rw [ht]
    exact le_iSup₂ (f := fun (g : Γ(X, A)) (_ : g ∈ t) => X.basicOpen g) _
      (t.equivFin.symm l).2
  refine ⟨t.card, fun l => (t.equivFin.symm l).1, hmem, ?_,
    fun l => hA.bijective_awayMap_res hW hWA (hmem l)⟩
  refine ht.trans (le_antisymm (iSup₂_le fun x hx => ?_)
    (iSup_le fun l => (hmem l).trans ht.le))
  have hx' : ((t.equivFin.symm (t.equivFin ⟨x, hx⟩)).1 : Γ(X, A)) = x := by simp
  exact hx' ▸ le_iSup (fun l => X.basicOpen ((t.equivFin.symm l).1 : Γ(X, A)))
    (t.equivFin ⟨x, hx⟩)

end AlgebraicGeometry

end
