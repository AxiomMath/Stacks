module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothAtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace

/-!
# Reduction of smooth base change to the affine line

The second proof of the smooth base change theorem (Stacks, Theorem 0EYU) reduces the theorem to
the projection of the affine line: the question is étale local on `X` and `S` (Stacks 0EZR), a
smooth morphism is locally an étale morphism to an affine space (Stacks, Morphisms, Lemma 054L),
the projection `𝔸^d_S ⟶ S` is a composite of projections of affine lines, and the condition is
stable under composition (Stacks 0EZS). This file carries out that reduction for the condition
`BC(f, n, q)` in every degree, `Stacks.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees`,
for every integer `n` invertible on `S`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.baseChangeAllDegrees_affineSpace` — affine spaces,
  from the affine line.
* `Stacks.EtaleCohomology.SmoothBaseChange.baseChangeAllDegrees_of_smooth` — smooth morphisms,
  from the affine line.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 054L](https://stacks.math.columbia.edu/tag/054L)
* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- An integer invertible on `S` is invertible on every `S`-scheme. -/
theorem isUnit_intCast_of_hom {X S : Scheme.{u}} (φ : X ⟶ S) {n : ℤ}
    (hn : IsUnit (n : Γ(S, ⊤))) : IsUnit (n : Γ(X, ⊤)) := by
  simpa using hn.map φ.appTop.hom

/-- **Affine spaces satisfy `BC(f, n, q)` in every degree once the affine line does.** For every
`r`, the projection `𝔸^r_T ⟶ T` satisfies the condition for every `T` on which `n` is
invertible, provided the projection of the affine line does: `𝔸^0_T ⟶ T` is an isomorphism, and
`𝔸^{r+1}_T ⟶ T` is `𝔸^r` over `𝔸^1_T` followed by `𝔸^1_T ⟶ T`. -/
theorem baseChangeAllDegrees_affineSpace (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) {n : ℤ}
    (hA1 : ∀ T : Scheme.{u}, IsUnit (n : Γ(T, ⊤)) →
      BaseChangeAllDegrees (𝔸(ULift.{u} (Fin 1); T) ↘ T) n) :
    ∀ (r : ℕ) (T : Scheme.{u}), IsUnit (n : Γ(T, ⊤)) →
      BaseChangeAllDegrees (𝔸(ULift.{u} (Fin r); T) ↘ T) n
  | 0, T, _ => baseChangeAllDegrees_of_etale h0EZR _ n
  | r + 1, T, hn => by
    have H := (BaseChangeAllDegrees.comp h0EZS
      (baseChangeAllDegrees_affineSpace h0EZR h0EZS hA1 r (𝔸(ULift.{u} (Fin 1); T))
        (isUnit_intCast_of_hom (𝔸(ULift.{u} (Fin 1); T) ↘ T) hn)) (hA1 T hn)).of_iso
      (Stacks.Chow.affineSpaceSuccIso T r)
    rwa [Stacks.Chow.affineSpaceSuccIso_hom_over] at H

/-- **Smooth morphisms satisfy `BC(f, n, q)` in every degree once the affine line does.** For a
smooth `f : X ⟶ S` and an integer `n` invertible on `S`, every point of `X` has an affine open
neighbourhood `U` mapping into an affine open `V` of `S` such that `U ⟶ V` is an étale morphism
to an affine space over `V` followed by its projection (Stacks 054L). The open immersions cover
`X` and are étale, so Stacks 0EZR reduces the condition for `f` to the one for the morphisms
`U ⟶ V`, which are composites of an étale morphism and the projection of an affine space. -/
theorem baseChangeAllDegrees_of_smooth (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) {n : ℤ}
    (hA1 : ∀ T : Scheme.{u}, IsUnit (n : Γ(T, ⊤)) →
      BaseChangeAllDegrees (𝔸(ULift.{u} (Fin 1); T) ↘ T) n)
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (hn : IsUnit (n : Γ(S, ⊤))) :
    BaseChangeAllDegrees f n := by
  have hloc : ∀ x : X, ∃ (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V),
      x ∈ U ∧ BaseChangeAllDegrees (f.resLE V U hUV) n := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    change S.Opens at V
    obtain ⟨d, U, -, hxU, hUV, π, hπ, hcomp⟩ := exists_affine_open_etale_affineSpace f x V hV hxV
      (InfinitesimalLifting.smoothAt_of_smooth_ι_comp f (U := ⊤) (Set.mem_univ x) inferInstance)
    have : Etale π := hπ
    refine ⟨V, U, hUV, hxU, ?_⟩
    rw [← hcomp]
    exact BaseChangeAllDegrees.comp h0EZS (baseChangeAllDegrees_of_etale h0EZR π n)
      (baseChangeAllDegrees_affineSpace h0EZR h0EZS hA1 d V
        (isUnit_intCast_of_hom (Scheme.Opens.ι V) hn))
  choose V U hUV hxU H using hloc
  exact BaseChangeAllDegrees.of_etaleCover h0EZR f n (fun x => (U x).toScheme)
    (fun x => (V x).toScheme) (fun x => (U x).ι) (fun x => (V x).ι)
    (fun x => f.resLE (V x) (U x) (hUV x))
    (fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩) (fun x => Scheme.Hom.resLE_comp_ι _ _) H

end Stacks.EtaleCohomology.SmoothBaseChange

end
