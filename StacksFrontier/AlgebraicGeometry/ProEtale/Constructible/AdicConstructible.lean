module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LisseStratification
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.OpenImmersion

/-!
# Adic constructibility from a lisse stratification

Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. If a sheaf of
`Λ`-modules on `X_proét` restricts to a lisse constructible `Λ`-sheaf on each stratum of a finite
partition of `X` into locally closed subschemes, then it is adic constructible: every affine open
`U` is partitioned by the connected components of the strata met with `U`, which are open in the
strata, and on each of them the sheaf is lisse, hence adic lisse by Stacks 09BW. This is the
argument of Stacks 09BX from Stacks 09BU.

## Main results

* `AlgebraicGeometry.ProEtale.IsAdicLisse.of_iso`: adic lisseness is invariant under isomorphism.
* `AlgebraicGeometry.ProEtale.isAdicConstructibleModuleSheaf_of_isLisse_stratification`: a sheaf
  which is lisse on the strata of a partition of a Noetherian scheme is adic constructible.
* `AlgebraicGeometry.ProEtale.isAdicConstructibleModuleSheaf_of_isConstructibleAdicModuleSheaf`:
  Stacks 09BX, a constructible `Λ`-sheaf on a Noetherian scheme is adic constructible.

## References

* [Stacks Project, Tag 09BX](https://stacks.math.columbia.edu/tag/09BX)
* [Stacks Project, Tag 04MF](https://stacks.math.columbia.edu/tag/04MF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] hasWeakSheafify_proEt_moduleCat hasWeakSheafify_proEt_over_moduleCat

variable {Λ : Type v} [CommRing Λ] {I : Ideal Λ}

/-- Adic lisseness is invariant under isomorphism. -/
theorem IsAdicLisse.of_iso {X : Scheme.{u}}
    {F F' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)} (e : F ≅ F')
    (hF : IsAdicLisse X Λ I F) : IsAdicLisse X Λ I F' := by
  obtain ⟨M, hMc, hMf, h⟩ := hF
  refine ⟨M, hMc, hMf, fun U => ?_⟩
  obtain ⟨K, V, f, hf, hV⟩ := h U
  exact ⟨K, V, f, hf, fun k => (hV k).map fun c =>
    ((Scheme.ProEt.topology X).overPullback _ (V k)).mapIso e.symm ≪≫ c⟩

/-- **A sheaf which is lisse on the strata of a partition of a Noetherian scheme is adic
constructible.** Given an affine open `U`, the strata of the partition met with `U` are refined
by their connected components, which are open subschemes of the strata; the sheaf restricts to a
lisse constructible `Λ`-sheaf on each of them, which is adic lisse because it is connected
(Stacks 09BW). -/
theorem isAdicConstructibleModuleSheaf_of_isLisse_stratification [IsNoetherianRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (s : Scheme.ConstructibleStratification X ⊤)
    (hs : ∀ i, IsLisseAdicModuleSheaf.{w} (s.piece i) Λ I
      ((proetaleModuleInverseImage.{u, v, w} (s.inclusion i) Λ).obj F)) :
    IsAdicConstructibleModuleSheaf.{w} X Λ I F := by
  intro U
  obtain ⟨t, ht, hfac⟩ := (s.restrict U.1).exists_connectedSpace_refines
  refine ⟨t, fun j => ?_⟩
  obtain ⟨i, q, hq, hqi⟩ := hfac j
  have : IsOpenImmersion q := hq
  let r : (s.restrict U.1).piece i ⟶ s.piece i := ((s.inclusion i) ⁻¹ᵁ U.1).ι
  have hr : (s.restrict U.1).inclusion i = r ≫ s.inclusion i := rfl
  have : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion ((s.inclusion i) ⁻¹ᵁ U.1).ι)
  have hcomp : (q ≫ r) ≫ s.inclusion i = t.inclusion j := by
    rw [Category.assoc, ← hr, hqi]
  have : ConnectedSpace (t.piece j) := ht j
  have h := isAdicLisse_of_isLisseAdicModuleSheaf
    (((hs i).proetaleModuleInverseImage (q ≫ r)).of_iso
      ((proetaleModuleInverseImageCompIso.{u, v, w} Λ (q ≫ r) (s.inclusion i)).app F))
  rwa [hcomp] at h

/-- **Stacks 09BX.** Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal.
A constructible `Λ`-sheaf on the small pro-étale site of `X` is adic constructible: it is lisse on
the strata of a finite partition of `X` (Stacks 09BU). -/
@[stacks 09BX]
theorem isAdicConstructibleModuleSheaf_of_isConstructibleAdicModuleSheaf [IsNoetherianRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)}
    (hF : IsConstructibleAdicModuleSheaf.{w} X Λ I F) :
    IsAdicConstructibleModuleSheaf.{w} X Λ I F :=
  let ⟨s, hs⟩ := exists_isLisseAdicModuleSheaf_stratification I hF
  isAdicConstructibleModuleSheaf_of_isLisse_stratification s hs

end AlgebraicGeometry.ProEtale

end
