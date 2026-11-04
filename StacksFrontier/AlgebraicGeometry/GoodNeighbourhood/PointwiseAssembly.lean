module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodSections
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.ClosedFibreSpreading
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.NormalProjectiveCompactification
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.PreimageDimension

/-!
# Elementary fibration neighbourhoods from good sections

The pointwise form of Artin's good neighbourhoods (SGA 4, Exposé XI, Proposition 3.3),
`Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood`, is reduced here to two
statements about a normal projective compactification `X̄` of an affine neighbourhood of the
point:

* `AlgebraicGeometry.GoodNeighbourhood.ExistsGoodSections`: there are sections `v₁, …, v_{d-1}`,
  `w₀` of an invertible module on `X̄` that are good through the point (the Bertini input);
* `AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections`: good sections through a point
  of the smooth open `W ⊆ X̄` give an elementary fibration on an open neighbourhood of the point
  inside `W` (the incidence family `V(vⱼ - tⱼ w₀) ⊆ X̄ × 𝔸^{d-1}` and its spreading out from the
  fibre through the point).

The reduction itself: take an affine open `W₀ ∋ x` of `X`, normal because smooth over a field,
compactify it to a normal integral projective `X̄`
(`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_isNormal`), apply the two
statements to the image `W` of `W₀` and the image of `x`, which is a closed point of `X̄`, and
transport the resulting open of `W` back to `X` through `W₀ ≅ W`.

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.exists_elementaryFibrationNeighbourhood_of_goodSections`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **Elementary fibrations from good sections** (SGA 4, Exposé XI, Proposition 3.3, the
construction). For every integral projective `X̄` over `k`, every open `W ⊆ X̄` smooth of relative
dimension `d ≥ 1` over `k`, every closed point `x ∈ W` and every family of good sections through
`x` (`AlgebraicGeometry.GoodNeighbourhood.GoodSections`), some open `U ⊆ W` containing `x` is an
elementary fibration over an irreducible affine scheme smooth of relative dimension `d - 1` over
`k`, compatibly with the structure morphisms. -/
def IncidenceFromGoodSections (k : Type u) [Field k] : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (d : ℕ), IsProjectiveMorphism p → IsIntegral X →
    ∀ W : X.Opens, SmoothOfRelativeDimension d (W.ι ≫ p) → 1 ≤ d →
    ∀ x ∈ W, IsClosed ({x} : Set X) →
    ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
      (v : Fin (d - 1) → Γ(L, ⊤)) (w₀ : Γ(L, ⊤)), GoodSections k p d L W x v w₀ →
    ∃ (U : X.Opens) (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S),
      U ≤ W ∧ x ∈ U ∧ IsElementaryFibration f ∧ SmoothOfRelativeDimension (d - 1) q ∧
        IsAffine S ∧ IrreducibleSpace S ∧ f ≫ q = U.ι ≫ p

/-- **Elementary fibration neighbourhoods from good sections and the incidence construction.**
If good sections exist (`AlgebraicGeometry.GoodNeighbourhood.ExistsGoodSections`) and give
elementary fibrations (`AlgebraicGeometry.GoodNeighbourhood.IncidenceFromGoodSections`), then
every closed point `x` of a smooth irreducible scheme `X` of relative dimension `d ≥ 1` over `k`
has an open neighbourhood which is an elementary fibration over an irreducible affine scheme
smooth of relative dimension `d - 1` over `k`, compatibly with the structure morphisms. This is
the body of `Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood`. -/
theorem exists_elementaryFibrationNeighbourhood_of_goodSections (k : Type u) [Field k]
    (hgs : ExistsGoodSections k) (hinc : IncidenceFromGoodSections k)
    (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d p]
    [IrreducibleSpace X] (hd : 1 ≤ d) (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (U : X.Opens) (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S),
      x ∈ U ∧ IsElementaryFibration f ∧ SmoothOfRelativeDimension (d - 1) q ∧
        IsAffine S ∧ IrreducibleSpace S ∧ f ≫ q = U.ι ≫ p := by
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsReduced X := Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field k p
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  obtain ⟨W₀, hW₀, hxW₀⟩ : ∃ W₀ : X.Opens, IsAffineOpen W₀ ∧ x ∈ W₀ := by
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨W₀, hW₀, hxW₀⟩
  have : IsAffine W₀.toScheme := hW₀
  have : Nonempty W₀.toScheme := ⟨⟨x, hxW₀⟩⟩
  have : IsIntegral W₀.toScheme := isIntegral_of_isOpenImmersion W₀.ι
  have : IsNormal W₀.toScheme := isNormal_of_smooth_over_field (W₀.ι ≫ p)
  obtain ⟨Xb, j₀, pb, hj₀, hjp, hpb, hnorm, hint⟩ :=
    exists_isOpenImmersion_isProjectiveMorphism_isNormal k (W₀.ι ≫ p)
  have : IsOpenImmersion j₀ := hj₀
  have hXb : IsIntegral Xb := hint inferInstance
  have : IsProper pb := isProper_of_isProjectiveMorphism pb hpb
  let W : Xb.Opens := j₀.opensRange
  have hWι : W.ι ≫ pb = j₀.isoOpensRange.inv ≫ W₀.ι ≫ p := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp j₀, Category.assoc, hjp]
  have hsmW : SmoothOfRelativeDimension d (W.ι ≫ pb) := by
    rw [hWι]
    have h : SmoothOfRelativeDimension (0 + (0 + d)) (j₀.isoOpensRange.inv ≫ W₀.ι ≫ p) :=
      inferInstance
    simpa only [zero_add] using h
  set x' : Xb := j₀ ⟨x, hxW₀⟩
  have hx'W : x' ∈ W := ⟨⟨x, hxW₀⟩, rfl⟩
  have hcl : IsClosed ({x'} : Set Xb) := by
    refine isClosed_singleton_image_of_isImmersion k pb j₀ ⟨x, hxW₀⟩ ?_
    have h : ({⟨x, hxW₀⟩} : Set W₀.toScheme) = W₀.ι.base ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
    rw [h]
    exact hx.preimage W₀.ι.continuous
  obtain ⟨L, hL, v, w₀, hgood⟩ := hgs Xb pb d hpb hXb hnorm W hsmW hd x' hx'W hcl
  obtain ⟨U, S, q, f, hUW, hxU, hf, hq, hS, hSi, hfq⟩ :=
    hinc Xb pb d hpb hXb W hsmW hd x' hx'W hcl L v w₀ hgood
  -- transport the open `U ⊆ W` back to `X`
  let U₀ : W₀.toScheme.Opens := j₀ ⁻¹ᵁ U
  have hr : Set.range (U₀.ι ≫ j₀).base = Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hy
      obtain ⟨b, hb⟩ := hUW hy
      exact ⟨⟨b, show j₀ b ∈ U from hb ▸ hy⟩, hb⟩
  let φ : U₀.toScheme ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq (U₀.ι ≫ j₀) U.ι hr
  have hφ : φ.hom ≫ U.ι = U₀.ι ≫ j₀ := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let ψ := (U₀.ι ≫ W₀.ι).isoOpensRange
  refine ⟨(U₀.ι ≫ W₀.ι).opensRange, S, q, ψ.inv ≫ φ.hom ≫ f, ?_,
    (hf.precomp_iso φ).precomp_iso ψ.symm, hq, hS, hSi, ?_⟩
  · exact ⟨⟨⟨x, hxW₀⟩, hxU⟩, rfl⟩
  · calc (ψ.inv ≫ φ.hom ≫ f) ≫ q = ψ.inv ≫ (φ.hom ≫ U.ι) ≫ pb := by
          simp only [Category.assoc, hfq]
      _ = ψ.inv ≫ U₀.ι ≫ W₀.ι ≫ p := by rw [hφ, Category.assoc, hjp]
      _ = (U₀.ι ≫ W₀.ι).opensRange.ι ≫ p := by
          rw [← Scheme.Hom.isoOpensRange_inv_comp (U₀.ι ≫ W₀.ι), Category.assoc, Category.assoc]

end AlgebraicGeometry.GoodNeighbourhood

end
