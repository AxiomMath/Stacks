module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GenericFibreSpreading

/-!
# Dense elementary fibrations

Let `X` be a scheme over a field `k` and let `π : X̄ ⟶ T` be a *generic elementary fibration*: a
projective morphism to a normal integral `T` smooth of relative dimension `d - 1` over `k`, with
smooth geometrically irreducible generic fibre of relative dimension `1`, together with an open
`V ⊆ X` embedded in `X̄` over `k` and meeting the generic fibre, and a reduced boundary étale over
`T` at its points over the generic point, some of which exist. Then some nonempty open of `X` is an
elementary fibration over an affine scheme smooth of relative dimension `d - 1` over `k` (SGA 4,
Exposé XI, Proposition 3.3, in its weakest form: some nonempty open, with no condition at a given
point).

## Main results

* `AlgebraicGeometry.IsElementaryFibration.precomp_iso`: elementary fibrations are stable under
  precomposition with an isomorphism.
* `AlgebraicGeometry.exists_dense_isElementaryFibration_of_genericFibre`: a nonempty open
  elementary fibration from a generic one.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Elementary fibrations are stable under precomposition with an isomorphism.** -/
theorem IsElementaryFibration.precomp_iso {U U' S : Scheme.{u}} {f : U ⟶ S}
    (hf : IsElementaryFibration f) (φ : U' ≅ U) : IsElementaryFibration (φ.hom ≫ f) := by
  obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, hZ, hrange, hfin, het, hsurj⟩ :=
    hf.exists_compactification
  refine ⟨⟨Xbar, Z, φ.hom ≫ j, fbar, i, inferInstance, by rw [Category.assoc, hjf], hsm, hproj,
    hgi, hi, hZ, ?_, hfin, het, hsurj⟩⟩
  rw [hrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr φ.hom.surjective, Set.image_univ]

/-- **A dense elementary fibration from a generic one.** Let `X` be a scheme over a field `k`, let
`T` be a normal integral scheme smooth of relative dimension `d - 1` over `k` with generic point
`η`, and let `π : X̄ ⟶ T` be projective with smooth geometrically irreducible generic fibre of
relative dimension `1`. Let `V ⊆ X` be an open with an open immersion `j : V ⟶ X̄` over `k` meeting
the generic fibre, and let `i : Z ⟶ X̄` be a reduced closed subscheme with support the complement
of the image of `j`, étale over `T` at its points over `η`, some of which exist. Then some nonempty
open `U ⊆ X` is an elementary fibration over an affine scheme smooth of relative dimension `d - 1`
over `k`, compatibly with the structure morphisms. -/
theorem exists_dense_isElementaryFibration_of_genericFibre (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (d : ℕ)
    {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) [IsIntegral T] [IsNormal T]
    [SmoothOfRelativeDimension (d - 1) τ]
    {Xt : Scheme.{u}} (π : Xt ⟶ T) (hπ : IsProjectiveMorphism π)
    (hsm : SmoothOfRelativeDimension 1 (π.fiberToSpecResidueField (genericPoint T)))
    (hgi : GeometricallyIrreducible (π.fiberToSpecResidueField (genericPoint T)))
    (V : X.Opens) (j : V.toScheme ⟶ Xt) [IsOpenImmersion j] (hj : j ≫ π ≫ τ = V.ι ≫ p)
    (hV : ∃ v : V.toScheme, π (j v) = genericPoint T)
    {Z : Scheme.{u}} (i : Z ⟶ Xt) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ)
    (het : ∀ z : Z, π (i z) = genericPoint T → EtaleAt (i ≫ π) z)
    (hne : ∃ z : Z, π (i z) = genericPoint T) :
    ∃ (U : X.Opens) (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S),
      (U : Set X).Nonempty ∧ IsElementaryFibration f ∧ SmoothOfRelativeDimension (d - 1) q ∧
        IsAffine S ∧ f ≫ q = U.ι ≫ p := by
  have : Smooth τ := SmoothOfRelativeDimension.smooth (d - 1) τ
  obtain ⟨S₀, U₀, e, f₀, hS₀, hηS₀, he, hf₀, hcomm, hrange⟩ :=
    exists_isElementaryFibration_of_genericFibre k τ π hπ hsm hgi j i hZ het hne
  have : IsOpenImmersion e := he
  let φ := (e ≫ V.ι).isoOpensRange
  have : IsAffine S₀.toScheme := hS₀
  have hq : SmoothOfRelativeDimension (d - 1) (S₀.ι ≫ τ) := by
    have h : SmoothOfRelativeDimension (0 + (d - 1)) (S₀.ι ≫ τ) := inferInstance
    rwa [zero_add] at h
  refine ⟨(e ≫ V.ι).opensRange, S₀.toScheme, S₀.ι ≫ τ, φ.inv ≫ f₀, ?_, hf₀.precomp_iso φ.symm, hq,
    inferInstance, ?_⟩
  · obtain ⟨v, hv⟩ := hV
    have hv' : v ∈ Set.range e.base := by
      rw [hrange, Set.mem_preimage, Scheme.Hom.comp_apply, hv]
      exact hηS₀
    obtain ⟨u₀, rfl⟩ := hv'
    exact ⟨_, ⟨u₀, rfl⟩⟩
  · calc (φ.inv ≫ f₀) ≫ S₀.ι ≫ τ = φ.inv ≫ (f₀ ≫ S₀.ι) ≫ τ := by
          simp only [Category.assoc]
      _ = φ.inv ≫ e ≫ j ≫ π ≫ τ := by rw [hcomm]; simp only [Category.assoc]
      _ = φ.inv ≫ (e ≫ V.ι) ≫ p := by rw [hj, Category.assoc]
      _ = (e ≫ V.ι).opensRange.ι ≫ p := Scheme.Hom.isoOpensRange_inv_comp_assoc _ _

end AlgebraicGeometry

end
