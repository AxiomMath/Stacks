module

public import StacksFrontier.Cotangent.SurjectionSiteLocalClaim
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.RingTheory.TensorInterchange

/-!
# The local claim of [Stacks, Tag 08RF], in the form a resolution of the ideal computes

Let `A` be a commutative ring, let `E` be a type in the same universe, let `S = A[E]` with
`𝔪 = (X_e ; e ∈ E)` the ideal of variables, let `T` be an `A`-module and let `M` be an `S`-module
killed by `𝔪`.  `StacksFrontier.Cotangent.SurjectionSiteLocalClaim` proves the local claim in the
shape its proof produces: the transition `W_{n+k} ⟶ W_n` of the complexes `W_m = Q_• ⊗_S 𝔪ᵐ`,
for a fixed projective resolution `Q_•` of `M`, is zero on `Hⁱ(F(-))` for every additive `F` and
every `i > -k`.  Those complexes resolve the **fixed** module `M` and are functorial in the
ideal, so with `F = (-) ⊗_A T` what they compute is the map

`Tor'_j^S(M, 𝔪^{n+k} ⊗_A T) ⟶ Tor'_j^S(M, 𝔪ⁿ ⊗_A T)`,

the second variable of `Tor'` — the one which is *not* resolved.

The consumer of the claim is the change of coefficients: the derived tensor product
`𝒦ⁿ ⊗^L_𝒪 B̲` of the global argument is computed from a projective resolution **of `𝒦ⁿ`**, so
what it produces is the map on `Tor'_j^S(-, T)`, the variable which *is* resolved.  This file
puts the claim in that shape.  Two steps intervene.

* **The orientation of the tensor factors.**  The local complexes are
  `W_m ⊗_A T = (Q_• ⊗_S 𝔪ᵐ) ⊗_A T`, while a resolution of the ideal computes with
  `Q_• ⊗_S (𝔪ᵐ ⊗_A T)`.  The two are identified by `ModuleCat.tensorRightAssoc`
  (`StacksFrontier.RingTheory.TensorInterchange`), a natural isomorphism of functors of the first
  factor, compatibly with the inclusions `𝔪ᵐ ⊆ 𝔪ⁿ`.  `𝔪ᵐ ⊗_A T` carries the `S`-action of its
  left factor, which is the one `Tor'` over `S` is taken with.
* **The two variables of `Tor'`.**  They are exchanged by
  `StacksDraft.AugmentationTor.tor'_map_app_eq_zero_of_obj_map_eq_zero`, which is the balancing
  of [Stacks, Tag 00M1] flipped against the braiding comparison of [Stacks, Tag 00M3].

Also recorded here is the reindexing that carries the claim from the cochain complexes over `ℤ`
it is stated on to the chain complexes over `ℕ` a `CategoryTheory.ProjectiveResolution` is:
`Stacks.DerivedIndexing.mapExtendNatIsoSymm`, which commutes an additive functor applied
termwise past extension by zero, and `Stacks.DerivedIndexing.extendHomologyNatIso`.

## Main definitions

* `StacksDraft.PolynomialLocalComplex.tensorVariableIdealPow`: the `S`-module `𝔪ᵐ ⊗_A T`.
* `StacksDraft.PolynomialLocalComplex.tensorVariableIdealPowMap`: the map
  `𝔪ᵐ ⊗_A T ⟶ 𝔪ⁿ ⊗_A T` induced by `𝔪ᵐ ⊆ 𝔪ⁿ`.

## Main results

* `StacksDraft.PolynomialLocalComplex.tor'_map_app_tensorVariableIdealPowMap_eq_zero`: **the
  local claim with the ideal resolved.** For `j < k` the map `𝔪^{n+k} ⊗_A T ⟶ 𝔪ⁿ ⊗_A T` induces
  the zero map on `Tor'_j^S(-, M)`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped TensorProduct

universe u

namespace StacksDraft.PolynomialLocalComplex

/-! ### Vanishing of a homology map is reflected by a faithful functor -/

section Faithful

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.Faithful] {ι : Type*} (c : ComplexShape ι)
  (j : ι)

/-- **Vanishing of a homology map is reflected by a faithful functor which preserves homology.**
This is the converse of `StacksDraft.PolynomialLocalComplex.homologyMap_map_eq_zero`, and is how
a statement about complexes of `S`-modules is read off the same statement about the underlying
complexes of `A`-modules. -/
lemma homologyMap_eq_zero_of_map_eq_zero {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (hφ : HomologicalComplex.homologyMap ((G.mapHomologicalComplex c).map φ) j = 0) :
    HomologicalComplex.homologyMap φ j = 0 := by
  have hnat := (mapHomologicalComplexHomologyFunctorIso G c j).hom.naturality φ
  have hz : (G.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c j).map φ = 0 := hφ
  rw [hz, zero_comp] at hnat
  have hG : G.map (HomologicalComplex.homologyMap φ j) = 0 :=
    zero_of_epi_comp ((mapHomologicalComplexHomologyFunctorIso G c j).hom.app K) hnat.symm
  exact G.map_eq_zero_iff.1 hG

end Faithful

/-! ### The local claim on chain complexes over `ℕ` -/

section Reindex

variable {A : Type u} [CommRing A] {E : Type u}
  {M : ModuleCat.{u} (MvPolynomial E A)} (Q : ProjectiveResolution M)

/-- **The local claim of [Stacks, Tag 08RF], reindexed as a statement about the chain complex of
the projective resolution.** For every additive functor `F` out of `A`-modules, the transition
`Q_• ⊗_S 𝔪^{n+k} ⟶ Q_• ⊗_S 𝔪ⁿ` is zero on `H_j(F(-))` for every `j < k`.

This is `StacksDraft.PolynomialLocalComplex.homologyMap_map_localComplexMap_eq_zero` carried
across the reindexing: `Stacks.DerivedIndexing.mapExtendNatIsoSymm` commutes `F` applied
termwise past extension by zero along `ComplexShape.embeddingUpIntLE 0`, and
`HomologicalComplex.extendHomologyIso_hom_naturality` identifies `H^{-j}` of an extension with
`H_j`. -/
theorem homologyMap_map_tensorRestrictMap_eq_zero
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0)
    {D : Type*} [Category* D] [Abelian D] (F : ModuleCat.{u} A ⥤ D) [F.Additive]
    (n k j : ℕ) (hj : j < k) :
    HomologicalComplex.homologyMap
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((NatTrans.mapHomologicalComplex (tensorRestrictMap A E (Nat.le_add_right n k))
          (ComplexShape.down ℕ)).app Q.complex))) j = 0 := by
  set e := ComplexShape.embeddingUpIntLE (0 : ℤ) with he
  have hj' : e.f j = -(j : ℤ) := by simp [he]
  set φ := (NatTrans.mapHomologicalComplex (tensorRestrictMap A E (Nat.le_add_right n k))
    (ComplexShape.down ℕ)).app Q.complex with hφ
  -- the local claim, on the extended cochain complexes
  have h1 : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap φ e)) (-(j : ℤ)) = 0 :=
    homologyMap_map_localComplexMap_eq_zero Q hM F n k (-(j : ℤ)) (by omega)
  -- commute `F` past the extension
  have h2 : HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) e)
        (-(j : ℤ)) = 0 := by
    have h := congrArg (fun ψ => HomologicalComplex.homologyMap ψ (-(j : ℤ)))
      (Stacks.DerivedIndexing.mapExtendIsoSymm_naturality F e φ)
    simp only [HomologicalComplex.homologyMap_comp] at h
    rw [h1, zero_comp] at h
    exact zero_of_epi_comp _ h.symm
  -- read `H^{-j}` of the extension as `H_j`
  have hnat := HomologicalComplex.extendHomologyIso_hom_naturality
    (φ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) (e := e) (hj' := hj')
  rw [h2, zero_comp] at hnat
  exact zero_of_epi_comp _ hnat.symm

end Reindex

/-! ### `𝔪ᵐ ⊗_A T` and the local claim with the ideal resolved -/

section Resolved

variable {A : Type u} [CommRing A] {E : Type u} (T : ModuleCat.{u} A)

/-- **The `S`-module `𝔪ᵐ ⊗_A T`**, for `S = A[E]` and `𝔪 = (X_e ; e ∈ E)`: the base change of
the `m`-th power of the ideal of variables along `A → T`, with `S` acting on the left factor.
This is the orientation in which the sections of `𝒦ᵐ` on an object of the polynomial site in
normal form carry their `𝒪`-action. -/
abbrev tensorVariableIdealPow (m : ℕ) : ModuleCat.{u} (MvPolynomial E A) :=
  ModuleCat.of (MvPolynomial E A)
    (↥(Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m) ⊗[A] (T : Type u))

/-- **The map `𝔪ᵐ ⊗_A T ⟶ 𝔪ⁿ ⊗_A T`** induced by the inclusion `𝔪ᵐ ⊆ 𝔪ⁿ`, for `n ≤ m`. -/
def tensorVariableIdealPowMap {n m : ℕ} (h : n ≤ m) :
    tensorVariableIdealPow (E := E) T m ⟶ tensorVariableIdealPow (E := E) T n :=
  ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.map
    (Submodule.inclusion (Ideal.pow_le_pow_right h :
      (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ m :
          Ideal (MvPolynomial E A)) ≤
        Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n))
    (LinearMap.id (R := A) (M := (T : Type u))))

variable {M : ModuleCat.{u} (MvPolynomial E A)}

/-- **The local claim of [Stacks, Tag 08RF], with the second variable of `Tor'` the ideal.** For
an `S`-module `M` killed by `𝔪`, the map `𝔪^{n+k} ⊗_A T ⟶ 𝔪ⁿ ⊗_A T` induces the zero map on
`Tor'_j^S(M, -)` for every `j < k`.

`Tor'_j^S(M, -)` is computed by any projective resolution `Q_•` of `M`, so this is
`StacksDraft.PolynomialLocalComplex.homologyMap_map_tensorRestrictMap_eq_zero` at
`F = (-) ⊗_A T` read through `ModuleCat.tensorRightAssoc`, which identifies
`(Q_• ⊗_S 𝔪ᵐ) ⊗_A T` with `Q_• ⊗_S (𝔪ᵐ ⊗_A T)` compatibly with the inclusions, and through
`CategoryTheory.ProjectiveResolution.leftDerived_app_eq`. -/
theorem tor'_obj_map_tensorVariableIdealPowMap_eq_zero (Q : ProjectiveResolution M)
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0)
    (n k j : ℕ) (hj : j < k) :
    ((Tor' (ModuleCat.{u} (MvPolynomial E A)) j).obj M).map
      (tensorVariableIdealPowMap T (Nat.le_add_right n k)) = 0 := by
  set ι := Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_add_right n k) :
    (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ (n + k) :
        Ideal (MvPolynomial E A)) ≤
      Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n) with hι
  have hA : HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        (ModuleCat.tensorRightTensorRightMap A (MvPolynomial E A) _ T ι)
        (ComplexShape.down ℕ)).app Q.complex) j = 0 :=
    homologyMap_map_tensorRestrictMap_eq_zero Q hM (tensorRight T) n k j hj
  have hassoc := NatTrans.congr_app
    (show NatTrans.mapHomologicalComplex
          (ModuleCat.tensorRightTensorRightMap A (MvPolynomial E A) _ T ι)
          (ComplexShape.down ℕ) ≫
        (NatIso.mapHomologicalComplex (ModuleCat.tensorRightAssoc A (MvPolynomial E A) _ T)
            (ComplexShape.down ℕ)).hom =
      (NatIso.mapHomologicalComplex (ModuleCat.tensorRightAssoc A (MvPolynomial E A) _ T)
            (ComplexShape.down ℕ)).hom ≫
        NatTrans.mapHomologicalComplex
          (ModuleCat.tensorRightTensorProductMap A (MvPolynomial E A) _ T ι)
          (ComplexShape.down ℕ) from by
      dsimp only [NatIso.mapHomologicalComplex]
      rw [← NatTrans.mapHomologicalComplex_comp, ← NatTrans.mapHomologicalComplex_comp,
        ModuleCat.tensorRightTensorRightMap_comp_tensorRightAssoc]) Q.complex
  have hB := congrArg (fun ψ => HomologicalComplex.homologyMap ψ j) hassoc
  simp only [NatTrans.comp_app, HomologicalComplex.homologyMap_comp, hA, zero_comp] at hB
  replace hB := zero_of_epi_comp _ hB.symm
  have hS : HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{u} (MvPolynomial E A))).map
          (tensorVariableIdealPowMap T (Nat.le_add_right n k)))
        (ComplexShape.down ℕ)).app Q.complex) j = 0 :=
    homologyMap_eq_zero_of_map_eq_zero
      (ModuleCat.restrictScalars (algebraMap A (MvPolynomial E A))) (ComplexShape.down ℕ) j _ hB
  simp only [Tor'_obj_map]
  rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq _ Q j]
  rw [show (HomologicalComplex.homologyFunctor (ModuleCat.{u} (MvPolynomial E A))
        (ComplexShape.down ℕ) j).map
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat.{u} (MvPolynomial E A))).map
          (tensorVariableIdealPowMap T (Nat.le_add_right n k)))
        (ComplexShape.down ℕ)).app Q.complex) = 0 from hS, zero_comp, comp_zero]
  exact rfl

/-- **The local claim of [Stacks, Tag 08RF], with the ideal resolved.** For an `S`-module `M`
killed by `𝔪`, the map `𝔪^{n+k} ⊗_A T ⟶ 𝔪ⁿ ⊗_A T` induces the zero map on `Tor'_j^S(-, M)` —
the variable which a projective resolution of the ideal computes — for every `j < k`.

This is `StacksDraft.PolynomialLocalComplex.tor'_obj_map_tensorVariableIdealPowMap_eq_zero`
read through `StacksDraft.AugmentationTor.tor'_map_app_eq_zero_of_obj_map_eq_zero`, which
exchanges the two variables of `Tor'`. It is the shape in which the derived tensor product with
a new coefficient ring consumes the claim: `𝒦ⁿ ⊗^L_𝒪 B̲` is computed from a projective
resolution of `𝒦ⁿ`. -/
theorem tor'_map_app_tensorVariableIdealPowMap_eq_zero (Q : ProjectiveResolution M)
    (hM : ∀ r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) :
        Ideal (MvPolynomial E A)), ∀ x : M, r • x = 0)
    (n k j : ℕ) (hj : j < k) :
    ((Tor' (ModuleCat.{u} (MvPolynomial E A)) j).map
      (tensorVariableIdealPowMap T (Nat.le_add_right n k))).app M = 0 :=
  StacksDraft.AugmentationTor.tor'_map_app_eq_zero_of_obj_map_eq_zero j M _
    (tor'_obj_map_tensorVariableIdealPowMap_eq_zero T Q hM n k j hj)

end Resolved

end StacksDraft.PolynomialLocalComplex

end
