module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCanonicalTwist

/-!
# Tag 03VK: `H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}(-1)` as `Gal(k^{sep}/k)`-modules

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure,
`Λ` a finite ring with `n = #Λ` invertible, and `ℱ_ρ` the sheaf on `X_étale` attached to a finite
`Λ`-module `M` with a continuous action `ρ` of `π₁(X, η̄)`. Following the source's reformulation
(Deligne, Weil II, p. 338), the identification is built in three steps.

* `ℱ_ρ ⟶ ℱ_{ρ_N}`, the largest quotient constant on `X_k̄` (`N` the image of `π₁(X_k̄, η̄)` and
  `ρ_N = M_N`), induces `H²_c(X_k̄, ℱ_ρ) ≅ H²_c(X_k̄, ℱ_{ρ_N})`
  (`AlgebraicGeometry.compactSupportNormalCoinvariantsEquiv`).
* For `ρ'` on which `π₁(X_k̄)` acts trivially, `Ξ_ζ : H²_c(X_k̄, ℱ_{ρ'}) ≅ M'` is the smooth model
  `H²_c(X_k̄, ℱ) ≅ H²(C, q^{-1}(j_! ℱ))`, the trace through a primitive `n`-th root of unity `ζ` on
  the smooth projective model `C` of `X_k̄` onto `Γ(X_k̄, ℱ|_{X_k̄})`, and
  `Γ(X_k̄, ℱ_{ρ'}|_{X_k̄}) ≅ M'` by evaluation at `η̄`
  (`AlgebraicGeometry.compactSupportTrivialTrace`). It satisfies `Ξ_{σ(ζ)}(σ x) = ρ'(γ) Ξ_ζ(x)` for
  `γ` lifting `σ` (`AlgebraicGeometry.compactSupportTrivialTrace_galois`) and `Ξ_{ζ^b} = b Ξ_ζ`.
* `x ↦ (ζ ↦ Ξ_ζ(x))` is then a choice-free isomorphism onto `Hom(μ_n(k̄), M') = M'(-1)`
  (`AlgebraicGeometry.compactSupportTrivialTwistEquiv`).

## Main definitions

* `AlgebraicGeometry.compactSupportCanonicalTwistEquiv` — the isomorphism
  `Ψ : H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_N)`.
* `AlgebraicGeometry.geometricNormalCoinvariantsGaloisRepresentation` — the residual Galois action
  on `M_N`.

## Main results

* `AlgebraicGeometry.compactSupportCanonicalTwistEquiv_galois` — `Ψ` is Galois-equivariant.
* `AlgebraicGeometry.compactSupportCanonicalTwistEquiv_apply_ofMul` — `Ψ` involves no choice of a
  root of unity.
* `AlgebraicGeometry.geometricNormalCoinvariantsEquiv_galoisRepresentation` — the action on `M_N`
  is the residual action of `π₁(X, η̄)/π₁(X_k̄, η̄) ≅ Aut_k(k̄)` on the coinvariants.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace AlgebraicGeometry

section Canonical

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))
  (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

/-- **`ρ_N = M_N`**: the module of `ρ_N` is the coinvariants `M_N` of the restriction of `ρ` to
the image `N` of `π₁(X_k̄, η̄)`, on the nose. -/
def geometricNormalCoinvariantsEquiv (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V ≃ₗ[Λ]
      Stacks.Trace.coinvariants ((finiteTypeContinuousModuleRepresentation Λ _ ρ).comp
          (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype) :=
  LinearEquiv.refl Λ _

omit [Fintype Λ] [Smooth f] in
/-- Under `ρ_N = M_N`, the action of `γ` on `ρ_N` is the residual Galois action of its image. -/
theorem geometricNormalCoinvariantsEquiv_galois (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (w : letI := connectedSpace_of_isCurve B X f
      (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricCoinvariantsGaloisRepresentation B X f kbar Λ y ρ
        (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ))
        (geometricNormalCoinvariantsEquiv B X f kbar Λ y ρ w) =
      geometricNormalCoinvariantsEquiv B X f kbar Λ y ρ
        ((finiteTypeContinuousModuleRepresentation Λ _
          (geometricNormalCoinvariants B X f kbar Λ y ρ)) γ w) :=
  geometricCoinvariantsGaloisRepresentation_mk B X f kbar Λ y ρ γ w

/-- **The residual Galois action on `ρ_N = M_N`**: `ρ_N` is trivial on the image `N` of
`π₁(X_k̄, η̄)`, so its action factors through `π₁(X, η̄)/N ≅ Aut_k(k̄)`
(`AlgebraicGeometry.geometricQuotientGaloisEquiv`, Tags 0BTX and 0BNE). Under `ρ_N = M_N` it is
`AlgebraicGeometry.geometricCoinvariantsGaloisRepresentation`
(`AlgebraicGeometry.geometricNormalCoinvariantsEquiv_galoisRepresentation`). -/
def geometricNormalCoinvariantsGaloisRepresentation (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Representation Λ (kbar ≃ₐ[k] kbar)
      (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI : Representation.IsTrivial ((finiteTypeContinuousModuleRepresentation Λ _
      (geometricNormalCoinvariants B X f kbar Λ y ρ)).comp
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype) :=
    ⟨fun ⟨_, g, hg⟩ =>
      hg ▸ geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ g⟩
  (Representation.ofQuotient (finiteTypeContinuousModuleRepresentation Λ _
      (geometricNormalCoinvariants B X f kbar Λ y ρ))
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range).comp
    (geometricQuotientGaloisEquiv B X f kbar y).symm.toMonoidHom

omit [Fintype Λ] [Smooth f] in
/-- The residual action of the image of `γ` is the action of `γ`. -/
theorem geometricNormalCoinvariantsGaloisRepresentation_mk
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (w : letI := connectedSpace_of_isCurve B X f
      (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y ρ
        (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)) w =
      (finiteTypeContinuousModuleRepresentation Λ _
        (geometricNormalCoinvariants B X f kbar Λ y ρ)) γ w := by
  unfold geometricNormalCoinvariantsGaloisRepresentation
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

omit [Smooth f] in
/-- Every `σ ∈ Aut_k(k̄)` is the image of some `γ ∈ π₁(X, η̄)`. -/
theorem exists_geometricQuotientGaloisEquiv_mk_eq (σ : kbar ≃ₐ[k] kbar) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ∃ γ : EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom),
      geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) = σ := by
  obtain ⟨γ, hγ⟩ :=
    QuotientGroup.mk_surjective ((geometricQuotientGaloisEquiv B X f kbar y).symm σ)
  exact ⟨γ, by rw [hγ, MulEquiv.apply_symm_apply]⟩

omit [Fintype Λ] [Smooth f] in
/-- Under `ρ_N = M_N`, the residual action on `ρ_N` is the residual action on the coinvariants,
for an element of `π₁(X, η̄)/N`. -/
theorem geometricNormalCoinvariantsEquiv_galoisRepresentation_quot
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (q : letI := connectedSpace_of_isCurve B X f
      letI := connectedSpace_fieldBaseChange f kbar
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) ⧸
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range)
    (w : letI := connectedSpace_of_isCurve B X f
      (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricNormalCoinvariantsEquiv B X f kbar Λ y ρ
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y ρ
          (geometricQuotientGaloisEquiv B X f kbar y q) w) =
      geometricCoinvariantsGaloisRepresentation B X f kbar Λ y ρ
        (geometricQuotientGaloisEquiv B X f kbar y q)
        (geometricNormalCoinvariantsEquiv B X f kbar Λ y ρ w) :=
  QuotientGroup.induction_on q fun γ => by
    rw [geometricNormalCoinvariantsGaloisRepresentation_mk, geometricNormalCoinvariantsEquiv_galois]

omit [Fintype Λ] [Smooth f] in
/-- **Under `ρ_N = M_N`, the residual Galois action on `ρ_N` is the Galois action
`AlgebraicGeometry.geometricCoinvariantsGaloisRepresentation` on `M_{π₁(X_k̄, η̄)}`.** -/
theorem geometricNormalCoinvariantsEquiv_galoisRepresentation (σ : kbar ≃ₐ[k] kbar)
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (w : letI := connectedSpace_of_isCurve B X f
      (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    geometricNormalCoinvariantsEquiv B X f kbar Λ y ρ
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y ρ σ w) =
      geometricCoinvariantsGaloisRepresentation B X f kbar Λ y ρ σ
        (geometricNormalCoinvariantsEquiv B X f kbar Λ y ρ w) := by
  have h := geometricNormalCoinvariantsEquiv_galoisRepresentation_quot B X f kbar Λ y ρ
    ((geometricQuotientGaloisEquiv B X f kbar y).symm σ) w
  rwa [MulEquiv.apply_symm_apply] at h

/-- **`Ψ : H²_c(X_k̄, ℱ_ρ) ≅ Hom(μ_n(k̄), M_N) = M_N(-1)`**, canonical: `H²_c` of the largest
quotient `ℱ_ρ ⟶ ℱ_{ρ_N}` constant on `X_k̄`
(`AlgebraicGeometry.compactSupportNormalCoinvariantsEquiv`), followed by the trace on the smooth
projective model of `X_k̄` and `Γ(X_k̄, ℱ_{ρ_N}) = M_N`, with no root of unity chosen
(`AlgebraicGeometry.compactSupportTrivialTwistEquiv`). The module of
`ρ_N = AlgebraicGeometry.geometricNormalCoinvariants` is the coinvariants `M_N` of the restriction
of `ρ` to the image `N` of `π₁(X_k̄, η̄)` on the nose
(`AlgebraicGeometry.geometricNormalCoinvariantsEquiv`), and `M_N = M_{π₁(X_k̄, η̄)}`
(`AlgebraicGeometry.geometricCoinvariantsRangeEquiv`). -/
def compactSupportCanonicalTwistEquiv (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      (Additive (_root_.rootsOfUnity (Fintype.card Λ) kbar) →+
        (geometricNormalCoinvariants B X f kbar Λ y ρ).obj.obj.obj.V) :=
  (compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ).trans
    (compactSupportTrivialTwistEquiv B X f kbar Λ y j hn
      (geometricNormalCoinvariants B X f kbar Λ y ρ)
      (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ))

/-- `Ψ x` is the image under `AlgebraicGeometry.compactSupportTrivialTwistEquiv` of the image of
`x` under `AlgebraicGeometry.compactSupportNormalCoinvariantsEquiv`. -/
theorem compactSupportCanonicalTwistEquiv_apply (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ x =
      (compactSupportTrivialTwistEquiv B X f kbar Λ y j hn
        (geometricNormalCoinvariants B X f kbar Λ y ρ)
        (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ))
        ((compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ) x) := by
  unfold compactSupportCanonicalTwistEquiv
  rw [LinearEquiv.trans_apply]

/-- For a primitive `n`-th root of unity `ζ`, the value of `Ψ x` at `ζ` is the trace
`Ξ_ζ` (`AlgebraicGeometry.compactSupportTrivialTrace`) of the image of `x` in
`H²_c(X_k̄, ℱ_{ρ_N})`. -/
theorem compactSupportCanonicalTwistEquiv_apply_ofMul (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    {ζ : kbar} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    haveI : NeZero (Fintype.card Λ) := ⟨Fintype.card_ne_zero⟩
    compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ x (Additive.ofMul hζ.toRootsOfUnity) =
      compactSupportTrivialTrace B X f kbar Λ y j hn
        (geometricNormalCoinvariants B X f kbar Λ y ρ)
        (geometricNormalCoinvariants_representation_map_eq_one B X f kbar Λ y ρ) hζ
        (compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ x) := by
  rw [compactSupportCanonicalTwistEquiv_apply]
  exact compactSupportTrivialTwistEquiv_apply_ofMul B X f kbar Λ y j hn _ _ hζ _

/-- **`H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄, η̄)}(-1)` canonically, as `Gal(k^{sep}/k)`-modules.**
Let `X` be a geometrically connected smooth curve over a field `k` (`f : X ⟶ Spec k`), `k̄` an
algebraic closure of `k`, `Λ` a finite ring with `n = #Λ` invertible (in `k̄`, equivalently in
`k`), `η̄` a geometric point of `X_k̄`, and `ℱ_ρ` the sheaf on `X_étale` attached to a finite
`Λ`-module `M` with a continuous action `ρ` of `π₁(X, η̄)`
(`AlgebraicGeometry.representationSheaf`). The canonical `Λ`-linear isomorphism
`Ψ = AlgebraicGeometry.compactSupportCanonicalTwistEquiv : H²_c(X_k̄, ℱ_ρ) ≃ Hom(μ_n(k̄), M_N)`
carries the action of every `σ ∈ Aut_k(k̄)` on `H²_c` (induced by `id × Spec σ`) to the action
`g ↦ σ ∘ g ∘ σ⁻¹` on `Hom(μ_n(k̄), M_N) = M_N(-1)`
(`Stacks.EtaleCohomology.rootsOfUnityHomRepresentation`).

Here `M_N` is the module of `ρ_N = AlgebraicGeometry.geometricNormalCoinvariants`, which is on the
nose the coinvariants of `M` under the image `N` of `π₁(X_k̄, η̄)` in `π₁(X, η̄)`
(`AlgebraicGeometry.geometricNormalCoinvariantsEquiv`), that is `M_{π₁(X_k̄, η̄)}`
(`AlgebraicGeometry.geometricCoinvariantsRangeEquiv`); `σ` acts on it through
`π₁(X, η̄)/N ≅ Aut_k(k̄)` (`AlgebraicGeometry.geometricNormalCoinvariantsGaloisRepresentation`,
which is `AlgebraicGeometry.geometricCoinvariantsGaloisRepresentation` on the coinvariants by
`AlgebraicGeometry.geometricNormalCoinvariantsEquiv_galoisRepresentation`). `Hom(μ_n(k̄), M_N)`
with this action is the Tate twist `M_N(-1)`: evaluation at any primitive `n`-th root of unity
turns it into `σ ↦ χ_cycl(σ)⁻¹ σ`
(`Stacks.EtaleCohomology.rootsOfUnityHomRepresentation_apply_ofMul`, into
`Stacks.EtaleCohomology.tateTwistNegOne`).

Conventions: `Aut_k(k̄) ≅ Gal(k^{sep}/k)` by restriction
(`AlgebraicGeometry.separableClosureRestrictMulEquiv`); `H²_c` is that of Remark 03UI (2),
`RΓ(X̄_k̄, (j_! ℱ)|_{X̄_k̄})` for a compactification `j : X ⟶ X̄` over `k`, independent of `j`
(`geometricCompactSupportGroupCanonicalComparison`, Tag 03UI); `Λ : Type`, a finite ring being
isomorphic to one in `Type`.

Canonicity: `Ψ` is the source's own reformulation (Deligne), `H²_c` of the largest quotient
`ℱ_ρ ⟶ ℱ_{ρ_N}` constant on `X_k̄` followed by the trace on the smooth projective model of `X_k̄`
and evaluation at `η̄`; its values involve no choice, in particular no root of unity
(`AlgebraicGeometry.compactSupportCanonicalTwistEquiv_apply_ofMul`). The isomorphism `θ` of
`AlgebraicGeometry.compactSupportGeometricCoinvariantsMap` (and
`AlgebraicGeometry.compactSupportGaloisTwistEquiv` built on it) is not used: it goes through
`AlgebraicGeometry.representationSheafPullbackIso`, a *chosen* isomorphism
`ℱ_ρ|_{X_k̄} ≅ ℱ_{ρ|π₁(X_k̄)}` (Tag 0DV6 only gives its existence). Two choices differ by a
natural automorphism of restriction to `π₁(X_k̄)`, such as `ρ(c)` for `c` centralising the image
of `π₁(X_k̄)`, which changes `θ` by the action of `c` on `M_π`; so Galois equivariance holds for
`θ` only for suitable choices and cannot be proved for `θ` as defined. -/
@[stacks 03VK]
theorem compactSupportCanonicalTwistEquiv_galois (σ : kbar ≃ₐ[k] kbar)
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ
        ((galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)).hom x) =
      rootsOfUnityHomRepresentation k kbar (Fintype.card Λ) Λ
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar Λ y ρ) σ
        (compactSupportCanonicalTwistEquiv B X f kbar Λ y j hn ρ x) := by
  obtain ⟨γ, hγ⟩ := exists_geometricQuotientGaloisEquiv_mk_eq B X f kbar y σ
  subst hγ
  rw [compactSupportCanonicalTwistEquiv_apply, compactSupportCanonicalTwistEquiv_apply,
    compactSupportNormalCoinvariantsEquiv_galois, compactSupportTrivialTwistEquiv_galois]
  refine AddMonoidHom.ext fun z => ?_
  rw [rootsOfUnityHomRepresentation_apply, geometricNormalCoinvariantsGaloisRepresentation_mk,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive,
    Function.comp_apply, Function.comp_apply, LinearMap.toAddMonoidHom_coe]

end Canonical

end AlgebraicGeometry

end
