module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricCoinvariantsGaloisAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportActionNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.NormalCoinvariantsContinuousModule

/-!
# Reduction of `H²_c(X_k̄, ℱ_ρ)` to the largest quotient constant on `X_k̄`

Let `X` be a geometrically connected smooth curve over `k` and `ρ` a finite `Λ`-module with a
continuous action of `π₁(X, η̄)`. Let `N` be the image of `π₁(X_k̄, η̄)`. The quotient
`q : M ⟶ M_N` onto the `N`-coinvariants, with the residual action of `π₁(X, η̄)`, is a morphism
of representations `ρ ⟶ ρ_N`. On sheaves it is the largest quotient `ℱ_ρ ⟶ ℱ''` that is constant
on `X_k̄` (Deligne's reformulation of Tag 03VK). This file shows that
`H²_c(X_k̄, ℱ_ρ) ⟶ H²_c(X_k̄, ℱ_{ρ_N})` is an isomorphism of `Aut(k̄/k)`-modules.

Bijectivity follows from the map `θ` of `AlgebraicGeometry.compactSupportGeometricCoinvariantsMap`:
it is bijective and natural in `ρ`, and `q` induces a bijection of geometric coinvariants
`M_{π₁(X_k̄)} ⟶ (M_N)_{π₁(X_k̄)} = M_N`. Neither fact depends on how `θ` was built, so the
comparison is canonical. Galois equivariance is the naturality of the Galois action on `H²_c`
(`Stacks.EtaleCohomology.galoisCompactSupportGroupAction_naturality`).

## Main definitions

* `AlgebraicGeometry.geometricNormalCoinvariants` — `ρ_N`.
* `AlgebraicGeometry.compactSupportNormalCoinvariantsEquiv` —
  `H²_c(X_k̄, ℱ_ρ) ≃ H²_c(X_k̄, ℱ_{ρ_N})`.

## Main results

* `AlgebraicGeometry.bijective_coinvariantsMk_mapQ_normal` — `M_{H} ⟶ (M_N)_{H}` is bijective
  when `H` maps onto the normal subgroup `N`.
* `AlgebraicGeometry.compactSupportNormalCoinvariantsEquiv_galois` — the comparison is Galois
  equivariant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

section Algebra

variable {Λ : Type*} [Ring Λ] {M : Type*} [AddCommGroup M] [Module Λ M] {G H : Type*} [Group G]
  [Group H] (ρ : Representation Λ G M) (N : Subgroup G) [N.Normal] (ι : H →* G)

/-- `M ⟶ M_N` carries the differences `h m - m`, `h ∈ H`, to the differences for the residual
action. -/
theorem coinvariantsKer_le_comap_coinvariantsMk_normal :
    Stacks.Trace.coinvariantsKer (ρ.comp ι) ≤
      (Stacks.Trace.coinvariantsKer ((normalCoinvariantsRepresentation ρ N).comp ι)).comap
        (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype)) := by
  rw [Stacks.Trace.coinvariantsKer, Submodule.span_le]
  rintro _ ⟨⟨h, m⟩, rfl⟩
  refine Submodule.subset_span ⟨(h, Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m), ?_⟩
  change normalCoinvariantsRepresentation ρ N (ι h)
      (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m) -
        Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m =
    Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) (ρ (ι h) m - m)
  rw [normalCoinvariantsRepresentation_apply_mk, map_sub]

/-- **`M_H ⟶ (M_N)_H` is bijective** when `H` maps onto the normal subgroup `N`: the residual
action of `H` on `M_N` is trivial, and the `H`-coinvariants of `M` are its `N`-coinvariants. -/
theorem bijective_coinvariantsMk_mapQ_normal (hι : ι.range = N) :
    Function.Bijective (Submodule.mapQ (Stacks.Trace.coinvariantsKer (ρ.comp ι))
      (Stacks.Trace.coinvariantsKer ((normalCoinvariantsRepresentation ρ N).comp ι))
      (Stacks.Trace.coinvariantsMk (ρ.comp N.subtype))
      (coinvariantsKer_le_comap_coinvariantsMk_normal ρ N ι)) := by
  have hbot : Stacks.Trace.coinvariantsKer ((normalCoinvariantsRepresentation ρ N).comp ι) = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨⟨h, w⟩, rfl⟩
    exact sub_eq_zero.mpr (congrArg (fun φ => φ w)
      ((isTrivial_normalCoinvariantsRepresentation ρ N).out ⟨ι h, hι ▸ ⟨h, rfl⟩⟩))
  have hker : Stacks.Trace.coinvariantsKer (ρ.comp ι) =
      Stacks.Trace.coinvariantsKer (ρ.comp N.subtype) := by
    refine congrArg (Submodule.span Λ) (Set.ext fun v => ⟨?_, ?_⟩)
    · rintro ⟨⟨h, m⟩, rfl⟩
      exact ⟨(⟨ι h, hι ▸ ⟨h, rfl⟩⟩, m), rfl⟩
    · rintro ⟨⟨⟨g, hg⟩, m⟩, rfl⟩
      obtain ⟨h, rfl⟩ := hι.symm ▸ hg
      exact ⟨(h, m), rfl⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
    have h1 : Stacks.Trace.coinvariantsMk (ρ.comp N.subtype) m ∈
        Stacks.Trace.coinvariantsKer ((normalCoinvariantsRepresentation ρ N).comp ι) :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    rw [hbot] at h1
    have h2 : m ∈ Stacks.Trace.coinvariantsKer (ρ.comp N.subtype) :=
      (Submodule.Quotient.mk_eq_zero _).mp ((Submodule.mem_bot Λ).mp h1)
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hker ▸ h2)
  · intro x
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ w
    exact ⟨Submodule.mkQ _ m, rfl⟩

end Algebra

section Reduction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (Λ : Type) [Ring Λ] [Fintype Λ]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

/-- **`ρ_N`: the coinvariants `M_N` of the image `N` of `π₁(X_k̄, η̄)`**, with the residual action
of `π₁(X, η̄)`; its sheaf is the largest quotient of `ℱ_ρ` that is constant on `X_k̄`. -/
abbrev geometricNormalCoinvariants
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  finiteTypeContinuousModuleNormalCoinvariants Λ
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range ρ

/-- **The quotient `ρ ⟶ ρ_N`.** -/
abbrev geometricNormalCoinvariantsQuotient
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    ρ ⟶ geometricNormalCoinvariants B X f kbar Λ y ρ :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  finiteTypeContinuousModuleNormalCoinvariantsQuotient Λ
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range ρ

omit [Fintype Λ] [Smooth f] in
/-- **`M_{π₁(X_k̄)} ⟶ (M_N)_{π₁(X_k̄)}` is bijective.** -/
theorem bijective_geometricCoinvariantsMap_normalCoinvariantsQuotient
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    Function.Bijective (geometricCoinvariantsMap B X f kbar Λ y
      (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  exact bijective_coinvariantsMk_mapQ_normal (finiteTypeContinuousModuleRepresentation Λ _ ρ)
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range
    (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom rfl

variable (j : CompactificationOf (Over.mk f)) (hn : IsUnit ((Fintype.card Λ : ℕ) : kbar))

include hn in
/-- **`H²_c(X_k̄, ℱ_ρ) ⟶ H²_c(X_k̄, ℱ_{ρ_N})` is bijective.** -/
theorem bijective_compactSupportNormalCoinvariantsQuotient
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    Function.Bijective ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ)
        ((2 : ℕ) : ℤ)).map (galoisCompactSupportCohomologyMap Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
            ((representationSheaf B X _ Λ).map
              (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ))))).hom := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have hζ := (exists_isPrimitiveRoot_of_isUnit hn).choose_spec
  have hnat := compactSupportGeometricCoinvariantsMap_naturality B X f kbar Λ y j hn hζ
    (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ)
  have h₂ := bijective_compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ
    (geometricNormalCoinvariants B X f kbar Λ y ρ)
  refine (Function.Bijective.of_comp_iff' h₂ _).mp ?_
  rw [← LinearMap.coe_comp, hnat]
  exact (bijective_geometricCoinvariantsMap_normalCoinvariantsQuotient B X f kbar Λ y ρ).comp
    (bijective_compactSupportGeometricCoinvariantsMap B X f kbar Λ y j hn hζ ρ)

/-- **`H²_c(X_k̄, ℱ_ρ) ≃ H²_c(X_k̄, ℱ_{ρ_N})`**, induced by the largest quotient of `ℱ_ρ` that is
constant on `X_k̄`. -/
def compactSupportNormalCoinvariantsEquiv
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    letI := connectedSpace_of_isCurve B X f
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ) ≃ₗ[Λ]
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj (geometricNormalCoinvariants B X f kbar Λ y ρ)))
        ((2 : ℕ) : ℤ) :=
  letI := connectedSpace_of_isCurve B X f
  LinearEquiv.ofBijective _
    (bijective_compactSupportNormalCoinvariantsQuotient B X f kbar Λ y j hn ρ)

/-- The isomorphism `compactSupportNormalCoinvariantsEquiv` is the map on `H²_c` induced by the
quotient `ℱ_ρ → ℱ_{ρ_N}`. -/
theorem compactSupportNormalCoinvariantsEquiv_apply
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ x =
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ)
        ((2 : ℕ) : ℤ)).map (galoisCompactSupportCohomologyMap Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
            ((representationSheaf B X _ Λ).map
              (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ))))).hom x := rfl

/-- **The comparison `H²_c(X_k̄, ℱ_ρ) ≃ H²_c(X_k̄, ℱ_{ρ_N})` commutes with `Aut(k̄/k)`.** -/
theorem compactSupportNormalCoinvariantsEquiv_galois (σ : kbar ≃ₐ[k] kbar)
    (ρ : letI := connectedSpace_of_isCurve B X f
      FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ
        ((galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ Λ).obj ρ)) ((2 : ℕ) : ℤ)).hom x) =
      (galoisCompactSupportGroupAction Λ f j kbar σ
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ Λ).obj (geometricNormalCoinvariants B X f kbar Λ y ρ)))
          ((2 : ℕ) : ℤ)).hom (compactSupportNormalCoinvariantsEquiv B X f kbar Λ y j hn ρ x) :=
  let := connectedSpace_of_isCurve B X f
  congrArg (fun φ => φ.hom x) (galoisCompactSupportGroupAction_naturality Λ f j kbar σ
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
      ((representationSheaf B X _ Λ).map
        (geometricNormalCoinvariantsQuotient B X f kbar Λ y ρ))) ((2 : ℕ) : ℤ))

end Reduction

end AlgebraicGeometry

end
