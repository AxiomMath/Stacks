module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquareComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceAffineModel
public import StacksFrontier.AlgebraicGeometry.DeRham.TotalSpaceAbelianAcyclic
public import StacksFrontier.AlgebraicGeometry.Scheme.SectionsAlgebraOverBase
public import StacksFrontier.RingTheory.DeRham.PolynomialAlgEquivQuasiIso
public import StacksFrontier.Topology.Sheaves.Sheaf.AbelianComplexLocality

/-!
# The de Rham complex of the total space of a line bundle in characteristic zero

Let `f : X ⟶ S` be a morphism of schemes, let `L` be an invertible `𝒪_X`-module and let
`π : 𝕃 ⟶ X` be the total space of `L`. If `S` lies over `Spec ℚ`, then the canonical map
`Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` is a quasi-isomorphism and `H^*_{dR}(X/S) ⟶ H^*_{dR}(𝕃/S)` is an
isomorphism. This is [Stacks, Tag 0FUI].

## The proof

The source's proof is the affine local statement: for a `ℚ`-algebra `A` over `R` the inclusion
`Ω^•_{A/R} ⟶ Ω^•_{A[T]/R}` is a homotopy equivalence (`PolynomialDeRham.inclHomotopyEquiv`).
The passage to the global statement runs as follows.

* The affine opens `U ⊆ X` lying over an affine open of `S` on which `L` is trivial form a basis
  of the topology of `X` (`Stacks.LineBundle.Situation.isBasis_chartOpens`).
* On such a `U`, with `A = Γ(X, U)` and `R = Γ(S, V)`, the sections over `U` of
  `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` are, up to the affine-open comparison at both ends, the restriction
  of forms `Ω^•_{A/R} ⟶ Ω^•_{B/R}` for `B = Γ(𝕃, π^{-1}U)`
  (`Stacks.LineBundle.Situation.ringDeRhamAbSquareMap_eq`), and `B ≅ A[T]` as `A`-algebras, so
  this is a quasi-isomorphism (`Stacks.LineBundle.Situation.quasiIso_sections_deRhamPushforward`).
* A morphism of complexes of abelian sheaves which is a quasi-isomorphism on sections over the
  members of a basis is a quasi-isomorphism
  (`Stacks.AbelianSheaves.quasiIso_of_forall_sections_quasiIso_nat`).
* `π` is affine, so `π_* = Rπ_*` on the de Rham complex of `𝕃`
  (`Stacks.LineBundle.Situation.isIso_deRhamPushforwardToDerived`), and the de Rham cohomology of
  `𝕃` is therefore computed on `X` by `π_*Ω^•_{𝕃/S}`.

## Main results

* `Stacks.LineBundle.Situation.quasiIso_deRhamPushforward`: **`Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` is a
  quasi-isomorphism** over a base lying over `Spec ℚ`.
* `Stacks.LineBundle.Situation.isIso_deRhamCohomologyPullback`:
  **`H^i_{dR}(X/S) ≅ H^i_{dR}(𝕃/S)`** in every degree, by the pullback along `π`.

The rationality hypothesis is a morphism `S ⟶ Spec R` for a `ℚ`-algebra `R`; the source's
hypothesis, a morphism `S ⟶ Spec ℚ`, is the case `R = ℚ` (in universe `u`, `ULift ℚ`), and
conversely a morphism to `Spec R` composes with `Spec R ⟶ Spec ℚ`.

## References

* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite Polynomial
open Stacks.AlgebraicGeometry.AffineOpenDeRham Stacks.Cohomology.LerayLowDegree

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### A basis of sections from a trivialization -/

/-- A trivialization of the line bundle over an open `U`, read on sections over `U`: the
evaluation of an isomorphism `L|_U ≅ 𝒪_U` of sheaves of modules at `U` itself. -/
def Situation.trivializationSectionsEquiv (U : D.X.Opens)
    (t : D.L.over U ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U)) :
    Γ(D.L, U) ≃ₗ[Γ(D.X, U)] Γ(D.X, U) :=
  ((PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).mapIso
    ((_root_.SheafOfModules.forget _).mapIso t)).toLinearEquiv

/-- **A trivialization of the line bundle over an open `U` gives a basis of `Γ(L, U)` with one
element** over `Γ(X, U)`. -/
def Situation.trivializationBasis (U : D.X.Opens)
    (t : D.L.over U ≅ SheafOfModules.unit (D.X.ringCatSheaf.over U)) :
    Module.Basis PUnit.{u + 1} Γ(D.X, U) Γ(D.L, U) :=
  (Module.Basis.singleton PUnit.{u + 1} Γ(D.X, U)).map (D.trivializationSectionsEquiv U t).symm

/-! ### The basis of charts -/

/-- The charts of the comparison: the affine opens `U ⊆ X` lying over an affine open of the base
on which the sections of the line bundle are free of rank one. -/
def Situation.chartOpens : Set D.X.Opens :=
  {U | IsAffineOpen U ∧ (∃ V : D.S.Opens, IsAffineOpen V ∧ U ≤ D.f ⁻¹ᵁ V) ∧
    Nonempty (Module.Basis PUnit.{u + 1} Γ(D.X, U) Γ(D.L, U))}

/-- **The charts form a basis of the topology of `X`.** Around a point of an open `W` choose an
affine open trivializing the line bundle and an affine open of the base containing the image of
the point; an affine open neighbourhood of the point inside both and inside `W` is a chart, the
trivialization restricting to it. -/
theorem Situation.isBasis_chartOpens : Opens.IsBasis D.chartOpens := by
  refine Opens.isBasis_iff_nbhd.2 fun {W x} hxW => ?_
  obtain ⟨U₀, hxU₀, ⟨t⟩⟩ := D.exists_trivializing_affineOpen x
  obtain ⟨V, hV, hxV, -⟩ :=
    Opens.isBasis_iff_nbhd.1 D.S.isBasis_affineOpens (show D.f x ∈ (⊤ : D.S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 D.X.isBasis_affineOpens
    (show x ∈ W ⊓ U₀.1 ⊓ D.f ⁻¹ᵁ V from ⟨⟨hxW, hxU₀⟩, hxV⟩)
  refine ⟨U, ⟨hU, ⟨V, hV, fun y hy => (hUW hy).2⟩, ⟨D.trivializationBasis U
    (Stacks.SheafOfModules.isoUnitOverOfHom D.L (homOfLE fun y hy => (hUW hy).1.2) t)⟩⟩,
    hxU, fun y hy => (hUW hy).1.1⟩

/-! ### The comparison on a chart -/

section Chart

variable {D} {U : D.X.Opens} {V : D.S.Opens} (e : U ≤ D.f ⁻¹ᵁ V)

include e in
/-- The inverse image in the total space of an open lying over `V` lies over `V`. -/
theorem Situation.preimage_le_preimage_comp :
    D.totalSpaceToBase ⁻¹ᵁ U ≤ (D.totalSpaceToBase ≫ D.f) ⁻¹ᵁ V :=
  fun _ hx => e hx

/-- The ring maps `Γ(S, V) ⟶ Γ(X, U) ⟶ Γ(𝕃, π^{-1}U)` compose to the structure map of the total
space over `V`. -/
theorem Situation.appLE_comp_app_totalSpaceToBase :
    D.f.appLE V U e ≫ D.totalSpaceToBase.app U =
      (D.totalSpaceToBase ≫ D.f).appLE V (D.totalSpaceToBase ⁻¹ᵁ U)
        (Situation.preimage_le_preimage_comp e) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

variable (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV in
/-- **On a chart the comparison is the restriction of forms along `Γ(X, U) ⟶ Γ(𝕃, π^{-1}U)`**:
the map of algebraic de Rham complexes `Ω^•_{Γ(X,U)/Γ(S,V)} ⟶ Ω^•_{Γ(𝕃,π^{-1}U)/Γ(S,V)}` that
the canonical map of de Rham complexes of the square of `π` induces is
`KaehlerDifferential.deRhamComplexMap` for the tower `Γ(S, V) ⟶ Γ(X, U) ⟶ Γ(𝕃, π^{-1}U)`. -/
theorem Situation.ringDeRhamAbSquareMap_eq :
    letI : Algebra Γ(D.S, V) Γ(D.X, U) := (D.f.appLE V U e).hom.toAlgebra
    letI : Algebra Γ(D.S, V) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      ((D.totalSpaceToBase ≫ D.f).appLE V _ (Situation.preimage_le_preimage_comp e)).hom.toAlgebra
    letI : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      (D.totalSpaceToBase.app U).hom.toAlgebra
    haveI : IsScalarTower Γ(D.S, V) Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (ConcreteCategory.congr_hom (Situation.appLE_comp_app_totalSpaceToBase e) r).symm
    ringDeRhamAbSquareMap D.totalSpaceToBase D.f (D.totalSpaceToBase ≫ D.f) (𝟙 D.S)
        hU (hU.preimage D.totalSpaceToBase) hV hV e (Situation.preimage_le_preimage_comp e)
        D.totalSpaceToBase_comp =
      ((forget₂ (ModuleCat.{u} Γ(D.S, V)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (KaehlerDifferential.deRhamComplexMap Γ(D.S, V) Γ(D.X, U)
          Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U)) := by
  let : Algebra Γ(D.S, V) Γ(D.X, U) := (D.f.appLE V U e).hom.toAlgebra
  let : Algebra Γ(D.S, V) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    ((D.totalSpaceToBase ≫ D.f).appLE V _ (Situation.preimage_le_preimage_comp e)).hom.toAlgebra
  let : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    (D.totalSpaceToBase.app U).hom.toAlgebra
  have : IsScalarTower Γ(D.S, V) Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (ConcreteCategory.congr_hom (Situation.appLE_comp_app_totalSpaceToBase e) r).symm
  ext n : 1
  refine ringDeRhamAb_hom_ext D.f e n fun b => ?_
  rw [ringDeRhamAbSquareMap_f_smul_ιMulti_d]
  exact (KaehlerDifferential.mapExteriorPower_smul_ιMulti_D Γ(D.S, V) Γ(D.X, U)
    Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) n b).symm

variable {R : CommRingCat.{u}} [Algebra ℚ R] (g : D.S ⟶ Spec R)

include e hU hV g in
/-- **On a chart the comparison is a quasi-isomorphism on sections**, over a base lying over a
`ℚ`-algebra: the sections over `U` of `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` are, up to the affine-open
comparison at both ends, the restriction of forms `Ω^•_{A/R} ⟶ Ω^•_{B/R}` for `A = Γ(X, U)`,
`B = Γ(𝕃, π^{-1}U)` and `R = Γ(S, V)`, and `B ≅ A[T]` as an `A`-algebra by the trivialization,
so the Poincaré lemma applies. -/
theorem Situation.quasiIso_sections_deRhamPushforward
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U) Γ(D.L, U)) :
    QuasiIso (((abelianSections.{u, u} D.X.carrier U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map D.deRhamPushforward) := by
  let : Algebra ℚ Γ(D.X, U) := Scheme.Hom.sectionsRatAlgebra (D.f ≫ g) U
  let : Algebra Γ(D.S, V) Γ(D.X, U) := (D.f.appLE V U e).hom.toAlgebra
  let : Algebra Γ(D.S, V) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    ((D.totalSpaceToBase ≫ D.f).appLE V _ (Situation.preimage_le_preimage_comp e)).hom.toAlgebra
  let : Algebra Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    (D.totalSpaceToBase.app U).hom.toAlgebra
  have : IsScalarTower Γ(D.S, V) Γ(D.X, U) Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (ConcreteCategory.congr_hom (Situation.appLE_comp_app_totalSpaceToBase e) r).symm
  let eT : Γ(D.X, U)[X] ≃ₐ[Γ(D.X, U)] Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) :=
    AlgEquiv.ofRingEquiv (f := D.polynomialSectionsRingEquiv ⟨U, hU⟩ b)
      fun r => D.polynomialSectionsRingEquiv_C ⟨U, hU⟩ b r
  have := PolynomialDeRham.quasiIso_deRhamComplexMap_of_algEquiv Γ(D.S, V) Γ(D.X, U)
    Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U) eT
  have hring := Situation.ringDeRhamAbSquareMap_eq e hU hV
  have hsq : ((abelianSections.{u, u} D.X.carrier U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map D.deRhamPushforward =
      (deRhamSectionsAbComplexIso D.f hU hV e).inv ≫
        ringDeRhamAbSquareMap D.totalSpaceToBase D.f (D.totalSpaceToBase ≫ D.f) (𝟙 D.S)
          hU (hU.preimage D.totalSpaceToBase) hV hV e (Situation.preimage_le_preimage_comp e)
          D.totalSpaceToBase_comp ≫
        (deRhamSectionsAbComplexIso (D.totalSpaceToBase ≫ D.f) (hU.preimage D.totalSpaceToBase)
          hV (Situation.preimage_le_preimage_comp e)).hom := by
    simp only [ringDeRhamAbSquareMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
    rfl
  rw [hsq, hring]
  have : QuasiIso (((forget₂ (ModuleCat.{u} Γ(D.S, V)) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (KaehlerDifferential.deRhamComplexMap Γ(D.S, V) Γ(D.X, U)
        Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U))) := inferInstance
  have h₁ := quasiIso_of_isIso (deRhamSectionsAbComplexIso D.f hU hV e).inv
  have h₃ := quasiIso_of_isIso (deRhamSectionsAbComplexIso (D.totalSpaceToBase ≫ D.f)
    (hU.preimage D.totalSpaceToBase) hV (Situation.preimage_le_preimage_comp e)).hom
  have h₂₃ := quasiIso_comp (hφ := this) (hφ' := h₃)
  exact quasiIso_comp (hφ := h₁) (hφ' := h₂₃)

end Chart

/-! ### The two conclusions -/

section Global

variable {R : CommRingCat.{u}} [Algebra ℚ R] (g : D.S ⟶ Spec R)

include g in
/-- **Stacks Project, Tag 0FUI, first assertion.** Let `f : X ⟶ S` be a morphism of schemes with
`S` lying over `Spec R` for a `ℚ`-algebra `R` — for instance `R = ℚ` — let `L` be an invertible
`𝒪_X`-module and let `π : 𝕃 ⟶ X` be its total space. Then the canonical map
`Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}` is a quasi-isomorphism. -/
@[stacks 0FUI "first assertion: `Ω^•_{X/S} ⟶ π_*Ω^•_{L/S}` is a quasi-isomorphism when `S`
lies over `Spec ℚ` (here over `Spec R` for any `ℚ`-algebra `R`)"]
theorem Situation.quasiIso_deRhamPushforward : QuasiIso D.deRhamPushforward :=
  Stacks.AbelianSheaves.quasiIso_of_forall_sections_quasiIso_nat D.deRhamPushforward
    D.isBasis_chartOpens fun _ ⟨hU, ⟨_, hV, e⟩, ⟨b⟩⟩ =>
      Situation.quasiIso_sections_deRhamPushforward e hU hV g b

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

include g in
/-- The comparison `Ω^•_{X/S} ⟶ π_*Ω^•_{𝕃/S}`, extended by zero to bounded-below complexes, is
inverted in `D⁺`. -/
theorem Situation.isIso_Q_map_deRhamAbelianPushforwardMapPlus :
    IsIso (DerivedCategory.Plus.Q.map
      (Scheme.Hom.deRhamAbelianPushforwardMapPlus D.totalSpaceToBase D.f
        (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp)) := by
  have := D.quasiIso_deRhamPushforward g
  have : QuasiIso (HomologicalComplex.extendMap D.deRhamPushforward
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
  have hq : QuasiIso (Scheme.Hom.deRhamAbelianPushforwardMapPlus D.totalSpaceToBase D.f
      (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp).hom := by
    change QuasiIso (HomologicalComplex.extendMap D.deRhamPushforward
      ComplexShape.embeddingUpNat ≫ _)
    have h₂ := quasiIso_of_isIso (HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} D.totalSpaceToBase.base)
      (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras (D.totalSpaceToBase ≫ D.f))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (D.totalSpaceToBase ≫ D.f))))
      ComplexShape.embeddingUpNat).hom
    exact quasiIso_comp (hφ := ‹QuasiIso (HomologicalComplex.extendMap D.deRhamPushforward
      ComplexShape.embeddingUpNat)›) (hφ' := h₂)
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
      (Scheme.Hom.deRhamAbelianPushforwardMapPlus D.totalSpaceToBase D.f
        (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp))) := by
    change IsIso (DerivedCategory.Q.map _)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hq
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

include g in
/-- **Stacks Project, Tag 0FUI, second assertion.** In the situation of
`Stacks.LineBundle.Situation.quasiIso_deRhamPushforward`, pullback along the projection
`π : 𝕃 ⟶ X` of the total space of the line bundle is an isomorphism
`H^i_{dR}(X/S) ≅ H^i_{dR}(𝕃/S)` in every degree `i`. -/
@[stacks 0FUI "second assertion: `H^*_dR(X/S) = H^*_dR(L/S)`, the pullback along `π` being an
isomorphism in every degree, when `S` lies over `Spec ℚ` (here over `Spec R` for any
`ℚ`-algebra `R`)"]
theorem Situation.isIso_deRhamCohomologyPullback (i : ℤ) :
    IsIso (Scheme.Hom.deRhamCohomologyPullback D.totalSpaceToBase D.f
      (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp i) :=
  D.isIso_deRhamCohomologyPullback_of_isIso_derivedComparison
    (D.isIso_Q_map_deRhamAbelianPushforwardMapPlus g) i

end Global

end Stacks.LineBundle

end
