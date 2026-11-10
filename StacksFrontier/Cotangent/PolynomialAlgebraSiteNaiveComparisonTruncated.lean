module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Cotangent.ConormalLowDegree
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteNaiveComparison

/-!
# Remark 08R7: `H₀`, `H₁` of `𝒥/𝒥²` vanish; the map `(J/J² → Ω_{P/A} ⊗_P B) → τ_{≥-1}L_{B/A}`

Let `A → B` be a ring map and work on the site `C_{B/A}` of [Stacks, Tag 08PR], with
`𝒥 = ker(𝒪 → B̲)` and `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`. The second half of Remark 08R7 asserts

* `H₀(C_{B/A}, 𝒥/𝒥²) = 0` and `H₁(C_{B/A}, 𝒥/𝒥²) = 0`, where `𝒥/𝒥² = Tor₀^𝒪(𝒥, B̲)`;
* hence `τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}`;
* hence, for every object `U = (P → B)` of `C_{B/A}`, a map
  `(J/J² → Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}` in `D(B)` (the display (08R9)), obtained from the
  canonical map of [Stacks, Tag 08Q6].

This file proves all three, in `D(B)`, at the site `C_{B/A}` itself. Here `H_n(C_{B/A}, ℱ)` is
`H^{-n}(Lπ_!ℱ)`, the homology of the site in the sense of [Stacks, Tag 08PS].

## Main results

* `CommAlgCat.isZero_polynomialSiteConormalHomology_zero` and
  `CommAlgCat.isZero_polynomialSiteConormalHomology_one`: **`H₀(C_{B/A}, 𝒥/𝒥²) = 0`** and
  **`H₁(C_{B/A}, 𝒥/𝒥²) = 0`**.
* `CommAlgCat.polynomialSiteTruncGEConormalComplexIso`:
  **`τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}`** in `D(B)`.
* `CommAlgCat.conormalComplexToTruncGECotangentComplex`: **the map (08R9)**
  `(J/J² → Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}` in `D(B)`, for every object `U = (P → B)`.
* `CommAlgCat.polynomialSiteDerivedLowerShriekCotangentLiftIso`: `Lπ_!(Ω) = L_{B/A}` in `D(B)`,
  at the site itself.

## Implementation notes

**`𝒥/𝒥²`.** As explained in `StacksFrontier/Cotangent/PolynomialAlgebraSiteConormalPresheaves.lean`,
the `B̲`-module the remark calls `𝒥/𝒥² = Tor₀^𝒪(𝒥, B̲)` is `𝒥 ⊗_𝒪 B̲`, with sections
`B ⊗_P J` over `(P → B)`; these are `J/J²` whenever `P → B` is surjective
(`Algebra.Extension.tensorKerEquivCotangent`). In particular the domain of the map (08R9) at a
surjective `U` is the naive complex `J/J² → Ω_{P/A} ⊗_P B`.

**The vanishing.** The source reads it off the spectral sequence of `𝒥 ⊗^L_𝒪 B̲`. Here it is read
on the standard resolution `P_•`, which computes `Lπ_!` by Tag 08PS: the terms of `P_•` surject
onto `B`, so `(𝒥 ⊗_𝒪 B̲)(P_•)` is the simplicial conormal module `n ↦ Jₙ/Jₙ²`
(`CommAlgCat.standardResolutionConormalIso`), whose Moore complex is acyclic in degrees `0` and
`1` by `Stacks.Cotangent.isLE_conormalComplex`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open scoped TensorProduct

universe u

/-! ### `B ⊗_P J = J/J²` for a surjection -/

namespace Algebra.Extension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (E : Algebra.Extension.{u} R S)

/-- The map `S ⊗_P J → J/J²`, `s ⊗ j ↦ s · [j]`, for an extension `P → S` with kernel `J`. -/
def tensorKerToCotangent : S ⊗[E.Ring] E.ker →ₗ[S] E.Cotangent :=
  (Cotangent.mk (P := E)).liftBaseChange S

/-- `tensorKerToCotangent` sends `s ⊗ j` to `s · [j]`. -/
@[simp]
theorem tensorKerToCotangent_tmul (s : S) (j : E.ker) :
    E.tensorKerToCotangent (s ⊗ₜ j) = s • Cotangent.mk j :=
  rfl

/-- The `P`-linear map `J/J² → S ⊗_P J`, `[j] ↦ 1 ⊗ j`, well defined because `J` acts by zero
on `S`. -/
def cotangentToTensorKerAux : E.ker.Cotangent →ₗ[E.Ring] S ⊗[E.Ring] E.ker :=
  Ideal.Cotangent.lift (TensorProduct.mk E.Ring S E.ker 1) (fun x y => by
    change (1 : S) ⊗ₜ[E.Ring] (x * y) = 0
    rw [show x * y = (x : E.Ring) • y from Subtype.ext rfl, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      show algebraMap E.Ring S x = 0 from x.2, TensorProduct.zero_tmul])

/-- The map `J/J² → S ⊗_P J`, `[j] ↦ 1 ⊗ j`. -/
def cotangentToTensorKer (c : E.Cotangent) : S ⊗[E.Ring] E.ker :=
  E.cotangentToTensorKerAux c.val

/-- `cotangentToTensorKer` is a left inverse of `tensorKerToCotangent`. -/
theorem cotangentToTensorKer_tensorKerToCotangent (t : S ⊗[E.Ring] E.ker) :
    E.cotangentToTensorKer (E.tensorKerToCotangent t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul s j =>
    rw [tensorKerToCotangent_tmul]
    change E.cotangentToTensorKerAux (s • Cotangent.mk j).val = _
    rw [Cotangent.val_smul, map_smul, Cotangent.val_mk]
    change E.σ s • Ideal.Cotangent.lift _ _ (Ideal.toCotangent _ j) = _
    rw [Ideal.Cotangent.lift_toCotangent]
    change E.σ s • ((1 : S) ⊗ₜ[E.Ring] j) = _
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, E.algebraMap_σ]
  | add x y hx hy =>
    change E.cotangentToTensorKerAux (E.tensorKerToCotangent (x + y)).val = x + y
    rw [map_add]
    change E.cotangentToTensorKerAux ((E.tensorKerToCotangent x).val +
      (E.tensorKerToCotangent y).val) = x + y
    rw [map_add]
    exact congrArg₂ (· + ·) hx hy

/-- **`S ⊗_P J = J/J²`** for an extension `P → S` with kernel `J`: the sheaf `𝒥 ⊗_𝒪 B̲` of
Remark 08R7 has sections `J/J²` at every surjective augmentation. -/
def tensorKerEquivCotangent : S ⊗[E.Ring] E.ker ≃ₗ[S] E.Cotangent :=
  LinearEquiv.ofBijective E.tensorKerToCotangent
    ⟨Function.LeftInverse.injective E.cotangentToTensorKer_tensorKerToCotangent, fun c => by
      obtain ⟨j, rfl⟩ := Cotangent.mk_surjective c
      exact ⟨(1 : S) ⊗ₜ j, by rw [tensorKerToCotangent_tmul, one_smul]⟩⟩

end Algebra.Extension

namespace CommAlgCat

open Stacks.CategoryHomology Stacks.Cotangent

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### `(𝒥 ⊗_𝒪 B̲)(P_•)` is the simplicial conormal module -/

/-- In degree `n`: `B ⊗_{Pₙ} Jₙ = Jₙ/Jₙ²`, the augmentation `Pₙ → B` being surjective. -/
def standardResolutionConormalIsoApp (n : SimplexCategoryᵒᵖ) :
    ((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
        polynomialSiteConormalPresheaf A B).obj n ≅
      (Stacks.Cotangent.conormalSimplicialModule.{u, u} A B).obj n :=
  (Algebra.Extension.tensorKerEquivCotangent
    (Stacks.Cotangent.conormalExtension.{u, u} A B n)).toModuleIso

/-- `standardResolutionConormalIsoApp` sends the class of `x ∈ Jₙ` in `B ⊗_{Pₙ} Jₙ` to its class
in `Jₙ/Jₙ²`. -/
theorem standardResolutionConormalIsoApp_hom_mk (n : SimplexCategoryᵒᵖ)
    (x : overIdeal ((polynomialSiteToOver A B).obj
      ((standardResolutionPolynomialSiteCosimplicialObject A B).op.obj n))) :
    (standardResolutionConormalIsoApp A B n).hom (overConormalMk _ x) =
      Algebra.Extension.Cotangent.mk (P := Stacks.Cotangent.conormalExtension.{u, u} A B n) x :=
  one_smul (B : Type u)
    (Algebra.Extension.Cotangent.mk (P := Stacks.Cotangent.conormalExtension.{u, u} A B n) x)

/-- **`(𝒥 ⊗_𝒪 B̲)(P_•) = 𝒥_•/𝒥_•²`** on the standard resolution: in degree `n` the augmentation
`Pₙ → B` is surjective and `B ⊗_{Pₙ} Jₙ = Jₙ/Jₙ²`. -/
def standardResolutionConormalIso :
    (standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
        polynomialSiteConormalPresheaf A B ≅
      Stacks.Cotangent.conormalSimplicialModule.{u, u} A B :=
  NatIso.ofComponents (standardResolutionConormalIsoApp A B)
    (fun {i j} f => by
      refine overConormal_hom_ext _ _ fun x => ?_
      change (standardResolutionConormalIsoApp A B j).hom
          ((((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
            polynomialSiteConormalPresheaf A B).map f) (overConormalMk _ x)) =
        ((Stacks.Cotangent.conormalSimplicialModule.{u, u} A B).map f)
          ((standardResolutionConormalIsoApp A B i).hom (overConormalMk _ x))
      have h1 : (((standardResolutionPolynomialSiteCosimplicialObject A B).op ⋙
          polynomialSiteConormalPresheaf A B).map f) (overConormalMk _ x) =
            overConormalMk _ ⟨_, map_mem_overIdeal _ x.2⟩ :=
        overConormalPush_mk _ x
      rw [h1, standardResolutionConormalIsoApp_hom_mk, standardResolutionConormalIsoApp_hom_mk]
      exact (Stacks.Cotangent.conormalSimplicialModule_map_mk.{u, u} A B f x _ rfl).symm)

/-- The sheaf `𝒥/𝒥² = 𝒥 ⊗_𝒪 B̲` on `C_{B/A}`, as a sheaf of `B`-modules at the coefficient
universe of the site. -/
abbrev polynomialSiteConormalSheaf :
    (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)) :=
  polynomialSiteConormalPresheaf A B ⋙ liftModuleFunctor (B : Type u)

/-- `Lπ_!(𝒥/𝒥²)` in `D(B)`. -/
abbrev polynomialSiteDerivedLowerShriekConormal :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))).obj
    (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (polynomialSiteConormalSheaf A B)))

/-- `Lπ_!(𝒥/𝒥²)` is the conormal complex of the standard resolution, lifted to the coefficient
universe of the site. -/
def polynomialSiteDerivedLowerShriekConormalIso :
    polynomialSiteDerivedLowerShriekConormal A B ≅
      DerivedCategory.Q.obj (((liftModuleFunctor (B : Type u)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Stacks.Cotangent.conormalComplex.{u, u} A B)) :=
  polynomialSiteLiftDerivedLowerShriekIso A B _ ≪≫
    DerivedCategory.Q.mapIso (((liftModuleFunctor (B : Type u)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
        (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor _).mapIso
          ((alternatingFaceMapComplex _).mapIso (standardResolutionConormalIso A B))))

/-- **`Lπ_!(𝒥/𝒥²)` lies in `D^{≤ -2}(B)`**: its cohomology vanishes in every degree `> -2`. -/
theorem isLE_polynomialSiteDerivedLowerShriekConormal :
    (polynomialSiteDerivedLowerShriekConormal A B).IsLE (-2) := by
  have : CochainComplex.IsLE (((liftModuleFunctor (B : Type u)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (Stacks.Cotangent.conormalComplex.{u, u} A B)) (-2) := by
    have hK := Stacks.Cotangent.isLE_conormalComplex.{u, u} A B
    rw [CochainComplex.isLE_iff] at hK ⊢
    intro i hi
    have hKi := hK i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at hKi ⊢
    exact (Functor.map_isZero _ hKi).of_iso
      (Stacks.mapHomologicalComplexHomologyIso _ _ i)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (polynomialSiteDerivedLowerShriekConormalIso A B).symm (-2)

/-- **`H₀(C_{B/A}, 𝒥/𝒥²) = 0`**, Remark 08R7, at the site `C_{B/A}` itself:
`H⁰(Lπ_!(𝒥/𝒥²)) = 0` for `𝒥/𝒥² = 𝒥 ⊗_𝒪 B̲ = Tor₀^𝒪(𝒥, B̲)`. -/
@[stacks 08R7 "H_0(C_{B/A}, 𝒥/𝒥²) = 0, read as H⁰(Lπ_!(𝒥/𝒥²)) = 0 in D(B) at the site \
  C_{B/A} of Tag 08PR itself, for the B̲-module 𝒥/𝒥² = Tor₀^𝒪(𝒥, B̲) = 𝒥 ⊗_𝒪 B̲"]
theorem isZero_polynomialSiteConormalHomology_zero :
    IsZero ((DerivedCategory.homologyFunctor _ 0).obj
      (polynomialSiteDerivedLowerShriekConormal A B)) :=
  DerivedCategory.isZero_of_isLE _ (-2) 0 (by norm_num)
    (hX := isLE_polynomialSiteDerivedLowerShriekConormal A B)

/-- **`H₁(C_{B/A}, 𝒥/𝒥²) = 0`**, Remark 08R7, at the site `C_{B/A}` itself:
`H⁻¹(Lπ_!(𝒥/𝒥²)) = 0` for `𝒥/𝒥² = 𝒥 ⊗_𝒪 B̲ = Tor₀^𝒪(𝒥, B̲)`. -/
@[stacks 08R7 "H_1(C_{B/A}, 𝒥/𝒥²) = 0, read as H⁻¹(Lπ_!(𝒥/𝒥²)) = 0 in D(B) at the site \
  C_{B/A} of Tag 08PR itself, for the B̲-module 𝒥/𝒥² = Tor₀^𝒪(𝒥, B̲) = 𝒥 ⊗_𝒪 B̲"]
theorem isZero_polynomialSiteConormalHomology_one :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
      (polynomialSiteDerivedLowerShriekConormal A B)) :=
  DerivedCategory.isZero_of_isLE _ (-2) (-1) (by norm_num)
    (hX := isLE_polynomialSiteDerivedLowerShriekConormal A B)

/-! ### `τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}` and the map (08R9) -/

/-- `L_{B/A}`, the cotangent complex of Tag 08PN, as an object of `D(B)` at the coefficient
universe of the site. -/
abbrev cotangentComplexLift : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  DerivedCategory.Q.obj (((liftModuleFunctor (B : Type u)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B))

/-- `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` on `C_{B/A}`, as a sheaf of `B`-modules at the coefficient universe of
the site. -/
abbrev polynomialSiteCotangentSheafLift :
    (polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)) :=
  polynomialCotangentModulePresheaf A B ⋙ liftModuleFunctor (B : Type u)

/-- **`Lπ_!(Ω) = L_{B/A}` in `D(B)`**, Tag 08PU at the site `C_{B/A}` itself. -/
def polynomialSiteDerivedLowerShriekCotangentLiftIso :
    (polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (polynomialSiteCotangentSheafLift A B))) ≅
      cotangentComplexLift A B :=
  polynomialSiteModuleDerivedLowerShriekIso A B _ _ ≪≫
    DerivedCategory.Q.mapIso (polynomialSiteCotangentMooreComplexIsoOf A B _)

/-- The differential `d : 𝒥/𝒥² → Ω` at the coefficient universe of the site. -/
abbrev polynomialSiteConormalSheafToCotangent :
    polynomialSiteConormalSheaf A B ⟶ polynomialSiteCotangentSheafLift A B :=
  Functor.whiskerRight (polynomialSiteConormalToCotangent A B) (liftModuleFunctor (B : Type u))

/-- **The two-term complex `𝒥/𝒥² → Ω`** of sheaves of `B`-modules on `C_{B/A}`, in degrees
`-1, 0`. -/
abbrev polynomialSiteConormalComplex :
    CochainComplex ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ℤ :=
  CochainComplex.doubleNegOneZero (polynomialSiteConormalSheafToCotangent A B)

/-- The inclusion `Ω → (𝒥/𝒥² → Ω)` becomes an isomorphism after `Lπ_!` and `τ_{≥ -1}`, the third
vertex of its triangle being `Lπ_!(𝒥/𝒥²)[1]`, which lies in `D^{≤ -3}(B)`. -/
instance isIso_truncGE_polynomialSiteDerivedLowerShriek_map_inr :
    IsIso ((DerivedCategory.TStructure.t.truncGE (-1)).map
      ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))).map
        (DerivedCategory.Q.map (CochainComplex.mappingCone.inr
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            (polynomialSiteConormalSheafToCotangent A B)))))) := by
  let L := polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))
  let T := L.mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      (polynomialSiteConormalSheafToCotangent A B))))
  exact DerivedCategory.TStructure.t.isIso₂_truncGE_map_of_isLE T
    (L.map_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _))
    (-2) (-1) (by norm_num) (isLE_polynomialSiteDerivedLowerShriekConormal A B)

/-- **`τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}` in `D(B)`**, Remark 08R7, at the site
`C_{B/A}` itself, for the two-term complex `𝒥/𝒥² → Ω` in degrees `-1, 0`. -/
@[stacks 08R7 "τ_{≥-1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥-1} L_{B/A} in D(B), at the site C_{B/A} of \
  Tag 08PR itself, for the two-term complex 𝒥/𝒥² → Ω of B̲-modules in degrees -1, 0, \
  𝒥/𝒥² = Tor₀^𝒪(𝒥, B̲) = 𝒥 ⊗_𝒪 B̲, the identification being induced by Ω → (𝒥/𝒥² → Ω) and \
  Tag 08PU"]
def polynomialSiteTruncGEConormalComplexIso :
    (DerivedCategory.TStructure.t.truncGE (-1)).obj
        ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))).obj
          (DerivedCategory.Q.obj (polynomialSiteConormalComplex A B))) ≅
      (DerivedCategory.TStructure.t.truncGE (-1)).obj (cotangentComplexLift A B) :=
  (DerivedCategory.TStructure.t.truncGE (-1)).mapIso
      ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))).mapIso
        (DerivedCategory.Q.mapIso (CochainComplex.doubleIsoMappingConeSingle _))) ≪≫
    (asIso ((DerivedCategory.TStructure.t.truncGE (-1)).map
      ((polynomialSiteModuleDerivedLowerShriek A B (ULift.{u + 1} (B : Type u))).map
        (DerivedCategory.Q.map (CochainComplex.mappingCone.inr
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            (polynomialSiteConormalSheafToCotangent A B))))))).symm ≪≫
    (DerivedCategory.TStructure.t.truncGE (-1)).mapIso
      (polynomialSiteDerivedLowerShriekCotangentLiftIso A B)

/-- **The map (08R9) of Remark 08R7**: for an object `U = (P → B)` of `C_{B/A}`, with
`J = ker(P → B)`, the map `(J/J² → Ω_{P/A} ⊗_P B) ⟶ τ_{≥ -1} L_{B/A}` in `D(B)`. Its domain is the
value at `U` of the two-term complex `𝒥/𝒥² → Ω`, whose degree `-1` term is `B ⊗_P J`, which is
`J/J²` whenever `P → B` is surjective (`Algebra.Extension.tensorKerEquivCotangent`). The map is
the canonical map `K(U) ⟶ Lπ_!(K)` of Tag 08Q6 for `K = (𝒥/𝒥² → Ω)`, followed by the truncation
and by `τ_{≥ -1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥ -1} L_{B/A}`. -/
@[stacks 08R7 "the map (08R9): (J/J² → Ω_{P/A} ⊗_P B) → τ_{≥-1} L_{B/A} in D(B) for every \
  object U = (P → B) of C_{B/A}, the degree -1 term being the sections B ⊗_P J of \
  𝒥/𝒥² = 𝒥 ⊗_𝒪 B̲, which are J/J² for surjective P → B, as the canonical map of Tag 08Q6 \
  followed by τ_{≥-1} Lπ_!(𝒥/𝒥² → Ω) = τ_{≥-1} L_{B/A}"]
def conormalComplexToTruncGECotangentComplex (U : polynomialSite A B) :
    DerivedCategory.Q.obj (CochainComplex.doubleNegOneZero
        ((liftModuleFunctor (B : Type u)).map
          ((polynomialSiteConormalToCotangent A B).app (op U)))) ⟶
      (DerivedCategory.TStructure.t.truncGE (-1)).obj (cotangentComplexLift A B) :=
  DerivedCategory.Q.map (CochainComplex.mapDoubleNegOneZeroIso
      (polynomialSiteConormalSheafToCotangent A B)
      ((evaluation (polynomialSite A B)ᵒᵖ
        (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).obj (op U))).inv ≫
    (evaluationToTotalDerivedColimit' (polynomialSite A B)
      (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) U).app
        (polynomialSiteConormalComplex A B) ≫
    (DerivedCategory.TStructure.t.truncGEπ (-1)).app _ ≫
    (polynomialSiteTruncGEConormalComplexIso A B).hom

end CommAlgCat

end
