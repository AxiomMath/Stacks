module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModelAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.VanishingAndSupport
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.NormalizedClosedPoint
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension
import all StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings

/-!
# Dualizing complexes normalized at the closed points

Let `X` be a Noetherian scheme of dimension `n` and `K` a dualizing complex on `X` whose derived
stalk at every closed point is a normalized dualizing complex, i.e. whose associated dimension
function `δ` of [Stacks, Tag 0AWF] vanishes at the closed points. Then `δ(x) = dim(closure {x})`
for every `x`, so the derived stalk of `K` at `x`, shifted by the dimension of the closure of `x`,
is a normalized dualizing complex over `𝒪_{X,x}`: `K` has the local description
`Stacks.Duality.HasNormalizedStalks` from which [Stacks, Tag 0AWN] is read off.

This is the first paragraph of the proof of [Stacks, Tag 0AWN]: "every closed subscheme of `X`
contains a closed point `x` [...] and `δ_X(x) = 0`. Hence `δ_X(ξ) = dim(closure {ξ})` for any
point `ξ ∈ X`."

## Main results

* `Stacks.Duality.stalkLinearEquivSchemeStalk` — the two module structures on the stalk of a
  sheaf of modules over the local ring agree.
* `Stacks.Duality.standardHomologyDerivedStalkIso` — the cohomology of the derived stalk of a
  complex is the stalk of its cohomology.
* `Stacks.Duality.hasNormalizedStalks_of_associatedShiftFunction_eq_zero` — the local
  description `Stacks.Duality.HasNormalizedStalks`.
* `Stacks.Duality.dim_add_dim_eq_iff_of_associatedShiftFunction_eq_zero` — the points where
  `dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)` are those on a component of dimension `dim(X)`.

## References

* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w w' u

namespace Stacks.Duality

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Stalks of cohomology sheaves -/

/-- The stalk of a sheaf of modules on a scheme, with the module structure over `𝒪_{X,x}` of
`Stacks.Duality.moduleStalkAtPoint`, is the value of `Stacks.Duality.schemeStalkModuleFunctor`:
the underlying groups are the same stalk, and both actions are the action of sections on germs. -/
def stalkLinearEquivSchemeStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    moduleStalkAtPoint F x ≃ₗ[X.presheaf.stalk x] (schemeStalkModuleFunctor x).obj F where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by
    obtain ⟨V, hV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    obtain ⟨W, hW, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (C := AddCommGrpCat.{u}) F.val.presheaf m
    have ea : X.presheaf.germ V x hV a = X.presheaf.germ (V ⊓ W) x ⟨hV, hW⟩
        (X.presheaf.map (homOfLE inf_le_left).op a) :=
      (X.presheaf.germ_res_apply _ _ _ _).symm
    have en : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf W x hW n =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf (V ⊓ W) x ⟨hV, hW⟩
          (F.val.presheaf.map (homOfLE inf_le_right).op n) :=
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    rw [ea, en, RingHom.id_apply]
    exact (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul
      X.toRingedSpace F.val x (V ⊓ W) ⟨hV, hW⟩ (X.presheaf.map (homOfLE inf_le_left).op a)
      (F.val.presheaf.map (homOfLE inf_le_right).op n)).symm.trans
      (schemeStalkModuleFunctor_germ_smul x F (V ⊓ W) ⟨hV, hW⟩
        (X.presheaf.map (homOfLE inf_le_left).op a)
        (F.val.presheaf.map (homOfLE inf_le_right).op n))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The cohomology of the derived stalk is the stalk of the cohomology**: the stalk functor is
exact, so it commutes with the cohomology of complexes. -/
def standardHomologyDerivedStalkIso {X : Scheme.{u}} (x : X) (E : CochainComplex X.Modules ℤ)
    (i : ℤ) :
    standardHomology (derivedStalkOfComplex x E) i ≅
      (schemeStalkModuleFunctor x).obj (E.homology i) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (X.presheaf.stalk x)) i).app _ ≪≫
    (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (schemeStalkModuleFunctor x) (ComplexShape.up ℤ) i).app E

/-! ### The local description of a dualizing complex normalized at the closed points -/

section

variable {X : Scheme.{u}} [IsNoetherian X] [HasDerivedCategory.{w} X.Modules]
  {K : DerivedCategory X.Modules}

/-- The associated dimension function of a dualizing complex normalized at the closed points
vanishes at the closed points. -/
theorem exists_dimensionFunction_of_associatedShiftFunction_eq_zero (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    ∃ d : TopologicalSpace.DimensionFunction X, (∀ x, d x = associatedShiftFunction K x) ∧
      ∀ x : X, IsClosed ({x} : Set X) → d x = 0 := by
  obtain ⟨-, -, d, hd⟩ := isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK
  exact ⟨d, hd, fun x hx => (hd x).trans (h0 x hx)⟩

/-- **A dualizing complex normalized at the closed points has the local description of
[Stacks, Tag 0AWN].** Let `X` be a Noetherian scheme of dimension `n` and `K` a dualizing complex
whose associated dimension function vanishes at the closed points. Then at every point `x` the
derived stalk of `K`, shifted by `dim(closure {x})`, is a normalized dualizing complex over
`𝒪_{X,x}`, and `dim(closure {x}) + dim(𝒪_{X,x}) ≤ n`. -/
theorem hasNormalizedStalks_of_associatedShiftFunction_eq_zero (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) (n : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) : HasNormalizedStalks K n := by
  obtain ⟨-, hnorm, -⟩ := isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK
  obtain ⟨d, hd, hd0⟩ := exists_dimensionFunction_of_associatedShiftFunction_eq_zero hK h0
  refine ⟨hn, hK, fun x => ?_⟩
  obtain ⟨hδ0, hcl⟩ := AlgebraicGeometry.topologicalKrullDim_closure_eq_of_dimensionFunction d hd0 x
  rw [hd] at hδ0 hcl
  set δ := associatedShiftFunction K x
  let E := DerivedCategory.Q.objPreimage K
  have hE : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  -- the dimension of the local ring is the coheight, which is finite
  have hcoh : (Order.coheight x : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← hn, Stacks.ResolutionOfSurfaces.topologicalKrullDim_eq_krullDim]
    exact Order.coheight_le_krullDim x
  have hcoh' : Order.coheight x ≤ (n : ℕ∞) := by exact_mod_cast hcoh
  obtain ⟨h, hh⟩ : ∃ h : ℕ, Order.coheight x = h :=
    ⟨(Order.coheight x).toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) hcoh')).symm⟩
  have hsum := Order.height_add_coheight_le_krullDim x
  rw [← Stacks.ResolutionOfSurfaces.topologicalKrullDim_eq_krullDim, hn,
    ← AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height, hcl, hh] at hsum
  refine ⟨(DerivedCategory.Q.obj (((schemeStalkModuleFunctor x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E))⟦-δ⟧, δ.toNat, h, (hnorm x E ⟨hE⟩ δ).mpr rfl, hcl,
    by rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hh]; rfl,
    by exact_mod_cast hsum, fun i => ⟨?_⟩⟩
  refine stalkLinearEquivSchemeStalk _ x ≪≫ₗ
    ((schemeStalkModuleFunctor x).mapIso
      ((DerivedCategory.homologyFunctor X.Modules i).mapIso hE.symm ≪≫
        (DerivedCategory.homologyFunctorFactors X.Modules i).app E)).toLinearEquiv ≪≫ₗ
    (standardHomologyDerivedStalkIso x E i).symm.toLinearEquiv ≪≫ₗ
    (((@DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) _ _
      (HasDerivedCategory.standard _) 0).shiftIso (-δ) (i + (δ.toNat : ℤ)) i
        (by omega)).app _).symm.toLinearEquiv

/-- **The points where `dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)`.** For a dualizing complex
normalized at the closed points of a Noetherian scheme of dimension `n`, these are exactly the
points lying on an irreducible component of dimension `n`. -/
theorem dim_add_dim_eq_iff_of_associatedShiftFunction_eq_zero (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) (n : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) + ringKrullDim (X.presheaf.stalk x) =
        (n : WithBot ℕ∞) ↔
      x ∈ ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = (n : WithBot ℕ∞)} := by
  obtain ⟨d, -, hd0⟩ := exists_dimensionFunction_of_associatedShiftFunction_eq_zero hK h0
  exact AlgebraicGeometry.dim_closure_add_dim_stalk_eq_iff_of_dimensionFunction d hd0 n hn x

/-! ### The conclusions of [Stacks, Tag 0AWN] in the dimension convention of `ω_X` -/

/-- The dimension of `X` as a natural number, in the convention of
`Stacks.Duality.relativeDualizingModule`: `dim(X)` when `X` is nonempty, `0` on the empty
scheme. -/
abbrev natDim (X : Scheme.{u}) : ℕ := ENat.toNat ((topologicalKrullDim X).getD 0)

omit [AlgebraicGeometry.IsNoetherian X] [HasDerivedCategory.{w} X.Modules] in
/-- On a nonempty scheme whose dimension is a natural number, `natDim` is that number. -/
theorem topologicalKrullDim_eq_natDim {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    topologicalKrullDim X = (natDim X : WithBot ℕ∞) := by
  rw [natDim, hn]
  rfl

omit [AlgebraicGeometry.IsNoetherian X] [HasDerivedCategory.{w} X.Modules] in
/-- Every sheaf of modules on the empty scheme is zero. -/
theorem isZero_of_isEmpty [IsEmpty X] (F : X.Modules) : IsZero F :=
  Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty F
    (Set.eq_empty_of_isEmpty _)

/-- On a nonempty Noetherian scheme a dualizing complex normalized at the closed points lives
over a scheme of finite dimension `natDim X`, and it has the local description of
[Stacks, Tag 0AWN] there. -/
theorem hasNormalizedStalks_natDim (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) [Nonempty X] :
    topologicalKrullDim X = (natDim X : WithBot ℕ∞) ∧ HasNormalizedStalks K (natDim X) := by
  obtain ⟨d, -, hd0⟩ := exists_dimensionFunction_of_associatedShiftFunction_eq_zero hK h0
  obtain ⟨n, hn⟩ := AlgebraicGeometry.exists_topologicalKrullDim_eq_of_dimensionFunction d hd0
  have hn' := topologicalKrullDim_eq_natDim hn
  exact ⟨hn', hasNormalizedStalks_of_associatedShiftFunction_eq_zero hK h0 _ hn'⟩

/-- **Vanishing range** ([Stacks, Tag 0AWN] (1)): a dualizing complex normalized at the closed
points of a Noetherian scheme has cohomology only in degrees `-dim(X), …, 0`. -/
theorem mem_Icc_of_not_isZero_homology_of_associatedShiftFunction_eq_zero
    (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) (i : ℤ)
    (hi : ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    i ∈ Set.Icc (-(natDim X : ℤ)) 0 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact absurd (isZero_of_isEmpty _) hi
  · exact mem_Icc_of_not_isZero_homology (hasNormalizedStalks_natDim hK h0).2 i hi

/-- **Dimension of the supports** ([Stacks, Tag 0AWN] (2)): the support of `H^i` has dimension
at most `-i`; for `i > 0` it is empty. -/
theorem topologicalKrullDim_supp_homology_le_of_associatedShiftFunction_eq_zero
    (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) (i : ℤ) :
    topologicalKrullDim (_root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) ≤
      if i ≤ 0 then (((-i).toNat : ℕ) : WithBot ℕ∞) else ⊥ := by
  by_cases hzero : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)
  · have hsupp : _root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj K) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have hnt : Nontrivial (moduleStalkAtPoint
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) x) :=
        (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mp hx
      have hsub : Subsingleton (moduleStalkAtPoint
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) x) :=
        (stalkLinearEquivSchemeStalk _ x).toEquiv.subsingleton_congr.mpr
          (ModuleCat.isZero_iff_subsingleton.mp
            ((schemeStalkModuleFunctor x).map_isZero hzero))
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
    rw [hsupp]
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds ((∅ : Set X))) :=
      ⟨fun Z => by obtain ⟨z, -⟩ := Z.isIrreducible.nonempty; exact z.2.elim⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  · have hmem := mem_Icc_of_not_isZero_homology_of_associatedShiftFunction_eq_zero hK h0 i hzero
    have hX : Nonempty X := not_isEmpty_iff.mp fun _ => hzero (isZero_of_isEmpty _)
    rw [ite_eq_left hmem.2]
    exact topologicalKrullDim_supp_homology_le (hasNormalizedStalks_natDim hK h0).2 i

/-- **The first cohomology sheaf** ([Stacks, Tag 0AWN] (3), (4)): `H^{-dim(X)}` is coherent, has
property `(S₂)`, and its support is the union of the irreducible components of dimension
`dim(X)`. -/
theorem homology_natDim_of_associatedShiftFunction_eq_zero (hK : IsDualizingComplex K)
    (h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0) :
    ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K).IsCoherent ∧
      SheafHasPropertySk X ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K)
        2 ∧
      _root_.SheafOfModules.supp
          ((DerivedCategory.homologyFunctor X.Modules (-(natDim X : ℤ))).obj K) =
        ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = topologicalKrullDim X} := by
  refine ⟨isCoherent_homology_of_isDualizingComplex hK _, ?_⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun x => isEmptyElim x, Set.ext fun x => isEmptyElim x⟩
  · obtain ⟨hn, hloc⟩ := hasNormalizedStalks_natDim hK h0
    refine ⟨sheafHasPropertySk_two_homology_neg hloc, ?_⟩
    rw [hn]
    exact supp_homology_neg_eq_topDimensionalComponents hloc
      (dim_add_dim_eq_iff_of_associatedShiftFunction_eq_zero hK h0 _ hn)

end

/-! ### Normalization at closed points from upper shriek chart models -/

/-- A closed point of a scheme lying in an affine open corresponds to a maximal ideal of the ring
of sections. -/
theorem isMaximal_primeIdealOf_of_isClosed {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (hcl : IsClosed ({x} : Set X)) :
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal := by
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  have heq : (hU.fromSpec : Spec Γ(X, U) → X) ⁻¹' {x} = {hU.primeIdealOf ⟨x, hx⟩} := by
    ext q
    change hU.fromSpec q = x ↔ q = hU.primeIdealOf ⟨x, hx⟩
    refine ⟨fun h => hU.fromSpec.isOpenEmbedding.injective
      (by rw [h, hU.fromSpec_primeIdealOf]), ?_⟩
    rintro rfl
    exact hU.fromSpec_primeIdealOf _
  have := hcl.preimage hU.fromSpec.continuous
  rwa [heq] at this

/-- Shifting by `-0` does not change whether a complex is a normalized dualizing complex. -/
private theorem isNormalizedDualizingComplex_shift_neg_zero_iff {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (C : DerivedCategory (ModuleCat.{u} R)) :
    Dualizing.IsNormalizedDualizingComplex.{u, u} (C⟦-(0 : ℤ)⟧) ↔
      Dualizing.IsNormalizedDualizingComplex.{u, u} C :=
  Dualizing.isNormalizedDualizingComplex_congr.{u, u}
    ((shiftFunctorZero' (DerivedCategory (ModuleCat.{u} R)) (-(0 : ℤ)) (by simp)).app _)

/-- **A complex modelled on an affine chart by the upper shriek of a normalized dualizing complex
is normalized at the closed points over the closed point.** Let `U ⊆ X` be affine, `R` a
Noetherian local ring with a ring map `φ : R → Γ(X, U)` and normalized dualizing complex `ω`, and
suppose `K|_U` is the associated sheaf of `φ^!ω` for a polynomial presentation of `φ`. At a closed
point `x ∈ U` whose prime lies over the maximal ideal of `R`, the associated dimension function
of `K` vanishes. This is [Stacks, Tag 0E9N] read through [Stacks, Tag 0AWF]. -/
theorem associatedShiftFunction_eq_zero_of_isTildeModelOn_upperShriekFunctor {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    {U : X.Opens} (hU : IsAffineOpen U) {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {φ : R →+* Γ(X, U)} (p : Dualizing.PolynomialPresentation φ)
    (ω : DerivedCategory (ModuleCat.{u} R))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel K U hU (p.upperShriekFunctor.{u, u}.obj ω)) {x : X}
    (hx : x ∈ U)
    (hcl : IsClosed ({x} : Set X))
    (hlies : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.comap φ = IsLocalRing.maximalIdeal R) :
    associatedShiftFunction K x = 0 := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hdual := Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p ω hω.1
  rw [associatedShiftFunction_eq_dualizingDimension hU _ ⟨hdual, hmodel⟩ x hx]
  have := isMaximal_primeIdealOf_of_isClosed hU hx hcl
  have hnorm := p.upperShriekFunctor_localization_isNormalizedDualizingComplex
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal hlies ω hω
  exact ((Dualizing.dualizingDimension_eq_iff.{u, u} _ hdual (hU.primeIdealOf ⟨x, hx⟩) 0).mp
    ((isNormalizedDualizingComplex_shift_neg_zero_iff _).mpr hnorm)).symm

/-- **Vanishing of the dimension function is normalization of the stalk.** For a dualizing
complex `K`, the associated dimension function vanishes at `x` exactly when the derived stalk at
`x` of every complex representing `K` is a normalized dualizing complex over `𝒪_{X,x}`. -/
theorem associatedShiftFunction_eq_zero_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) :
    associatedShiftFunction K x = 0 ↔
      ∀ E : CochainComplex X.Modules ℤ, Nonempty (DerivedCategory.Q.obj E ≅ K) →
        Dualizing.IsNormalizedDualizingComplex.{u, u} (derivedStalkOfComplex x E) := by
  obtain ⟨-, hnorm, -⟩ := isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK
  refine ⟨fun h E hE => (isNormalizedDualizingComplex_shift_neg_zero_iff _).mp
    ((hnorm x E hE 0).mpr h.symm), fun h => ?_⟩
  have hE : Nonempty (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K) ≅ K) :=
    ⟨DerivedCategory.Q.objObjPreimageIso K⟩
  exact ((hnorm x _ hE 0).mp
    ((isNormalizedDualizingComplex_shift_neg_zero_iff _).mpr (h _ hE))).symm

/-- **Upper shriek charts preserve the dimension function at closed points.** If `L` has upper
shriek charts relative to a dualizing complex `K` along `f : X ⟶ Y`, then at a closed point `x`
the dimension functions of `L` at `x` and of `K` at `f x` agree. This is the computation of the
proof of [Stacks, Tag 0AWL], read on dimension functions. -/
theorem associatedShiftFunction_eq_of_hasUpperShriekCharts {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} Y.Modules]
    {K : DerivedCategory Y.Modules} {L : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (hchart : HasUpperShriekCharts f K L) {x : X}
    (hx : IsClosed ({x} : Set X)) :
    associatedShiftFunction L x = associatedShiftFunction K (f x) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, hmodel⟩ := exists_isTildeModelOnAnyModel_of_hasDualizingModelOn (hK V hV)
  obtain ⟨p, hp⟩ := hchart U hU V hV hUV ω hmodel
  have hdual := Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p ω hω
  rw [associatedShiftFunction_eq_dualizingDimension hU _ ⟨hdual, hp⟩ x hxU,
    associatedShiftFunction_eq_dualizingDimension hV ω ⟨hω, hmodel⟩ (f x) hxV]
  have := isMaximal_primeIdealOf_of_isClosed hU hxU hx
  have hlies := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  exact p.dualizingDimension_upperShriekFunctor_of_isMaximal _ _ hlies ω hω

/-! ### Depth at a closed point -/

/-- **Depth at a closed point from the cohomology of the stalk.** Let `K` have the local
description `Stacks.Duality.HasNormalizedStalks` and let `x` be a closed point. Then one of the
stalks `H^i(K)_x, …, H^0(K)_x` is nonzero exactly when `depth(𝒪_{X,x}) ≤ -i`. At a closed point
the stalk itself is a normalized dualizing complex, and [Stacks, Tag 0AWR] identifies the depth
with the first nonvanishing degree. -/
theorem exists_nontrivial_stalk_homology_iff_depth_le {X : Scheme.{u}} [IsNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules} {n : ℕ}
    (hloc : HasNormalizedStalks K n) {x : X} (hx : IsClosed ({x} : Set X)) (i : ℤ) :
    (∃ j : ℤ, i ≤ j ∧ j ≤ 0 ∧
        Nontrivial (moduleStalkAtPoint ((DerivedCategory.homologyFunctor X.Modules j).obj K) x)) ↔
      i ≤ 0 ∧ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≤ ((-i).toNat : ℕ∞) := by
  obtain ⟨L, e, h, hL, he, -, -, hiso⟩ := hloc.exists_normalized x
  have he0 : e = 0 := by
    rw [hx.closure_eq] at he
    have : Nonempty ({x} : Set X) := ⟨⟨x, rfl⟩⟩
    rw [topologicalKrullDim_eq_zero_of_subsingleton] at he
    exact_mod_cast he.symm
  subst he0
  obtain ⟨δ, hleast, hdepth⟩ := Dualizing.depth_eq_least_nonzero_negative_ext.{u, u}
    (M := X.presheaf.stalk x) L hL inferInstance
  simp only [Dualizing.ext_nontrivial_iff] at hleast
  have hnt : ∀ j : ℤ, Nontrivial (moduleStalkAtPoint
      ((DerivedCategory.homologyFunctor X.Modules j).obj K) x) ↔
      Nontrivial (standardHomology L j) := fun j => by
    obtain ⟨φ⟩ := hiso j
    rw [Nat.cast_zero, add_zero] at φ
    exact φ.toEquiv.nontrivial_congr
  rw [hdepth]
  constructor
  · rintro ⟨j, hij, hj0, hj⟩
    refine ⟨hij.trans hj0, ?_⟩
    have hm : (-j).toNat ∈ {i : ℕ | Nontrivial
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) (-(i : ℤ))).obj
          L)} := by
      change Nontrivial (standardHomology L _)
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
      exact (hnt j).mp hj
    have := hleast.2 hm
    exact_mod_cast (show δ ≤ (-i).toNat by omega)
  · rintro ⟨hi, hδ⟩
    have hδ' : δ ≤ (-i).toNat := by exact_mod_cast hδ
    exact ⟨-(δ : ℤ), by omega, by omega, (hnt _).mpr hleast.1⟩

end Stacks.Duality
