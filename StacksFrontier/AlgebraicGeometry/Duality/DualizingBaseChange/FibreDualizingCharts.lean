module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartOpens
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransportModels
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingBaseChange.FibreDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexAffineCover
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreOfOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibres
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# The fibres of `f^!𝒪_Y` are dualizing

Let `f : X ⟶ Y` be a flat morphism of `AlgebraicGeometry.FTS S`, `S` Noetherian, and `j` a
compactification. The derived pullback of `f^!𝒪_Y` to every fibre `X_y` is a dualizing complex
([Stacks, Tag 0BZZ]), from the affine chart description
`Stacks.Duality.upperShriekStructureSheafCharts` of `f^!𝒪_Y`.

On the chart `U' = Spec(A ⊗_R κ(y))` of `X_y` over affine opens `U = Spec A ⊆ X` and
`V = Spec R ⊆ Y`, the derived pullback of `f^!𝒪_Y` is the sheaf associated to
`ω^•_{A/R} ⊗ᴸ_A (A ⊗_R κ(y))`, by the affine comparison of [Stacks, Tag 08DW]; this is a
dualizing complex by [Stacks, Tag 0BZW] (2)(b), and [Stacks, Tag 0A86] glues.

## Main results

* `Stacks.Duality.FibreChart.incU'` — the chart `Spec(Γ(X, U) ⊗_{Γ(Y, V)} κ(y)) ⟶ X_y` of the
  fibre over an affine chart of `f`, with `FibreChart.isPullback_incU'` and
  `FibreChart.exists_incU'_eq`.
* `Stacks.Duality.hasDualizingModelOn_opensRange` — a dualizing model presented on a spectrum
  mapping isomorphically onto an open.
* `Stacks.Duality.isDualizingComplex_derivedPullback_fibreι_upperShriek_unconditional` —
  **[Stacks, Tag 0BZZ]**.
* `Stacks.Duality.isDualizingComplex_derivedPullback_fibreι_upperShriek` — the same statement,
  under a second name, by which it is also cited.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u

/-- Extension of scalars along a ring isomorphism preserves finite limits. -/
private theorem preservesFiniteLimits_extendScalars_of_ringEquiv {A B : Type u} [CommRing A]
    [CommRing B] (e : A ≃+* B) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (e : A →+* B)) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ (RingHom.Flat.of_bijective e.bijective)

/-! ### The ring-level input -/

namespace Dualizing

attribute [local instance 10000] HasDerivedCategory.standard

/-- The base change `A ⊗[R] k` of a finite type algebra along a map to a Noetherian ring `k` is
Noetherian. -/
private theorem isNoetherianRing_tensor_baseChange {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (k : Type u) [CommRing k] [IsNoetherianRing k] [Algebra R k]
    (p : PolynomialPresentation (algebraMap R A)) : IsNoetherianRing (A ⊗[R] k) :=
  have := isNoetherianRing_baseChange k p
  isNoetherianRing_of_ringEquiv (k ⊗[R] A) (Algebra.TensorProduct.comm R k A).toRingEquiv

/-- **The fibre of `ω^•_{A/R}` along the left coprojection is dualizing.** For `R → A` flat of
finite type between Noetherian rings and `R → k` a field, the derived base change of
`ω^•_{A/R}` along `A → A ⊗_R k` is a dualizing complex: this is [Stacks, Tag 0BZW] (2)(b),
transported along `A ⊗_R k ≅ k ⊗_R A`. -/
theorem isDualizingComplex_totalDerivedExtensionScalars_includeLeft_of_field
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (k : Type u) [Field k] [Algebra R k]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : IsNoetherianRing (k ⊗[R] A) := isNoetherianRing_baseChange k p
    letI : IsNoetherianRing (A ⊗[R] k) := isNoetherianRing_of_ringEquiv (k ⊗[R] A)
      (Algebra.TensorProduct.comm R k A).toRingEquiv
    IsDualizingComplex
      ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] k)).functor.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  have : IsNoetherianRing (k ⊗[R] A) := isNoetherianRing_baseChange k p
  have := isNoetherianRing_tensor_baseChange k p
  let e : k ⊗[R] A ≃+* A ⊗[R] k := (Algebra.TensorProduct.comm R k A).toRingEquiv
  let ι : A →+* k ⊗[R] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] k ⊗[R] A).toRingHom
  have hcomp : (e : k ⊗[R] A →+* A ⊗[R] k).comp ι =
      Algebra.TensorProduct.includeLeftRingHom := by
    ext a
    simp [e, ι]
  have hω := isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field k p hflat
  have := preservesFiniteLimits_extendScalars_of_ringEquiv e
  refine isDualizingComplex_of_iso ?_ (isDualizingComplex_of_ringEquiv e _ hω)
  rw [← hcomp]
  exact ((totalDerivedExtensionScalarsIsoExtendScalarsOfModels
      (e : k ⊗[R] A →+* A ⊗[R] k)).app _).symm ≪≫
    (totalDerivedExtensionScalarsComp ι (e : k ⊗[R] A →+* A ⊗[R] k)).app _

end Dualizing

/-! ### The affine charts of a fibre -/

namespace Stacks.Duality.FibreChart

variable {X Y : Scheme.{u}}

/-- The ring map `Γ(Y, V) → κ(y)` for `y ∈ V`: the germ at `y` followed by the residue map. -/
abbrev residueMap (y : Y) {V : Y.Opens} (hyV : y ∈ V) : Γ(Y, V) ⟶ Y.residueField y :=
  Y.presheaf.germ V y hyV ≫ Y.residue y

/-- `Spec κ(y) ⟶ Y` factors through `V ≅ Spec Γ(Y, V)` along the residue map. -/
theorem specMap_residueMap_fromSpec (y : Y) {V : Y.Opens} (hV : IsAffineOpen V) (hyV : y ∈ V) :
    Spec.map (residueMap y hyV) ≫ hV.fromSpec = Y.fromSpecResidueField y := by
  rw [Scheme.fromSpecResidueField, ← hV.fromSpecStalk_eq_fromSpecStalk hyV,
    IsAffineOpen.fromSpecStalk, Spec.map_comp, Category.assoc]

variable (f : X ⟶ Y) (y : Y) {V : Y.Opens} (hV : IsAffineOpen V) (hyV : y ∈ V)
  {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)

/-- The chart ring `Γ(X, U) ⊗_{Γ(Y, V)} κ(y)` of the fibre over `U`. -/
abbrev ring : CommRingCat.{u} :=
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField y) := (residueMap y hyV).hom.toAlgebra
  CommRingCat.of (TensorProduct Γ(Y, V) Γ(X, U) (Y.residueField y))

/-- The coprojection `Γ(X, U) → Γ(X, U) ⊗_{Γ(Y, V)} κ(y)`. -/
abbrev inl : Γ(X, U) ⟶ ring f y hyV hUV :=
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField y) := (residueMap y hyV).hom.toAlgebra
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := Γ(Y, V)) (A := Γ(X, U))
    (B := Y.residueField y))

/-- The coprojection `κ(y) → Γ(X, U) ⊗_{Γ(Y, V)} κ(y)`. -/
abbrev inr : Y.residueField y ⟶ ring f y hyV hUV :=
  letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField y) := (residueMap y hyV).hom.toAlgebra
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Γ(Y, V)) (A := Γ(X, U))
    (B := Y.residueField y)).toRingHom

/-- The chart ring of the fibre is the pushout of `Γ(X, U) ← Γ(Y, V) → κ(y)`. -/
theorem isPushout :
    IsPushout (f.appLE V U hUV) (residueMap y hyV) (inl f y hyV hUV) (inr f y hyV hUV) :=
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Y, V) (Y.residueField y) := (residueMap y hyV).hom.toAlgebra
  CommRingCat.isPushout_tensorProduct Γ(Y, V) Γ(X, U) (Y.residueField y)

include hV in
/-- The two maps from the spectrum of the chart ring of the fibre to `Y` agree. -/
theorem specMap_inl_fromSpec_comp :
    (Spec.map (inl f y hyV hUV) ≫ hU.fromSpec) ≫ f =
      Spec.map (inr f y hyV hUV) ≫ Y.fromSpecResidueField y := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV,
    ← specMap_residueMap_fromSpec y hV hyV, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    (isPushout f y hyV hUV).w]

/-- The open immersion `Spec(Γ(X, U) ⊗_{Γ(Y, V)} κ(y)) ⟶ X_y` of the chart of the fibre. -/
def incU' : Spec (ring f y hyV hUV) ⟶ f.fiber y :=
  (isPullback_fiberι_fiberToSpecResidueField f y).lift (Spec.map (inl f y hyV hUV) ≫ hU.fromSpec)
    (Spec.map (inr f y hyV hUV)) (specMap_inl_fromSpec_comp f y hV hyV hU hUV)

/-- The chart of the fibre followed by `X_y ⟶ X` is the chart of `X` over `U`. -/
@[reassoc]
theorem incU'_fiberι : incU' f y hV hyV hU hUV ≫ f.fiberι y =
    Spec.map (inl f y hyV hUV) ≫ hU.fromSpec :=
  (isPullback_fiberι_fiberToSpecResidueField f y).lift_fst _ _ _

/-- The chart of the fibre followed by `X_y ⟶ Spec κ(y)` is the second coprojection. -/
@[reassoc]
theorem incU'_fiberToSpecResidueField :
    incU' f y hV hyV hU hUV ≫ f.fiberToSpecResidueField y = Spec.map (inr f y hyV hUV) :=
  (isPullback_fiberι_fiberToSpecResidueField f y).lift_snd _ _ _

/-- **The chart of the fibre over `U`**, a chart of the cartesian square defining `X_y`. -/
def chart : BaseChangeChart f (Y.fromSpecResidueField y) (f.fiberToSpecResidueField y)
    (f.fiberι y) where
  R := Γ(Y, V)
  A := Γ(X, U)
  R' := Y.residueField y
  A' := ring f y hyV hUV
  incV := hV.fromSpec
  incU := hU.fromSpec
  incV' := 𝟙 _
  incU' := incU' f y hV hyV hU hUV
  isOpenImmersion_incV := hV.isOpenImmersion_fromSpec
  isOpenImmersion_incU := hU.isOpenImmersion_fromSpec
  isOpenImmersion_incV' := inferInstance
  a := f.appLE V U hUV
  b := residueMap y hyV
  c := inl f y hyV hUV
  d := inr f y hyV hUV
  wU := (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV).symm
  wV' := by rw [Category.id_comp, specMap_residueMap_fromSpec y hV hyV]
  wU'U := incU'_fiberι f y hV hyV hU hUV
  wU'V' := by rw [Category.comp_id, incU'_fiberToSpecResidueField]
  isPushout := isPushout f y hyV hUV

/-- The chart of the fibre is an open immersion, by [Stacks, Tag 0DJ8]. -/
instance isOpenImmersion_incU' : IsOpenImmersion (incU' f y hV hyV hU hUV) :=
  BaseChangeChart.isOpenImmersion_incU' (isPullback_fiberι_fiberToSpecResidueField f y)
    (chart f y hV hyV hU hUV)

/-- The chart square of the fibre is cartesian: the chart of `X_y` over `U` is the preimage
of `U`. -/
theorem isPullback_incU' :
    IsPullback (Spec.map (inl f y hyV hUV)) (incU' f y hV hyV hU hUV) hU.fromSpec
      (f.fiberι y) := by
  have hbot : IsPullback (Spec.map (residueMap y hyV)) (𝟙 _) hV.fromSpec
      (Spec.map (residueMap y hyV) ≫ hV.fromSpec) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]⟩
  have big := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout f y hyV hUV)).paste_vert hbot
  rw [Category.comp_id, IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV,
    specMap_residueMap_fromSpec y hV hyV,
    ← incU'_fiberToSpecResidueField f y hV hyV hU hUV] at big
  exact big.of_bot (incU'_fiberι f y hV hyV hU hUV).symm
    (isPullback_fiberι_fiberToSpecResidueField f y)

/-- Every point of the fibre over `U` lies in the chart over `U`. -/
theorem exists_incU'_eq (x' : f.fiber y) (hx' : f.fiberι y x' ∈ U) :
    ∃ z : Spec (ring f y hyV hUV), incU' f y hV hyV hU hUV z = x' := by
  have hP := isPullback_incU' f y hV hyV hU hUV
  have hmem : x' ∈ Set.range (pullback.snd hU.fromSpec (f.fiberι y)) := by
    rw [Scheme.Pullback.range_snd, Set.mem_preimage, hU.range_fromSpec]
    exact hx'
  obtain ⟨w, rfl⟩ := hmem
  refine ⟨hP.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_snd]

end Stacks.Duality.FibreChart

/-! ### A dualizing model on the image of an open immersion from a spectrum -/

namespace Stacks.Duality

/-- **A dualizing model presented on a spectrum mapping isomorphically onto an open.** Let
`i : Spec B ⟶ Z` be an open immersion and `L ∈ D(𝒪_Z)`. If `L` restricted along `i` is the
sheaf associated to a dualizing complex `ω` over `B`, then `L` carries a dualizing model on the
affine open `i(Spec B)`: transport `ω` along the ring isomorphism `B ≅ Γ(Z, i(Spec B))`. -/
theorem hasDualizingModelOn_opensRange {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    {B : CommRingCat.{u}} (i : Spec B ⟶ Z) [IsOpenImmersion i] (L : DerivedCategory Z.Modules)
    (ω : @DerivedCategory (ModuleCat.{u} B) _ _ (HasDerivedCategory.standard _))
    [IsNoetherianRing B]
    (hω : @Dualizing.IsDualizingComplex B _ _ (HasDerivedCategory.standard _) ω)
    (e : (Scheme.Modules.restrictFunctor i).mapDerivedCategory.obj L ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (tilde.functor B) _ _ _).obj ω) :
    HasDualizingModelOn L i.opensRange (isAffineOpen_opensRange i) := by
  set W := i.opensRange
  have hW : IsAffineOpen W := isAffineOpen_opensRange i
  have hrange : Set.range i = Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rfl
  let E := IsOpenImmersion.isoOfRangeEq i hW.fromSpec hrange
  let ψ : B ⟶ Γ(Z, W) := Spec.preimage E.inv
  have hψ : Spec.map ψ = E.inv := Spec.map_preimage _
  have : IsIso ψ := by
    have : IsIso (Scheme.Spec.map ψ.op) := by
      change IsIso (Spec.map ψ)
      rw [hψ]
      infer_instance
    have : IsIso ψ.op := isIso_of_reflects_iso ψ.op Scheme.Spec
    exact isIso_of_op ψ
  have hfac : hW.isoSpec.inv ≫ W.ι = Spec.map ψ ≫ i := by
    rw [IsAffineOpen.isoSpec_inv_ι, hψ, ← IsOpenImmersion.isoOfRangeEq_hom_fac i hW.fromSpec hrange,
      Iso.inv_hom_id_assoc]
  have : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Z, W))
  let φ : B ≃+* Γ(Z, W) := (asIso ψ).commRingCatIsoToRingEquiv
  have := preservesFiniteLimits_extendScalars_of_ringEquiv φ
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} ψ.hom) :=
    preservesFiniteLimits_extendScalars_of_ringEquiv φ
  let ω'' := (ModuleCat.extendScalars.{u, u, u} ψ.hom).mapDerivedCategory.obj ω
  have hω'' : Dualizing.IsDualizingComplex ω'' := Dualizing.isDualizingComplex_of_ringEquiv φ ω hω
  let Φ : Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor hW.isoSpec.inv ≅
      Scheme.Modules.restrictFunctor i ⋙ Scheme.Modules.restrictFunctor (Spec.map ψ) :=
    (Scheme.Modules.restrictFunctorComp hW.isoSpec.inv W.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hfac ≪≫
      Scheme.Modules.restrictFunctorComp (Spec.map ψ) i
  let i₁ := ((Functor.mapDerivedCategoryCompIsoOfCompIso hW.restrictIsoSpecInvCompIso ≪≫
    Functor.mapDerivedCategoryId _).app
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj L)).symm
  let i₂ := (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr Φ ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _)).symm).app L
  let i₄ := (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr (Stacks.AffineTilde.tildeRestrictIso ψ) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _)).symm).app ω
  let i₅ := (Functor.mapDerivedCategoryCompIsoOfCompIso
    (Iso.refl (tilde.functor Γ(Z, W) ⋙ Scheme.Modules.restrictFunctor hW.isoSpec.hom))).app ω''
  refine ⟨ω'', hω'', ⟨Stacks.Injectives.isoOfTargetModelIso W.toScheme.Modules
    (Scheme.Modules.restrictFunctor W.ι)
    (tilde.functor Γ(Z, W) ⋙ Scheme.Modules.restrictFunctor hW.isoSpec.hom) L ω'' ?_⟩⟩
  exact i₁ ≪≫ (Scheme.Modules.restrictFunctor hW.isoSpec.hom).mapDerivedCategory.mapIso
    (i₂ ≪≫ (Scheme.Modules.restrictFunctor (Spec.map ψ)).mapDerivedCategory.mapIso e ≪≫ i₄) ≪≫ i₅

/-- **Derived extension of scalars at the two models agrees on objects.** The standard model and
the locally small model compute the same total left derived functor, and the comparison
equivalences are the identity on objects. -/
def totalDerivedExtensionScalarsModelIso {A A' : Type u} [CommRing A] [CommRing A']
    (φ : A →+* A') (M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)) :
    (Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} A')).functor.obj
        (letI := HasDerivedCategory.standard (ModuleCat.{u} A)
        letI := HasDerivedCategory.standard (ModuleCat.{u} A')
        (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj M) ≅
      (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
          ((Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} A)).functor.obj M) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  letI := HasDerivedCategory.standard (ModuleCat.{u} A')
  let T₁ := totalDerivedExtensionScalars.{u, u, u} φ
  (StacksDraft.DerivedModel.leftDerivedModelIso
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (L₂ := @DerivedCategory.Q _ _ _ ModuleCat.hasDerivedCategory)
    (G := (Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} A)).functor)
    (J := (Stacks.Injectives.grothendieckModelEquiv (ModuleCat.{u} A')).functor)
    T₁.comparison
    (@TotalDerivedExtensionScalars.comparison _ _ _ _ φ ModuleCat.hasDerivedCategory
      ModuleCat.hasDerivedCategory
      (@totalDerivedExtensionScalars.{u, u, u} _ _ _ _ φ ModuleCat.hasDerivedCategory
        ModuleCat.hasDerivedCategory))
    (Iso.refl _) (Iso.refl _)).app M

/-! ### The chart model of the fibre of `f^!𝒪_Y` -/

section Fibre

open DerivedPushforward

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The chart model of the fibre.** Over affine opens `U ⊆ f⁻¹(V)` with `y ∈ V` and a
polynomial presentation `p` of `Γ(Y, V) → Γ(X, U)`, the derived pullback of `f^!𝒪_Y` to `X_y`,
restricted to the chart `Spec(Γ(X, U) ⊗_{Γ(Y, V)} κ(y))`, is the sheaf associated to the
derived base change of the algebraic upper shriek of `Γ(Y, V)`, by [Stacks, Tag 08DW]. -/
theorem nonempty_fibreChartModelIso (h : UpperShriekStructureSheafCharts f j) (y : Y.left)
    {V : Y.left.Opens} (hV : IsAffineOpen V) (hyV : y ∈ V) {U : X.left.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    Nonempty ((Scheme.Modules.restrictFunctor
        (FibreChart.incU' f.left y hV hyV hU hUV)).mapDerivedCategory.obj
        ((derivedPullback (f.left.fiberι y)).obj (relativeDualizingComplexObj f j)) ≅
      (tilde.functor (FibreChart.ring f.left y hyV hUV)).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} (FibreChart.inl f.left y hyV hUV).hom).functor.obj
          (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))) := by
  let K := relativeDualizingComplexObj f j
  let ω := p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)
  let A := Γ(X.left, U)
  let iU := hU.fromSpec
  let ι' := FibreChart.incU' f.left y hV hyV hU hUV
  let inl := FibreChart.inl f.left y hyV hUV
  obtain ⟨e⟩ := h V hV U hU hUV p
  let e' := e ≪≫ Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} A)
    (tilde.functor A ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ω
  let d4 : (tilde.functor A ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory ⋙
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory ≅
        (tilde.functor A).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCongr (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ hU.restrictIsoSpecCompIso ≪≫ Functor.rightUnitor _)
  let eA : (derivedPullback iU).obj K ≅ (tilde.functor A).mapDerivedCategory.obj ω :=
    ((derivedRestrictIsoDerivedPullback iU).app K).symm ≪≫
      ((Functor.mapDerivedCategoryCompIsoOfCompIso
        (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm).app K).symm ≪≫
      (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso e' ≪≫ d4.app ω
  exact ⟨(derivedRestrictIsoDerivedPullback ι').app _ ≪≫
    (derivedPullbackCompIso ι' (f.left.fiberι y)).app K ≪≫
    eqToIso (congrArg (fun g => (derivedPullback g).obj K)
      (FibreChart.incU'_fiberι f.left y hV hyV hU hUV)) ≪≫
    ((derivedPullbackCompIso (Spec.map inl) iU).app K).symm ≪≫
    (derivedPullback (Spec.map inl)).mapIso eA ≪≫
    (affinePullbackComparison A (FibreChart.ring f.left y hyV hUV) inl).app ω⟩

/-- **The fibre chart carries a dualizing model.** In the situation of
`Stacks.Duality.nonempty_fibreChartModelIso`, with `f` flat, the derived pullback of `f^!𝒪_Y` to
`X_y` carries a dualizing model on the image of the chart over `U`: its model is the derived base
change of `ω^•_{Γ(X, U)/Γ(Y, V)}` to the fibre ring, a dualizing complex by
[Stacks, Tag 0BZW] (2)(b). -/
theorem hasDualizingModelOn_fibreChart [Flat f.left] (h : UpperShriekStructureSheafCharts f j)
    (y : Y.left) {V : Y.left.Opens} (hV : IsAffineOpen V) (hyV : y ∈ V) {U : X.left.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    HasDualizingModelOn ((derivedPullback (f.left.fiberι y)).obj (relativeDualizingComplexObj f j))
      (FibreChart.incU' f.left y hV hyV hU hUV).opensRange (isAffineOpen_opensRange _) := by
  have hloc (Z : AlgebraicGeometry.FTS S) : IsLocallyNoetherian Z.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have := hloc X
  have := hloc Y
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Y.left, V) (Y.left.residueField y) :=
    (FibreChart.residueMap y hyV).hom.toAlgebra
  have hflat : (algebraMap Γ(Y.left, V) Γ(X.left, U)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (f.left.flat_appLE hV hU hUV)
  have : IsNoetherianRing (FibreChart.ring f.left y hyV hUV) :=
    Dualizing.isNoetherianRing_tensor_baseChange (Y.left.residueField y) p
  have hω := Dualizing.isDualizingComplex_totalDerivedExtensionScalars_includeLeft_of_field
    (Y.left.residueField y) p hflat
  obtain ⟨e⟩ := nonempty_fibreChartModelIso f j h y hV hyV hU hUV p
  let B := FibreChart.ring f.left y hyV hUV
  let ω := p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)
  let inl := FibreChart.inl f.left y hyV hUV
  let ω' :=
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X.left, U))
    let := HasDerivedCategory.standard (ModuleCat.{u} B)
    (totalDerivedExtensionScalars.{u, u, u} inl.hom).functor.obj ω
  refine hasDualizingModelOn_opensRange _ _ ω' hω ?_
  exact e ≪≫ (tilde.functor B).mapDerivedCategory.mapIso
      (totalDerivedExtensionScalarsModelIso inl.hom ω).symm ≪≫
    (Stacks.Injectives.mapDerivedCategoryObjIso (ModuleCat.{u} B) (tilde.functor B) _).symm

/-- **Stacks Project, Tag 0BZZ (Lemma 48.18.4).** In Situation 48.16.1 let `f : X ⟶ Y` be a flat
morphism of `FTS S` and set `ω^•_{X/Y} = f^!𝒪_Y`, for any compactification `j` defining `f^!`.
For `y ∈ Y` let `h : X_y ⟶ X` be the projection from the fibre. Then `Lh^*ω^•_{X/Y}` is a
dualizing complex on `X_y`.

The fibre charts over the affine charts of `f` cover `X_y`; on each, by
`Stacks.Duality.upperShriekStructureSheafCharts` and [Stacks, Tag 08DW], `Lh^*ω^•_{X/Y}` is the
sheaf associated to `ω^•_{A/R} ⊗ᴸ_A (A ⊗_R κ(y))`, which is dualizing by [Stacks, Tag 0BZW];
[Stacks, Tag 0A86] glues. -/
@[stacks 0BZZ]
theorem isDualizingComplex_derivedPullback_fibreι_upperShriek_unconditional [Flat f.left]
    (y : Y.left) :
    IsDualizingComplex
      ((derivedPullback (f.left.fiberι y)).obj (relativeDualizingComplexObj f j)) := by
  have h := upperShriekStructureSheafCharts f j
  have := locallyOfFiniteType_left f
  have hpt : ∀ x' : f.left.fiber y, ∃ (W : (f.left.fiber y).Opens) (hW : IsAffineOpen W),
      x' ∈ W ∧ HasDualizingModelOn
        ((derivedPullback (f.left.fiberι y)).obj (relativeDualizingComplexObj f j)) W hW := by
    intro x'
    have hfx : f.left (f.left.fiberι y x') = y := by
      have : f.left.fiberι y x' ∈ f.left ⁻¹' {y} := by
        rw [← Scheme.Hom.range_fiberι]
        exact ⟨x', rfl⟩
      exact this
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y.left) (x := y) (U := ⊤) (by simp)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.left)
      (x := f.left.fiberι y x') (U := f.left ⁻¹ᵁ V) (show f.left (f.left.fiberι y x') ∈ V by
        rw [hfx]
        exact hyV)
    obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation (f.left.appLE V U hUV).hom
      (f.left.finiteType_appLE hV hU hUV)
    obtain ⟨z, hz⟩ := FibreChart.exists_incU'_eq f.left y hV hyV hU hUV x' hxU
    have := FibreChart.isOpenImmersion_incU' f.left y hV hyV hU hUV
    exact ⟨(FibreChart.incU' f.left y hV hyV hU hUV).opensRange,
      isAffineOpen_opensRange (FibreChart.incU' f.left y hV hyV hU hUV),
      ⟨z, hz⟩, hasDualizingModelOn_fibreChart f j h y hV hyV hU hUV p⟩
  choose W hW hxW hmod using hpt
  exact isDualizingComplex_of_hasDualizingModelOn_cover W hW
    (top_unique fun x' _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x', hxW x'⟩) hmod

alias isDualizingComplex_derivedPullback_fibreι_upperShriek :=
  isDualizingComplex_derivedPullback_fibreι_upperShriek_unconditional

end Fibre

end Stacks.Duality
