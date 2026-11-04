module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialFrobenius
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCechHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCechBaseChange
public import StacksFrontier.Algebra.Homology.FlatComplexTopDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.ProperSmoothFiniteTypeSubring
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import StacksFrontier.RingTheory.Jacobson.Examples
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The top differential of a smooth proper scheme over a field vanishes on cohomology

Let `X` be smooth and proper over a field `k`, equidimensional of dimension `d`. Then
`d : Hᵈ(X, Ω^{d-1}_{X/k}) ⟶ Hᵈ(X, Ω^d_{X/k})` is zero ([Stacks, Tag 0FW6]).

In positive characteristic this is
`AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero_of_charP`. In general
`X` descends to a smooth proper `Y` over a subring `R ⊆ k` of finite type over `ℤ`
(`AlgebraicGeometry.exists_isPullback_specAdjoin_smoothOfRelativeDimension`). Fix a finite affine
covering of `Y`. The alternating Čech complexes of `Ω^{d-1}_{Y/R}` and `Ω^d_{Y/R}` are bounded
complexes of flat `R`-modules, with cohomology vanishing above `d` and finite in degree `d`, and
their base changes to `k` and to the residue fields `R/𝔪` are the Čech complexes of the base
changes of `Y`, compatibly with `d`. The residue fields are finite, so `d` vanishes on `Hᵈ` of
every closed fibre, and
`Stacks.FlatComplexTopDegree.homologyMap_extendScalars_eq_zero_of_forall_isMaximal` then gives
the vanishing over `k`.

The statements before the last one take as a hypothesis `hω` the identification
`ω_Z ≅ Ω^n_{Z/K}` of the dualizing module of a smooth proper scheme over a field, which is how
[Stacks, Tag 0FW4] enters (`AlgebraicGeometry.Scheme.Hom.hodgeDuality_of_smooth_of_iso`); the
last one supplies it by [Stacks, Tag 0FVV], part (7).

## Main results

* `AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero`: the vanishing,
  given `hω`.
* `AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero_of_isProper_of_smooth`
  — the vanishing without `hω`, [Stacks, Tag 0FW6].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ModuleCat AlgebraicGeometry
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.Duality (dualizingModule)

universe u

namespace Stacks.Cech

/-- **On an empty scheme every morphism of alternating Čech complexes is zero on cohomology in
positive degrees**: all sections, hence all cochains, vanish. -/
theorem homologyMap_alternatingCechModulePush_eq_zero_of_isEmpty {A : Type u} [CommRing A]
    {X : Scheme.{u}} [IsEmpty X] (f : X ⟶ Spec (.of A)) {I : Type u} (U : I → X.Opens)
    {F G : X.Modules} (ψ : F.presheaf ⟶ G.presheaf)
    (hψ : ∀ (W : X.Opens) (a : A) (x : Γ(F, W)),
      ψ.app (op W) ((baseRingHom f W).hom a • x) = (baseRingHom f W).hom a • ψ.app (op W) x)
    (n : ℕ) :
    HomologicalComplex.homologyMap (alternatingCechModulePush f U ψ hψ) (n + 1) = 0 := by
  have hsec : ∀ W : X.Opens, Subsingleton Γ(F, W) := fun W =>
    AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEqEmpty
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      (Opens.ext (Set.eq_empty_of_isEmpty _))).isZero
  rw [CochainComplex.moduleCat_homologyMap_succ_eq_zero_iff]
  intro x _
  obtain rfl : x = 0 := Subtype.ext (funext fun i => (hsec _).elim _ _)
  exact ⟨0, (map_zero _).trans (map_zero _).symm⟩

section BaseChange

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  {I : Type u} [Finite I] [IsSeparated f] (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i))

include hsq hUaff in
/-- **The de Rham differential on the Čech complexes of a base change**: its base change is zero
on `Hⁿ` exactly when the de Rham differential of the base change is. -/
theorem homologyMap_extendScalars_deRham_eq_zero_iff (e n : ℕ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (alternatingCechModulePush f U (Scheme.Hom.deRhamPresheafD f e)
            (Scheme.Hom.deRhamPresheafD_app_smul f e))) n = 0 ↔
      HomologicalComplex.homologyMap
        (alternatingCechModulePush f' (fun i => g ⁻¹ᵁ U i) (Scheme.Hom.deRhamPresheafD f' e)
          (Scheme.Hom.deRhamPresheafD_app_smul f' e)) n = 0 := by
  have sq := congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
    (formsCechBaseChangeIso_comm φ f f' g hsq U hUaff e)
  simp only [HomologicalComplex.homologyMap_comp] at sq
  have : ∀ e', IsIso (HomologicalComplex.homologyMap
      (formsCechBaseChangeIso φ f f' g hsq U hUaff e').hom n) := fun e' =>
    (inferInstance : IsIso ((HomologicalComplex.homologyFunctor _ _ n).map
      (formsCechBaseChangeIso φ f f' g hsq U hUaff e').hom))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, zero_comp] at sq
    exact (cancel_epi _).1 (sq.symm.trans comp_zero.symm)
  · rw [h, comp_zero] at sq
    exact (cancel_mono _).1 (sq.trans zero_comp.symm)

end BaseChange

end Stacks.Cech

namespace AlgebraicGeometry.TopDegreeDifferential

open Stacks.Cech

/-- **The residue fields at the maximal ideals of a ring of finite type over `ℤ` have prime
characteristic**: such a residue field is finite over `ℤ` (`ℤ` is a Jacobson ring), so integral
over `ℤ`, and `ℤ` is not a field. -/
@[ega "IV 10.4.6" "base ring Z"]
theorem exists_prime_charP_quotient_of_finiteType {R : Type u} [CommRing R]
    [Algebra.FiniteType ℤ R] (m : Ideal R) [m.IsMaximal] :
    ∃ p : ℕ, p.Prime ∧ CharP (R ⧸ m) p := by
  let := Ideal.Quotient.field m
  have : Algebra.FiniteType ℤ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ m) Ideal.Quotient.mk_surjective
  have := int_isJacobsonRing
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ m)
  have : Algebra.IsIntegral ℤ (R ⧸ m) := Algebra.IsIntegral.of_finite ℤ (R ⧸ m)
  have hninj : ¬ Function.Injective (algebraMap ℤ (R ⧸ m)) := fun h =>
    Int.not_isField (isField_of_isIntegral_of_isField h (Field.toIsField (R ⧸ m)))
  obtain ⟨p, hp⟩ := CharP.exists (R ⧸ m)
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := CharP.charP_to_charZero (R ⧸ m)
    exact hninj (algebraMap ℤ (R ⧸ m)).injective_int
  exact ⟨p, (CharP.char_is_prime_or_zero (R ⧸ m) p).resolve_right hp0, hp⟩

/-- **The top differential on the Čech complexes of a smooth proper scheme over a ring of finite
type over `ℤ`, base changed to a residue field at a maximal ideal, is zero on top cohomology**,
given the identification of the dualizing module of smooth proper schemes over fields with their
top forms: the residue field is finite. -/
private theorem homologyMap_extendScalars_quotient_deRham_eq_zero
    (hω : ∀ {K : Type u} [Field K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K)) [IsProper h]
      (n : ℕ) [SmoothOfRelativeDimension n h],
      Nonempty (dualizingModule h ≅ Scheme.Hom.relativeDifferentialForms h n))
    {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of R)) [IsProper h] (e : ℕ) [SmoothOfRelativeDimension (e + 1) h]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) (m : Ideal R) [m.IsMaximal] :
    HomologicalComplex.homologyMap
      (((extendScalars (Ideal.Quotient.mk m)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (alternatingCechModulePush h U (Scheme.Hom.deRhamPresheafD h e)
          (Scheme.Hom.deRhamPresheafD_app_smul h e))) (e + 1) = 0 := by
  let πm : R →+* R ⧸ m := Ideal.Quotient.mk m
  set g := pullback.snd h (Spec.map (CommRingCat.ofHom πm))
  have hsqm : IsPullback (pullback.fst h (Spec.map (CommRingCat.ofHom πm))) g h
      (Spec.map (CommRingCat.ofHom πm)) :=
    IsPullback.of_hasPullback _ _
  have : IsProper g := MorphismProperty.of_isPullback hsqm ‹IsProper h›
  have : SmoothOfRelativeDimension (e + 1) g :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := e + 1)
    MorphismProperty.of_isPullback hsqm ‹SmoothOfRelativeDimension (e + 1) h›
  have : IsAffineHom (pullback.fst h (Spec.map (CommRingCat.ofHom πm))) :=
    MorphismProperty.of_isPullback hsqm.flip inferInstance
  refine (homologyMap_extendScalars_deRham_eq_zero_iff πm h _ _ hsqm U hUaff e (e + 1)).2 ?_
  rcases isEmpty_or_nonempty (pullback h (Spec.map (CommRingCat.ofHom πm)) : Scheme.{u}) with
    hE | hN
  · exact homologyMap_alternatingCechModulePush_eq_zero_of_isEmpty _ _ _ _ e
  have hUm : (⊤ : (pullback h (Spec.map (CommRingCat.ofHom πm))).Opens) =
      ⨆ i, pullback.fst h (Spec.map (CommRingCat.ofHom πm)) ⁻¹ᵁ U i := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  rw [← rightDerived_map_deRham_d_eq_zero_iff_homologyMap _ _ hUm
    (fun i => (hUaff i).preimage _) e e]
  obtain ⟨p, hp, hcp⟩ := exists_prime_charP_quotient_of_finiteType m
  have := Fact.mk hp
  let := Ideal.Quotient.field m
  have : Smooth g := SmoothOfRelativeDimension.smooth (e + 1) _
  exact rightDerived_map_deRham_d_eq_zero_of_charP hω p g
    (equidimensional_of_topologicalKrullDimAt_eq (R ⧸ m) _ g (d := e + 1) fun z =>
      topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field (e + 1) g z) e
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (e + 1) g)

/-- **The top differential on the Čech complexes of a smooth proper scheme over a ring of finite
type over `ℤ`, base changed to a field containing the ring, is zero on top cohomology**, given the
identification of the dualizing module of smooth proper schemes over fields with their top forms.
It is zero on top cohomology over every residue field at a maximal ideal, which is finite
(`AlgebraicGeometry.TopDegreeDifferential.rightDerived_map_deRham_d_eq_zero_of_charP`), and the
Čech complexes satisfy the hypotheses of
`Stacks.FlatComplexTopDegree.homologyMap_extendScalars_eq_zero_of_forall_isMaximal`. -/
theorem homologyMap_extendScalars_deRham_eq_zero_of_finiteType
    (hω : ∀ {K : Type u} [Field K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K)) [IsProper h]
      (n : ℕ) [SmoothOfRelativeDimension n h],
      Nonempty (dualizingModule h ≅ Scheme.Hom.relativeDifferentialForms h n))
    {R : Type u} [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of R)) [IsProper h] (e : ℕ) [SmoothOfRelativeDimension (e + 1) h]
    {I : Type u} [Finite I] [LinearOrder I] (U : I → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) {k : Type u} [Field k] (ι : R →+* k)
    (hι : Function.Injective ι) :
    HomologicalComplex.homologyMap
      (((extendScalars ι).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (alternatingCechModulePush h U (Scheme.Hom.deRhamPresheafD h e)
          (Scheme.Hom.deRhamPresheafD_app_smul h e))) (e + 1) = 0 := by
  classical
  have := Fintype.ofFinite I
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have := int_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  have : Smooth h := SmoothOfRelativeDimension.smooth (e + 1) h
  have hflat : ∀ p : ℕ, ∀ i, Module.Flat R
      ((alternatingCechModuleComplex h U (h.relativeDifferentialForms (p : ℤ))).X i) := fun p =>
    have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms h p
    have := ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms h p
    alternatingCechModuleComplex_flat h U _ hUaff
      (VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree h _)
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms h e
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms h (e + 1)
  have := hflat e
  have := hflat (e + 1)
  have := Scheme.Hom.isCoherent_relativeDifferentialForms h e
  have := Scheme.Hom.isCoherent_relativeDifferentialForms h (e + 1)
  have : Module.Finite R ((alternatingCechModuleComplex h U
      (h.relativeDifferentialForms ((e + 1 : ℕ) : ℤ))).homology (e + 1)) :=
    moduleFinite_homology_alternatingCechModuleComplex h U hU _ hUaff (e + 1)
  have hfib := topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension (e + 1) h
  exact Stacks.FlatComplexTopDegree.homologyMap_extendScalars_eq_zero_of_forall_isMaximal
    (alternatingCechModulePush h U (Scheme.Hom.deRhamPresheafD h e)
      (Scheme.Hom.deRhamPresheafD_app_smul h e)) e (Fintype.card I)
    (fun i hi => subsingleton_alternatingSubmodule h U _ hi)
    (fun i hi => subsingleton_alternatingSubmodule h U _ hi)
    (fun i hi => isZero_homology_alternatingCechModuleComplex h U hU _ hUaff hfib hi)
    (fun i hi => isZero_homology_alternatingCechModuleComplex h U hU _ hUaff hfib hi)
    (fun m _ => homologyMap_extendScalars_quotient_deRham_eq_zero hω h e U hU hUaff m) ι hι

/-- **The top differential vanishes on cohomology, for a scheme smooth of relative dimension
`e + 1` and proper over a field**, given the identification of the dualizing module of smooth
proper schemes over fields with their top forms. -/
theorem rightDerived_map_deRham_d_eq_zero_of_smoothOfRelativeDimension
    (hω : ∀ {K : Type u} [Field K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K)) [IsProper h]
      (n : ℕ) [SmoothOfRelativeDimension n h],
      Nonempty (dualizingModule h ≅ Scheme.Hom.relativeDifferentialForms h n))
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (e : ℕ)
    [SmoothOfRelativeDimension (e + 1) f] :
    ((sectionsFunctor X.carrier ⊤).rightDerived (e + 1)).map
      ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d e (e + 1))) = 0 := by
  classical
  obtain ⟨j, Y, h, q', hprop, hsm, hpb⟩ :=
    exists_isPullback_specAdjoin_smoothOfRelativeDimension k f (e + 1)
  let R₀ := Algebra.adjoin ℤ ((j.unop : Finset k) : Set k)
  have : Algebra.FiniteType ℤ R₀ := finiteType_adjoinFinset_int k j.unop
  let h₀ : Y ⟶ Spec (.of R₀) := h
  have : IsProper h₀ := hprop
  have : SmoothOfRelativeDimension (e + 1) h₀ := hsm
  let ι : R₀ →+* k := R₀.val.toRingHom
  have hsq : IsPullback q' f h₀ (Spec.map (CommRingCat.ofHom ι)) := hpb
  have : IsAffineHom q' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h₀
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := Y)
  let : LinearOrder s := linearOrderOfSTO WellOrderingRel
  let U : s → Y.Opens := fun i => i.1.1
  have hU : (⊤ : Y.Opens) = ⨆ i, U i := hs.symm.trans iSup_subtype'
  have hUaff : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  have hU' : (⊤ : X.Opens) = ⨆ i, q' ⁻¹ᵁ U i := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  rw [rightDerived_map_deRham_d_eq_zero_iff_homologyMap f (fun i => q' ⁻¹ᵁ U i) hU'
    (fun i => (hUaff i).preimage q') e e]
  exact (homologyMap_extendScalars_deRham_eq_zero_iff ι h₀ f q' hsq U hUaff e (e + 1)).1
    (homologyMap_extendScalars_deRham_eq_zero_of_finiteType hω h₀ e U hU hUaff ι
      Subtype.val_injective)

/-- **The top differential of a smooth proper scheme over a field vanishes on top cohomology**
([Stacks, Tag 0FW6]), given the identification of the dualizing module of smooth proper schemes
over fields with their top forms: for `X` smooth and proper over `k`, equidimensional of
dimension `d`, `d : Hᵈ(X, Ω^{d-1}_{X/k}) ⟶ Hᵈ(X, Ω^d_{X/k})` is zero. -/
theorem rightDerived_map_deRham_d_eq_zero
    (hω : ∀ {K : Type u} [Field K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K)) [IsProper h]
      (n : ℕ) [SmoothOfRelativeDimension n h],
      Nonempty (dualizingModule h ≅ Scheme.Hom.relativeDifferentialForms h n))
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    ((sectionsFunctor X.carrier ⊤).rightDerived d).map
      ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d (d - 1) d)) = 0 := by
  cases d with
  | zero =>
    rw [HomologicalComplex.shape _ _ _ (by simp), Functor.map_zero, Functor.map_zero]
  | succ e =>
    have := smoothOfRelativeDimension_of_equidimensional k f hequi (e + 1) hd
    exact rightDerived_map_deRham_d_eq_zero_of_smoothOfRelativeDimension hω f e

/-- **[Stacks, Tag 0FW6].** Let `k` be a field and `X` a smooth proper scheme over `k`,
equidimensional of dimension `d`. Then the map `d : Hᵈ(X, Ω^{d-1}_{X/k}) ⟶ Hᵈ(X, Ω^d_{X/k})`
induced by the de Rham differential is zero. The dualizing module of a smooth proper scheme over
a field is its sheaf of top forms by [Stacks, Tag 0FVV], part (7). -/
@[stacks 0FW6 "for X smooth proper over a field k, equidimensional of dimension d, the map \
d : H^d(X, Omega^{d-1}_{X/k}) -> H^d(X, Omega^d_{X/k}) is zero"]
theorem rightDerived_map_deRham_d_eq_zero_of_isProper_of_smooth {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    ((sectionsFunctor X.carrier ⊤).rightDerived d).map
      ((SheafOfModules.toSheaf _).map (f.deRhamComplex.d (d - 1) d)) = 0 :=
  rightDerived_map_deRham_d_eq_zero
    (@fun _ _ _ h _ n _ => And.right <|
      Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
        h n)
    f hequi d hd

end AlgebraicGeometry.TopDegreeDifferential
