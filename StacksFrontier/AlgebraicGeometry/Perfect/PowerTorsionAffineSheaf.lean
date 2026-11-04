module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.Homology.Perfect.PowerTorsionTargetWitness
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.PowerTorsionGlobalSection
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# The affine case of Stacks 08EJ in the sheaf language

Let `R` be a commutative ring, let `g ∈ R` and let `T = V(g)` be the zero locus of `g` in
`Spec R`. Let `E` and `E'` be objects of `D_QCoh(𝒪_{Spec R})` with `E` perfect and `E'`
cohomologically supported on `T`. Then every morphism `α : E ⟶ E'` is annihilated by a power of
the global section of `𝒪_{Spec R}` corresponding to `g`.

## Main definitions

* `Stacks.AffineTilde.linearSpec`: the `R`-linear structure on `𝒪_{Spec R}`-modules given by
  `R ≅ Γ(Spec R, 𝒪)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.linearGlobalSectionRing`: sheaves of modules on a scheme,
  at the spelling `X.Modules`, are linear over the ring of global sections.
* `Stacks.AffineTilde.support_homology_subset_of_cohomologySupportedOn`: if the derived
  sheafification of `E` is cohomologically supported on `V(g)`, then every cohomology module of
  `E` has support contained in `V(g)`.
* `Stacks.AffineTilde.cohomologySupportedOn_mapDerivedCategory_tilde`: the converse.
* `Stacks.AffineTilde.mapDerivedCategory_tilde_map_smul`: derived sheafification carries `g • φ`
  to `g̃ • φ̃`, where `g̃` is the global scalar of the section of `𝒪_{Spec R}` named by `g`.
* `Stacks.AffineTilde.tilde_functor_linear` and
  `Stacks.AffineTilde.mapDerivedCategory_tilde_linear`: sheafification and its derived functor
  are `R`-linear for `Stacks.AffineTilde.linearSpec`.
* `Stacks.AffineTilde.exists_pow_smul_eq_zero_mapDerivedCategory` and
  `Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn`: Stacks
  08EJ for an affine scheme, first between two derived sheafifications and then for arbitrary
  objects with quasi-coherent cohomology.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` wrapping `SheafOfModules X.ringCatSheaf` with
separately declared instances, so the linear structure
`Stacks.Cohomology.SiteModules.linearSheafOfModules` is transported to `X.Modules` by the
instance `AlgebraicGeometry.Scheme.Modules.linearGlobalSectionRing`.

The scalars of the two sides are different rings: `R` acts on `D(R)`, and the global sections
`Stacks.Cohomology.SiteModules.GlobalSectionRing` act on `D(𝒪_{Spec R})`. So
`Stacks.AffineTilde.mapDerivedCategory_tilde_map_smul` is an identity between the two actions;
after `Stacks.AffineTilde.linearSpec` makes `𝒪_{Spec R}`-modules `R`-linear, the two actions on
the derived category agree definitionally.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 36.10.4 (Tag 08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Section 36.6 (Tag 08DA)](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/-- Sheaves of modules on a scheme `X`, at the spelling `X.Modules`, are linear over the ring of
global sections. -/
instance linearGlobalSectionRing (X : Scheme.{u}) :
    Linear ↥(GlobalSectionRing X.ringCatSheaf) X.Modules :=
  inferInstanceAs (Linear ↥(GlobalSectionRing X.ringCatSheaf)
    (SheafOfModules.{u} X.ringCatSheaf))

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AffineTilde

variable {R : CommRingCat.{u}}

/-! ### `R`-linearity of derived sheafification -/

/-- The `R`-linear structure on `𝒪_{Spec R}`-modules attached to the isomorphism
`R ≅ Γ(Spec R, 𝒪)`. -/
@[instance_reducible]
def linearSpec (R : CommRingCat.{u}) : Linear R (Spec R).Modules :=
  letI := Scheme.linearOfRingHom.{u, u} (Spec R) R (Scheme.ΓSpecIso R).inv.hom
  inferInstanceAs (Linear R (SheafOfModules.{u} (Spec R).ringCatSheaf))

attribute [local instance 20000] linearSpec

/-- The global sections functor on `Spec R` is `R`-linear. -/
theorem moduleSpecΓFunctor_linear :
    Functor.Linear R (moduleSpecΓFunctor (R := R)) :=
  ⟨fun f a => by
    ext x
    exact Scheme.smul_val_app_top.{u, u} (Spec R) R (Scheme.ΓSpecIso R).inv.hom a f x⟩

/-- Sheafification `M ↦ M̃` is `R`-linear. -/
theorem tilde_functor_linear : Functor.Linear R (tilde.functor R) := by
  have hΓ : Functor.Linear R (moduleSpecΓFunctor (R := R)) := moduleSpecΓFunctor_linear
  have hcomp : Functor.Linear R (tilde.functor R ⋙ moduleSpecΓFunctor) :=
    Functor.linear_of_iso R (tilde.toTildeΓNatIso (R := R))
  rw [Functor.linear_iff]
  intro N a
  refine (tilde.adjunction.homEquiv N ((tilde.functor R).obj N)).injective ?_
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, ← Functor.comp_map,
    hcomp.map_smul, hΓ.map_smul]
  simp only [CategoryTheory.Functor.map_id, Functor.comp_obj]

/-- Derived sheafification is `R`-linear. -/
theorem mapDerivedCategory_tilde_linear :
    Functor.Linear R (tilde.functor R).mapDerivedCategory := by
  have := tilde_functor_linear (R := R)
  exact (Localization.functor_linear_iff (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) R
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (tilde.functor R).mapDerivedCategory).1 inferInstance

/-- Derived sheafification carries the scalar multiple `g • φ` of a morphism of `D(R)` to the
multiple of `φ̃` by the global scalar of the section of `𝒪_{Spec R}` that `g` names. -/
theorem mapDerivedCategory_tilde_map_smul (g : R)
    {E E' : DerivedCategory (ModuleCat.{u} R)} (φ : E ⟶ E') :
    (tilde.functor R).mapDerivedCategory.map (g • φ) =
      Stacks.ExtensionByZero.globalScalar (Spec R).ringCatSheaf
        ((Scheme.ΓSpecIso R).inv g) • (tilde.functor R).mapDerivedCategory.map φ := by
  rw [mapDerivedCategory_tilde_linear.map_smul]
  rfl

/-! ### Supported cohomology against the support of the cohomology modules -/

/-- If the derived sheafification of an object `E` of `D(R)` is cohomologically supported on the
zero locus `V(g)`, then the support of every cohomology module of `E` is contained in `V(g)`. -/
theorem support_homology_subset_of_cohomologySupportedOn (g : R)
    (E : DerivedCategory (ModuleCat.{u} R))
    (h : AlgebraicGeometry.CohomologySupportedOn (Spec R).ringCatSheaf
      (PrimeSpectrum.zeroLocus {g}) ((tilde.functor R).mapDerivedCategory.obj E)) (p : ℤ) :
    Module.support R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj E) ⊆
      PrimeSpectrum.zeroLocus {g} := by
  intro x hx
  by_contra hxT
  obtain ⟨e⟩ := nonempty_homology_mapDerivedCategory_tilde_iso E p
  exact notMem_support_of_isZero_stalk_tilde _ x ((h p x hxT).of_iso ((Scheme.Modules.toPresheaf
    (Spec R) ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso e).symm) hx

/-- If every cohomology module of `E` has support inside `V(g)`, then the derived sheafification
of `E` is cohomologically supported on `V(g)`. -/
theorem cohomologySupportedOn_mapDerivedCategory_tilde (g : R)
    (E : DerivedCategory (ModuleCat.{u} R))
    (h : ∀ p : ℤ, Module.support R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj E) ⊆
      PrimeSpectrum.zeroLocus {g}) :
    AlgebraicGeometry.CohomologySupportedOn (Spec R).ringCatSheaf
      (PrimeSpectrum.zeroLocus {g}) ((tilde.functor R).mapDerivedCategory.obj E) := by
  intro i x hx
  obtain ⟨e⟩ := nonempty_homology_mapDerivedCategory_tilde_iso E i
  have hg : g ∉ x.asIdeal := fun hg =>
    hx ((PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 hg))
  have htor := StacksDraft.Perfect.isElementPowerTorsion_of_support_subset_zeroLocus (h i)
  exact (isZero_stalk_tilde_of_exists_pow_smul_eq_zero _ g
    (fun m => (htor m).imp fun _ hk => hk.2) x hg).of_iso ((Scheme.Modules.toPresheaf (Spec R) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso e)

/-! ### The affine case of Stacks 08EJ, in the sheaf language -/

/-- For `M` perfect and every cohomology module of `N` supported on `V(g)`, every morphism
`M̃ ⟶ Ñ` of derived sheafifications is annihilated by a power of the global scalar of `g`. -/
theorem exists_pow_smul_eq_zero_mapDerivedCategory (g : R)
    {M N : DerivedCategory (ModuleCat.{u} R)} (hM : StacksDraft.Perfect.IsPerfect M)
    (hN : ∀ p : ℤ, Module.support R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj N) ⊆
      PrimeSpectrum.zeroLocus {g})
    (φ : (tilde.functor R).mapDerivedCategory.obj M ⟶
      (tilde.functor R).mapDerivedCategory.obj N) :
    ∃ n : ℕ, Stacks.ExtensionByZero.globalScalar (Spec R).ringCatSheaf
      ((Scheme.ΓSpecIso R).inv g) ^ n • φ = 0 := by
  have hmap : (tilde.functor R).mapDerivedCategory.map (StandardModel.homEquiv R M N φ) = φ :=
    (StandardModel.mapDerivedCategoryFullyFaithful R).homEquiv.apply_symm_apply φ
  obtain ⟨n, hn⟩ :=
    StacksDraft.Perfect.exists_pow_smul_eq_zero_of_isPerfect_of_support_subset_zeroLocus
      g hM hN (StandardModel.homEquiv R M N φ)
  have hscalar : Stacks.ExtensionByZero.globalScalar (Spec R).ringCatSheaf
      ((Scheme.ΓSpecIso R).inv g) ^ n =
      Stacks.ExtensionByZero.globalScalar (Spec R).ringCatSheaf
        ((Scheme.ΓSpecIso R).inv (g ^ n)) :=
    (Stacks.ExtensionByZero.globalScalar_pow (Spec R).ringCatSheaf
      ((Scheme.ΓSpecIso R).inv g) n).symm.trans (congrArg _ (map_pow _ g n).symm)
  refine ⟨n, ?_⟩
  rw [hscalar, ← hmap, ← mapDerivedCategory_tilde_map_smul, hn, Functor.map_zero]

/-- A power of a scalar annihilating a morphism conjugated by two isomorphisms annihilates the
morphism itself. -/
private theorem eq_zero_of_conj_eq_zero {C : Type*} [Category C] [Preadditive C]
    {S : Type*} [Ring S] [Linear S C] (a : S) {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (α : X ⟶ Y) (h : a • (eX.inv ≫ α ≫ eY.hom) = 0) : a • α = 0 := by
  simpa [Linear.smul_comp, Linear.comp_smul] using congrArg (fun f => eX.hom ≫ f ≫ eY.inv) h

/-- An object of `D(R)` whose derived sheafification is isomorphic to a perfect object is
perfect. -/
private theorem isPerfect_of_iso_mapDerivedCategory {M : DerivedCategory (ModuleCat.{u} R)}
    {E : DerivedCategory (Spec R).Modules}
    (e : (tilde.functor R).mapDerivedCategory.obj M ≅ E)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E) :
    StacksDraft.Perfect.IsPerfect M := by
  have hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory (Spec R).Modules =>
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) K) :=
    @Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.{u, u, u + 1}
      (Spec R).toRingedSpace inferInstance
  exact (isPerfect_tilde_iff M).1 (hiso.of_iso e.symm hE)

/-- Let `R` be a commutative ring, let `g ∈ R` and let `T = V(g)`. Let `E` and `E'` be objects of
`D(𝒪_{Spec R})` with quasi-coherent cohomology such that `E` is perfect and `E'` is
cohomologically supported on `T`. Then for every `α : E ⟶ E'` there is an `n ≥ 0` with
`g ^ n · α = 0`, the scalar being the global section of `𝒪_{Spec R}` named by `g`. -/
theorem exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn (g : R)
    {E E' : DerivedCategory (Spec R).Modules}
    (hEqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent)
    (hE'qc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E').IsQuasicoherent)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hE' : AlgebraicGeometry.CohomologySupportedOn (Spec R).ringCatSheaf
      (PrimeSpectrum.zeroLocus {g}) E')
    (α : E ⟶ E') :
    ∃ n : ℕ, Stacks.ExtensionByZero.globalScalar (Spec R).ringCatSheaf
      ((Scheme.ΓSpecIso R).inv g) ^ n • α = 0 := by
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E hEqc
  obtain ⟨N, ⟨eN⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E' hE'qc
  have hM : StacksDraft.Perfect.IsPerfect M := isPerfect_of_iso_mapDerivedCategory eM hE
  have hN : ∀ p : ℤ, Module.support R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) p).obj N) ⊆
      PrimeSpectrum.zeroLocus {g} :=
    support_homology_subset_of_cohomologySupportedOn g N
      (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso
        (Spec R).ringCatSheaf _ eN.symm hE')
  obtain ⟨n, hn⟩ :=
    exists_pow_smul_eq_zero_mapDerivedCategory g hM hN (eM.hom ≫ α ≫ eN.inv)
  exact ⟨n, eq_zero_of_conj_eq_zero _ eM.symm eN.symm α hn⟩

/-! ### Non-vacuity -/

/-- Over `R = ℤ` with `g = 2`, the hypotheses of
`Stacks.AffineTilde.exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn` hold for the
derived sheafification of the Koszul complex on `(2)` and that of `ℤ/2` in degree zero. -/
example (α : (tilde.functor (CommRingCat.of ℤ)).mapDerivedCategory.obj
      StacksDraft.Perfect.koszulTwo ⟶
    (tilde.functor (CommRingCat.of ℤ)).mapDerivedCategory.obj
      StacksDraft.Perfect.zmodTwoSingle) :=
  exists_pow_smul_eq_zero_of_isPerfect_of_cohomologySupportedOn (2 : ℤ)
    (fun n => AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj _ _ n)
    (fun n => AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj _ _ n)
    ((isPerfect_tilde_iff _).2 (StacksDraft.Perfect.isPerfect_extend_koszul _))
    (cohomologySupportedOn_mapDerivedCategory_tilde _ _
      StacksDraft.Perfect.support_homology_subset_zeroLocus_zmodTwoSingle)
    α

end Stacks.AffineTilde

end
