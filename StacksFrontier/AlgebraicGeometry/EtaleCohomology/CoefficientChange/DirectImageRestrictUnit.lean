module

public import StacksFrontier.Algebra.Homology.DerivedCategory.FaithfulConservative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DirectImageForgetUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.RestrictForgetIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded

/-!
# The derived direct image is computed by a restricted K-injective complex

Let `φ : Λ₁ → Λ₂` be a homomorphism of rings and `f : X ⟶ Y` a morphism of schemes.  A
K-injective complex `I` of sheaves of `Λ₂`-modules on the small étale site of `X` is *not*
K-injective after restricting its coefficients along `φ`, but it still computes the derived
direct image of sheaves of `Λ₁`-modules: the derivation unit of `Rf_*` for `Λ₁`-coefficients is
invertible at `res_φ I`.

This is the one non-formal input to the first diagram of [Stacks, Tag 0GL6], the commutation of
`Rf_!` with restriction of coefficients.  The source's argument is followed: it is
[Stacks, Tag 0D6J] -- that an underlying abelian complex of a K-injective complex of modules
computes the derived direct image of abelian sheaves -- applied twice, once for each coefficient
ring.

## Main results

* `Stacks.EtaleCohomology.quasiIso_etaleAbelianDirectImage_map_of_isIso_unit`: degreewise direct
  image of abelian étale sheaves takes a quasi-isomorphism to a quasi-isomorphism whenever the
  derived unit is invertible at both of its ends.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_restrictScalars`:
  the statement above.

## Implementation notes

The argument has three moves, and the order matters because each one is only available after the
previous.

*The restricted complex is compared with integral coefficients, not with `I`.*  Let `q : res_φ I
⟶ J` be a K-injective resolution over `Λ₁`.  What has to be shown is that the degreewise
`Λ₁`-linear direct image of `q` is a quasi-isomorphism; the unit is then invertible at `res_φ I`
by `Stacks.Injectives.KInjectiveResolution.isIso_app_of_quasiIso_resolution`, two of the three
maps in its naturality square being known.

*Quasi-isomorphy descends to abelian coefficients and is detected there.*  Forgetting the module
structure is exact, so it preserves homology, and faithful, so by
`Stacks.Cohomology.reflectsIsomorphisms_of_faithful` it reflects isomorphisms; hence
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` turns the goal into the same statement
for the abelian direct image of the forgotten `q`.  Faithfulness is all that is used -- forgetting
the module structure is very far from full -- which is why the conservativity statements of
`StacksFrontier/Algebra/Homology/DerivedCategory/FaithfulConservative.lean` exist at all.

*Tag 0D6J is applied at both coefficient rings.*  The abelian derived unit is invertible at the
forgotten `J` because `J` is K-injective over `Λ₁`, and at the forgotten `res_φ I` because that
complex is *canonically isomorphic* -- not equal -- to the forgotten `I`, by
`Stacks.EtaleCohomology.etaleRestrictForgetToIntIso`, and `I` is K-injective over `Λ₂`.  This is
where the generality of 0D6J in the coefficient ring is used: a version stated for one fixed
coefficient ring would give only one of the two.

Two of the three squares of underived functors involved are equalities and one is not, and the
asymmetry is exactly the one recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CoefficientChange/RestrictForgetIso.lean`:
direct image is precomposition of the underlying presheaf with base change while restriction of
coefficients and forgetting are postcomposition with a functor of coefficient categories, so the
two commute by associativity of composition of functors, whereas comparing two coefficient
changes with each other is a statement about `Module ℤ` instances and is not definitional.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section Squares

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **Restricting the coefficients of an étale module sheaf and then forgetting to abelian
groups is forgetting to abelian groups**, canonically.  The abelian-coefficient form of
`Stacks.EtaleCohomology.etaleRestrictForgetToIntIso`, obtained from it by the identity
`Stacks.EtaleCohomology.etaleModuleForgetToAbelian_eq`. -/
def etaleRestrictForgetToAbelianIso (X : Scheme.{u}) :
    etaleModuleForgetToAbelian.{u, r} Λ₂ X ≅
      etaleModuleRestrictScalarsUniv.{u, r} φ X ⋙ etaleModuleForgetToAbelian.{u, r} Λ₁ X :=
  Functor.isoWhiskerRight (etaleRestrictForgetToIntIso.{u, r} φ X)
      (etaleIntCoefficientEquivalence.{u, r} X).inverse ≪≫
    Functor.associator _ _ _

/-- **Direct image commutes with restriction of coefficients on the nose.**  Both sides
precompose the underlying presheaf with base change and postcompose it with restriction of
scalars, in the two orders. -/
theorem etaleModuleDirectImage_comp_restrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDirectImage.{u, r} Λ₂ f ⋙ etaleModuleRestrictScalarsUniv.{u, r} φ Y =
      etaleModuleRestrictScalarsUniv.{u, r} φ X ⋙ etaleModuleDirectImage.{u, r} Λ₁ f :=
  rfl

/-- **Direct image commutes with forgetting to abelian groups on the nose.** -/
theorem etaleModuleDirectImage_comp_forgetToAbelian (Λ : Type r) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleForgetToAbelian.{u, r} Λ Y =
      etaleModuleForgetToAbelian.{u, r} Λ X ⋙ etaleAbelianDirectImage.{u, r} f :=
  rfl

end Squares

section AbelianUnit

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Degreewise direct image of abelian étale sheaves takes a quasi-isomorphism to a
quasi-isomorphism whenever the derived unit is invertible at both of its ends.**  Two of the
three maps in the naturality square of the unit at the given quasi-isomorphism are then
isomorphisms, and so is the fourth, the localization of a quasi-isomorphism; the degreewise
direct image is the remaining one. -/
theorem quasiIso_etaleAbelianDirectImage_map_of_isIso_unit
    {M N : CochainComplex (EtaleAbelianSheaves.{u, r} X) ℤ} (g : M ⟶ N) (hg : QuasiIso g)
    (hM : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, r} f).app
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (ComplexShape.up ℤ)).obj M)))
    (hN : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, r} f).app
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (ComplexShape.up ℤ)).obj N))) :
    QuasiIso (((etaleAbelianDirectImage.{u, r} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := by
  have := hg
  have := hM
  have := hN
  have h₁ : IsIso ((DerivedCategory.Qh ⋙ etaleAbelianDerivedDirectImage.{u, r} f).map
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X)
        (ComplexShape.up ℤ)).map g)) :=
    inferInstanceAs (IsIso ((etaleAbelianDerivedDirectImage.{u, r} f).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X)
        (ComplexShape.up ℤ)).map g))))
  have h₂ : IsIso ((etaleAbelianPushforwardToDerivedCategory.{u, r} f).map
        ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (ComplexShape.up ℤ)).map g) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, r} f).app
        ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X)
          (ComplexShape.up ℤ)).obj N)) := by
    rw [(etaleAbelianDerivedDirectImageUnit.{u, r} f).naturality]
    infer_instance
  have h₃ : IsIso ((etaleAbelianPushforwardToDerivedCategory.{u, r} f).map
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X)
        (ComplexShape.up ℤ)).map g)) :=
    IsIso.of_isIso_comp_right _ ((etaleAbelianDerivedDirectImageUnit.{u, r} f).app
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (ComplexShape.up ℤ)).obj N))
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    ← DerivedCategory.isIso_Qh_map_iff, ← Functor.mapHomotopyCategory_map]
  exact h₃

end AbelianUnit

section Main

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A K-injective complex of `Λ₂`-modules computes the derived direct image of
`Λ₁`-modules after restriction of coefficients.**  The derivation unit of the unbounded `Rf_*`
for `Λ₁`-coefficients is invertible at `res_φ I` for `I` K-injective over `Λ₂`, even though
`res_φ I` is not itself K-injective.

This is the non-formal input to the first diagram of [Stacks, Tag 0GL6]. -/
theorem isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_restrictScalars
    (I : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) (hI : I.IsKInjective) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f).app
      (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) := by
  have := hI
  obtain ⟨NR⟩ := Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective
    (EtaleModules.{u, r} Λ₁ X)
  set Z := ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have hq : QuasiIso (NR.inclusion.app Z) := NR.quasiIso Z
  have hJ : (NR.functor.obj Z).IsKInjective := NR.isKInjective Z
  refine Stacks.Injectives.KInjectiveResolution.isIso_app_of_quasiIso_resolution
    DerivedCategory.Q _ _
    (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
      (etaleModuleDirectImage.{u, r} Λ₁ f)) (NR.inclusion.app Z) hJ hq ?_
  change IsIso (DerivedCategory.Q.map
    (((etaleModuleDirectImage.{u, r} Λ₁ f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (NR.inclusion.app Z)))
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : (etaleModuleForgetToAbelian.{u, r} Λ₁ Y).ReflectsIsomorphisms :=
    Stacks.Cohomology.reflectsIsomorphisms_of_faithful _
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (etaleModuleForgetToAbelian.{u, r} Λ₁ Y)]
  refine quasiIso_etaleAbelianDirectImage_map_of_isIso_unit.{u, r} f
    (((etaleModuleForgetToAbelian.{u, r} Λ₁ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (NR.inclusion.app Z)) inferInstance ?_ ?_
  · refine (NatTrans.isIso_app_iff_of_iso (etaleAbelianDerivedDirectImageUnit.{u, r} f)
      ((HomotopyCategory.quotient (EtaleAbelianSheaves.{u, r} X) (ComplexShape.up ℤ)).mapIso
        ((NatIso.mapHomologicalComplex (etaleRestrictForgetToAbelianIso.{u, r} φ X)
          (ComplexShape.up ℤ)).app I))).mp ?_
    exact etaleAbelianDerivedDirectImageUnit_isIso_at_underlying_kInjective.{u, r} Λ₂ f I
  · exact etaleAbelianDerivedDirectImageUnit_isIso_at_underlying_kInjective.{u, r} Λ₁ f
      (NR.functor.obj Z)

end Main

end Stacks.EtaleCohomology

end
