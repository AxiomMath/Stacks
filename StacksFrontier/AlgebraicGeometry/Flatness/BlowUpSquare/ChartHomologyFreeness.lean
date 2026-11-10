module

public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTriple
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CohomologyFiniteFreeLocus

/-!
# Freeness of the chart homology on the finite free cohomology locus

Let `(X, D, M)` be a triple as in Situation 0F8S and let `(U, f, M^•)` be an affine chart for
it, with coordinate ring `A = Γ(X, U)`.  If every point of `U` lies in the locus where the
cohomology sheaves of `M` have finite free stalks, then for every point `x ∈ U` and every
degree `i` the localization of `H^i(M^•)` at the prime of `A` corresponding to `x` is a free
module over the local ring of `A` there.

The argument restricts the cohomology sheaf `H^i(M)` to `U`, identifies it with the sheaf
associated with the `A`-module `H^i(M^•)` using the chart's representation of `M|_U` in the
derived category, and reads off the stalk at `x` as the localization of `H^i(M^•)`.

This is the input to the Zariski-local principality of the determinantal ideals,
`Stacks.DeterminantalIdeal.FreeHomology.exists_away_map_idealI_eq_span_pow_of_free_homology`.

## Main definitions

All in the namespace `AlgebraicGeometry.ComplexAndDivisorSituation`.

* `modulesHasDerivedCategory`: the derived category carried by a triple, read at the
  `Scheme.Modules` spelling of the category of `𝒪_X`-modules.
* `AffineChart.restrictToChart`, `AffineChart.chartTilde`: restriction of `𝒪_X`-modules to the
  chart, and passage from `Γ(X, U)`-modules to `𝒪_U`-modules through `U ≅ Spec Γ(X, U)`.
* `AffineChart.representsDerivedIso`: the chart's representation of `M|_U`, read as an
  isomorphism in the derived category of `𝒪_U`-modules.

## Main results

* `AffineChart.free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus`, in the
  namespace `AlgebraicGeometry.ComplexAndDivisorSituation`: on a chart contained in the finite
  free cohomology locus, every localization of every cohomology module of the chart's complex
  is free.

## References

* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.AlgebraicGeometry.ReflexiveEquivalence

attribute [local instance 10] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry

/-! ### Stalks of a restriction to an open subscheme -/

/-- The stalk of `F|_W` at `w` is free over the local ring of `W` if and only if the stalk of `F`
at the image of `w` is free over the local ring of the ambient scheme. -/
private theorem free_restrict_stalk_iff {X W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) :
    Module.Free (W.presheaf.stalk w) ((F.restrict j).presheaf.stalk w) ↔
      Module.Free (X.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
  have _h₁ : RingHomInvPair
      (openImmersionStalkRingEquiv j w : W.presheaf.stalk w →+* X.presheaf.stalk (j w))
      ((openImmersionStalkRingEquiv j w).symm :
        X.presheaf.stalk (j w) →+* W.presheaf.stalk w) := RingHomInvPair.of_ringEquiv _
  have _h₂ : RingHomInvPair
      ((openImmersionStalkRingEquiv j w).symm :
        X.presheaf.stalk (j w) →+* W.presheaf.stalk w)
      (openImmersionStalkRingEquiv j w : W.presheaf.stalk w →+* X.presheaf.stalk (j w)) :=
    RingHomInvPair.of_ringEquiv_symm _
  ⟨fun _ => Module.Free.of_equiv (restrictStalkSemilinearEquiv j F w),
    fun _ => Module.Free.of_equiv (restrictStalkSemilinearEquiv j F w).symm⟩

/-! ### Stalks of the sheaf associated with a module -/

/-- A localization of an `A`-module at a prime `p` is free over the local ring `A_p` as soon as
the stalk at `p` of the associated quasi-coherent sheaf on `Spec A` is free over the local ring
of `Spec A` there. -/
private theorem free_localizedModule_of_free_tilde_stalk {A : CommRingCat.{u}}
    (N : ModuleCat.{u} A) (p : PrimeSpectrum A)
    (h : letI := AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde N) p
      Module.Free ((Spec A).presheaf.stalk p) ((tilde N).presheaf.stalk p)) :
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N) := by
  let _inst := AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde N) p
  let eR : (Spec A).presheaf.stalk p ≃+* Localization.AtPrime p.asIdeal :=
    (StructureSheaf.stalkIso A p).symm.toRingEquiv
  let _ : Module (Localization.AtPrime p.asIdeal) ((tilde N).presheaf.stalk p) :=
    Module.compHom _ eR.symm.toRingHom
  have _hp : RingHomInvPair eR.toRingHom eR.symm.toRingHom := RingHomInvPair.of_ringEquiv eR
  have _hp' : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eR
  let eScalar : (tilde N).presheaf.stalk p ≃ₛₗ[eR.toRingHom] (tilde N).presheaf.stalk p :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' a z := by
        change a • z = eR.symm (eR a) • z
        simp }
  have hTloc : Module.Free (Localization.AtPrime p.asIdeal) ((tilde N).presheaf.stalk p) := by
    have _hfree : Module.Free ((Spec A).presheaf.stalk p) ((tilde N).presheaf.stalk p) := h
    exact Module.Free.of_equiv eScalar
  have _htower : IsScalarTower A (Localization.AtPrime p.asIdeal)
      ((tilde N).presheaf.stalk p) :=
    .of_algebraMap_smul fun r m => by
      change eR.symm (algebraMap A _ r) • m = r • m
      rw [show eR.symm (algebraMap A _ r) = (StructureSheaf.toStalk A p).hom r from
        (StructureSheaf.stalkIso A p).commutes r]
      rfl
  let eLoc : LocalizedModule p.asIdeal.primeCompl N
      ≃ₗ[Localization.AtPrime p.asIdeal] (tilde N).presheaf.stalk p :=
    LinearEquiv.extendScalarsOfIsLocalization p.asIdeal.primeCompl _
      (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) (tilde.toStalk N p).hom)
  exact Module.Free.of_equiv eLoc.symm

namespace ComplexAndDivisorSituation

/-- The derived category of a complex-and-divisor situation, at the `Scheme.Modules` spelling
of its category of modules. -/
public abbrev modulesHasDerivedCategory (S : ComplexAndDivisorSituation.{u, d}) :
    HasDerivedCategory.{d} S.X.Modules := S.hasDerivedCategory

attribute [local instance 100000] modulesHasDerivedCategory

/-- The `i`-th cohomology sheaf of the derived object of a complex-and-divisor situation. -/
private abbrev homologySheaf (S : ComplexAndDivisorSituation.{u, d}) (i : ℤ) : S.X.Modules :=
  (DerivedCategory.homologyFunctor (OXMod S.X.toRingedSpace) i).obj S.M

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- Restriction of `𝒪_X`-modules along the inclusion of the chart. -/
public abbrev restrictToChart (C : AffineChart S) : S.X.Modules ⥤ C.U.1.toScheme.Modules :=
  Scheme.Modules.restrictFunctor C.U.1.ι

/-- Passage from `Γ(X, U)`-modules to `𝒪_U`-modules through the isomorphism
`U ≅ Spec Γ(X, U)`. -/
public abbrev chartTilde (C : AffineChart S) :
    ModuleCat Γ(S.X, C.U) ⥤ C.U.1.toScheme.Modules :=
  tilde.functor Γ(S.X, C.U) ⋙ Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom

/-- The comparison, in the derived category of `𝒪_U`-modules, between the restriction of the
derived object of the situation and the complex of the chart. -/
public def representsDerivedIso (C : AffineChart S) :
    (restrictToChart C).mapDerivedCategory.obj S.M ≅
      (chartTilde C).mapDerivedCategory.obj
        (DerivedCategory.Q.obj C.complex.toCochainComplex) :=
  let E := Classical.choose C.represents
  let hE := Classical.choose_spec C.represents
  (restrictToChart C).mapDerivedCategory.mapIso (Classical.choice hE.1).symm ≪≫
    (restrictToChart C).mapDerivedCategoryFactors.app E ≪≫ Classical.choice hE.2 ≪≫
    ((chartTilde C).mapDerivedCategoryFactors.app C.complex.toCochainComplex).symm

/-- The restriction to the chart of the `i`-th cohomology sheaf of the situation is the sheaf
associated with the `i`-th cohomology module of the chart's complex. -/
public def chartHomologyIso (C : AffineChart S) (i : ℤ) :
    (restrictToChart C).obj
        ((DerivedCategory.homologyFunctor (OXMod S.X.toRingedSpace) i).obj S.M) ≅
      (chartTilde C).obj ((HomologicalComplex.homologyFunctor (ModuleCat Γ(S.X, C.U))
        (ComplexShape.up ℤ) i).obj C.complex.toCochainComplex) :=
  (((restrictToChart C).mapDerivedCategoryHomologyIso i).app S.M).symm ≪≫
    (DerivedCategory.homologyFunctor C.U.1.toScheme.Modules i).mapIso
      (representsDerivedIso C) ≪≫
    ((chartTilde C).mapDerivedCategoryHomologyIso i).app
      (DerivedCategory.Q.obj C.complex.toCochainComplex) ≪≫
    (chartTilde C).mapIso ((DerivedCategory.homologyFunctorFactors
      (ModuleCat Γ(S.X, C.U)) i).app C.complex.toCochainComplex)

/-- **On a chart contained in the finite free cohomology locus the chart complex has free
localized cohomology.** If every point of the affine chart `(U, f, M^•)` lies in the locus
where all cohomology stalks of `M` are finite free, then for every point `x` of `U` and every
degree `i` the localization of `H^i(M^•)` at the prime of `Γ(X, U)` corresponding to `x` is a
free module over the local ring there. -/
theorem free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus
    {S : ComplexAndDivisorSituation.{u, d}} (C : AffineChart S)
    (hCW : (C.U.1 : Set S.X) ⊆ RingedSpace.cohomologyFiniteFreeLocus S.M)
    (x : C.U.1.toScheme) (i : ℤ) :
    Module.Free (Localization.AtPrime (C.U.2.primeIdealOf x).asIdeal)
      (LocalizedModule (C.U.2.primeIdealOf x).asIdeal.primeCompl
        ((HomologicalComplex.homologyFunctor (ModuleCat Γ(S.X, C.U))
          (ComplexShape.up ℤ) i).obj C.complex.toCochainComplex)) := by
  have h₁ : Module.Free (C.U.1.toScheme.presheaf.stalk x)
      (((restrictToChart C).obj (homologySheaf S i)).presheaf.stalk x) :=
    (free_restrict_stalk_iff C.U.1.ι (homologySheaf S i) x).2 (hCW x.2 i).1
  have h₂ : Module.Free (C.U.1.toScheme.presheaf.stalk x)
      (((chartTilde C).obj ((HomologicalComplex.homologyFunctor (ModuleCat Γ(S.X, C.U))
        (ComplexShape.up ℤ) i).obj C.complex.toCochainComplex)).presheaf.stalk x) :=
    Module.Free.of_equiv (stalkLinearEquivOfIso (chartHomologyIso C i) x)
  exact free_localizedModule_of_free_tilde_stalk _ (C.U.2.primeIdealOf x)
    ((free_restrict_stalk_iff C.U.2.isoSpec.hom _ x).1 h₂)

end AffineChart

end ComplexAndDivisorSituation

end AlgebraicGeometry

end
