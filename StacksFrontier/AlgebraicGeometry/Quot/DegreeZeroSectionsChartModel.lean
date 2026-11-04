module

public import StacksFrontier.AlgebraicGeometry.Quot.ChartStrictlyPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.FreeComplexLocalSplitting
public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsLocal
public import StacksFrontier.AlgebraicGeometry.Quot.MatrixKernelRepresentable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes

/-!
# The degree-zero sections functor over a chart carrying a strictly perfect approximation

Let `P₀` be a K-flat complex with flat terms representing an object `K` of `D(𝒪_X)` on an
algebraic space `X`, and let `V` be an étale chart of `X` over which the pullback of `P₀` is
approximated, above degree `-2`, by a strictly perfect complex `P`.  Then on the schemes over `V`
the degree-zero sections functor of `P₀` is that of `P`, and if `H⁻¹(Lg^*K)` vanishes for every
`g`, it is Zariski locally on every scheme over `V` the kernel functor of a matrix of functions,
hence represented by the scheme of solutions of the linear equations of the matrix.  This is the
local part of the proof of Stacks 08JX, part (1).

## Main results

* `AlgebraicGeometry.Space.isKFlat_quotient_of_isStrictlyPerfect`,
  `AlgebraicGeometry.Space.isKFlat_quotient_pull`: K-flatness of strictly perfect complexes and of
  pullbacks of K-flat complexes with flat terms.
* `AlgebraicGeometry.Space.isZero_homology_pull_of_hasVanishingDegreeNegOne`: the vanishing
  hypothesis of Stacks 08JX, part (1), read on a K-flat representative.
* `AlgebraicGeometry.Space.chartRestrictionIso`: the degree-zero sections functor of `P₀` on the
  schemes over `V` is that of `P`.
* `AlgebraicGeometry.Space.exists_open_restriction_matKerIso`: the local model.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Costructured arrows along a composite are costructured arrows along the two morphisms in
turn.** -/
def _root_.CategoryTheory.CostructuredArrow.mapCompIso {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {T T' T'' : D} (f : T ⟶ T') (g : T' ⟶ T'') :
    CostructuredArrow.map (S := F) (f ≫ g) ≅ CostructuredArrow.map f ⋙ CostructuredArrow.map g :=
  NatIso.ofComponents (fun A => CostructuredArrow.isoMk (Iso.refl _) (by simp))
    (fun _ => by ext; simp)

/-! ### K-flatness -/

/-- **A strictly perfect complex of modules on an algebraic space is K-flat with flat terms.** -/
theorem isKFlat_quotient_of_isStrictlyPerfect (Y : AlgebraicSpaces B S hS)
    (P : CochainComplex (toposModules B S hS Y) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O) P) :
    IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) :=
  ⟨Stacks.SheafOfModules.isKFlat_of_isStrictlyPerfect (Y := smallEtaleRingedSite B S hS Y.1 Y.2)
      P hP,
    fun i => Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree'
      (Y := smallEtaleRingedSite B S hS Y.1 Y.2) (P.X i) (hP.termDirectSummand i)⟩

/-- **The pullback of a K-flat complex with flat terms is K-flat with flat terms**, for the
inverse image of `𝒪`-modules of Stacks 03LU (Stacks 0G7E). -/
theorem isKFlat_quotient_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (P : CochainComplex (toposModules B S hS Y) ℤ)
    (hP : IsKFlat (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :
    IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  have h := Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
    (smallEtaleRingedToposHom B S hS f) _ hP
  have e : (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules =
      (toposModulePullbackData B S hS).pull f :=
    congrArg (fun h => h.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom (smallEtaleRingedToposHom B S hS f))
  change IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) at h
  have key : ∀ (G : toposModules B S hS Y ⥤ toposModules B S hS X) [G.PreservesZeroMorphisms],
      (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules = G →
        IsKFlat (Y := smallEtaleRingedTopos B S hS X)
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
    intro G _ hG
    subst hG
    exact h
  exact key _ e


/-! ### The vanishing hypothesis on a K-flat representative -/

/-- **The hypothesis of Stacks 08JX, part (1), on a K-flat representative.**  If `H⁻¹(Lg^*K)`
vanishes for every scheme `g : T → X` and `P₀` is a K-flat complex with flat terms representing
`K`, then `H⁻¹` of the degreewise pullback of `P₀` to every scheme over `X` vanishes: on such a
complex the derived pullback is computed degreewise (Stacks 06YY). -/
theorem isZero_homology_pull_of_hasVanishingDegreeNegOne {X : AlgebraicSpaces B S hS}
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS) {K : derivedModules B S hS X}
    (hvan : HasVanishingDegreeNegOneDerivedPullback hL K)
    (P₀ : CochainComplex (toposModules B S hS X) ℤ)
    (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
    (e : DerivedCategory.Q.obj P₀ ≅ K) {T : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj T ⟶ X) :
    IsZero (((((toposModulePullbackData B S hS).pull h).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀).homology (-1)) :=
  (hvan (CostructuredArrow.mk h)).of_iso
    (((DerivedCategory.homologyFunctorFactors (toposModules B S hS _) (-1)).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (toposModules B S hS _) (-1)).mapIso
        ((derivedPullbackQIso h P₀ hP₀).symm ≪≫
          (smallEtaleDerivedModulePullback B S hS h).mapIso e))


/-- The inverse image of a complex along a composite is the iterated inverse image. -/
def pullCompIsoComplex {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (toposModules B S hS Z) ℤ) :
    (((toposModulePullbackData B S hS).pull (f ≫ g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ≅
      (((toposModulePullbackData B S hS).pull f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((toposModulePullbackData B S hS).pull g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  (NatIso.mapHomologicalComplex ((toposModulePullbackData B S hS).compIso f g)
      (ComplexShape.up ℤ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app K).symm

/-- The inverse image of a strictly perfect complex is strictly perfect (Stacks 08H3). -/
theorem isStrictlyPerfect_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {P : CochainComplex (toposModules B S hS Y) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O) P) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)
      ((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  SheafOfModules.isStrictlyPerfect_map ((toposModulePullbackData B S hS).pull f)
    (modulePullbackUnitIsoTopos f) hP

/-! ### The degree-zero sections functor over a chart -/

section Chart

/-- The étale chart `V` of `X` as a morphism of algebraic spaces out of the algebraic space of
its scheme, `AlgebraicGeometry.Space.chartToSpace` with its source spelled through
`AlgebraicGeometry.Space.schemeSpaceFunctor`. -/
abbrev chartMorphism {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1) :
    (schemeSpaceFunctor B S hS).obj V.1.left ⟶ X :=
  chartToSpace B S hS X V

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {Y₀ : BigFppfOver B S hS} (g : (schemeSpaceFunctor B S hS).obj Y₀ ⟶ X)
  (P : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj Y₀)) ℤ)
  (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS ((schemeSpaceFunctor B S hS).obj Y₀).1
      ((schemeSpaceFunctor B S hS).obj Y₀).2).O) P)
  (γ : P ⟶ (((toposModulePullbackData B S hS).pull (g)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P₀)
  (hiso : ∀ j : ℤ, -2 < j → IsIso (HomologicalComplex.homologyMap γ j))
  (hepi : Epi (HomologicalComplex.homologyMap γ (-2)))

include hP₀ hP hiso hepi in
/-- The approximation induces an isomorphism of degree-zero sections functors on the schemes over
the chart. -/
theorem isIso_degreeZeroSectionsMap_chart :
    IsIso (degreeZeroSectionsMap (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) γ) :=
  isIso_degreeZeroSectionsMap_of_approximation _
    (isKFlat_quotient_of_isStrictlyPerfect _ P hP)
    (isKFlat_quotient_pull (g) P₀ hP₀) γ (-2) (by norm_num) hiso hepi

/-- **On the schemes over `Y₀`, the degree-zero sections functor of `P₀` is that of the
strictly perfect approximation**, read along `a : c ⟶ Y₀` for a scheme `c`. -/
def chartRestrictionIso {c : BigFppfOver B S hS} (a : c ⟶ Y₀) :
    (CostructuredArrow.map ((schemeSpaceFunctor B S hS).map a ≫ g)).op ⋙
        degreeZeroSectionsFunctor (schemesOverCone X) P₀ ≅
      degreeZeroSectionsFunctor (schemesOverCone ((schemeSpaceFunctor B S hS).obj c))
        ((((toposModulePullbackData B S hS).pull
          ((schemeSpaceFunctor B S hS).map a)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  haveI := isIso_degreeZeroSectionsMap_chart P₀ hP₀ g P hP γ hiso hepi
  let f := (schemeSpaceFunctor B S hS).map a
  let D := degreeZeroSectionsFunctor (schemesOverCone X) P₀
  let e₁ : (CostructuredArrow.map (f ≫ g)).op ⋙ D ≅
      ((CostructuredArrow.map f).op ⋙ (CostructuredArrow.map g).op) ⋙ D :=
    Functor.isoWhiskerRight (NatIso.op (CostructuredArrow.mapCompIso f g).symm) D
  let e₂ : ((CostructuredArrow.map f).op ⋙ (CostructuredArrow.map g).op) ⋙ D ≅
      (CostructuredArrow.map f).op ⋙ ((CostructuredArrow.map g).op ⋙ D) :=
    Functor.associator _ _ _
  let e₃ : (CostructuredArrow.map f).op ⋙ ((CostructuredArrow.map g).op ⋙ D) ≅
      (CostructuredArrow.map f).op ⋙ degreeZeroSectionsFunctor
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀))
        ((((toposModulePullbackData B S hS).pull g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P₀) :=
    Functor.isoWhiskerLeft _ (degreeZeroSectionsPrecompIso g P₀)
  let e₄ : (CostructuredArrow.map f).op ⋙ degreeZeroSectionsFunctor
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀))
        ((((toposModulePullbackData B S hS).pull g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P₀) ≅
      (CostructuredArrow.map f).op ⋙ degreeZeroSectionsFunctor
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) P :=
    Functor.isoWhiskerLeft _
      (asIso (degreeZeroSectionsMap (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) γ)).symm
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ degreeZeroSectionsPrecompIso f P


include hP in
/-- The pullback of a strictly perfect complex to a scheme has its terms retracts of free
modules. -/
theorem exists_retract_pull {c : BigFppfOver B S hS} (a : c ⟶ Y₀) (j : ℤ) :
    ∃ (n : ℕ) (i : ((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).X j ⟶ freeObj (unitT c) n)
      (r : freeObj (unitT c) n ⟶ ((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map a)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X j),
      i ≫ r = 𝟙 _ := by
  have hP' : IsStrictlyPerfect
      (ringedToposStructureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj Y₀)) P := hP
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free
    (ringedToposStructureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj Y₀)) (P.X j)).1
      (hP'.termDirectSummand j)
  let ι : SheafOfModules.free
      (R := ringedToposStructureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj Y₀))
      (ULift.{u} (Fin n)) ≅ freeObj (unitT Y₀) n :=
    Sigma.whiskerEquiv (f := fun _ : ULift.{u} (Fin n) => SheafOfModules.unit
        (ringedToposStructureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj Y₀)))
      (g := fun _ : Fin n => unitT Y₀) Equiv.ulift (fun _ => Iso.refl _) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n => unitT Y₀)).symm
  let ρ : Retract (P.X j) (freeObj (unitT Y₀) n) :=
    (⟨i, r, hir⟩ : Retract _ _).trans ι.retract
  let F := (toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map a)
  let ρ' : Retract (F.obj (P.X j)) (freeObj (unitT c) n) :=
    (ρ.map F).trans (pullFreeIso ((schemeSpaceFunctor B S hS).map a) n).retract
  exact ⟨n, ρ'.i, ρ'.r, ρ'.retract⟩

variable {K : derivedModules B S hS X} (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
  (hvan : HasVanishingDegreeNegOneDerivedPullback hL K) (e : DerivedCategory.Q.obj P₀ ≅ K)

include hvan hP₀ e hP hiso hepi in
/-- **The pullback of the approximation to a scheme over the chart has vanishing `H⁻¹` after
every further pullback**, by the vanishing hypothesis of Stacks 08JX, part (1): the
approximation is an isomorphism on `H⁻¹` after every pullback. -/
theorem isZero_homology_pull_chart {c : BigFppfOver B S hS} (a : c ⟶ Y₀)
    (T' : BigFppfOver B S hS) (t' : T' ⟶ c) :
    IsZero (((((toposModulePullbackData B S hS).pull
      ((schemeSpaceFunctor B S hS).map t')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((((toposModulePullbackData B S hS).pull
          ((schemeSpaceFunctor B S hS).map a)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)).homology (-1)) := by
  let h := (schemeSpaceFunctor B S hS).map (t' ≫ a)
  have : ((toposModulePullbackData B S hS).pull g).Additive := toposModulePullbackData_additive g
  have : ((toposModulePullbackData B S hS).pull h).Additive := toposModulePullbackData_additive h
  have h0 := isZero_homology_pull_of_hasVanishingDegreeNegOne hL hvan P₀ hP₀ e (h ≫ g)
  have h1 : IsZero (((((toposModulePullbackData B S hS).pull h).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((((toposModulePullbackData B S hS).pull g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P₀)).homology (-1)) :=
    h0.of_iso (HomologicalComplex.homologyMapIso (pullCompIsoComplex h g P₀) (-1)).symm
  have hq := quasiIsoAt_pullback_of_approximation h (isKFlat_quotient_of_isStrictlyPerfect _ P hP)
    (isKFlat_quotient_pull g P₀ hP₀) γ (-2) hiso hepi (-1) (by norm_num)
  rw [quasiIsoAt_iff_isIso_homologyMap] at hq
  have h2 : IsZero (((((toposModulePullbackData B S hS).pull h).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology (-1)) :=
    h1.of_iso (asIso (HomologicalComplex.homologyMap
      ((((toposModulePullbackData B S hS).pull h).mapHomologicalComplex (ComplexShape.up ℤ)).map γ)
        (-1)))
  exact h2.of_iso (HomologicalComplex.homologyMapIso (pullCompComplexIso t' a P) (-1)).symm

include hvan hP₀ e hP hiso hepi in
/-- **Stacks 08JX, the local model on a chart.**  For every scheme `c` over the chart `V` and
every point of `c`, there is an open neighbourhood `d` of the point on which the degree-zero
sections functor of `P₀` is the kernel functor of a matrix of functions. -/
theorem exists_open_restriction_matKerIso {c : BigFppfOver B S hS} (a : c ⟶ Y₀)
    (x : (BigFppfOver.toScheme B S hS).obj c) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ c),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map t).base ∧
        ∃ (r m : ℕ) (N : Matrix (Fin r) (Fin m) (Gam d)),
          Nonempty ((CostructuredArrow.map ((schemeSpaceFunctor B S hS).map (t ≫ a) ≫
              g)).op ⋙ degreeZeroSectionsFunctor (schemesOverCone X) P₀ ≅
            matKerFunctor d N) := by
  obtain ⟨d, t, hoi, hx, r, m, N, ⟨eN⟩⟩ := exists_open_matKerIso _ (exists_retract_pull P hP a)
    (isZero_homology_pull_chart P₀ hP₀ g P hP γ hiso hepi hL hvan e a) x
  exact ⟨d, t, hoi, hx, r, m, N, ⟨chartRestrictionIso P₀ hP₀ g P hP γ hiso hepi (t ≫ a) ≪≫
    degreeZeroSectionsIsoOfIso _ (pullCompComplexIso t a P) ≪≫ eN⟩⟩


include hP₀ hP hiso hepi in
/-- **The pullback of the approximation to a scheme over `Y₀` is again a strictly perfect
approximation**, of the pullback of `P₀` along the composite. -/
theorem exists_approximation_pull {c : BigFppfOver B S hS} (a : c ⟶ Y₀) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS ((schemeSpaceFunctor B S hS).obj c).1
        ((schemeSpaceFunctor B S hS).obj c).2).O)
      ((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map a)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
    ∃ φ : (((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map a)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
          (((toposModulePullbackData B S hS).pull
            ((schemeSpaceFunctor B S hS).map a ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P₀,
      (∀ j : ℤ, -2 < j → IsIso (HomologicalComplex.homologyMap φ j)) ∧
        Epi (HomologicalComplex.homologyMap φ (-2)) := by
  let f := (schemeSpaceFunctor B S hS).map a
  let c' := pullCompIsoComplex f g P₀
  have hK := isKFlat_quotient_of_isStrictlyPerfect _ P hP
  have hK' := isKFlat_quotient_pull g P₀ hP₀
  exact ⟨isStrictlyPerfect_pull f hP,
    (((toposModulePullbackData B S hS).pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map γ ≫
      c'.inv, fun j hj => RingedSite.isIso_homologyMap_comp_iso _ c'.symm j
        ((quasiIsoAt_iff_isIso_homologyMap _ _).1
          (quasiIsoAt_pullback_of_approximation f hK hK' γ (-2) hiso hepi j hj)),
    RingedSite.epi_homologyMap_comp_iso _ c'.symm (-2)
      (epi_homologyMap_pullback_of_approximation f hK hK' γ (-2) hiso hepi)⟩

end Chart

end AlgebraicGeometry.Space

end
