module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackHomComplexUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackModelAbstract
public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso

/-!
# The cochain-level comparison of Hom complexes at a strictly perfect source

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The cochain-level comparison

`h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`,

`Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap`, is an isomorphism of
complexes whenever `E` has finitely many nonzero terms, each of them a direct summand of a finite
free `𝒪_Y`-module, for every complex `F`.

## Main results

All names below are in the namespace `Stacks.Cohomology.DerivedInternalHomPullback`.

* `isIso_pullbackHomComplexMap_shiftedUnit`: the comparison is an isomorphism at every shift of
  the structure sheaf placed in degree zero.
* `isIso_pullbackHomComplexMap_of_degreewiseSplit`: two out of three along a degreewise split
  short complex of sources.
* `isIso_pullbackHomComplexMap_of_isFiniteFreeSummand`: the comparison is an isomorphism at a
  bounded complex of direct summands of finite free modules.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local implicit_reducible] structureSheafRing StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal

attribute [local instance] hasMapBifunctorSpace

/-! ### Tensoring with a shift of the structure sheaf -/

section ShiftedUnit

variable (Z : RingedSpace.{u, u})

/-- The right unit constraint of the total tensor complex, as an isomorphism of functors. -/
def rightUnitorNatIsoComplex :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map₂CochainComplex).flip.obj
        (𝟙_ (CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)) ≅
      𝟭 _ :=
  NatIso.ofComponents
    (fun W : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ => ρ_ W)
    (fun g => MonoidalCategory.rightUnitor_naturality g)

/-- Tensoring on the right by a shift of the structure sheaf in degree zero is an equivalence. -/
instance isEquivalence_tensorRightOf_shiftedUnitComplex (m : ℤ) :
    (Stacks.ProjectionFormula.tensorRightOf
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))
      ((𝟙_ (CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ))⟦m⟧)).IsEquivalence :=
  Functor.isEquivalence_tensorRightOf_shiftedUnit
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map₂CochainComplex) _
    (rightUnitorNatIsoComplex Z) m

end ShiftedUnit

section PullbackShiftedUnit

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The pullback of a shift of the structure sheaf in degree zero is that shift of the structure
sheaf. -/
def pullbackShiftedUnitIso (m : ℤ) :
    (pullbackComplex h).obj ((𝟙_ (CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))⟦m⟧) ≅
      (𝟙_ (CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ))⟦m⟧ :=
  ((pullbackComplex h).commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (CategoryTheory.Functor.Monoidal.εIso (pullbackComplex h)).symm

/-- Tensoring on the right by the pullback of a shift of the structure sheaf is an
equivalence. -/
instance isEquivalence_tensorRightOf_pullbackShiftedUnit (m : ℤ) :
    (Stacks.ProjectionFormula.tensorRightOf
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
      ((pullbackComplex h).obj ((𝟙_ (CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))⟦m⟧))).IsEquivalence :=
  Functor.isEquivalence_tensorRightOf_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map₂HomologicalComplexReg
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (pullbackShiftedUnitIso h m) inferInstance

/-- **The cochain-level comparison is an isomorphism at every shift of the structure sheaf.** -/
theorem isIso_pullbackHomComplexMap_shiftedUnit (m : ℤ)
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h ((𝟙_ (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))⟦m⟧) F) :=
  Transpose.isIso_homComparison_of_isEquivalence (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h)
    (fun _ target factor result sourceHom homMorphism =>
      (AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source
        (AlgebraicGeometry.RingedSpace.ringedSite Y) sourceHom factor result homMorphism).trans
          (congrArg (fun morphism => morphism ≫
            AlgebraicGeometry.RingedSite.curryHomEquivPair
              (AlgebraicGeometry.RingedSpace.ringedSite Y) target factor result homMorphism)
            (CategoryTheory.uncurry_map_mkHom_id
              (Functor.map₂HomologicalComplexReg
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
                (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
              sourceHom factor)).symm)
    (fun _ target factor result sourceHom homMorphism =>
      (AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source
        (AlgebraicGeometry.RingedSpace.ringedSite X) sourceHom factor result homMorphism).trans
          (congrArg (fun morphism => morphism ≫
            AlgebraicGeometry.RingedSite.curryHomEquivPair
              (AlgebraicGeometry.RingedSpace.ringedSite X) target factor result homMorphism)
            (CategoryTheory.uncurry_map_mkHom_id
              (Functor.map₂HomologicalComplexReg
                (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
                (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
              sourceHom factor)).symm)
    ((𝟙_ (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))⟦m⟧) F

end PullbackShiftedUnit

/-! ### The dévissage along the stupid filtration -/

section Devissage

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- A zero source gives an isomorphism, both complexes being zero. -/
theorem isIso_pullbackHomComplexMap_of_isZero
    {E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (hE : IsZero E)
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h E F) :=
  ⟨⟨0, ((pullbackComplex h).map_isZero
      (AlgebraicGeometry.RingedSite.sheafHomComplex_isZero_of_isZero
        (AlgebraicGeometry.RingedSpace.ringedSite Y) hE F)).eq_of_src _ _,
    (AlgebraicGeometry.RingedSite.sheafHomComplex_isZero_of_isZero
      (AlgebraicGeometry.RingedSpace.ringedSite X) ((pullbackComplex h).map_isZero hE)
        ((pullbackComplex h).obj F)).eq_of_src _ _⟩⟩

/-- The comparison along a short complex of sources, as a morphism of short complexes from the
pullback of the internal Hom row to the internal Hom row of the pullback. -/
def pullbackHomShortComplexMap
    (S : ShortComplex (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (AlgebraicGeometry.RingedSite.internalHomShortComplex
        (AlgebraicGeometry.RingedSpace.ringedSite Y) S F).map (pullbackComplex h) ⟶
      AlgebraicGeometry.RingedSite.internalHomShortComplex
        (AlgebraicGeometry.RingedSpace.ringedSite X) (S.map (pullbackComplex h))
        ((pullbackComplex h).obj F) where
  τ₁ := pullbackHomComplexMap h S.X₃ F
  τ₂ := pullbackHomComplexMap h S.X₂ F
  τ₃ := pullbackHomComplexMap h S.X₁ F
  comm₁₂ := (pullbackHomComplexMap_naturality_source h S.g F).symm
  comm₂₃ := (pullbackHomComplexMap_naturality_source h S.f F).symm

/-- **Two out of three for a degreewise split short complex of sources.** If `S` is split in each
degree and the comparison is an isomorphism at `S.X₁` and `S.X₃`, it is an isomorphism at
`S.X₂`. -/
theorem isIso_pullbackHomComplexMap_of_degreewiseSplit
    (S : ShortComplex (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))
    (σ : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).Splitting)
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (h₁ : IsIso (pullbackHomComplexMap h S.X₁ F)) (h₃ : IsIso (pullbackHomComplexMap h S.X₃ F)) :
    IsIso (pullbackHomComplexMap h S.X₂ F) := by
  have hS₁ : ((AlgebraicGeometry.RingedSite.internalHomShortComplex
      (AlgebraicGeometry.RingedSpace.ringedSite Y) S F).map (pullbackComplex h)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
      ((AlgebraicGeometry.RingedSite.internalHomTermwiseSplitting
        (AlgebraicGeometry.RingedSpace.ringedSite Y) S F σ n).map
          (StacksDraft.KFlat.modulePullback h)).shortExact)
  have hS₂ : (AlgebraicGeometry.RingedSite.internalHomShortComplex
      (AlgebraicGeometry.RingedSpace.ringedSite X) (S.map (pullbackComplex h))
        ((pullbackComplex h).obj F)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
      (AlgebraicGeometry.RingedSite.internalHomTermwiseSplitting
        (AlgebraicGeometry.RingedSpace.ringedSite X) (S.map (pullbackComplex h))
          ((pullbackComplex h).obj F)
          (fun p => (σ p).map (StacksDraft.KFlat.modulePullback h)) n).shortExact)
  have : IsIso (pullbackHomShortComplexMap h S F).τ₁ := h₃
  have : IsIso (pullbackHomShortComplexMap h S F).τ₃ := h₁
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (pullbackHomShortComplexMap h S F) hS₁ hS₂

end Devissage

section FiniteFree

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- Sheaves of modules on a ringed space have finite biproducts, being abelian. -/
local instance hasFiniteBiproducts_modules (Z : RingedSpace.{u, u}) :
    HasFiniteBiproducts (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **The comparison at the structure sheaf placed in an arbitrary degree.** -/
theorem isIso_pullbackHomComplexMap_single_unit (k : ℤ)
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h
      ((HomologicalComplex.single (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
        (ComplexShape.up ℤ) k).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (AlgebraicGeometry.RingedSpace.ringedSite Y).O))) F) := by
  let e := ((CochainComplex.singleFunctors
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)).shiftIso (-k) k 0
      (by lia)).app (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
  exact isIso_pullbackHomComplexMap_of_retract h F e.inv e.hom e.inv_hom_id
    (isIso_pullbackHomComplexMap_shiftedUnit h (-k) F)

/-- **The comparison at a power of the structure sheaf placed in a single degree.** -/
theorem isIso_pullbackHomComplexMap_single_unitPower (k : ℤ) (r : ℕ)
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h
      ((HomologicalComplex.single (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
        (ComplexShape.up ℤ) k).obj
          (AlgebraicGeometry.RingedSite.unitPower
            (AlgebraicGeometry.RingedSpace.ringedSite Y) r)) F) := by
  let Sg := HomologicalComplex.single
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) (ComplexShape.up ℤ) k
  induction r with
  | zero =>
    exact isIso_pullbackHomComplexMap_of_isZero h (Sg.map_isZero (isZero_zero _)) F
  | succ r ih =>
    let T := (AlgebraicGeometry.RingedSite.unitPowerShortComplex
      (AlgebraicGeometry.RingedSpace.ringedSite Y) r).map Sg
    have hT (p : ℤ) : (T.map (HomologicalComplex.eval _ _ p)).Splitting :=
      ((ShortComplex.Splitting.ofHasBinaryBiproduct
        (AlgebraicGeometry.RingedSite.unitPower (AlgebraicGeometry.RingedSpace.ringedSite Y) r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (AlgebraicGeometry.RingedSpace.ringedSite Y).O))).map Sg).map _
    exact isIso_pullbackHomComplexMap_of_degreewiseSplit h T hT F ih
      (isIso_pullbackHomComplexMap_single_unit h k F)

/-- **The comparison at a direct summand of a finite free module placed in a single degree.** -/
theorem isIso_pullbackHomComplexMap_single_of_isFiniteFreeSummand (k : ℤ)
    {A : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y}
    (hA : AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
      (AlgebraicGeometry.RingedSpace.ringedSite Y) A)
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h
      ((HomologicalComplex.single (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
        (ComplexShape.up ℤ) k).obj A) F) := by
  obtain ⟨r, ⟨ρ⟩⟩ := hA
  let ρ' := ρ.map (HomologicalComplex.single
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) (ComplexShape.up ℤ) k)
  exact isIso_pullbackHomComplexMap_of_retract h F ρ'.i ρ'.r ρ'.retract
    (isIso_pullbackHomComplexMap_single_unitPower h k r F)

/-- **The bounded case.** If `E` vanishes outside the window `[a, a + r)` and each of its terms
is a direct summand of a finite free `𝒪_Y`-module, the cochain-level comparison is an
isomorphism. -/
theorem isIso_pullbackHomComplexMap_of_bounded (r : ℕ) (a : ℤ)
    (E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
      (AlgebraicGeometry.RingedSpace.ringedSite Y) (E.X i))
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h E F) := by
  induction r generalizing a E with
  | zero =>
    refine isIso_pullbackHomComplexMap_of_isZero h
      (AlgebraicGeometry.RingedSite.complex_isZero_of_terms E fun i => ?_) F
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; lia)
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by lia)
    set p := AlgebraicGeometry.RingedSite.bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) :=
      AlgebraicGeometry.RingedSite.isZero_kernel_bottomProjection_X_self E a ha
    have hKterm (i : ℤ) : AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
        (AlgebraicGeometry.RingedSpace.ringedSite Y) (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact AlgebraicGeometry.RingedSite.IsFiniteFreeSummand.of_isZero _ hz
      · have := AlgebraicGeometry.RingedSite.isIso_kernel_ι_bottomProjection_f E a ha i hi
        exact AlgebraicGeometry.RingedSite.IsFiniteFreeSummand.of_iso _
          (asIso ((kernel.ι p).f i)) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · have := AlgebraicGeometry.RingedSite.isIso_kernel_ι_bottomProjection_f E a ha i hia
        exact IsZero.of_iso (hlo i (by lia)) (asIso ((kernel.ι p).f i))
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) := by
      have hia : i ≠ a := by lia
      have := AlgebraicGeometry.RingedSite.isIso_kernel_ι_bottomProjection_f E a ha i hia
      exact IsZero.of_iso (hhi i (by push_cast; lia)) (asIso ((kernel.ι p).f i))
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine isIso_pullbackHomComplexMap_of_degreewiseSplit h T (fun i => ?_) F
      (ih (a + 1) K hKlo hKhi hKterm)
      (isIso_pullbackHomComplexMap_single_of_isFiniteFreeSummand h a (hterm a) F)
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz
        (AlgebraicGeometry.RingedSite.isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
        (AlgebraicGeometry.RingedSite.isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The cochain-level comparison is an isomorphism at a strictly perfect source.**  If `E` has
finitely many nonzero terms, each of them a direct summand of a finite free `𝒪_Y`-module, then
`h^*𝓗om^•(E, F) ⟶ 𝓗om^•(h^*E, h^*F)` is an isomorphism of complexes, for every complex `F`. -/
theorem isIso_pullbackHomComplexMap_of_isFiniteFreeSummand
    (E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, AlgebraicGeometry.RingedSite.IsFiniteFreeSummand
      (AlgebraicGeometry.RingedSpace.ringedSite Y) (E.X i))
    (F : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h E F) := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine isIso_pullbackHomComplexMap_of_bounded h (b - a + 1).toNat a E ?_ ?_ hterm F
  · intro i hi
    by_contra hz
    have := ha hz
    lia
  · intro i hi
    by_contra hz
    have := hb hz
    lia

end FiniteFree

end Stacks.Cohomology.DerivedInternalHomPullback

end
