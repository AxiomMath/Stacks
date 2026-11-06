module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHom
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# `Ext` of continuous group modules is continuous group cohomology of `Mᵛ ⊗ N`

Let `G` be a topological group, `R` a commutative ring, and let `M` and `N` be continuous
discrete `R`-`G`-modules with `M` finite projective over `R`. Then

`Extⁱ(M, N) = Hⁱ(G, Mᵛ ⊗_R N)`,

the `Ext` being taken in the category of continuous discrete `R`-`G`-modules and `Mᵛ ⊗_R N`
carrying the contragredient action on the dual factor and the diagonal action overall. This is
[Stacks, Tag 0DVE].

## Main definitions

* `Stacks.ContinuousCohomology.trivialModule` — the ring `R` as a continuous discrete
  `R`-`G`-module with trivial action; it corepresents `G`-invariants.
* `Stacks.ContinuousCohomology.extIsoCohomologyDualTensor` — the comparison of the tag, as an
  `R`-linear isomorphism in every degree.
* `Stacks.ContinuousCohomology.extFunctorIsoCohomologyInternalHom` — the same comparison as a
  natural isomorphism of functors in the second variable.

## Implementation notes

The comparison is stated for `Mathlib`'s `CategoryTheory.Abelian.Ext` in the category of
continuous discrete `R`-`G`-modules — not `Ext` over `R` alone — and for the library's
continuous group cohomology `Stacks.ContinuousCohomology.cohomologyFunctor`, the right derived
functor of `G`-invariants on continuous discrete modules, which is the functor
[Stacks, Tag 0DVD] compares with the `R = ℤ` case.

## References

* [Stacks Project, Tag 0DVE](https://stacks.math.columbia.edu/tag/0DVE)
* [Stacks Project, Tag 0DVD](https://stacks.math.columbia.edu/tag/0DVD)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe d t z z' u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

section Corepresentation

/-- Multiplication by a vector of an `R`-module, as an `R`-linear map out of `ULift R`. -/
def uliftSpan (R : Type u) [CommRing R] (N : Type z) [AddCommGroup N] [Module R N] (y : N) :
    ULift.{t} R →ₗ[R] N :=
  (LinearMap.toSpanSingleton R N y).comp
    (ULift.moduleEquiv (R := R) (M := R) : ULift.{t} R ≃ₗ[R] R).toLinearMap

variable (R : Type u) [CommRing R]

/-- A linear map carries multiplication by a vector to multiplication by its image. -/
lemma uliftSpan_map (N : Type z) [AddCommGroup N] [Module R N]
    (P : Type z') [AddCommGroup P] [Module R P] (ψ : N →ₗ[R] P) (y : N) (n : ULift.{t} R) :
    ψ (uliftSpan.{t} R N y n) = uliftSpan.{t} R P (ψ y) n := by
  simp [uliftSpan, LinearMap.toSpanSingleton_apply]

/-- Multiplication by a vector commutes with an endomorphism fixing it. -/
lemma uliftSpan_fixed (N : Type z) [AddCommGroup N] [Module R N]
    (φ : N →ₗ[R] N) (y : N) (hy : φ y = y) (n : ULift.{t} R) :
    φ (uliftSpan.{t} R N y n) = uliftSpan.{t} R N y n := by
  rw [uliftSpan_map.{t} R N N φ y n, hy]

/-- Multiplication by a vector sends `1` to that vector. -/
lemma uliftSpan_up_one (N : Type z) [AddCommGroup N] [Module R N] (y : N) :
    uliftSpan.{t} R N y (ULift.up 1) = y :=
  LinearMap.toSpanSingleton_apply_one R N y

/-- Multiplication by a vector is additive in the vector. -/
lemma uliftSpan_add (N : Type z) [AddCommGroup N] [Module R N] (y z : N) (n : ULift.{t} R) :
    uliftSpan.{t} R N (y + z) n = uliftSpan.{t} R N y n + uliftSpan.{t} R N z n := by
  simp [uliftSpan, LinearMap.toSpanSingleton_apply, smul_add]

/-- Multiplication by `1` is the identity of `ULift R`. -/
lemma uliftSpan_one (n : ULift.{t} R) :
    uliftSpan.{t} R (ULift.{t} R) (ULift.up 1) n = n := by
  apply ULift.ext
  simp [uliftSpan, LinearMap.toSpanSingleton_apply]

/-- An `R`-linear map out of `ULift R` is multiplication by the image of `1`. -/
lemma uliftSpan_eq (N : Type z) [AddCommGroup N] [Module R N]
    (φ : ULift.{t} R →ₗ[R] N) (n : ULift.{t} R) :
    uliftSpan.{t} R N (φ (ULift.up 1)) n = φ n := by
  rw [← uliftSpan_map.{t} R (ULift.{t} R) N φ (ULift.up 1) n, uliftSpan_one.{t} R n]

variable (G : Type v) [Group G] [TopologicalSpace G]

/-- The ring `R` with the trivial `G`-action, as a continuous discrete `R`-`G`-module. -/
def trivialModule : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G :=
  ⟨⟨Action.trivial G (ModuleCat.of R (ULift.{max u v w} R)), by
      exact (Action.isContinuous_def _).2
        (continuous_prod_of_discrete_right.2 fun _ => continuous_const)⟩, ⟨rfl⟩⟩

/-- An invariant vector is fixed by every group element. -/
lemma rho_apply_mem_invariants {M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (x : (continuousModuleInvariants.{u, v, max u v w} R G).obj M) (g : G) :
    (M.obj.obj.ρ g).asHom x.val = x.val := x.property g

/-- The morphism of continuous discrete `R`-`G`-modules out of the trivial module `R` given by
multiplication by an invariant vector. -/
def invariantModuleHom {M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G}
    (x : (continuousModuleInvariants.{u, v, max u v w} R G).obj M) :
    trivialModule.{u, v, w} R G ⟶ M :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (uliftSpan.{max u v w} R (M.obj.obj.V : Type max u v w) x.val)
      comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun n =>
        (uliftSpan_fixed.{max u v w} R (M.obj.obj.V : Type max u v w) (M.obj.obj.ρ g).asHom.hom x.val
          (rho_apply_mem_invariants R G x g) n).symm) })

/-- The invariants of a continuous discrete `R`-`G`-module `M` are additively equivalent to the
morphisms from the trivial module `R` to `M`, an invariant vector `x` corresponding to
multiplication by `x`. -/
def invariantsModuleHomAddEquiv
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    (continuousModuleInvariants.{u, v, max u v w} R G).obj M ≃+
      (trivialModule.{u, v, w} R G ⟶ M) where
  toFun x := invariantModuleHom.{u, v, w} R G x
  invFun f := ⟨f.hom.hom.hom.hom (ULift.up 1), fun g =>
    (ConcreteCategory.congr_hom (f.hom.hom.comm g) (ULift.up 1)).symm⟩
  left_inv x := Subtype.ext (uliftSpan_up_one.{max u v w} R (M.obj.obj.V : Type max u v w) x.val)
  right_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun n =>
      uliftSpan_eq.{max u v w} R (M.obj.obj.V : Type max u v w) f.hom.hom.hom.hom n
  map_add' x y := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun n =>
      uliftSpan_add.{max u v w} R (M.obj.obj.V : Type max u v w) x.val y.val n

/-- Taking `G`-invariants of a continuous discrete `R`-`G`-module, read as an abelian group, is
corepresented by the trivial module `R`, naturally in the module. -/
def invariantsCorepresentationModule :
    continuousModuleInvariants.{u, v, max u v w} R G ⋙
        forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} ≅
      preadditiveCoyoneda.obj (op (trivialModule.{u, v, w} R G)) :=
  NatIso.ofComponents
    (fun M => (invariantsModuleHomAddEquiv.{u, v, w} R G M).toAddCommGrpIso)
    (fun {M N} f => by
      ext x
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun n =>
        (uliftSpan_map.{max u v w} R (M.obj.obj.V : Type max u v w) (N.obj.obj.V : Type max u v w)
          f.hom.hom.hom.hom x.val n).symm)

end Corepresentation

section DegreeZero

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- Taking `G`-invariants of a continuous discrete `R`-`G`-module, read as an abelian group. -/
def invariantsToAb :
    Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G ⥤ AddCommGrpCat.{max u v w} :=
  continuousModuleInvariants.{u, v, max u v w} R G ⋙
    forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}

/-- Taking `G`-invariants, read as abelian groups, is additive. -/
instance additive_invariantsToAb : (invariantsToAb.{u, v, w} R G).Additive :=
  inferInstanceAs ((continuousModuleInvariants.{u, v, max u v w} R G ⋙
    forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}).Additive)

/-- Taking `G`-invariants is left exact. -/
instance preservesFiniteLimits_invariantsToAb :
    PreservesFiniteLimits (invariantsToAb.{u, v, w} R G) :=
  preservesFiniteLimits_of_natIso (invariantsCorepresentationModule.{u, v, w} R G).symm

/-- Taking `G`-invariants is `R`-linear. -/
instance continuousModuleInvariants_linear :
    (continuousModuleInvariants.{u, v, w} R G).Linear R where
  map_smul := by
    intros
    ext x : 2
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    apply Subtype.ext
    rfl

variable (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
  [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]

/-- The internal hom out of `M` is `R`-linear: on morphisms it is postcomposition. -/
instance internalHomFunctor_linear : (internalHomFunctor R G M).Linear R where
  map_smul := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    rfl

/-- A morphism `M ⟶ N` of continuous discrete `R`-`G`-modules is a `G`-invariant element of
`Hom_R(M, N)`. -/
def homEquivInvariantsInternalHom
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :
    (M ⟶ N) ≃ₗ[R] (continuousModuleInvariants.{u, v, max u v w} R G).obj
      ((internalHomFunctor R G M).obj N) :=
  homEquivLinHomInvariants R G M N

/-- `Hom(M, -)` is `G`-invariants of `Hom_R(M, -)`, naturally in the second variable. -/
def coyonedaIsoInternalHomInvariants :
    preadditiveCoyoneda.obj (op M) ≅
      internalHomFunctor R G M ⋙ invariantsToAb.{u, v, w} R G :=
  NatIso.ofComponents
    (fun N => (homEquivInvariantsInternalHom.{u, v, w} R G M N).toAddEquiv.toAddCommGrpIso)
    (fun {N N'} f => by
      ext φ
      apply Subtype.ext
      rfl)

/-- `Hom_R(M, -)` followed by `G`-invariants is left exact. -/
instance preservesFiniteLimits_internalHomInvariants :
    PreservesFiniteLimits (internalHomFunctor R G M ⋙ invariantsToAb.{u, v, w} R G) :=
  preservesFiniteLimits_of_natIso (coyonedaIsoInternalHomInvariants.{u, v, w} R G M)

end DegreeZero

section Comparison

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The category of continuous discrete `R`-`G`-modules has `Ext` groups in the universe of its
morphisms. -/
lemma hasExt_continuousModule :
    HasExt.{max u v w} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :=
  hasExt_of_enoughInjectives.{max u v w, max u v w, max (max (u + 1) (v + 1)) (w + 1)}
    (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)

variable [HasExt.{max u v w} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
  (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
  [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]

/-- `Ext` out of `M` is the right derived functor of `Hom(M, -)`, which is `Hom_R(M, -)`
followed by `G`-invariants. -/
def extFunctorIsoRightDerivedComposite (n : ℕ) :
    extFunctorObj M n ≅
      (internalHomFunctor R G M ⋙ invariantsToAb.{u, v, w} R G).rightDerived n :=
  ModuleSheafCohomology.extFunctorObjIsoRightDerived
    (internalHomFunctor R G M ⋙ invariantsToAb.{u, v, w} R G) M
    (coyonedaIsoInternalHomInvariants.{u, v, w} R G M).symm n

/-- The Grothendieck comparison: deriving `Hom_R(M, -)` followed by `G`-invariants is applying
`Hom_R(M, -)` and then deriving `G`-invariants. -/
def grothendieckComparisonInternalHom (n : ℕ) :
    (internalHomFunctor R G M ⋙ invariantsToAb.{u, v, w} R G).rightDerived n ≅
      internalHomFunctor R G M ⋙ (invariantsToAb.{u, v, w} R G).rightDerived n :=
  ModuleSheafCohomology.comparisonIso (internalHomFunctor R G M)
    (invariantsToAb.{u, v, w} R G) (trivialModule.{u, v, w} R G)
    (invariantsCorepresentationModule.{u, v, w} R G) M
    (coyonedaIsoInternalHomInvariants.{u, v, w} R G M ≪≫
      Functor.isoWhiskerLeft (internalHomFunctor R G M)
        (invariantsCorepresentationModule.{u, v, w} R G))
    (fun I hI _ e => by
      have := hI
      exact Ext.eq_zero_of_injective e) n

/-- Forgetting the `R`-module structure may be pulled out of the derived functors of
`G`-invariants. -/
def rightDerivedInvariantsToAbIso (n : ℕ) :
    (invariantsToAb.{u, v, w} R G).rightDerived n ≅
      (continuousModuleInvariants.{u, v, max u v w} R G).rightDerived n ⋙
        forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} :=
  Functor.rightDerivedCompIso (continuousModuleInvariants.{u, v, max u v w} R G)
    (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}) n

/-- For `M` finite projective over `R`,
`Extⁿ(M, -)` is continuous group cohomology `Hⁿ(G, Hom_R(M, -))`, naturally in the second
variable and in every degree, as abelian groups. -/
def extFunctorIsoCohomologyInternalHom (n : ℕ) :
    extFunctorObj M n ≅
      internalHomFunctor R G M ⋙
        (continuousModuleInvariants.{u, v, max u v w} R G).rightDerived n ⋙
          forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} :=
  extFunctorIsoRightDerivedComposite.{u, v, w} R G M n ≪≫
    grothendieckComparisonInternalHom.{u, v, w} R G M n ≪≫
    Functor.isoWhiskerLeft (internalHomFunctor R G M)
      (rightDerivedInvariantsToAbIso.{u, v, w} R G n)

/-- A composition of morphisms of abelian groups, evaluated at an element. -/
lemma addCommGrpCat_comp_apply {A B C : AddCommGrpCat.{z}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    ConcreteCategory.hom (f ≫ g) a = ConcreteCategory.hom g (ConcreteCategory.hom f a) := rfl

/-- Scalar multiplication on an `R`-module, read through the forgetful functor to abelian
groups. -/
lemma forget₂_map_smul_id_apply {X : ModuleCat.{z} R} (r : R) (x : (X : Type z)) :
    ConcreteCategory.hom
      ((forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}).map (r • 𝟙 X)) x = r • x := rfl

set_option maxHeartbeats 1000000 in
omit [HasExt.{max u v w} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)] in
/-- On the target of the comparison, multiplication by `r` is the functor applied to `r • 𝟙`. -/
lemma internalHomRightDerived_map_smul_id_apply
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) (r : R)
    (y : (((continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i).obj
      ((internalHomFunctor R G M).obj N) : Type max u v w)) :
    ConcreteCategory.hom ((internalHomFunctor R G M ⋙
      (continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i ⋙
      forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}).map (r • 𝟙 N)) y = r • y := by
  have hK : ((continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i).map
      ((internalHomFunctor R G M).map (r • 𝟙 N)) = r • 𝟙 _ := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rw [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_map, hK]
  exact forget₂_map_smul_id_apply R r _

/-- The forgetful image of an `R`-module in abelian groups has the same underlying additive
group. -/
def forget₂CarrierAddEquiv (X : ModuleCat.{z} R) :
    (((forget₂ (ModuleCat.{z} R) AddCommGrpCat.{z}).obj X : AddCommGrpCat.{z}) : Type z) ≃+
      (X : Type z) := AddEquiv.refl _

/-- The value at `N` of the `Ext` functor out of `M` is the `Ext` group `Extⁱ(M, N)`. -/
def extFunctorObjCarrierAddEquiv
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) :
    (((extFunctorObj M i).obj N : AddCommGrpCat.{max u v w}) : Type max u v w) ≃+
      Ext.{max u v w} M N i := AddEquiv.refl _

set_option maxHeartbeats 1000000 in
/-- For `M` finite projective over `R`, `Extⁱ(M, N)` is additively isomorphic to the `i`-th right
derived functor of `G`-invariants at `Hom_R(M, N)`. -/
def extAddEquivRightDerived
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) :
    Ext.{max u v w} M N i ≃+
      (((continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i).obj
        ((internalHomFunctor R G M).obj N) : Type max u v w) :=
  (extFunctorObjCarrierAddEquiv.{u, v, w} R G M N i).symm.trans
    (((extFunctorIsoCohomologyInternalHom.{u, v, w} R G M i).app
        N).addCommGroupIsoToAddEquiv.trans
      (forget₂CarrierAddEquiv R
        (((continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i).obj
          ((internalHomFunctor R G M).obj N))))

/-- The comparison is evaluation of the natural isomorphism. -/
lemma extAddEquivRightDerived_apply
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ)
    (y : Ext.{max u v w} M N i) :
    extAddEquivRightDerived.{u, v, w} R G M N i y
      = ConcreteCategory.hom
        ((extFunctorIsoCohomologyInternalHom.{u, v, w} R G M i).hom.app N) y := rfl

/-- The comparison `extAddEquivRightDerived` is `R`-linear. -/
lemma extAddEquivRightDerived_map_smul
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) (r : R)
    (x : Ext.{max u v w} M N i) :
    extAddEquivRightDerived.{u, v, w} R G M N i (r • x)
      = r • extAddEquivRightDerived.{u, v, w} R G M N i x := by
  have hnat0 := ConcreteCategory.congr_hom
    ((extFunctorIsoCohomologyInternalHom.{u, v, w} R G M i).hom.naturality (r • 𝟙 N)) x
  have h1 := addCommGrpCat_comp_apply ((extFunctorObj M i).map (r • 𝟙 N))
    ((extFunctorIsoCohomologyInternalHom.{u, v, w} R G M i).hom.app N) x
  have h2 := addCommGrpCat_comp_apply
    ((extFunctorIsoCohomologyInternalHom.{u, v, w} R G M i).hom.app N)
    ((internalHomFunctor R G M ⋙
      (continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i ⋙
      forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}).map (r • 𝟙 N)) x
  have hL : ConcreteCategory.hom ((extFunctorObj M i).map (r • 𝟙 N)) x = r • x := by
    simp only [extFunctorObj_map]
    exact (Ext.smul_eq_comp_mk₀ x r).symm
  have h3 := congrArg
    (fun y => ConcreteCategory.hom
      ((extFunctorIsoCohomologyInternalHom.{u, v, w} R G M i).hom.app N) y) hL
  exact (extAddEquivRightDerived_apply.{u, v, w} R G M N i (r • x)).trans
    ((h3.symm.trans ((h1.symm.trans hnat0).trans h2)).trans
      ((internalHomRightDerived_map_smul_id_apply.{u, v, w} R G M N i r _).trans
        (congrArg (fun y => r • y)
          (extAddEquivRightDerived_apply.{u, v, w} R G M N i x).symm)))

/-- For `M` finite projective over `R`, `Extⁱ(M, N)` is `R`-linearly isomorphic to the `i`-th
right derived functor of `G`-invariants at `Hom_R(M, N)`. -/
def extLinearEquivRightDerived
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) :
    Ext.{max u v w} M N i ≃ₗ[R]
      ((continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i).obj
        ((internalHomFunctor R G M).obj N) :=
  AddEquiv.toLinearEquiv (extAddEquivRightDerived.{u, v, w} R G M N i)
    (extAddEquivRightDerived_map_smul.{u, v, w} R G M N i)

/-- Continuous group cohomology of `Mᵛ ⊗_R N`, read through the `ℕ`-indexed right derived
functors of `G`-invariants applied to `Hom_R(M, N)`. -/
def cohomologyIsoRightDerivedInternalHom
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
    [HasDerivedCategory.{d} (ModuleCat.{max u v w} R)]
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) :
    ((continuousModuleInvariants.{u, v, max u v w} R G).rightDerived i).obj
        ((internalHomFunctor R G M).obj N) ≅
      (cohomologyFunctor.{d, u, v, w} R G i).obj
        (dualTensorContinuousModule.{u, v, max u v w} R G M N) :=
  (Stacks.DerivedIndexing.rightDerivedIso
      (continuousModuleInvariants.{u, v, max u v w} R G) i).app
        ((internalHomFunctor R G M).obj N) ≪≫
    (cohomologyFunctor.{d, u, v, w} R G i).mapIso (dualTensorIsoInternalHom R G M N).symm

/-- Let `G` be a topological group, `R` a commutative ring and `M`, `N` continuous discrete
`R`-`G`-modules. If `M` is finite projective as an `R`-module, then `Extⁱ(M, N)`, computed in the
category of continuous discrete `R`-`G`-modules, is the continuous group cohomology
`Hⁱ(G, Mᵛ ⊗_R N)` of the diagonal action on `Mᵛ ⊗_R N`, `R`-linearly and in every degree. -/
@[stacks 0DVE
  "R-linear, in every degree; the `Ext`-universe smallness (hasExt_continuousModule) and the\
  model of the derived category are free instance arguments"]
def extIsoCohomologyDualTensor
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
    [HasDerivedCategory.{d} (ModuleCat.{max u v w} R)]
    (N : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) (i : ℕ) :
    Ext.{max u v w} M N i ≃ₗ[R]
      (cohomologyFunctor.{d, u, v, w} R G i).obj
        (dualTensorContinuousModule.{u, v, max u v w} R G M N) :=
  (extLinearEquivRightDerived.{u, v, w} R G M N i).trans
    (cohomologyIsoRightDerivedInternalHom.{d, u, v, w} R G M N i).toLinearEquiv

end Comparison

end Stacks.ContinuousCohomology
