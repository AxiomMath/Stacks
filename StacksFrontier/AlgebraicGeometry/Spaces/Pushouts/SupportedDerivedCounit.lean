module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubobjectDirectedSupremum
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import StacksFrontier.Homology.Injectives.KInjective.SectionsKilledByRestriction
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# The counit `Lf^*Rf_*Q ⟶ Q` on complexes supported over a closed subspace (Stacks 0AEU)

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `Z ⊆ X` be a closed
subspace such that `f^{-1}Z ⟶ Z` is an isomorphism and `f` is flat at every point of `f^{-1}Z`.
Stacks 0AEU asserts that for `Q` in `D_QCoh(𝒪_Y)` supported on `|f^{-1}Z|` the counit
`Lf^*Rf_*Q ⟶ Q` is an isomorphism. This file states that assertion, with the additional
hypothesis that `Z ⟶ X` is of finite presentation (see the implementation notes), and proves
several steps of the source's argument.

## Main definitions

* `AlgebraicGeometry.Space.SupportedDerivedCounitIsIso`: the statement of Stacks 0AEU, as a
  proposition.
* `AlgebraicGeometry.Space.openSubspaceRestriction`, `AlgebraicGeometry.Space.openSubspaceShriek`:
  restriction `j^*` to an open subspace `V ⊆ Y` and extension by zero `j_!`, along the inclusion
  `AlgebraicGeometry.Space.openSubspaceHom`.
* `AlgebraicGeometry.Space.sectionsOffOpen`: the functor `Γ_W M = ker(M ⟶ j_*j^*M)` of sections
  supported on the closed complement `W` of `V`.

## Main results

* `AlgebraicGeometry.Space.isIso_iff_forall_isIso_geometricModuleStalk_homology`: a morphism of
  the derived category of `𝒪`-modules on the small étale site is an isomorphism exactly when it
  induces isomorphisms on the geometric stalks of all cohomology sheaves.
* `isIso_derivedAdjunction_counit_app_iff_of_isKInjective`, in the namespace
  `Stacks.Cohomology.DerivedPullbackOfToposHom`: at a K-injective complex `I` the derived counit
  is invertible exactly when the map of complexes `Lf^*(f_*I) ⟶ f^*f_*I ⟶ I` is (Stacks 0FPI).
* `IPowerTorsion.bijective_actionMap_of_isIPowerTorsion`: for `R ⟶ S` flat and bijective modulo
  `I`, the action map `N ⊗_R S ⟶ N` is bijective on every `IS`-power torsion `S`-module `N`
  (Stacks 05E9).
* `AlgebraicGeometry.Space.mono_openSubspaceShriekCounit`: for an open immersion `j` the counit
  `j_!j^*M ⟶ M` is a monomorphism.
* `AlgebraicGeometry.Space.isKInjective_sectionsOffOpen`: `Γ_W` carries K-injective complexes to
  K-injective complexes.
* `AlgebraicGeometry.Space.quasiIso_sectionsOffOpen_ι`: for a K-injective complex `I` with
  injective terms whose restriction to `V` is acyclic, `Γ_W I ⟶ I` is a quasi-isomorphism.

## Implementation notes

**The statement as written in the source is false without finite presentation of `Z ⟶ X`.**
The source's proof uses that the ideal of `Z` is finitely generated (to pass from `I_ȳ`-power
torsion to `I_x̄`-power torsion and to apply Stacks 05E9), and the lemma does not hold without it.
Let `A` be the valuation ring of the field `ℚ((t^ℚ))` of Hahn series, `I` its maximal ideal (so
`I = I²` is not finitely generated), `X = Spec A`, `Z = V(I)`, `Y = Spec B` for the square-zero
extension `B = A ⊕ Iε`, and `M = B / t¹B`. Then `B` is flat over `A`, `A/I ⟶ B/IB` is bijective
and `M` is supported on `V(IB)`, but the counit `M ⊗_A B ⟶ M` is not bijective; this is the
machine-checked `IPowerTorsion.exists_not_bijective_actionMap_of_support_subset` (in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedCounitCounterexample`). The
hypothesis `IsFinitePresentation B S hS Z.ι` is therefore added to
`AlgebraicGeometry.Space.SupportedDerivedCounitIsIso`; it is also a field of the standing
situation `AlgebraicGeometry.Space.FormalGlueingSituation` of Stacks 0AEV, in which the source
applies the lemma.

The derived adjunction is `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction` for the
morphism of small étale ringed topoi of Stacks 03G8, which is unconditional. It is stated at the
standard model `HasDerivedCategory.standard` of the derived categories, the model at which
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` is formed. The categories of modules are
Grothendieck abelian at universe `u` because the small étale site is essentially small
(`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`); the spelling of the module categories
the ringed-topos adjunction resolves against differs from `AlgebraicGeometry.Space.Modules` up to
reducible transparency, so the instance is restated here in that spelling.

The functor `Γ_W` is the instance of `Stacks.Injectives.SectionsKilledByRestriction.sections` for
the triple `j_! ⊣ j^* ⊣ j_*` of an open immersion; its two inputs are the exactness of `j_!`
(Stacks 03DJ, `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek`) and the
injectivity of the counit `j_!j^* ⟶ 𝟭`, which is checked on stalks: at a geometric point of `V`
the point has one lift to `V` and the counit is invertible there, and at any other point the stalk
of `j_!j^*M` vanishes (Stacks 08GU).

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

/-! ### The algebraic step at a point of `f^{-1}Z` -/

namespace IPowerTorsion

universe v₀ w₀

/-- A module over `S` which is `IS`-power torsion is `I`-power torsion over `R`. -/
theorem isIPowerTorsion_of_isIPowerTorsion_map {R : Type u} {S : Type v₀} [CommRing R]
    [CommRing S] [Algebra R S] (I : Ideal R) (N : Type w₀) [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] (hN : IsIPowerTorsion S N (I.map (algebraMap R S))) :
    IsIPowerTorsion R N I := by
  intro m
  obtain ⟨n, hn, h⟩ := hN m
  refine ⟨n, hn, fun a ha ↦ ?_⟩
  rw [← IsScalarTower.algebraMap_smul S a m]
  refine h _ ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- The action map `N ⊗_R S ⟶ N`, `n ⊗ s ↦ s • n`, of an `S`-module. -/
noncomputable def actionMap (R : Type u) (S : Type v₀) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type w₀) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
    TensorProduct R N S →ₗ[R] N :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (n : N) (s : S) ↦ s • n)
    (fun _ _ _ ↦ smul_add _ _ _) (fun c n s ↦ smul_algebra_smul_comm c s n)
    (fun _ _ _ ↦ add_smul _ _ _) (fun c n s ↦ smul_assoc c s n))

/-- The action map sends `n ⊗ s` to `s • n`. -/
@[simp]
theorem actionMap_tmul (R : Type u) (S : Type v₀) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type w₀) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : N) (s : S) : actionMap R S N (n ⊗ₜ s) = s • n :=
  rfl

/-- **A flat map bijective modulo `I` acts bijectively on `IS`-power torsion modules.** Let
`R ⟶ S` be flat and an isomorphism modulo `I`, that is `R/I ⟶ S/IS` bijective. Then for every
`S`-module `N` which is `IS`-power torsion the action map `N ⊗_R S ⟶ N` is bijective. It is
Stacks 05E9, which says that `N ⟶ N ⊗_R S`, `n ↦ n ⊗ 1`, is bijective for the `I`-power torsion
`R`-module `N`, and the action map is a left inverse of that map. -/
theorem bijective_actionMap_of_isIPowerTorsion (R : Type u) (S : Type v₀) [CommRing R]
    [CommRing S] [Algebra R S] (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (N : Type (max u v₀ w₀)) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (hN : IsIPowerTorsion S N (I.map (algebraMap R S))) :
    Function.Bijective (actionMap R S N) := by
  have hg := (baseChange_bijective_iff_quotientMap_bijective.{u, v₀, w₀} R S I hflat).2 hq N
    (isIPowerTorsion_of_isIPowerTorsion_map I N hN)
  have hleft : ∀ n : N, actionMap R S N ((TensorProduct.mk R N S).flip 1 n) = n := fun n ↦ by
    simp
  refine ⟨fun x y hxy ↦ ?_, fun n ↦ ⟨_, hleft n⟩⟩
  obtain ⟨a, rfl⟩ := hg.2 x
  obtain ⟨b, rfl⟩ := hg.2 y
  rw [hleft, hleft] at hxy
  rw [hxy]

end IPowerTorsion

section CounitAtKInjective

open AlgebraicGeometry Stacks.Cohomology.DerivedPushforward

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))]

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/-- **The derived counit at a K-injective complex is an honest map of complexes.** For a
K-injective complex `I` of `𝒪`-modules the counit `Lf^*Rf_*I ⟶ I` of the derived adjunction is an
isomorphism exactly when the composite `Lf^*(f_*I) ⟶ f^*(f_*I) ⟶ I` of the comparison of
Stacks 06YY with the degreewise counit of Stacks 03D7 is one. This is Stacks 0FPI
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction_counit_fac`) together with the
fact that `f_*I ⟶ Rf_*I` is invertible for K-injective `I`. -/
theorem isIso_derivedAdjunction_counit_app_iff_of_isKInjective (f : RingedToposHom X Y)
    (I : CochainComplex (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    IsIso ((derivedAdjunction f).counit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) ↔
      IsIso ((derivedPullbackComparison f).app
          ((pushforwardMapHomotopy f).obj ((HomotopyCategory.quotient _ _).obj I)) ≫
        DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).counit.app
          ((HomotopyCategory.quotient _ _).obj I))) := by
  have hu := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (pushforwardOnHomotopy (X := X) (Y := Y) f) (derivedPushforward (X := X) (Y := Y) f)
    ((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
      (sourceQuasiIso X)) I
  rw [← derivedAdjunction_counit_fac f ((HomotopyCategory.quotient _ _).obj I)]
  exact (isIso_comp_left_iff _ _).symm

end Stacks.Cohomology.DerivedPullbackOfToposHom

end CounitAtKInjective

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪`-modules of the small étale ringed topos of an algebraic space form a Grothendieck
abelian category at universe `u`: this is `AlgebraicGeometry.Space.isGrothendieckAbelian_modules`
in the spelling of the module categories of the ringed topos. -/
theorem isGrothendieckAbelian_ringedToposModules (Y : AlgebraicSpaces B S hS) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  isGrothendieckAbelian_modules B S hS Y.1 Y.2

attribute [local instance] isGrothendieckAbelian_ringedToposModules in
open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- **The statement of Stacks 0AEU**, with the finite presentation of `Z ⟶ X` added. For every
morphism `f : Y ⟶ X` of algebraic spaces over `S` and every finitely presented closed subspace
`Z ⊆ X` such that `f^{-1}Z ⟶ Z` is an isomorphism and `f` is flat at every point of `f^{-1}Z`,
the counit `Lf^*Rf_*Q ⟶ Q` of the derived adjunction is an isomorphism for every `Q` in
`D_QCoh(𝒪_Y)` whose cohomology sheaves are supported on `|f^{-1}Z|`.

Without the finite presentation of `Z ⟶ X` the assertion is false: see the implementation notes
of this file for a counterexample over a valuation ring with divisible value group. -/
def SupportedDerivedCounitIsIso : Prop :=
  ∀ {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X) (Z : Subfunctor X.1)
    (_ : IsClosedSubspace B S hS Z) (_ : IsFinitePresentation B S hS Z.ι)
    (_ : IsIso (Z.fromPreimage f.hom))
    (_ : ∀ y : points B S hS (Z.preimage f.hom).toFunctor,
      IsFlatAt B S hS f.hom
        (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι y))
    (Q : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (_ : CohomologySupportedOn B S hS Y.1 Y.2
      (Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) Q.1),
    IsIso ((derivedAdjunction (smallEtaleRingedToposHom B S hS f)).counit.app Q.1)

/-! ### Reduction to geometric stalks -/

/-- **A morphism of the derived category of modules on the small étale site is an isomorphism
exactly when it is one on the geometric stalks of every cohomology sheaf.** It holds in any model
of the derived category and over an arbitrary sheaf of rings. -/
theorem isIso_iff_forall_isIso_geometricModuleStalk_homology
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (R : Sheaf (SmallEtale.topology B S hS X) RingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u} R)]
    {E F : DerivedCategory (SheafOfModules.{u} R)} (φ : E ⟶ F) :
    IsIso φ ↔ ∀ (n : ℤ) (x : GeometricPoint B S hS X),
      IsIso ((geometricModuleStalkFunctor B S hS X hX R x).map
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} R) n).map φ)) := by
  refine ⟨fun _ n x ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  exact fun n ↦ isIso_of_isIso_geometricModuleStalk B S hS X hX R _ (h n)

/-! ### Sections supported off an open subspace -/

section OpenSubspace

variable {Y : AlgebraicSpaces B S hS} (V : Subfunctor Y.1) (hV : IsOpenSubspace B S hS V)

/-- Restriction of modules to an open subspace, `j^*`. -/
abbrev openSubspaceRestriction :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤
      Modules.{u, u} B S hS (openSubspaceSpace B S hS V hV).1 (openSubspaceSpace B S hS V hV).2 :=
  etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS V hV)
    (isEtale_openSubspaceHom B S hS V hV)

/-- Extension by zero from an open subspace, `j_!`. -/
abbrev openSubspaceShriek :
    Modules.{u, u} B S hS (openSubspaceSpace B S hS V hV).1 (openSubspaceSpace B S hS V hV).2 ⥤
      Modules.{u, u} B S hS Y.1 Y.2 :=
  etaleModuleLowerShriek B S hS (openSubspaceHom B S hS V hV)
    (isEtale_openSubspaceHom B S hS V hV)

/-- `j_! ⊣ j^*` for an open subspace. -/
abbrev openSubspaceShriekAdjunction :
    openSubspaceShriek B S hS V hV ⊣ openSubspaceRestriction B S hS V hV :=
  etaleModuleLowerShriekAdjunction B S hS (openSubspaceHom B S hS V hV)
    (isEtale_openSubspaceHom B S hS V hV)

/-- `j^* ⊣ j_*` for an open subspace. -/
abbrev openSubspacePushforwardAdjunction :
    openSubspaceRestriction B S hS V hV ⊣ modulePushforward B S hS (openSubspaceHom B S hS V hV) :=
  etaleModulePullbackAdjunction B S hS (openSubspaceHom B S hS V hV)
    (isEtale_openSubspaceHom B S hS V hV)

/-- Restriction to an open subspace is additive, being a right adjoint. -/
instance : (openSubspaceRestriction B S hS V hV).Additive :=
  have : (openSubspaceRestriction B S hS V hV).IsRightAdjoint :=
    (openSubspaceShriekAdjunction B S hS V hV).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- Extension by zero from an open subspace is additive, being exact. -/
instance : (openSubspaceShriek B S hS V hV).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Direct image along the inclusion of an open subspace is additive, being a right adjoint. -/
instance : (modulePushforward B S hS (openSubspaceHom B S hS V hV)).Additive :=
  have : (modulePushforward B S hS (openSubspaceHom B S hS V hV)).IsRightAdjoint :=
    (openSubspacePushforwardAdjunction B S hS V hV).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- Restriction to an open subspace is exact: it has both adjoints, so it preserves finite
limits. -/
private instance : PreservesFiniteLimits (openSubspaceRestriction B S hS V hV) :=
  have : (openSubspaceRestriction B S hS V hV).IsRightAdjoint :=
    (openSubspaceShriekAdjunction B S hS V hV).isRightAdjoint
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- **The counit `j_!j^*M ⟶ M` of extension by zero from an open subspace is a monomorphism.**
At a geometric point of the open subspace the point has exactly one lift and the counit is
invertible on stalks; at any other geometric point the stalk of `j_!j^*M` vanishes. -/
theorem mono_openSubspaceShriekCounit (M : Modules.{u, u} B S hS Y.1 Y.2) :
    Mono ((openSubspaceShriekAdjunction B S hS V hV).counit.app M) := by
  refine (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).mono_of_mono_map ?_
  refine (((isConservativeFamilyOfPoints_etaleSitePoint B S hS Y.1
    Y.2).jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono_iff _).2 fun Φ ↦ ?_
  obtain ⟨Φ, hΦ⟩ := Φ
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  show Mono ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
    ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map
      ((openSubspaceShriekAdjunction B S hS V hV).counit.app M)))
  have hiff := nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS Y.2 V hV x
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)
  · have hne := hiff.2 hx
    have : Subsingleton (GeometricPointLift B S hS (openSubspaceHom B S hS V hV).hom x) :=
      subsingleton_geometricPointLift_of_mono B S hS V.ι inferInstance x
    have : Unique (GeometricPointLift B S hS (openSubspaceHom B S hS V hV).hom x) :=
      uniqueOfSubsingleton hne.some
    have := isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS (openSubspaceHom B S hS V hV)
      (isEtale_openSubspaceHom B S hS V hV) x M
      (EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS _
        (isEtale_openSubspaceHom B S hS V hV) x _)
    infer_instance
  · have : IsEmpty (GeometricPointLift B S hS (openSubspaceHom B S hS V hV).hom x) :=
      not_nonempty_iff.1 fun h ↦ hx (hiff.1 h)
    refine IsZero.mono ?_ _
    exact isZero_sheafFiber_toSheaf_etaleModuleShriek B S hS (openSubspaceHom B S hS V hV)
      (isEtale_openSubspaceHom B S hS V hV) x _
      (EtaleShriekStalk.isZero_sheafFiber_restriction_shriek_of_isEmpty B S hS _
        (isEtale_openSubspaceHom B S hS V hV) x
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj M))

/-- Restriction to an open subspace is a left inverse of the direct image: the counit
`j^*j_* ⟶ 𝟭` is invertible
(`AlgebraicGeometry.Space.isIso_etaleModulePullbackAdjunction_counit`). -/
theorem isIso_openSubspacePushforwardAdjunction_counit
    (N : Modules.{u, u} B S hS (openSubspaceSpace B S hS V hV).1
      (openSubspaceSpace B S hS V hV).2) :
    IsIso ((openSubspacePushforwardAdjunction B S hS V hV).counit.app N) :=
  isIso_etaleModulePullbackAdjunction_counit B S hS (openSubspaceHom B S hS V hV) hV.2 N

/-- **Sections supported off an open subspace**, `Γ_W M = ker(M ⟶ j_*j^*M)` for the inclusion
`j : V ⟶ Y` of an open subspace and `W` its closed complement. -/
abbrev sectionsOffOpen : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  Stacks.Injectives.SectionsKilledByRestriction.sections
    (openSubspacePushforwardAdjunction B S hS V hV)

/-- **`Γ_W M` restricts to zero on the open subspace**, the counit `j^*j_* ⟶ 𝟭` being
invertible. -/
theorem isZero_openSubspaceRestriction_sectionsOffOpen (M : Modules.{u, u} B S hS Y.1 Y.2) :
    IsZero ((openSubspaceRestriction B S hS V hV).obj ((sectionsOffOpen B S hS V hV).obj M)) :=
  Stacks.Injectives.SectionsKilledByRestriction.isZero_map_sections
    (openSubspacePushforwardAdjunction B S hS V hV)
    (isIso_openSubspacePushforwardAdjunction_counit B S hS V hV) M

/-- **A complex whose cohomology sheaves restrict to zero on an open subspace restricts to an
acyclic complex**: restriction is exact, so it commutes with cohomology. -/
theorem acyclic_openSubspaceRestriction_of_isZero
    (K : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (hK : ∀ n, IsZero ((openSubspaceRestriction B S hS V hV).obj (K.homology n))) :
    (((openSubspaceRestriction B S hS V hV).mapHomologicalComplex _).obj K).Acyclic := fun n ↦ by
  have : (openSubspaceRestriction B S hS V hV).IsLeftAdjoint :=
    (openSubspacePushforwardAdjunction B S hS V hV).isLeftAdjoint
  have : PreservesFiniteColimits (openSubspaceRestriction B S hS V hV) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hK n).of_iso ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (openSubspaceRestriction B S hS V hV) _ n).app K)

/-- **`Γ_W` carries K-injective complexes to K-injective complexes.** It has the exact left
adjoint `M ↦ coker(j_!j^*M ⟶ M)`. -/
theorem isKInjective_sectionsOffOpen
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((sectionsOffOpen B S hS V hV).mapHomologicalComplex _).obj I) :=
  Stacks.Injectives.SectionsKilledByRestriction.isKInjective_sections
    (openSubspaceShriekAdjunction B S hS V hV) (openSubspacePushforwardAdjunction B S hS V hV)
    (mono_openSubspaceShriekCounit B S hS V hV) I

/-- The restriction `j^*I` of a K-injective complex to an open subspace is K-injective
(Stacks 070G: `j^*` has the exact left adjoint `j_!`). -/
theorem isKInjective_openSubspaceRestriction
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((openSubspaceRestriction B S hS V hV).mapHomologicalComplex _).obj I) :=
  Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction _ _
    (openSubspaceShriekAdjunction B S hS V hV) I

/-- **`Γ_W I ⟶ I` is a quasi-isomorphism** for a K-injective complex `I` with injective terms
whose restriction to the open subspace `V` is acyclic, for instance one whose cohomology sheaves
are supported on the closed complement `W`. -/
theorem quasiIso_sectionsOffOpen_ι
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) [I.IsKInjective]
    [∀ n, Injective (I.X n)]
    (hI : (((openSubspaceRestriction B S hS V hV).mapHomologicalComplex _).obj I).Acyclic) :
    QuasiIso (Stacks.Injectives.SectionsKilledByRestriction.sectionsShortComplex
      (openSubspacePushforwardAdjunction B S hS V hV) I).f :=
  Stacks.Injectives.SectionsKilledByRestriction.quasiIso_sectionsι
    (openSubspaceShriekAdjunction B S hS V hV) (openSubspacePushforwardAdjunction B S hS V hV)
    (mono_openSubspaceShriekCounit B S hS V hV) I
    (isKInjective_openSubspaceRestriction B S hS V hV I) hI

end OpenSubspace

end AlgebraicGeometry.Space

end
