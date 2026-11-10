module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.RingTheory.Regular.Category
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessIsLocal

/-!
# Local cohomology over a Noetherian local ring is Artinian

Let `A` be a Noetherian local ring with maximal ideal `𝔪`, and let `M` be a finite `A`-module.
Every local cohomology module `Hⁱ_𝔪(M)` satisfies the descending chain condition.

The proof is an induction on the dimension of the support of `M`. Killing the `𝔪`-primary
component of `M` changes no local cohomology in positive degrees, so one may assume `𝔪` is not
associated to `M` and choose an `M`-regular element `x` of `𝔪`; the support of `M/xM` then has
strictly smaller dimension. From the long exact sequence, the kernel of multiplication by `x` on
`Hⁱ_𝔪(M)` is a quotient of `Hⁱ⁻¹_𝔪(M/xM)`, which is Artinian by induction, so it has finite
socle; since `Hⁱ_𝔪(M)` is `𝔪`-power torsion, the finiteness criterion of Tag 08Z8 makes it
Artinian. Degree zero is separate: there `H⁰_𝔪(M)` embeds in `M` as a finite torsion
submodule, hence has finite length.

## Main results

* `Stacks.LocalCohomology.isArtinian_localCohomology_maximalIdeal` — local cohomology of a
  finite module over a Noetherian local ring is Artinian in every degree.
* `Stacks.LocalCohomology.localCohomologyModuleMap_lsmul` — multiplication by `x : A` on a module
  induces multiplication by `x` on every local cohomology module. This is what turns the
  connecting map of the long exact sequence into a statement about the `x`-torsion of
  `Hⁱ_𝔪(M)`, and it is stated here for every finitely generated ideal, not just `𝔪`.

## Implementation notes

The descending chain condition is `IsArtinian`. Local cohomology is the homology of the derived
local-cohomology functor of Tag 0A6Q, with the module universe independent of the ring
universe.

The maps of the long exact sequence come from
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/Triangulated.lean`:
`Stacks.LocalCohomology.localCohomologyModuleMap`, the two `ObjectProperty` instances for the
derived objects with `I`-power-torsion cohomology, and the middle exactness
`Stacks.LocalCohomology.exact_localCohomologyModuleMap`. That file is imported
rather than duplicated.

## References

* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped ZeroObject Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

/-- Local cohomology supported at the maximal ideal is `𝔪`-power torsion, by construction of
the local-cohomology coreflection. -/
private lemma localCohomologyModule_torsion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{w} A) (i : ℤ) :
    IsIPowerTorsion A
      (localCohomologyModule A
        (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
        M i)
      (IsLocalRing.maximalIdeal A) := by
  change IsIPowerTorsion A
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
      ((Dualizing.derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).ι.obj
        ((Dualizing.localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M))))
    (IsLocalRing.maximalIdeal A)
  exact ((Dualizing.localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M)).property i

/-- A finite `𝔪`-power-torsion module over a Noetherian local ring has finite length. -/
private lemma finiteLength_of_finite_maximalTorsion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (N : Type w) [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hT : IsIPowerTorsion A N (IsLocalRing.maximalIdeal A)) :
    IsFiniteLength A N := by
  have hsupp : Module.support A N ⊆ PrimeSpectrum.zeroLocus
      (IsLocalRing.maximalIdeal A : Set A) :=
    (isIPowerTorsion_iff_support_subset A N (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).mp hT
  by_cases hsub : Subsingleton N
  · exact IsFiniteLength.of_subsingleton
  · have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hsub
    have hne : (Module.support A N).Nonempty := Module.nonempty_support_of_nontrivial
    have hsupp' : Module.support A N ⊆ {IsLocalRing.closedPoint A} := by
      intro p hp
      simpa [zeroLocus_maximalIdeal] using hsupp hp
    have hEq : Module.support A N = {IsLocalRing.closedPoint A} := by
      apply Set.Subset.antisymm hsupp'
      rintro p rfl
      obtain ⟨q, hq⟩ := hne
      have hq' : q = IsLocalRing.closedPoint A := Set.mem_singleton_iff.mp (hsupp' hq)
      simpa [hq'] using hq
    exact isFiniteLength_of_support hEq

/-- The maximal ideal is not associated to the quotient of a finite module by its `𝔪`-primary
component. -/
private lemma maximalIdeal_notMem_associatedPrimes_quotient_primaryComponent
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsLocalRing.maximalIdeal A ∉ associatedPrimes A
      (M ⧸ Ideal.primaryComponent M (IsLocalRing.maximalIdeal A)) := by
  let Q := M ⧸ Ideal.primaryComponent M (IsLocalRing.maximalIdeal A)
  have hpc := primaryComponent_quotient_eq_bot A (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M
  intro hm
  have hm' : IsLocalRing.maximalIdeal A ∈ associatedPrimes A Q := hm
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hm'
  obtain ⟨_, x, hxann⟩ := hm'
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    have hcolon : Submodule.colon (⊥ : Submodule A Q) ({(0 : Q)} : Set Q) = ⊤ := by
      ext a
      simp [Submodule.mem_colon]
    rw [hcolon] at hxann
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top hxann
  have hxt : x ∈ Ideal.primaryComponent Q (IsLocalRing.maximalIdeal A) := by
    apply (Ideal.primaryComponent_mem Q (IsLocalRing.maximalIdeal A) x).mpr
    refine ⟨1, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha : (a : A) ∈ IsLocalRing.maximalIdeal A := by simpa using a.2
    have ha' : (a : A) ∈ Submodule.colon (⊥ : Submodule A Q) ({x} : Set Q) := by
      rw [← hxann]
      exact ha
    have hk := Submodule.mem_colon.mp ha'
    simpa using hk x (by simp)
  rw [hpc] at hxt
  exact hx0 (by simpa using hxt)

/-- The homology functors of the derived category of `A`-modules are `A`-linear. -/
private lemma derivedCategory_homologyFunctor_linear
    (A : Type u) [CommRing A] (i : ℤ) :
    Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{w} A) i) := by
  let : Functor.Linear A
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{w} A) (.up ℤ) i) := by
    constructor
    intro X Y f r
    ext <;> rfl
  let : Functor.Linear A
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (.up ℤ) i) :=
    Functor.linear_of_iso A
      (HomologicalComplex.homologyFunctorIso (ModuleCat.{w} A) (.up ℤ) i).symm
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{w} A) (.up ℤ)) A _ _).mp
      (Functor.linear_of_iso A
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} A) i).symm)

/-- The right adjoint of an `R`-linear functor between `R`-linear categories is `R`-linear. -/
public theorem rightAdjoint_linear
    {R : Type*} [CommRing R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} [Functor.Linear R F] (adj : F ⊣ G) :
    Functor.Linear R G := by
  constructor
  intro X Y f r
  apply (adj.homEquiv (G.obj X) Y).symm.injective
  rw [adj.homEquiv_counit, adj.homEquiv_counit]
  calc
    F.map (G.map (r • f)) ≫ adj.counit.app Y = adj.counit.app X ≫ (r • f) := by
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] using
        adj.counit.naturality (r • f)
    _ = r • (adj.counit.app X ≫ f) := by rw [Linear.comp_smul]
    _ = r • (F.map (G.map f) ≫ adj.counit.app Y) :=
      congrArg (r • ·) (by simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj] using
        (adj.counit.naturality f).symm)
  simp only [Functor.map_smul, Linear.smul_comp]

/-- **Multiplication by a ring element induces multiplication by that element on local
cohomology.** The functor `M ↦ H^i_{V(I)}(M)` is `A`-linear — the inclusion of the derived objects
with `I`-power-torsion cohomology, the homology functors and `RΓ_{V(I)}` are all `A`-linear, the
last because it is a right adjoint of an `A`-linear functor — so it carries `x • 𝟙 M` to
`x • 𝟙 H^i_{V(I)}(M)`. -/
public lemma localCohomologyModuleMap_lsmul
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{w} A) (x : A) (i : ℤ) :
    localCohomologyModuleMap A I hI M M (ModuleCat.ofHom (LinearMap.lsmul A M x)) i =
      x • 𝟙 (localCohomologyModule A I hI M i) := by
  let P := Dualizing.derivedPowerTorsionProperty A I hI
  let G := (Dualizing.localCohomologyRightAdjoint
    A I hI).1
  let adj : P.ι ⊣ G := (Dualizing.localCohomologyRightAdjoint
    A I hI).2
  let : Functor.Linear A P.ι := inferInstance
  let : Functor.Linear A (Dualizing.localCohomologyFunctor A I hI) :=
    rightAdjoint_linear adj
  let : Functor.Linear A G := rightAdjoint_linear adj
  let : Functor.Linear A (DerivedCategory.singleFunctor (ModuleCat.{w} A) 0) := inferInstance
  let : Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{w} A) i) :=
    derivedCategory_homologyFunctor_linear A i
  let H := DerivedCategory.homologyFunctor (ModuleCat.{w} A) i
  let F : ModuleCat.{w} A ⥤ ModuleCat.{w} A :=
    DerivedCategory.singleFunctor (ModuleCat.{w} A) 0 ⋙
      Dualizing.localCohomologyFunctor.{u, w} A I hI ⋙ P.ι ⋙ H
  let : Functor.Linear A F := inferInstance
  have hf : ModuleCat.ofHom (LinearMap.lsmul A M x) = x • 𝟙 M := by
    ext m
    rfl
  change F.map (ModuleCat.ofHom (LinearMap.lsmul A M x)) = _
  rw [hf, Functor.map_smul]
  exact congrArg (fun z => x • z) (F.map_id M)

attribute [local instance] derivedPowerTorsionProperty_isClosedUnderIsomorphisms
attribute [local instance] derivedPowerTorsionProperty_isTriangulated

/-- If local cohomology of `M/xM` is Artinian in degree `i - 1`, then the kernel of
multiplication by `x` on `Hⁱ_𝔪(M)` is Artinian. -/
private lemma isArtinian_localCohomology_smulKernel
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{w} A) (x : A) (_hx : x ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsSMulRegular (M : Type w) x) (i : ℤ)
    (hprev : IsArtinian A
      (localCohomologyModule A
        (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
        (ModuleCat.of A (QuotSMulTop x (M : Type w))) (i - 1))) :
    IsArtinian A
      (LinearMap.ker (LinearMap.lsmul A
        (localCohomologyModule A
          (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
          M i) x)) := by
  let I := IsLocalRing.maximalIdeal A
  let hI := I.fg_of_isNoetherianRing
  let S := ModuleCat.smulShortComplex M x
  have hS : S.ShortExact := hreg.smulShortComplex_shortExact
  let T₂ := idealLocalCohomologyTriangle A I hI S hS
  have hT₂ := idealLocalCohomologyTriangle_distinguished A I hI S hS
  let H := DerivedCategory.homologyFunctor (ModuleCat.{w} A) i
  let R := ShortComplex.mk
    (DerivedCategory.HomologySequence.δ T₂ (i - 1) i (by omega)) (H.map T₂.mor₁)
    (DerivedCategory.HomologySequence.δ_comp T₂ hT₂ (i - 1) i (by omega))
  have hR : R.Exact := DerivedCategory.HomologySequence.exact₁ T₂ hT₂ (i - 1) i (by omega)
  have : IsArtinian A R.X₁ := hprev
  have : IsArtinian A (LinearMap.range R.f.hom) :=
    isArtinian_of_surjective R.X₁ R.f.hom.rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hker : IsArtinian A (LinearMap.ker R.g.hom) := by
    rw [← (ShortComplex.moduleCat_exact_iff_range_eq_ker R).mp hR]
    infer_instance
  have hmor : R.g.hom = (localCohomologyModuleMap A I hI M M S.f i).hom := by
    dsimp [R, T₂, idealLocalCohomologyTriangle, localCohomologyModuleMap,
      Dualizing.localCohomologyFunctor, DerivedCategory.triangleOfSES]
    rfl
  have hSf : S.f = ModuleCat.ofHom (LinearMap.lsmul A M x) := by
    simp [S, ModuleCat.smulShortComplex]
  have hkernel : LinearMap.ker R.g.hom =
      LinearMap.ker (LinearMap.lsmul A (localCohomologyModule A I hI M i) x) := by
    rw [hmor, hSf, localCohomologyModuleMap_lsmul A I hI M x i]
    congr 1
  exact hkernel ▸ hker

/-- Degree-zero local cohomology of a finite module over a Noetherian local ring is Artinian:
it embeds in `M` as a finite torsion submodule, hence has finite length. -/
private lemma isArtinian_localCohomology_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{w} A) [Module.Finite A M] :
    IsArtinian A
      (localCohomologyModule A
        (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
        M 0) := by
  let f := localCohomologyZeroToModule A
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M
  have hf : Function.Injective f.hom :=
    localCohomologyZeroToModule_injective A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M
  let R := LinearMap.range f.hom
  have : Module.Finite A R := Module.Finite.of_injective R.subtype R.subtype_injective
  have hT : IsIPowerTorsion A R (IsLocalRing.maximalIdeal A) := by
    intro y
    rcases y with ⟨z, ⟨x, rfl⟩⟩
    obtain ⟨n, hn, hkill⟩ := (localCohomologyModule_torsion A M 0) x
    refine ⟨n, hn, ?_⟩
    intro a ha
    apply Subtype.ext
    simpa [map_smul] using congrArg f.hom (hkill a ha)
  have : IsArtinian A R :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (finiteLength_of_finite_maximalTorsion A R hT)).2
  exact isArtinian_of_linearEquiv (LinearEquiv.ofInjective f.hom hf).symm

/-- A single object placed in degree zero has no cohomology in any nonzero degree. -/
private lemma isZero_homology_single_obj (C : Type v) [Category.{u} C] [Abelian C]
    [HasDerivedCategory C] (M : C) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C 0).obj M)) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors C i).app _)

/-- The `I`-primary component of a module is `I`-power torsion. -/
private lemma primaryComponent_torsion
    (A : Type u) [CommRing A] (I : Ideal A) (M : Type w)
    [AddCommGroup M] [Module A M] :
    IsIPowerTorsion A (Ideal.primaryComponent M I) I := by
  intro x
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x.1).mp x.2
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  intro a ha
  apply Subtype.ext
  simpa using (Submodule.mem_torsionBySet_iff _ _).mp hn
    ⟨a, Ideal.pow_le_pow_right (Nat.le_succ n) ha⟩

/-- An `I`-power-torsion module has no local cohomology supported in `V(I)` in positive degrees. -/
private lemma isZero_localCohomology_of_torsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{w} A)
    (hM : IsIPowerTorsion A (M : Type w) I) (i : ℤ) (hi : 0 < i) :
    IsZero (localCohomologyModule A I hI M i) := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M
  let P := Dualizing.derivedPowerTorsionProperty A I hI
  have hP : P X := by
    intro j
    by_cases hj : j = 0
    · subst j
      exact (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} A) 0).app M).symm
        hM
    · exact (Dualizing.powerTorsionModuleProperty A I hI).prop_of_isZero
        (isZero_homology_single_obj (ModuleCat.{w} A) M j hj)
  let Y : Dualizing.PowerTorsionDerivedCategory A I hI := ⟨X, hP⟩
  let G := Dualizing.localCohomologyRightAdjoint A I hI
  let adj := Dualizing.localCohomologyAdjunction A I hI
  have : IsIso (adj.counit.app X) := Adjunction.isIso_counit_app_of_iso adj (Iso.refl (P.ι.obj Y))
  let e : (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj (G.1.obj X) ≅ X :=
    asIso (adj.counit.app X)
  have hsingle := isZero_homology_single_obj (ModuleCat.{w} A) M i (by omega)
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
    ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj X)))
  exact IsZero.of_iso hsingle
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).mapIso e)

/-- In positive degrees, dividing by the `I`-primary component does not change local cohomology. -/
private lemma localCohomologyModuleMap_quotientPrimary_isIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{w} A)
    (i : ℤ) (hi : 0 < i) :
    IsIso (localCohomologyModuleMap A I hI M
      (ModuleCat.of A (M ⧸ Ideal.primaryComponent (M : Type w) I))
      (ModuleCat.ofHom (Ideal.primaryComponent (M : Type w) I).mkQ) i) := by
  let N := Ideal.primaryComponent (M : Type w) I
  let S : ShortComplex (ModuleCat.{w} A) :=
    ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ) (by ext; simp)
  have hS : S.ShortExact := by
    refine ModuleCat.shortComplex_shortExact S ?_ N.subtype_injective N.mkQ_surjective
    exact LinearMap.exact_subtype_mkQ N
  have h₀ := isZero_localCohomology_of_torsion A I hI (ModuleCat.of A N)
    (primaryComponent_torsion A I (M : Type w)) i hi
  have h₁ := isZero_localCohomology_of_torsion A I hI (ModuleCat.of A N)
    (primaryComponent_torsion A I (M : Type w)) (i + 1) (by omega)
  have hinj : Function.Injective (localCohomologyModuleMap A I hI M
      (ModuleCat.of A (M ⧸ N)) (ModuleCat.ofHom N.mkQ) i).hom := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (exact_localCohomologyModuleMap A I hI S i hS y).mp hy
    have : Subsingleton (localCohomologyModule A I hI S.X₁ i) :=
      ModuleCat.isZero_iff_subsingleton.mp h₀
    rw [Subsingleton.elim z 0, map_zero]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj,
    surjective_localCohomologyModuleMap_of_isZero_X₁_succ A I hI S i hS h₁⟩

/-- A module over a local ring whose multiplication-by-`x` kernel is Artinian, for some `x` in
the maximal ideal, has finite socle. -/
private lemma finiteSocle_of_artinian_smulKernel
    (A : Type u) [CommRing A] [IsLocalRing A]
    (N : Type w) [AddCommGroup N] [Module A N] (x : A)
    (hx : x ∈ IsLocalRing.maximalIdeal A)
    (hK : IsArtinian A (LinearMap.ker (LinearMap.lsmul A N x))) :
    Dualizing.HasFiniteSocle A N := by
  let S := Submodule.torsionBySet A N (IsLocalRing.maximalIdeal A : Set A)
  let hS : Module.IsTorsionBySet A S (IsLocalRing.maximalIdeal A : Set A) :=
    Submodule.torsionBySet_isTorsionBySet _
  let : Module (IsLocalRing.ResidueField A) S := hS.module
  let : IsScalarTower A (IsLocalRing.ResidueField A) S := hS.isScalarTower
  let K := LinearMap.ker (LinearMap.lsmul A N x)
  let f : S →ₗ[A] K := LinearMap.codRestrict K S.subtype (by
    intro z
    apply LinearMap.mem_ker.mpr
    change x • z.1 = 0
    exact (Submodule.mem_torsionBySet_iff _ _).mp z.2 ⟨x, hx⟩)
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun y : K => (y.1 : N)) h)
  have : IsArtinian A K := hK
  exact ((IsArtinianRing.tfae (R := IsLocalRing.ResidueField A) (M := S)).out 3 1).mp
    (isArtinian_of_tower A (isArtinian_of_injective f hf))

/-- A subsingleton module is Artinian. -/
private lemma isArtinian_of_isZeroModule
    (A : Type u) [CommRing A] (N : Type w) [AddCommGroup N] [Module A N]
    (hN : Subsingleton N) : IsArtinian A N :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp IsFiniteLength.of_subsingleton).2

/-- All local cohomology of a subsingleton module vanishes. -/
private lemma isZero_localCohomology_of_subsingleton
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{w} A) [Subsingleton M] (i : ℤ) :
    IsZero (localCohomologyModule A I hI M i) := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, w} A I hI
  let G := (Dualizing.localCohomologyRightAdjoint
    A I hI).1
  let adj := (Dualizing.localCohomologyRightAdjoint
    A I hI).2
  let : P.ι.Additive := ⟨by intros; rfl⟩
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  let L := Dualizing.localCohomologyFunctor.{u, w} A I hI
  let : L.Additive := by
    change G.Additive
    infer_instance
  have hM : IsZero M := ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  let s := DerivedCategory.singleFunctor (ModuleCat.{w} A) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{w} A) i
  change IsZero (H.obj (P.ι.obj (L.obj (s.obj M))))
  exact H.map_isZero (P.ι.map_isZero (L.map_isZero (s.map_isZero hM)))

/-- Artinianness transfers along an isomorphism of modules. -/
private lemma isArtinian_of_moduleIso
    (A : Type u) [CommRing A] (M N : ModuleCat.{w} A) (f : M ⟶ N)
    [IsIso f] [IsArtinian A N] : IsArtinian A M :=
  isArtinian_of_linearEquiv (asIso f).toLinearEquiv.symm

/-- Induction on the dimension of the support: local cohomology of a finite module whose
support has dimension `e` is Artinian in every degree. -/
private theorem isArtinian_localCohomology_of_supportDim
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (e : ℕ) :
    ∀ (M : ModuleCat.{w} A), Module.Finite A M →
      Module.supportDim A (M : Type w) = ((e : ℕ∞) : WithBot ℕ∞) →
      ∀ i : ℤ, IsArtinian A
        (localCohomologyModule A
          (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
          M i) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro M hM hdim i
    let : Module.Finite A M := hM
    by_cases hiNeg : i < 0
    · have hz := isZero_localCohomologyModule_of_neg A (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i hiNeg
      exact isArtinian_of_isZeroModule A _ (ModuleCat.isZero_iff_subsingleton.mp hz)
    by_cases hiZero : i = 0
    · subst i
      exact isArtinian_localCohomology_zero A M
    have hiPos : 0 < i := by omega
    let I := IsLocalRing.maximalIdeal A
    let hI := I.fg_of_isNoetherianRing
    let N := Ideal.primaryComponent (M : Type w) I
    let Q := (M : Type w) ⧸ N
    let Qcat : ModuleCat.{w} A := ModuleCat.of A Q
    let : Module.Finite A Q := Module.Finite.of_surjective N.mkQ N.mkQ_surjective
    have hnot : I ∉ associatedPrimes A Q :=
      maximalIdeal_notMem_associatedPrimes_quotient_primaryComponent A (M : Type w)
    have hIso : IsIso (localCohomologyModuleMap A I hI M Qcat
        (ModuleCat.ofHom N.mkQ) i) :=
      localCohomologyModuleMap_quotientPrimary_isIso A I hI M i hiPos
    have hQle : Module.supportDim A Q ≤ Module.supportDim A (M : Type w) :=
      Module.supportDim_le_of_surjective N.mkQ N.mkQ_surjective
    have hArtQ : IsArtinian A (localCohomologyModule A I hI Qcat i) := by
      by_cases hQsub : Subsingleton Q
      · let : Subsingleton Qcat := hQsub
        exact isArtinian_of_isZeroModule A _ (ModuleCat.isZero_iff_subsingleton.mp
          (isZero_localCohomology_of_subsingleton A I hI Qcat i))
      · let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQsub
        obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast A Q
        have hdle : d ≤ e := by
          have hle : ((d : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ∞) : WithBot ℕ∞) := by
            simpa [hd, hdim] using hQle
          exact_mod_cast hle
        obtain ⟨x, hx, hreg⟩ :=
          (exists_smulRegular_iff_maximalIdeal_notMem_associatedPrimes (R := A) (Q := Q)).mpr
            hnot
        let Qx := QuotSMulTop x Q
        let Jx : Submodule A Q := x • (⊤ : Submodule A Q)
        let : Module.Finite A Qx := Module.Finite.of_surjective Jx.mkQ Jx.mkQ_surjective
        have hdrop := Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx
        have hQxSub : ¬ Subsingleton Qx := by
          intro hsub
          let : Subsingleton Qx := hsub
          have hbot : Module.supportDim A Qx = ⊥ :=
            Module.supportDim_eq_bot_of_subsingleton A Qx
          rw [hbot, hd] at hdrop
          simp at hdrop
        let : Nontrivial Qx := not_subsingleton_iff_nontrivial.mp hQxSub
        obtain ⟨d', hd'⟩ := exists_supportDim_eq_natCast A Qx
        have hnat : d' + 1 = d := by
          have h' := hdrop
          rw [hd', hd] at h'
          exact_mod_cast h'
        have hd'lt : d' < e := by omega
        have hprev := ih d' hd'lt (ModuleCat.of A Qx) inferInstance hd' (i - 1)
        have hker := isArtinian_localCohomology_smulKernel A Qcat x hx hreg i hprev
        have hsocle := finiteSocle_of_artinian_smulKernel A _ x hx hker
        exact (Dualizing.isArtinian_iff_powerTorsion_and_finiteSocle A _).mpr
          ⟨localCohomologyModule_torsion A Qcat i, hsocle⟩
    have := hIso
    exact isArtinian_of_moduleIso A (localCohomologyModule A I hI M i)
      (localCohomologyModule A I hI Qcat i)
      (localCohomologyModuleMap A I hI M Qcat (ModuleCat.ofHom N.mkQ) i)

/-- Local cohomology of a finite module over a Noetherian local ring has the
descending chain condition in every degree. -/
@[stacks 0DX0 "part (1)"]
public theorem isArtinian_localCohomology_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{w} A) [Module.Finite A M] (i : ℤ) :
    IsArtinian A
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
        ((Dualizing.derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).ι.obj
          ((Dualizing.localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
            (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M)))) := by
  change IsArtinian A
    (localCohomologyModule A
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i)
  by_cases hM : Subsingleton (M : Type w)
  · let : Subsingleton M := hM
    have hz := isZero_localCohomology_of_subsingleton A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i
    exact isArtinian_of_isZeroModule A _ (ModuleCat.isZero_iff_subsingleton.mp hz)
  · let : Module.Finite A M := inferInstance
    let : Nontrivial (M : Type w) := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨e, he⟩ := exists_supportDim_eq_natCast A (M : Type w)
    exact isArtinian_localCohomology_of_supportDim A e M inferInstance he i
end Stacks.LocalCohomology

end
