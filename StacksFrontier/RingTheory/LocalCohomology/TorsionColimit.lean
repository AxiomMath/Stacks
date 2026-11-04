module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.Kunneth
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Basic
import StacksFrontier.Homology.HomologyColimit

/-!
# Local cohomology as a colimit of derived Hom

For a finitely generated ideal `I`, local cohomology with support in `I` is the homotopy
colimit of the derived Hom complexes from the quotients by the powers of `I`.  Its cohomology
modules are consequently the corresponding filtered colimits of Ext modules.

## Main definitions

* `Stacks.LocalCohomology.homPowersComplex` is the system of Hom complexes out of the single
  complexes on `R ⧸ I ^ n`, and `Stacks.LocalCohomology.homPowersColimitIso` identifies its
  colimit with the `I`-power-torsion subcomplex.
* `Stacks.LocalCohomology.homologyToDerivedEquiv` identifies the cohomology of a Hom complex
  into a K-injective complex with the corresponding module of morphisms of the derived category,
  and `Stacks.LocalCohomology.derivedHomPowersHomologyIsoExt` assembles these into an
  isomorphism of `ℕ`-indexed systems.

The objects compared here — the `I`-power-torsion subcomplex `Dualizing.powerTorsionComplex`,
local cohomology `Dualizing.localCohomology`, the derived Hom system
`Dualizing.derivedHomPowersOf` and the Ext system `Dualizing.extPowers` — are those of
`StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Basic`.

## Main results

* `Stacks.LocalCohomology.localCohomology_isHomotopyColimit_derivedHomPowers` identifies local
  cohomology with the homotopy colimit of the derived Hom system.
* `Stacks.LocalCohomology.localCohomologyHomologyIsoColimitExt` identifies every cohomology
  module with the filtered colimit of the corresponding Ext modules.

## Implementation notes

We choose a K-injective representative of each `K ∈ D(R)`. Thus `RHom(R/I^n,K)` is
represented by the ordinary Hom complex into that representative, while `RΓ_I(K)` is represented
by its termwise subcomplex of elements killed by some power of `I`. The Ext groups live one
universe above the homology objects in the standard unbounded derived category, so the latter
are universe-lifted when stating their natural comparison and colimit. The finite-generation
hypothesis in the source is not used by either computation. Isomorphisms replace the source's
conventional equalities.

## References

* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (R : Type u) [CommRing R]

/-- The standard unbounded derived category of `R`-modules has countable coproducts. -/
noncomputable local instance :
    HasCountableCoproducts (DerivedCategory (ModuleCat.{u} R)) := by
  apply derivedCategory_hasCountableCoproducts
  exact ⟨inferInstance, fun J _ ↦ ⟨inferInstance, inferInstance⟩⟩

open Dualizing (powerTorsionComplex kInjectiveRepresentative kInjectiveRepresentativeIso
  localCohomology quotientSingle quotientPowerSucc derivedHomPowers derivedHomPowersOf extPowers)

open CochainComplex.HomComplex

/-- Two maps out of `R ⧸ I` agree as soon as they agree on the class of `1`. -/
lemma quotientHom_ext (I : Ideal R) (M : ModuleCat.{u} R)
    {f g : ModuleCat.of R (R ⧸ I) ⟶ M} (h : f (1 : R ⧸ I) = g 1) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : Ideal.Quotient.mk I r = r • (1 : R ⧸ I) := by
    show Ideal.Quotient.mk I r = Ideal.Quotient.mk I r * 1
    exact (mul_one _).symm
  rw [hr, map_smul, map_smul, h]

/-- Evaluation at the class of `1`, identifying a degree-`q` cochain out of the single complex
on `R ⧸ I` with an element of `J^q` killed by `I`. -/
noncomputable def singleEval (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    Cochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (R ⧸ I))) J q →ₗ[R] J.X q where
  toFun z := (Cochain.fromSingleEquiv (zero_add q) z) 1
  map_add' _ _ := by simp
  map_smul' r z := by
    simp [Cochain.fromSingleEquiv, Cochain.smul_v, Linear.comp_smul]

/-- Evaluation at the class of `1` sends the cochain built from `f` to `f 1`. -/
private theorem singleEval_fromSingleMk (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) (f : ModuleCat.of R (R ⧸ I) ⟶ J.X q) :
    singleEval R I J q (Cochain.fromSingleMk f (zero_add q)) = f 1 :=
  by simp [singleEval]

/-- Evaluation at the class of `1` is injective. -/
lemma singleEval_injective (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    Function.Injective (singleEval R I J q) := by
  intro x y h
  exact (Cochain.fromSingleEquiv (zero_add q)).injective (quotientHom_ext R I (J.X q) h)

/-- The value of `singleEval` is killed by `I`. -/
lemma singleEval_mem (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) (z) :
    singleEval R I J q z ∈ Submodule.torsionBySet R (J.X q) I := by
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  show a.val • (Cochain.fromSingleEquiv (zero_add q) z) 1 = 0
  rw [← map_smul]
  have h : a.val • (1 : R ⧸ I) = 0 := by
    show Ideal.Quotient.mk I a.val * 1 = 0
    rw [mul_one, Ideal.Quotient.eq_zero_iff_mem.mpr a.property]
  rw [h, map_zero]

/-- Evaluation at the class of `1` hits every element of `J^q` killed by `I`. -/
lemma singleEval_surjective (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) (x : J.X q)
    (hx : x ∈ Submodule.torsionBySet R (J.X q) I) :
    ∃ z, singleEval R I J q z = x := by
  let f : R ⧸ I →ₗ[R] J.X q := I.liftQ (LinearMap.toSpanSingleton R (J.X q) x)
    (fun r hr ↦ (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩)
  refine ⟨Cochain.fromSingleMk (ModuleCat.ofHom f) (zero_add q), ?_⟩
  rw [singleEval_fromSingleMk]
  exact one_smul R x

/-- Evaluation at the class of `1` intertwines the cochain differential with the differential
of `J`. -/
lemma singleEval_d (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (q q' : ℤ) (z) :
    singleEval R I J q' (δ q q' z) = (J.d q q') (singleEval R I J q z) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  rw [Cochain.δ_fromSingleMk _ _ _ q' (zero_add q'), singleEval_fromSingleMk,
    singleEval_fromSingleMk]
  simp

/-- The `ℕ`-indexed system of Hom complexes `Hom(R/I^n, J)`. -/
noncomputable def homPowersComplex (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  Functor.ofSequence (X := fun n ↦ CochainComplex.HomComplexR R (quotientSingle R I n) J)
    (fun n ↦ Stacks.HomComplex.TensorHomMap.precomp R _ _ J
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n)))

/-- The map `Hom(R/I^n, J) → Γ_I(J)` evaluating a cochain at the class of `1`. -/
noncomputable def homPowersToTorsion (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (homPowersComplex R I J).obj n ⟶ powerTorsionComplex R I J where
  f q := ModuleCat.ofHom ((singleEval R (I ^ n) J q).codRestrict _ fun z ↦
    (Ideal.primaryComponent_mem (J.X q) I _).mpr ⟨n, singleEval_mem R (I ^ n) J q z⟩)
  comm' q q' _ := ModuleCat.hom_ext <| LinearMap.ext fun z ↦
    Subtype.ext (singleEval_d R (I ^ n) J q q' z).symm

/-- The maps `Hom(R/I^n, J) → Γ_I(J)` are compatible with the transition maps of the system. -/
lemma homPowersToTorsion_naturality (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (homPowersComplex R I J).map (homOfLE (Nat.le_succ n)) ≫
      homPowersToTorsion R I J (n + 1) = homPowersToTorsion R I J n := by
  simp only [homPowersComplex, Functor.ofSequence_map_homOfLE_succ]
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z q (zero_add q)
  show singleEval R (I ^ (n + 1)) J q
      ((Cochain.ofHom ((CochainComplex.singleFunctor _ 0).map
        (quotientPowerSucc R I n))).comp (Cochain.fromSingleMk f (zero_add q)) (zero_add q)) =
    singleEval R (I ^ n) J q (Cochain.fromSingleMk f (zero_add q))
  rw [← Cochain.fromSingleMk_precomp, singleEval_fromSingleMk, singleEval_fromSingleMk]
  show f (Ideal.Quotient.factorPowSucc I n 1) = f 1
  rw [map_one]

/-- The cocone on the system of Hom complexes with vertex the `I`-power-torsion subcomplex. -/
noncomputable def homPowersCocone (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) : Cocone (homPowersComplex R I J) where
  pt := powerTorsionComplex R I J
  ι := NatTrans.ofSequence (homPowersToTorsion R I J) (fun n ↦ by
    simpa using homPowersToTorsion_naturality R I J n)

/-- The `I`-power-torsion subcomplex is the colimit of the Hom complexes `Hom(R/I^n, J)`:
in each degree, evaluation at the class of `1` identifies `Hom(R/I^n, J^q)` with the elements
of `J^q` killed by `I^n`, and the torsion submodule is the union of those. -/
noncomputable def homPowersCoconeIsColimit (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) : IsColimit (homPowersCocone R I J) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  letI := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (forget (ModuleCat.{u} R))
  letI := reflectsColimit_of_reflectsIsomorphisms
    (homPowersComplex R I J ⋙ HomologicalComplex.eval _ _ q) (forget (ModuleCat.{u} R))
  apply isColimitOfReflects (forget (ModuleCat.{u} R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (J.X q) I x.val).mp x.property
    obtain ⟨z, hz⟩ := singleEval_surjective R (I ^ n) J q x.val hn
    exact ⟨n, z, Subtype.ext hz.symm⟩
  · intro n x y h
    obtain rfl := singleEval_injective R (I ^ n) J q (congrArg Subtype.val h)
    exact ⟨n, 𝟙 n, rfl⟩

/-- The canonical identification of the colimit of the Hom complexes with the
`I`-power-torsion subcomplex. -/
noncomputable def homPowersColimitIso (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) :
    colimit (homPowersComplex R I J) ≅ powerTorsionComplex R I J :=
  (colimit.isColimit _).coconePointUniqueUpToIso (homPowersCoconeIsColimit R I J)

/-- Localizing the system of Hom complexes gives the system of derived Hom objects. -/
lemma homPowersComplex_comp_Q (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) :
    homPowersComplex R I J ⋙ DerivedCategory.Q = derivedHomPowers R I J := by
  refine CategoryTheory.Functor.hext (F := homPowersComplex R I J ⋙ DerivedCategory.Q)
    (G := derivedHomPowers R I J) (fun _ ↦ rfl) ?_
  intro n m f
  refine heq_of_eq ?_
  have h := (NatTrans.ofSequence
    (F := homPowersComplex R I J ⋙ DerivedCategory.Q)
    (G := derivedHomPowers R I J) (fun n ↦ 𝟙 _) (fun n ↦ by
      dsimp only [homPowersComplex, derivedHomPowers, Functor.comp_map]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)).naturality f
  exact ((Category.comp_id _).symm.trans h).trans (Category.id_comp _)

/-- The degree-`q` cocycles of the Hom complex: the kernel of the outgoing differential of the
relevant short complex of modules, which is the cycles object of its explicit left homology
data. -/
noncomputable abbrev homCycles (L J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :=
  ModuleCat.of R (LinearMap.ker
    (((CochainComplex.HomComplexR R L J).sc' (q - 1) q (q + 1)).g).hom)

/-- A cycle of the Hom complex, read as a cocycle. -/
noncomputable def cycleAsCocycle (L J : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ)
    (z : homCycles R L J q) : Cocycle L J q := ⟨z.val, z.property⟩

/-- The map from cycles of the Hom complex to morphisms `L ⟶ J[q]` in the derived category. -/
noncomputable def cycleToDerived (L J : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : ℤ) : homCycles R L J q →ₗ[R]
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj L) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (J⟦q⟧))) where
  toFun z := DerivedCategory.Qh.map
    (CohomologyClass.toHom (CohomologyClass.mk (cycleAsCocycle R L J q z)))
  map_add' x y := by
    change DerivedCategory.Qh.map (CohomologyClass.toHom
      (CohomologyClass.mk (cycleAsCocycle R L J q x + cycleAsCocycle R L J q y))) = _
    simp
  map_smul' r z := by
    simp only [CohomologyClass.toHom_mk]
    rw [← Functor.map_smul, ← Functor.map_smul]
    congr 2

/-- For K-injective `J`, every morphism `L ⟶ J[q]` of the derived category comes from a cycle
of the Hom complex. -/
lemma cycleToDerived_surjective (L J : CochainComplex (ModuleCat.{u} R) ℤ)
    [J.IsKInjective] (q : ℤ) : Function.Surjective (cycleToDerived R L J q) := by
  intro f
  obtain ⟨c, rfl⟩ := (cohomologyClassRHomAddEquivOfIsKInjective L J q).surjective f
  obtain ⟨z, rfl⟩ := c.mk_surjective
  exact ⟨⟨z.val, z.property⟩, rfl⟩

/-- For K-injective `J`, a cycle of the Hom complex dies in the derived category exactly when it
is a boundary. -/
lemma cycleToDerived_ker (L J : CochainComplex (ModuleCat.{u} R) ℤ)
    [J.IsKInjective] (q : ℤ) :
    (cycleToDerived R L J q).ker = LinearMap.range
      ((CochainComplex.HomComplexR R L J).sc' (q - 1) q (q + 1)).moduleCatToCycles := by
  ext z
  show cycleToDerived R L J q z = 0 ↔ _
  have hz : cycleToDerived R L J q z = 0 ↔
      cycleAsCocycle R L J q z ∈ coboundaries L J q := by
    show (cohomologyClassRHomAddEquivOfIsKInjective L J q)
      (CohomologyClass.mk (cycleAsCocycle R L J q z)) = 0 ↔ _
    rw [map_eq_zero_iff _ (cohomologyClassRHomAddEquivOfIsKInjective L J q).injective,
      CohomologyClass.mk_eq_zero_iff]
  rw [hz, mem_coboundaries_iff _ (q - 1) (by omega)]
  exact ⟨fun ⟨b, hb⟩ ↦ ⟨b, Subtype.ext hb⟩, fun ⟨b, hb⟩ ↦ ⟨b, congrArg Subtype.val hb⟩⟩

/-- For K-injective `J`, the degree-`q` cohomology of the Hom complex `Hom(L, J)` is the module
of morphisms `L ⟶ J[q]` in the derived category. -/
noncomputable def homologyToDerivedEquiv
    (L J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] (q : ℤ) :
    (CochainComplex.HomComplexR R L J).homology q ≃ₗ[R]
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj L) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (J⟦q⟧))) :=
  (((CochainComplex.HomComplexR R L J).homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
      ((CochainComplex.HomComplexR R L J).sc' (q - 1) q
        (q + 1)).moduleCatHomologyIso).toLinearEquiv).trans
    ((Submodule.quotEquivOfEq _ _ (cycleToDerived_ker R L J q).symm).trans
      ((cycleToDerived R L J q).quotKerEquivOfSurjective (cycleToDerived_surjective R L J q)))

/-- The quotient of the cycles by the boundaries, identified with the derived Hom module. This is
the second half of `homologyToDerivedEquiv`, isolated so that its behaviour on classes of cycles
is available. -/
noncomputable def quotientToDerivedEquiv
    (L J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] (q : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (cycleToDerived_ker R L J q).symm).trans
    ((cycleToDerived R L J q).quotKerEquivOfSurjective (cycleToDerived_surjective R L J q))

/-- `quotientToDerivedEquiv` sends the class of a cycle to the morphism it represents. -/
lemma quotientToDerivedEquiv_mk
    (L J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] (q : ℤ)
    (z : homCycles R L J q) :
    quotientToDerivedEquiv R L J q (Submodule.Quotient.mk z) = cycleToDerived R L J q z := by
  show (cycleToDerived R L J q).quotKerEquivOfSurjective
    (cycleToDerived_surjective R L J q)
      ((Submodule.quotEquivOfEq _ _ (cycleToDerived_ker R L J q).symm)
        (Submodule.Quotient.mk z)) = _
  rw [Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ z

/-- Precomposition with `f : L' ⟶ L` on cycles of the Hom complex. -/
noncomputable def cyclePrecomp {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (f : L' ⟶ L) (q : ℤ) :
    homCycles R L J q →ₗ[R] homCycles R L' J q :=
  (((Stacks.HomComplex.TensorHomMap.precomp R L' L J f).f q).hom.comp
    (LinearMap.ker (δ_hom R L J q (q + 1))).subtype).codRestrict _ (fun z ↦ by
      change δ q (q + 1) ((Cochain.ofHom f).comp z.val (zero_add q)) = 0
      rw [δ_ofHom_comp, show δ q (q + 1) z.val = 0 from z.property, Cochain.comp_zero])

/-- Precomposition on cycles corresponds to precomposition in the derived category. -/
lemma cycleToDerived_precomp {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (J : CochainComplex (ModuleCat.{u} R) ℤ) (f : L' ⟶ L) (q : ℤ)
    (z : homCycles R L J q) :
    cycleToDerived R L' J q (cyclePrecomp R J f q z) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫
        cycleToDerived R L J q z := by
  show DerivedCategory.Qh.map (CohomologyClass.toHom
      (CohomologyClass.mk ((cycleAsCocycle R L J q z).precomp f))) = _
  rw [CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp,
    Functor.map_comp, Functor.map_comp]
  rfl

/-- Precomposition with `f : L' ⟶ L` on the homology of the Hom complex, transported through
`quotientToDerivedEquiv`. -/
noncomputable def quotientPrecomp {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] (f : L' ⟶ L) (q : ℤ) :
    ((CochainComplex.HomComplexR R L J).sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData.H ⟶
      ((CochainComplex.HomComplexR R L' J).sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData.H :=
  ModuleCat.ofHom ((quotientToDerivedEquiv R L' J q).symm.toLinearMap.comp
    (({ toFun := fun g ↦ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ g
        map_add' := by intros; simp
        map_smul' := by intros; simp } : _ →ₗ[R] _).comp
      (quotientToDerivedEquiv R L J q).toLinearMap))

/-- The left homology map data computing the effect of precomposition by `f` on the homology of
the Hom complex. -/
noncomputable def leftHomologyPrecompData
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] (f : L' ⟶ L) (q : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' _ (.up ℤ) (q - 1) q (q + 1)).map
        (Stacks.HomComplex.TensorHomMap.precomp R L' L J f))
      ((CochainComplex.HomComplexR R L J).sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData
      ((CochainComplex.HomComplexR R L' J).sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData := by
  refine { φK := ModuleCat.ofHom (cyclePrecomp R J f q)
           φH := quotientPrecomp R J f q
           commi := rfl
           commf' := ?_
           commπ := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (δ_ofHom_comp f z q).symm
  · apply ModuleCat.hom_ext
    refine LinearMap.ext fun (z : homCycles R L J q) ↦ ?_
    apply (quotientToDerivedEquiv R L' J q).injective
    change quotientToDerivedEquiv R L' J q ((quotientToDerivedEquiv R L' J q).symm
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫
        quotientToDerivedEquiv R L J q (Submodule.Quotient.mk z))) =
      quotientToDerivedEquiv R L' J q (Submodule.Quotient.mk (cyclePrecomp R J f q z))
    rw [LinearEquiv.apply_symm_apply, quotientToDerivedEquiv_mk,
      quotientToDerivedEquiv_mk, cycleToDerived_precomp]

/-- `homologyToDerivedEquiv` is natural in the source complex. -/
lemma homologyToDerivedEquiv_precomp
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] (f : L' ⟶ L) (q : ℤ)
    (x : (CochainComplex.HomComplexR R L J).homology q) :
    homologyToDerivedEquiv R L' J q (homologyMap (Stacks.HomComplex.TensorHomMap.precomp R L' L J f)
      q x) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫
        homologyToDerivedEquiv R L J q x := by
  let H := CochainComplex.HomComplexR R L J
  let H' := CochainComplex.HomComplexR R L' J
  let ψ := Stacks.HomComplex.TensorHomMap.precomp R L' L J f
  have hn := (Functor.isoWhiskerRight
    (natIsoSc' (ModuleCat.{u} R) (.up ℤ) (q - 1) q (q + 1) (by simp) (by simp))
    (ShortComplex.homologyFunctor _)).hom.naturality ψ
  have hd := (leftHomologyPrecompData R J f q).homologyMap_comm
  change homologyMap ψ q ≫ (H'.homologyIsoSc' _ q _ (by simp) (by simp)).hom =
    (H.homologyIsoSc' _ q _ (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap ((shortComplexFunctor' _ (.up ℤ) (q - 1) q (q + 1)).map ψ) at hn
  have ht := congrArg (fun g ↦ g ≫
    ((H'.sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData.homologyIso).hom) hn
  simp only [Category.assoc] at ht
  rw [hd] at ht
  show quotientToDerivedEquiv R L' J q
    ((homologyMap ψ q ≫ (H'.homologyIsoSc' _ q _ (by simp) (by simp)).hom ≫
      ((H'.sc' (q - 1) q (q + 1)).moduleCatLeftHomologyData.homologyIso).hom) x) = _
  rw [ht]
  show quotientToDerivedEquiv R L' J q ((quotientToDerivedEquiv R L' J q).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The single complex on `R/I^n`, viewed in the derived category through the homotopy category,
is the single object `R/I^n`. -/
noncomputable def quotientSourceIso (I : Ideal R) (n : ℕ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (quotientSingle R I n)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ I ^ n)) :=
  (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- The shift of the chosen K-injective representative of `K`, viewed in the derived category,
is `K[q]`. -/
noncomputable def representativeShiftIso
    (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      ((kInjectiveRepresentative R K)⟦q⟧)) ≅ K⟦q⟧ :=
  (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    (DerivedCategory.Q.commShiftIso q).app _ ≪≫
      (shiftFunctor _ q).mapIso (kInjectiveRepresentativeIso R K)

/-- At each stage `n`, the degree-`q` cohomology of `RHom(R/I^n, K)` is `Ext^q(R/I^n, K)`. -/
noncomputable def homologyExtPointIso (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) (n : ℕ) :
    (derivedHomPowersOf R I K ⋙ DerivedCategory.homologyFunctor _ q ⋙
      ModuleCat.uliftFunctor.{u + 1} R).obj n ≅ (extPowers R I K q).obj n :=
  (ModuleCat.uliftFunctor.{u + 1} R).mapIso
    ((DerivedCategory.homologyFunctorFactors _ q).app _) ≪≫
    (ULift.moduleEquiv.trans
      ((homologyToDerivedEquiv R (quotientSingle R I n) (kInjectiveRepresentative R K) q).trans
        (Linear.homCongr R (quotientSourceIso R I n) (representativeShiftIso R K q)))).toModuleIso

/-- The identification of the single complexes on `R/I^n` is compatible with the transition
maps. -/
lemma quotientSourceIso_naturality (I : Ideal R) (n : ℕ) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n))) ≫
      (quotientSourceIso R I n).hom =
    (quotientSourceIso R I (n + 1)).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n) := by
  dsimp only [quotientSourceIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [← Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality]
  simp only [Category.assoc]
  have h := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).inv.naturality
    (quotientPowerSucc R I n)
  dsimp only [Functor.comp_map] at h
  rw [h]

/-- The identifications `H^q(RHom(R/I^n, K)) ≅ Ext^q(R/I^n, K)` are compatible with the
transition maps of the two systems. -/
lemma homologyExtPointIso_naturality (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) (n : ℕ) :
    (derivedHomPowersOf R I K ⋙ DerivedCategory.homologyFunctor _ q ⋙
        ModuleCat.uliftFunctor.{u + 1} R).map (homOfLE (Nat.le_succ n)) ≫
      (homologyExtPointIso R I K q (n + 1)).hom =
    (homologyExtPointIso R I K q n).hom ≫
      (extPowers R I K q).map (homOfLE (Nat.le_succ n)) := by
  let J := kInjectiveRepresentative R K
  let f := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n)
  let ψ := Stacks.HomComplex.TensorHomMap.precomp R _ _ J f
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality ψ q
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun (x : ULift.{u + 1}
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR R (quotientSingle R I n) J)))) ↦ ?_
  have hx := ConcreteCategory.congr_hom hn x.down
  simp only [ConcreteCategory.comp_apply] at hx
  simp only [Functor.comp_map, derivedHomPowersOf, derivedHomPowers, extPowers,
    Functor.ofSequence_map_homOfLE_succ]
  show ((quotientSourceIso R I (n + 1)).inv ≫
      homologyToDerivedEquiv R _ J q
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q).app _).hom
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map
            (DerivedCategory.Q.map ψ) x.down))) ≫
        (representativeShiftIso R K q).hom =
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n) ≫
      (((quotientSourceIso R I n).inv ≫
        homologyToDerivedEquiv R _ J q
          (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q).app _).hom x.down)) ≫
          (representativeShiftIso R K q).hom)
  simp only [Iso.app_hom]
  have hs := quotientSourceIso_naturality R I n
  have hs' : (quotientSourceIso R I (n + 1)).inv ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n) ≫
      (quotientSourceIso R I n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcat : ∀ g, ((quotientSourceIso R I (n + 1)).inv ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ g) ≫
      (representativeShiftIso R K q).hom =
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n) ≫
      ((quotientSourceIso R I n).inv ≫ g) ≫ (representativeShiftIso R K q).hom := fun g ↦ by
    simp only [← Category.assoc, hs']
  exact (congrArg (fun g ↦ ((quotientSourceIso R I (n + 1)).inv ≫ g) ≫
      (representativeShiftIso R K q).hom)
      ((congrArg (homologyToDerivedEquiv R (quotientSingle R I (n + 1)) J q) hx).trans
        (homologyToDerivedEquiv_precomp R J f q
          (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q).hom.app
            (CochainComplex.HomComplexR R (quotientSingle R I n) J)) x.down)))).trans (hcat _)

/-- Homology of the derived Hom system is naturally the system of Ext modules. -/
noncomputable def derivedHomPowersHomologyIsoExt (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    derivedHomPowersOf R I K ⋙ DerivedCategory.homologyFunctor _ q ⋙
        ModuleCat.uliftFunctor.{u + 1} R ≅
      extPowers R I K q := by
  let t := NatTrans.ofSequence (fun n ↦ (homologyExtPointIso R I K q n).hom)
    (by exact homologyExtPointIso_naturality R I K q)
  exact NatIso.ofComponents (homologyExtPointIso R I K q) (fun f ↦ t.naturality f)

section

variable {A : Type*} [Category A] [Abelian A]

/-- Homology commutes with colimits of `ℕ`-indexed systems of cochain complexes when colimits
over `ℕ` are exact: `H^i` is the short complex functor in degree `i` followed by the homology of
short complexes (`HomologicalComplex.homologyFunctorIso`), and both factors preserve colimits of
shape `ℕ`. -/
@[ega "III 1.1.6" "more general"]
lemma preservesColimitsOfShape_homologyFunctor
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] (i : ℤ) :
    PreservesColimitsOfShape ℕ
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i) :=
  have := CochainComplex.Kunneth.preservesColimitsOfShape_shortComplexFunctor (A := A) (J := ℕ) i
  have := Stacks.HomologyColimit.preservesColimitsOfShape_shortComplex_homologyFunctor
    (A := A) (J := ℕ)
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso A (ComplexShape.up ℤ) i).symm

attribute [local instance] preservesColimitsOfShape_homologyFunctor

/-- Universe lifting of modules preserves sequential colimits. -/
lemma ulift_preservesSequentialColimits :
    PreservesColimitsOfShape.{0, 0} ℕ (ModuleCat.uliftFunctor.{u + 1, u} R) := by
  let U := ModuleCat.uliftFunctor.{u + 1, u} R
  let V := CategoryTheory.forget (ModuleCat.{u + 1} R)
  let hbase : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits
      (forget (ModuleCat.{u} R))
  let : PreservesColimitsOfShape.{0, 0} ℕ (forget (ModuleCat.{u} R)) :=
    hbase.preserves_filtered_colimits ℕ
  let : PreservesColimitsOfShape.{0, 0} ℕ
      (CategoryTheory.uliftFunctor.{u + 1} : Type u ⥤ Type (u + 1)) := inferInstance
  let R' : Type (u + 1) := ULift.{u + 1, u} R
  let e : ModuleCat.{u + 1} R ≌ ModuleCat.{u + 1} R' :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : R' ≃+* R)
  let V' := CategoryTheory.forget (ModuleCat.{u + 1} R')
  let := preservesSmallestFilteredColimits_of_preservesFilteredColimits V'
  let : PreservesColimitsOfShape.{0, 0} ℕ V' := inferInstance
  let hV : e.functor ⋙ V' ≅ V :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ ↦ rfl)
  let : PreservesColimitsOfShape.{0, 0} ℕ (e.functor ⋙ V') := inferInstance
  let : PreservesColimitsOfShape.{0, 0} ℕ V :=
    preservesColimitsOfShape_of_natIso hV
  let : ReflectsColimitsOfShape.{0, 0} ℕ V :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  let : PreservesColimitsOfShape.{0, 0} ℕ (U ⋙ V) := by
    show PreservesColimitsOfShape.{0, 0} ℕ
      (forget (ModuleCat.{u} R) ⋙ CategoryTheory.uliftFunctor.{u + 1})
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves U V

attribute [local instance] ulift_preservesSequentialColimits

/-- Universe lifting of modules preserves the colimit of a given `ℕ`-indexed system. -/
lemma ulift_preservesSequentialColimit (F : ℕ ⥤ ModuleCat.{u} R)
    [HasColimit F] :
    PreservesColimit F (ModuleCat.uliftFunctor.{u + 1, u} R) :=
  inferInstance

attribute [local instance] ulift_preservesSequentialColimit

/-- **Stacks 0954.** In every degree, local cohomology is the filtered colimit of the Ext modules
from the quotients by powers of the ideal. -/
@[stacks 0954 "cohomology-module identification"]
noncomputable def localCohomologyHomologyIsoColimitExt (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    (ModuleCat.uliftFunctor.{u + 1} R).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).obj (localCohomology R I K)) ≅
      colimit (extPowers R I K q) := by
  let J := kInjectiveRepresentative R K
  let F := homPowersComplex R I J
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q
  let U : ModuleCat.{u} R ⥤ ModuleCat.{u + 1} R :=
    ModuleCat.uliftFunctor.{u + 1, u} R
  letI : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
    (AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)).ofShape ℕ
  letI : PreservesColimitsOfShape ℕ H :=
    preservesColimitsOfShape_homologyFunctor (A := ModuleCat.{u} R) q
  let e : F ⋙ H ⋙ U ≅
      derivedHomPowersOf R I K ⋙ DerivedCategory.homologyFunctor _ q ⋙ U := by
    change F ⋙ H ⋙ U ≅ derivedHomPowers R I J ⋙ DerivedCategory.homologyFunctor _ q ⋙ U
    rw [← homPowersComplex_comp_Q R I J]
    exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F (DerivedCategory.homologyFunctorFactors _ q).symm) U
  letI : PreservesColimit (F ⋙ H) U := by infer_instance
  exact U.mapIso ((DerivedCategory.homologyFunctorFactors _ q).app _) ≪≫
    U.mapIso (H.mapIso (homPowersColimitIso R I J).symm) ≪≫
    U.mapIso (preservesColimitIso H F) ≪≫ preservesColimitIso U (F ⋙ H) ≪≫
    HasColimit.isoOfNatIso (e ≪≫ derivedHomPowersHomologyIsoExt R I K q)

end

/-- **Stacks 0954.** Local cohomology is the homotopy colimit of the derived Hom complexes from
the powers of the ideal. -/
@[stacks 0954 "derived-category identification"]
theorem localCohomology_isHomotopyColimit_derivedHomPowers (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) :
    IsHomotopyColimit (derivedHomPowersOf R I K) (localCohomology R I K) := by
  let J := kInjectiveRepresentative R K
  show IsHomotopyColimit (derivedHomPowers R I J)
    (DerivedCategory.Q.obj (powerTorsionComplex R I J))
  let e := DerivedCategory.Q.mapIso (homPowersColimitIso R I J)
  let : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
    (AB5OfSize_of_univLE.{0, 0, u, u} (ModuleCat.{u} R)).ofShape ℕ
  have h := DerivedCategory.isHomotopyColimit_Q_obj_colimit (homPowersComplex R I J)
  rw [homPowersComplex_comp_Q] at h
  obtain ⟨p, q, h⟩ := h
  exact ⟨p ≫ e.hom, e.inv ≫ q, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp) (by simp))⟩

end Stacks.LocalCohomology
