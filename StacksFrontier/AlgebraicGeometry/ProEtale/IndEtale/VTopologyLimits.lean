module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Small
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.StandardFpqcCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard V coverings of inverse limits of affine schemes

A morphism from a cofiltered inverse limit of affine schemes over an affine scheme is a
standard V covering exactly when every stage morphism is a standard V covering. The inverse
system over the base is a functor `D` with a natural transformation `t` to the constant functor
at the base, its limit is a limit cone `c` with a compatible morphism `f` from its vertex to the
base, and singleton covering families are indexed by `Unit`.

## Main results

* `AlgebraicGeometry.ProEtale.isStandardVCovering_limit_iff'` characterizes a standard V
  covering of the limit of a small diagram by standard V coverings at every stage.
* `AlgebraicGeometry.ProEtale.isStandardVCovering_limit_iff` is the same statement for a
  diagram indexed by a category in an arbitrary universe, whose cocone of coordinate rings is a
  colimit on underlying sets.

## References

* [Stacks Project, Tag 0EVN](https://stacks.math.columbia.edu/tag/0EVN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w z

namespace AlgebraicGeometry.ProEtale

open scoped TensorProduct

/-- The ideal of an `R`-algebra `A`, for `R` a domain, consisting of the elements killed by
some nonzero scalar; its carrier is the torsion submodule `Submodule.torsion R A`. -/
private def torsionIdeal (R A : Type*) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] : Ideal A where
  carrier := Submodule.torsion R A
  zero_mem' := zero_mem _
  add_mem' hfirst hsecond := add_mem hfirst hsecond
  smul_mem' := by
    rintro factor element ⟨scalar, heq⟩
    refine ⟨scalar, ?_⟩
    change scalar • (factor * element) = 0
    rw [mul_comm factor element, ← smul_mul_assoc, heq, zero_mul]

/-- Membership in the torsion ideal, in terms of a nonzero scalar killing the element. -/
private lemma mem_torsionIdeal {R A : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] {element : A} :
    element ∈ torsionIdeal R A ↔ ∃ scalar : R, scalar ≠ 0 ∧ scalar • element = 0 := by
  simp [torsionIdeal, mem_nonZeroDivisors_iff_ne_zero]

/-- The quotient of an algebra over a domain by its ideal of torsion elements is
torsion-free. -/
private lemma torsionIdeal_quotient_isTorsionFree
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] :
    Module.IsTorsionFree R (A ⧸ torsionIdeal R A) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro scalar element heq
  by_cases hscalar : scalar = 0
  · exact Or.inl hscalar
  apply Or.inr
  obtain ⟨representative, rfl⟩ := Ideal.Quotient.mk_surjective element
  have hmem : scalar • representative ∈ torsionIdeal R A := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap] using heq
  obtain ⟨denominator, hdenominator, hzero⟩ := mem_torsionIdeal.mp hmem
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact mem_torsionIdeal.mpr ⟨denominator * scalar, mul_ne_zero hdenominator hscalar,
    by simpa only [mul_smul] using hzero⟩

/-- A ring map from an `R`-algebra to a domain which is injective on `R` kills every
`R`-torsion element. -/
private lemma torsionIdeal_le_ker
    {R A W : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [CommRing W] [IsDomain W] (map : A →+* W)
    (hinjective : Function.Injective (map.comp (algebraMap R A))) :
    torsionIdeal R A ≤ RingHom.ker map := by
  intro element hmem
  obtain ⟨scalar, hscalar, heq⟩ := mem_torsionIdeal.mp hmem
  have hnonzero : map (algebraMap R A scalar) ≠ 0 := fun hzero ↦
    hscalar (hinjective (by simpa using hzero))
  have hproduct : map (algebraMap R A scalar) * map element = 0 := by
    rw [← map.map_mul]
    simpa only [Algebra.smul_def, map.map_zero] using congrArg map heq
  exact (mul_eq_zero.mp hproduct).resolve_left hnonzero

/-- A flat algebra over a valuation ring whose structure map is local is faithfully flat. -/
private lemma faithfullyFlat_of_isLocalHom_of_valuationRing
    (R A : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A]
    [IsLocalHom (algebraMap R A)] : Module.FaithfullyFlat R A := by
  classical
  refine ⟨fun maximal hmaximal ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, ne_eq, Submodule.restrictScalars_eq_top_iff]
  have hspan : maximal = ⨆ element : maximal,
      Ideal.span ({element.val} : Set R) := by
    apply le_antisymm
    · intro element helement
      exact Submodule.mem_iSup_of_mem ⟨element, helement⟩
        (Ideal.mem_span_singleton_self element)
    · exact iSup_le fun element ↦ Ideal.span_le.mpr (by simp)
  have hnonempty : Nonempty maximal := ⟨0⟩
  have hdirected : Directed (· ≤ ·) (fun element : maximal ↦
      Ideal.map (algebraMap R A) (Ideal.span ({element.val} : Set R))) := by
    intro first second
    rcases le_total (Ideal.span ({first.val} : Set R))
        (Ideal.span ({second.val} : Set R)) with hle | hle
    · exact ⟨second, Ideal.map_mono hle, le_rfl⟩
    · exact ⟨first, le_rfl, Ideal.map_mono hle⟩
  intro htop
  have hone : (1 : A) ∈ Ideal.map (algebraMap R A) maximal := by rw [htop]; trivial
  rw [hspan, Ideal.map_iSup] at hone
  obtain ⟨element, helement⟩ := (Submodule.mem_iSup_of_directed _ hdirected).mp hone
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at helement
  obtain ⟨factor, hfactor⟩ := helement
  have hunit : IsUnit (algebraMap R A element.val) :=
    isUnit_iff_dvd_one.mpr ⟨factor, by simpa only [mul_comm] using hfactor.symm⟩
  have hunitR : IsUnit element.val := isUnit_of_map_unit (algebraMap R A) _ hunit
  exact hmaximal.ne_top (maximal.eq_top_of_isUnit_mem element.property hunitR)

/-- A compatible family of ring maps out of a filtered diagram of rings whose cocone is a
colimit on underlying sets descends to a ring map out of the cocone point. -/
private lemma ringHomDesc_of_typeColimit
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F)
    (hc : IsColimit ((forget CommRingCat).mapCocone c))
    (B : Type z) [CommRing B]
    (maps : ∀ i, F.obj i →+* B)
    (hmap : ∀ {i j} (arrow : i ⟶ j), (maps j).comp (F.map arrow).hom = maps i) :
    ∃ desc : c.pt →+* B, ∀ i, desc.comp (c.ι.app i).hom = maps i := by
  classical
  have hsurj := Types.jointly_surjective_of_isColimit hc
  let desc : c.pt → B := fun element ↦
    maps (hsurj element).choose (hsurj element).choose_spec.choose
  have hfac (i : J) (element : F.obj i) : desc (c.ι.app i element) = maps i element := by
    obtain ⟨stage, left, right, heq⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc).mp
        (hsurj (c.ι.app i element)).choose_spec.choose_spec
    change (F.map left) (hsurj (c.ι.app i element)).choose_spec.choose =
      (F.map right) element at heq
    show maps _ _ = _
    rw [← RingHom.congr_fun (hmap left), RingHom.comp_apply,
      heq, ← RingHom.comp_apply, hmap right]
  have hjoint (first second : c.pt) :
      ∃ (i : J) (left right : F.obj i), c.ι.app i left = first ∧ c.ι.app i right = second := by
    exact Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc first second
  let stage : J := Classical.choice IsFiltered.nonempty
  refine ⟨{ toFun := desc
            map_zero' := ?_
            map_one' := ?_
            map_add' := ?_
            map_mul' := ?_ }, fun i ↦ RingHom.ext (hfac i)⟩
  · simpa using hfac stage 1
  · intro first second
    obtain ⟨i, left, right, rfl, rfl⟩ := hjoint first second
    rw [← map_mul, hfac, hfac, hfac, map_mul]
  · simpa using hfac stage 0
  · intro first second
    obtain ⟨i, left, right, rfl, rfl⟩ := hjoint first second
    rw [← map_add, hfac, hfac, hfac, map_add]

/-- The point of a cocone on a filtered diagram of torsion-free algebras over a domain with
local structure maps, which is a colimit on underlying sets, carries a compatible algebra
structure which is again torsion-free with local structure map. -/
private lemma colimit_torsionFree_local
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (R : Type u) [CommRing R] [IsDomain R]
    (F : J ⥤ CommAlgCat.{z} R)
    [∀ i, Module.IsTorsionFree R (F.obj i)]
    [∀ i, IsLocalHom (algebraMap R (F.obj i))]
    (c : Cocone (F ⋙ forget₂ (CommAlgCat R) CommRingCat))
    (hc : IsColimit ((forget CommRingCat).mapCocone c)) :
    ∃ _algebra : Algebra R c.pt,
      Module.IsTorsionFree R c.pt ∧ IsLocalHom (algebraMap R c.pt) ∧
      ∀ i, (c.ι.app i).hom.comp (algebraMap R (F.obj i)) = algebraMap R c.pt := by
  classical
  let stage : J := Classical.choice IsFiltered.nonempty
  let base : R →+* c.pt := (c.ι.app stage).hom.comp (algebraMap R (F.obj stage))
  let : Algebra R c.pt := base.toAlgebra
  let inclusion (i : J) : F.obj i →+* c.pt := (c.ι.app i).hom
  have hbase (i : J) : (c.ι.app i).hom.comp (algebraMap R (F.obj i)) =
      algebraMap R c.pt := by
    obtain ⟨j, left, right, _⟩ := IsFilteredOrEmpty.cocone_objs i stage
    ext scalar
    show (c.ι.app i) (algebraMap R (F.obj i) scalar) =
      (c.ι.app stage) (algebraMap R (F.obj stage) scalar)
    have hleft := ConcreteCategory.congr_hom (c.ι.naturality left)
      (algebraMap R (F.obj i) scalar)
    have hright := ConcreteCategory.congr_hom (c.ι.naturality right)
      (algebraMap R (F.obj stage) scalar)
    change (c.ι.app j) ((F.map left) (algebraMap R (F.obj i) scalar)) =
      (c.ι.app i) (algebraMap R (F.obj i) scalar) at hleft
    change (c.ι.app j) ((F.map right) (algebraMap R (F.obj stage) scalar)) =
      (c.ι.app stage) (algebraMap R (F.obj stage) scalar) at hright
    simpa only [AlgHom.commutes] using hleft.symm.trans (by
      simpa only [AlgHom.commutes] using hright)
  have hbase_apply (i : J) (scalar : R) :
      (c.ι.app i) (algebraMap R (F.obj i) scalar) = algebraMap R c.pt scalar :=
    RingHom.congr_fun (hbase i) scalar
  have htf : Module.IsTorsionFree R c.pt := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro scalar element heq
    by_cases hscalar : scalar = 0
    · exact Or.inl hscalar
    apply Or.inr
    obtain ⟨i, representative, rfl⟩ := Types.jointly_surjective_of_isColimit hc element
    change F.obj i at representative
    have hzero : (c.ι.app i) (scalar • representative) = (c.ι.app i) 0 := by
      change algebraMap R c.pt scalar * inclusion i representative = 0 at heq
      simpa only [Algebra.smul_def, map_mul, hbase_apply, map_zero] using heq
    obtain ⟨j, left, right, hj⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc).mp hzero
    change (F.map left) (scalar • representative) = (F.map right) 0 at hj
    have hjzero : (F.map left) representative = 0 := by
      simpa only [map_smul, map_zero, smul_eq_zero, hscalar, false_or] using hj
    have hnat := ConcreteCategory.congr_hom (c.ι.naturality left) representative
    change (c.ι.app j) ((F.map left) representative) = (c.ι.app i) representative at hnat
    simpa [hjzero] using hnat.symm
  have hlocal : IsLocalHom (algebraMap R c.pt) := by
    constructor
    intro scalar hunit
    obtain ⟨inverse, hinverse⟩ := hunit.exists_right_inv
    obtain ⟨i, representative, rfl⟩ := Types.jointly_surjective_of_isColimit hc inverse
    change F.obj i at representative
    have heq : (c.ι.app i) (algebraMap R (F.obj i) scalar * representative) =
        (c.ι.app i) 1 := by
      change algebraMap R c.pt scalar * inclusion i representative = 1 at hinverse
      simpa only [map_mul, hbase_apply, map_one] using hinverse
    obtain ⟨j, left, right, hj⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc).mp heq
    change (F.map left) (algebraMap R (F.obj i) scalar * representative) =
      (F.map right) 1 at hj
    have hunitj : IsUnit (algebraMap R (F.obj j) scalar) := by
      apply isUnit_iff_dvd_one.mpr
      refine ⟨(F.map left) representative, ?_⟩
      simpa only [map_mul, AlgHom.commutes, map_one] using hj.symm
    exact isUnit_of_map_unit (algebraMap R (F.obj j)) scalar hunitj
  exact ⟨inferInstance, htf, hlocal, hbase⟩

/-- A filtered diagram of torsion-free algebras over a domain with local structure maps admits
a compatible cocone of algebra maps into a single torsion-free algebra with local structure
map. -/
private lemma exists_torsionFree_local_cocone
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (R : Type u) [CommRing R] [IsDomain R]
    (F : J ⥤ CommAlgCat.{u} R)
    [∀ i, Module.IsTorsionFree R (F.obj i)]
    [∀ i, IsLocalHom (algebraMap R (F.obj i))] :
    ∃ (A : Type (max u v w)) (_ : CommRing A) (_ : Algebra R A),
      Module.IsTorsionFree R A ∧ IsLocalHom (algebraMap R A) ∧
      ∃ maps : ∀ i, F.obj i →ₐ[R] A,
        ∀ {i j} (arrow : i ⟶ j), (maps j).comp (F.map arrow).hom = maps i := by
  classical
  let G : AsSmall.{u} J ⥤ CommAlgCat.{max u v w} R :=
    AsSmall.down ⋙ F ⋙ CommAlgCat.uliftFunctor.{max u v w} R
  have : ∀ i, Module.IsTorsionFree R (G.obj i) := fun i ↦
    Function.Injective.moduleIsTorsionFree (M := ULift (F.obj (AsSmall.down.obj i)))
      ULift.down ULift.down_injective fun _ _ ↦ rfl
  have : ∀ i, IsLocalHom (algebraMap R (G.obj i)) := fun i ↦ by
    show IsLocalHom (algebraMap R (ULift (F.obj (AsSmall.down.obj i))))
    constructor
    intro scalar hunit
    apply isUnit_of_map_unit (algebraMap R (F.obj (AsSmall.down.obj i)))
    exact hunit.map ULift.ringEquiv.toRingHom
  let c := CommRingCat.FilteredColimits.colimitCocone
    (G ⋙ forget₂ (CommAlgCat R) CommRingCat)
  have hc : IsColimit ((forget CommRingCat).mapCocone c) :=
    Types.TypeMax.colimitCoconeIsColimit _
  obtain ⟨algebra, htf, hlocal, hbase⟩ := colimit_torsionFree_local R G c hc
  let : Algebra R c.pt := algebra
  let inclusions (i : AsSmall.{u} J) : G.obj i →ₐ[R] c.pt :=
    { (c.ι.app i).hom with commutes' := RingHom.congr_fun (hbase i) }
  let maps (i : J) : F.obj i →ₐ[R] c.pt :=
    (inclusions (AsSmall.up.obj i)).comp ULift.algEquiv.symm.toAlgHom
  refine ⟨c.pt, inferInstance, inferInstance, htf, hlocal, maps, ?_⟩
  intro i j arrow
  ext element
  exact ConcreteCategory.congr_hom (c.ι.naturality (AsSmall.up.map arrow)) (ULift.up element)

/-- An algebra map over a domain carries torsion elements to torsion elements. -/
private lemma torsionIdeal_map_le
    {R A B : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (map : A →ₐ[R] B) :
    torsionIdeal R A ≤ (torsionIdeal R B).comap map := by
  intro element hmem
  obtain ⟨scalar, hscalar, heq⟩ := mem_torsionIdeal.mp hmem
  exact mem_torsionIdeal.mpr
    ⟨scalar, hscalar, by simpa only [map_smul, map_zero] using congrArg map heq⟩

/-- The endofunctor of algebras over a domain which quotients out torsion. -/
private noncomputable def torsionQuotientFunctor (R : Type*)
    [CommRing R] [IsDomain R] : CommAlgCat.{u} R ⥤ CommAlgCat.{u} R where
  obj A := .of R (A ⧸ torsionIdeal R A)
  map arrow := CommAlgCat.ofHom
    (Ideal.quotientMapₐ (torsionIdeal R _) arrow.hom (torsionIdeal_map_le arrow.hom))
  map_id A := by
    apply CommAlgCat.hom_ext
    ext element
    obtain ⟨element, rfl⟩ := Ideal.Quotient.mk_surjective element
    rfl
  map_comp first second := by
    apply CommAlgCat.hom_ext
    ext element
    obtain ⟨element, rfl⟩ := Ideal.Quotient.mk_surjective element
    rfl

/-- Base change of `R`-algebras to `V`-algebras along a fixed `R`-algebra `V`. -/
private noncomputable def tensorProductFunctor (R : Type u) (V : Type v)
    [CommRing R] [CommRing V] [Algebra R V] :
    CommAlgCat.{u} R ⥤ CommAlgCat.{max u v} V where
  obj A := .of V (V ⊗[R] A)
  map arrow := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id V V) arrow.hom)
  map_id A := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id
  map_comp first second := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id_comp second.hom first.hom

/-- If an algebra over a domain admits a ring map to a domain which is injective and local on
the base, then the structure map of its torsion quotient is local. -/
private lemma torsionIdeal_quotient_isLocalHom
    {R A W : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [CommRing W] [IsDomain W]
    (map : A →+* W) (hinjective : Function.Injective (map.comp (algebraMap R A)))
    [IsLocalHom (map.comp (algebraMap R A))] :
    IsLocalHom (algebraMap R (A ⧸ torsionIdeal R A)) := by
  let desc := Ideal.Quotient.lift (torsionIdeal R A) map (torsionIdeal_le_ker map hinjective)
  constructor
  intro scalar hunit
  apply isUnit_of_map_unit (map.comp (algebraMap R A)) scalar
  exact hunit.map desc

/-- For a cocone of `R`-algebras which is a colimit on underlying sets and a valuation ring `V`
over `R` such that every stage has local torsion quotient over `V`, there is a faithfully flat
`V`-algebra receiving the cocone point compatibly with `R`. -/
private lemma exists_faithfullyFlat_algebra_of_colimit
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (R V : Type u) [CommRing R] [CommRing V] [IsDomain V] [ValuationRing V]
    [Algebra R V] (F : J ⥤ CommAlgCat.{u} R)
    (c : Cocone (F ⋙ forget₂ (CommAlgCat R) CommRingCat))
    (hc : IsColimit ((forget CommRingCat).mapCocone c)) [Algebra R c.pt]
    (hbase : ∀ i, (c.ι.app i).hom.comp (algebraMap R (F.obj i)) = algebraMap R c.pt)
    [∀ i, IsLocalHom (algebraMap V
      ((V ⊗[R] F.obj i) ⧸ torsionIdeal V (V ⊗[R] F.obj i)))] :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra V Q), Module.FaithfullyFlat V Q ∧
      ∃ map : c.pt →+* Q,
        map.comp (algebraMap R c.pt) = (algebraMap V Q).comp (algebraMap R V) := by
  classical
  let G := F ⋙ tensorProductFunctor R V ⋙ torsionQuotientFunctor V
  have : ∀ i, Module.IsTorsionFree V (G.obj i) := fun i ↦
    torsionIdeal_quotient_isTorsionFree V _
  have : ∀ i, IsLocalHom (algebraMap V (G.obj i)) := fun i ↦ by
    show IsLocalHom (algebraMap V
      ((V ⊗[R] F.obj i) ⧸ torsionIdeal V (V ⊗[R] F.obj i)))
    infer_instance
  obtain ⟨A, hA, algebraA, htfA, hlocalA, maps, hmaps⟩ :=
    exists_torsionFree_local_cocone V G
  let : CommRing A := hA
  let : Algebra V A := algebraA
  have : Module.IsTorsionFree V A := htfA
  have : IsLocalHom (algebraMap V A) := hlocalA
  let : Algebra R A := Algebra.restrictScalars R V A
  let : IsScalarTower R V A := IsScalarTower.of_algebraMap_eq' rfl
  let (i : J) : Algebra R (G.obj i) := by
    show Algebra R ((V ⊗[R] F.obj i) ⧸ torsionIdeal V (V ⊗[R] F.obj i))
    infer_instance
  let (i : J) : IsScalarTower R V (G.obj i) := by
    show IsScalarTower R V ((V ⊗[R] F.obj i) ⧸ torsionIdeal V (V ⊗[R] F.obj i))
    infer_instance
  let stageMaps (i : J) : F.obj i →ₐ[R] A :=
    ((maps i).restrictScalars R).comp
      ((Ideal.Quotient.mkₐ V (torsionIdeal V (V ⊗[R] F.obj i))).restrictScalars R
        |>.comp Algebra.TensorProduct.includeRight)
  have hstageMaps {i j : J} (arrow : i ⟶ j) :
      (stageMaps j).toRingHom.comp (F.map arrow).hom.toRingHom =
        (stageMaps i).toRingHom := by
    ext element
    exact AlgHom.congr_fun (hmaps arrow) (Ideal.Quotient.mk _ (1 ⊗ₜ[R] element))
  obtain ⟨desc, hdesc⟩ := ringHomDesc_of_typeColimit
    (F ⋙ forget₂ (CommAlgCat R) CommRingCat) c hc
      A (fun i ↦ (stageMaps i).toRingHom) hstageMaps
  have hdescbase : desc.comp (algebraMap R c.pt) = algebraMap R A := by
    let stage : J := Classical.choice IsFiltered.nonempty
    rw [← hbase stage, ← RingHom.comp_assoc, hdesc]
    exact (stageMaps stage).comp_algebraMap
  let descAlg : c.pt →ₐ[R] A := { desc with commutes' := RingHom.congr_fun hdescbase }
  let product : (V ⊗[R] c.pt) →ₐ[V] A :=
    Algebra.TensorProduct.lift (Algebra.ofId V A) descAlg (fun _ _ ↦ Commute.all _ _)
  let Q := (V ⊗[R] c.pt) ⧸ RingHom.ker product.toRingHom
  let inclusion : Q →ₐ[V] A :=
    { Ideal.Quotient.lift _ product.toRingHom (fun _ helement ↦ helement) with
      commutes' := by
        intro scalar
        show product (algebraMap V (V ⊗[R] c.pt) scalar) = algebraMap V A scalar
        exact product.commutes scalar }
  have hinjective : Function.Injective inclusion := by
    intro first second heq
    obtain ⟨first, rfl⟩ := Ideal.Quotient.mk_surjective first
    obtain ⟨second, rfl⟩ := Ideal.Quotient.mk_surjective second
    apply Ideal.Quotient.eq.mpr
    show product (first - second) = 0
    change product first = product second at heq
    rw [map_sub, heq, sub_self]
  have : Module.IsTorsionFree V Q :=
    Function.Injective.moduleIsTorsionFree inclusion hinjective (fun _ _ ↦ map_smul _ _ _)
  have : IsLocalHom (algebraMap V Q) := by
    constructor
    intro scalar hunit
    apply isUnit_of_map_unit (algebraMap V A) scalar
    have hunitA : IsUnit (inclusion (algebraMap V Q scalar)) := hunit.map inclusion.toRingHom
    rwa [inclusion.commutes] at hunitA
  have : Module.Flat V Q := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  refine ⟨Q, inferInstance, inferInstance,
    faithfullyFlat_of_isLocalHom_of_valuationRing V Q,
    (Ideal.Quotient.mkₐ V (RingHom.ker product.toRingHom)).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext scalar
  show Ideal.Quotient.mk _ (1 ⊗ₜ[R] algebraMap R c.pt scalar) =
    Ideal.Quotient.mk _ (algebraMap R V scalar ⊗ₜ[R] 1)
  rw [← Algebra.TensorProduct.algebraMap_apply']
  rfl

/-- A morphism from the spectrum of a ring to an affine scheme is recovered from the ring map
it induces on global sections. -/
private lemma specMap_coordinateMap
    {V : Type u} [CommRing V] {Y : Scheme.{u}} [IsAffine Y]
    (g : Spec (.of V) ⟶ Y) :
    Spec.map (g.appTop ≫ (Scheme.ΓSpecIso (.of V)).hom) ≫ Y.isoSpec.inv = g := by
  rw [Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality, ← Scheme.isoSpec_Spec_hom]
  simp

/-- If a single morphism of affine schemes is a standard V covering, then for every morphism
from the spectrum of a valuation ring `V` to the base the torsion quotient of the base change
has local structure map over `V`. -/
private lemma tensorProduct_torsionQuotient_isLocalHom_of_covering
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (h : AlgebraicGeometry.IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f))
    (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    (g : Spec (.of V) ⟶ Y) :
    letI : Algebra Γ(Y, ⊤) V :=
      (g.appTop ≫ (Scheme.ΓSpecIso (.of V)).hom).hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    IsLocalHom (algebraMap V
      ((V ⊗[Γ(Y, ⊤)] Γ(X, ⊤)) ⧸ torsionIdeal V (V ⊗[Γ(Y, ⊤)] Γ(X, ⊤)))) := by
  classical
  let : Algebra Γ(Y, ⊤) V :=
    (g.appTop ≫ (Scheme.ΓSpecIso (.of V)).hom).hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  rw [AlgebraicGeometry.isStandardVCovering_iff] at h
  obtain ⟨W, hW, hdom, hval, e, he, index, lift, hsquare⟩ := h V g
  let : CommRing W := hW
  let : IsDomain W := hdom
  let : ValuationRing W := hval
  have : IsLocalHom e := he.2
  let : Algebra V W := e.toAlgebra
  let : Algebra Γ(Y, ⊤) W := Algebra.restrictScalars Γ(Y, ⊤) V W
  let : IsScalarTower Γ(Y, ⊤) V W := IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : f.appTop ≫ (lift.appTop ≫ (Scheme.ΓSpecIso (.of W)).hom) =
      (g.appTop ≫ (Scheme.ΓSpecIso (.of V)).hom) ≫ CommRingCat.ofHom e := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, ← hsquare,
      Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  let map : Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] W :=
    { (lift.appTop ≫ (Scheme.ΓSpecIso (.of W)).hom).hom with
      commutes' := fun scalar ↦ ConcreteCategory.congr_hom hcomm scalar }
  let product : V ⊗[Γ(Y, ⊤)] Γ(X, ⊤) →ₐ[V] W :=
    Algebra.TensorProduct.lift (Algebra.ofId V W) map (fun _ _ ↦ Commute.all _ _)
  have hproduct : product.toRingHom.comp
      (algebraMap V (V ⊗[Γ(Y, ⊤)] Γ(X, ⊤))) = e := product.comp_algebraMap
  have : IsLocalHom (product.toRingHom.comp
      (algebraMap V (V ⊗[Γ(Y, ⊤)] Γ(X, ⊤)))) := hproduct ▸ he.2
  apply torsionIdeal_quotient_isLocalHom product.toRingHom
  simpa only [hproduct] using he.1

/-- A morphism from a cofiltered limit of affine schemes over an affine base is a
standard V covering if and only if all stage morphisms are standard V coverings, for a diagram
indexed by a category in any universe whose cocone of coordinate rings is a colimit on
underlying sets. -/
public lemma isStandardVCovering_limit_iff
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    {Y : Scheme.{u}} [IsAffine Y]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj Y)
    (c : Cone D) (hc : IsLimit c)
    (hΓ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone c.op))
    (f : c.pt ⟶ Y)
    (hf : c.π ≫ t = (Functor.const I).map f) :
    (letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
     AlgebraicGeometry.IsStandardVCovering (fun _ : Unit ↦ c.pt) (fun _ ↦ f)) ↔
      ∀ i : I,
        (letI : IsAffine (((Functor.const I).obj Y).obj i) := by
           change IsAffine Y
           infer_instance
         AlgebraicGeometry.IsStandardVCovering (fun _ : Unit ↦ D.obj i)
           (fun _ ↦ t.app i)) := by
  have hY (i : I) : IsAffine (((Functor.const I).obj Y).obj i) := ‹IsAffine Y›
  have hfi (i : I) : c.π.app i ≫ t.app i = f := by
    simpa only [NatTrans.comp_app, Functor.const_map_app] using congrArg (fun η => η.app i) hf
  constructor
  · intro h i
    rw [AlgebraicGeometry.isStandardVCovering_iff] at h ⊢
    intro V hV hdom hval g
    obtain ⟨W, hW, hWdom, hWval, e, he, ⟨j, lift, hsquare⟩⟩ := h V g
    refine ⟨W, hW, hWdom, hWval, e, he, ⟨(), lift ≫ c.π.app i, ?_⟩⟩
    simpa [Category.assoc, hfi] using hsquare
  · intro h
    classical
    let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
    rw [AlgebraicGeometry.isStandardVCovering_iff]
    intro V hV hdom hval g
    let R := Γ(Y, ⊤)
    let : Algebra R V :=
      (g.appTop ≫ (Scheme.ΓSpecIso (.of V)).hom).hom.toAlgebra
    let (i : I) : Algebra R Γ(D.obj i, ⊤) := (t.app i).appTop.hom.toAlgebra
    let : Algebra R Γ(c.pt, ⊤) := f.appTop.hom.toAlgebra
    let F : Iᵒᵖ ⥤ CommAlgCat.{u} R :=
      { obj := fun i ↦ .of R Γ(D.obj i.unop, ⊤)
        map := fun {i j} arrow ↦ CommAlgCat.ofHom
          { (D.map arrow.unop).appTop.hom with
            commutes' := by
              intro scalar
              have heq := congrArg Scheme.Hom.appTop (t.naturality arrow.unop)
              simp only [Functor.const_obj_map,
                Scheme.Hom.comp_appTop] at heq
              exact ConcreteCategory.congr_hom heq scalar }
        map_id := by
          intro i
          apply CommAlgCat.hom_ext
          ext element
          show (D.map (𝟙 i.unop)).appTop element = element
          simp
        map_comp := by
          intro i j k first second
          apply CommAlgCat.hom_ext
          ext element
          show (D.map (second.unop ≫ first.unop)).appTop element =
            (D.map second.unop).appTop ((D.map first.unop).appTop element)
          rw [D.map_comp, Scheme.Hom.comp_appTop]
          rfl }
    let ringCone : Cocone (F ⋙ forget₂ (CommAlgCat R) CommRingCat) :=
      { pt := Γ(c.pt, ⊤)
        ι := { app := fun i ↦ (c.π.app i.unop).appTop
               naturality := by
                 intro i j arrow
                 have heq := congrArg Scheme.Hom.appTop (c.w arrow.unop)
                 show (D.map arrow.unop).appTop ≫ (c.π.app j.unop).appTop =
                   (c.π.app i.unop).appTop ≫ 𝟙 _
                 simpa only [Scheme.Hom.comp_appTop, Category.comp_id] using heq } }
    have hringCone : IsColimit ((forget CommRingCat).mapCocone ringCone) := hΓ
    have hbase (i : Iᵒᵖ) : (ringCone.ι.app i).hom.comp
        (algebraMap R (F.obj i)) = algebraMap R ringCone.pt := by
      ext scalar
      show (c.π.app i.unop).appTop ((t.app i.unop).appTop scalar) = f.appTop scalar
      have heq := congrArg Scheme.Hom.appTop (hfi i.unop)
      rw [Scheme.Hom.comp_appTop] at heq
      exact ConcreteCategory.congr_hom heq scalar
    have (i : Iᵒᵖ) : IsLocalHom (algebraMap V
        ((V ⊗[R] F.obj i) ⧸ torsionIdeal V (V ⊗[R] F.obj i))) := by
      have := hY i.unop
      exact tensorProduct_torsionQuotient_isLocalHom_of_covering
        (t.app i.unop) (h i.unop) V g
    obtain ⟨Q, hQ, algebraQ, hflat, map, hmap⟩ :=
      exists_faithfullyFlat_algebra_of_colimit R V F ringCone hringCone hbase
    let : CommRing Q := hQ
    let : Algebra V Q := algebraQ
    have : Module.FaithfullyFlat V Q := hflat
    let q : Spec (.of Q) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V Q))
    have hq : Flat q ∧ Surjective q := flat_and_surjective_SpecMap_iff _ |>.mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hflat)
    have : Flat q := hq.1
    have : Surjective q := hq.2
    let cover : (Spec (.of V)).AffineCover @Flat :=
      { I₀ := Unit
        X := fun _ ↦ .of Q
        f := fun _ ↦ q
        idx := fun _ ↦ ()
        covers := fun point ↦ Surjective.surj point
        map_prop := fun _ ↦ hq.1 }
    have hcover := AlgebraicGeometry.isStandardVCovering_of_flat_affineCover cover
    rw [AlgebraicGeometry.isStandardVCovering_iff] at hcover
    obtain ⟨W, hW, hWdom, hWval, e, he, index, lift, hlift⟩ := hcover V (𝟙 _)
    let : CommRing W := hW
    let : IsDomain W := hWdom
    let : ValuationRing W := hWval
    change Spec.map (CommRingCat.ofHom e) ≫ 𝟙 _ = lift ≫ q at hlift
    let a : Spec (.of Q) ⟶ c.pt := Spec.map (CommRingCat.ofHom map) ≫ c.pt.isoSpec.inv
    have hsquare : q ≫ g = a ≫ f := by
      rw [← specMap_coordinateMap g]
      dsimp only [q, a]
      rw [Category.assoc, ← Scheme.isoSpec_inv_naturality f,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 1
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact hmap.symm
    refine ⟨W, hW, hWdom, hWval, e, he, (), lift ≫ a, ?_⟩
    rw [Category.comp_id] at hlift
    simp only [hlift, hsquare, Category.assoc]

/-- A morphism from a cofiltered limit of affine schemes over an affine base is a
standard V covering if and only if all stage morphisms are standard V coverings. -/
@[stacks 0EVN]
public lemma isStandardVCovering_limit_iff'
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {Y : Scheme.{u}} [IsAffine Y]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj Y)
    (c : Cone D) (hc : IsLimit c)
    (f : c.pt ⟶ Y)
    (hf : c.π ≫ t = (Functor.const I).map f) :
    (letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
     AlgebraicGeometry.IsStandardVCovering (fun _ : Unit ↦ c.pt) (fun _ ↦ f)) ↔
      ∀ i : I,
        (letI : IsAffine (((Functor.const I).obj Y).obj i) := by
           change IsAffine Y
           infer_instance
         AlgebraicGeometry.IsStandardVCovering (fun _ : Unit ↦ D.obj i)
           (fun _ ↦ t.app i)) :=
  have : ∀ i, IsAffine (D.op.obj i).unop := fun i ↦ by
    show IsAffine (D.obj i.unop)
    infer_instance
  isStandardVCovering_limit_iff D t c hc
    (isColimitOfPreserves (Scheme.Γ ⋙ forget CommRingCat) hc.op) f hf

end AlgebraicGeometry.ProEtale
