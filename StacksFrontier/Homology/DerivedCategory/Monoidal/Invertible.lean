module

public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible objects in the derived category

An object of the derived category of a commutative ring is invertible exactly when it is, locally
near every prime, a shift of the ring. Such an object is perfect, it splits as the direct sum of
its cohomology modules, each of those is finite projective, and they are invertible modules over
the factors of a finite product decomposition of the ring.

## Main definitions

* `DerivedCategory.Invertible.IsLocallyShiftedUnit`: on a principal neighbourhood of every prime
  the derived localization is a shifted copy of the localized ring.
* `DerivedCategory.Invertible.SplitsAsCohomology`: the object is the direct sum of its cohomology
  modules, placed in their degrees, with only finitely many nonzero.
* `DerivedCategory.Invertible.HasInvertibleCohomologyDecomposition`: a finite product
  decomposition of the ring on whose factors the cohomology modules become invertible.

## Main results

* `DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank`: a
  perfect object whose derived fibre at every maximal ideal has one cohomology module, of rank
  one, is locally a shifted unit.
* `DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit` ([stacks 0FNT]): invertibility
  is equivalent to being locally a shifted unit, and it implies each of the three conclusions
  above together with finiteness and projectivity of every cohomology module.

## Implementation notes

The monoidal structure is the canonical one of [stacks 0FNQ] and invertibility is the predicate
of [stacks 0FFN] for it. The direct sum in `SplitsAsCohomology` is indexed by a finite interval
of degrees, with vanishing outside it stated separately; that is what identifies it with the
source's sum over all of `ℤ`. A cohomology module belonging to one ring factor is expressed as
restriction of scalars along the projection coming from the product decomposition.

Both directions are checked locally. Away from a prime the object becomes a shifted free module
of rank one, which is perfect, so the object is perfect by the local criterion of [stacks 066Y];
the converse reads off the ranks of the fibres at residue fields using the minimal free
representative of [stacks 0BCD].

## References

* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

namespace DerivedCategory.Invertible


attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A derived object is locally a shifted unit if every prime has a principal neighbourhood on
which its derived localization is a shift of the localized ring. -/
public def IsLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∀ (p : Ideal R), p.IsPrime →
    ∃ f : R, f ∉ p ∧ ∃ n : ℤ,
      let Rf := Localization.Away f
      let Mf :=
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap R Rf)).functor.obj M
      Nonempty (Mf ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} Rf) n).obj
          (ModuleCat.of Rf Rf))

/-- The bounded direct-sum decomposition of a derived object into its cohomology modules. -/
public def SplitsAsCohomology
    (M : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ a b : ℤ,
    (∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) ∧
    Nonempty (M ≅ ∐ fun n : Set.Icc a b =>
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n.1).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n.1).obj M))

/-- A finite product decomposition of the ring such that the cohomology in each indexed degree
is the restriction of scalars of an invertible module over the corresponding factor. -/
public def HasInvertibleCohomologyDecomposition
    (M : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ a b : ℤ,
    let I := Set.Icc a b
    ∃ (Rn : I → Type u) (_ : ∀ n, CommRing (Rn n))
      (e : R ≃+* ∀ n, Rn n)
      (L : ∀ n, ModuleCat.{u} (Rn n)),
      (∀ n, Module.Invertible (Rn n) (L n)) ∧
        (∀ n, Nonempty
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n.1).obj M) ≅
            (ModuleCat.restrictScalars
              ((Pi.evalRingHom Rn n).comp e.toRingHom)).obj (L n))) ∧
        ∀ n : ℤ, n ∉ I →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)

open CategoryTheory.MonoidalCategory

universe v w

open scoped DirectSum TensorProduct


private theorem isCompactObject_map_equivalence
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (q : C ≌ D) [q.functor.Additive]
    (P : C) [IsCompactObject.{w} P] : IsCompactObject.{w} (q.functor.obj P) := by
  classical
  constructor
  intro J _ E _
  refine ⟨StacksDraft.Perfect.injective_directSumToHom _ _, ?_⟩
  intro f
  let F := q.functor
  let K (j : J) := q.inverse.obj (E j)
  let e (j : J) : F.obj (K j) ≅ E j := q.counitIso.app (E j)
  have : HasCoproduct K := hasColimit_of_iso (Discrete.compNatIsoDiscrete E q.inverse).symm
  have hc : IsColimit (Cofan.mk (F.obj (∐ K)) (fun j => F.map (Sigma.ι K j))) :=
    (isColimitMapCoconeCofanMkEquiv F K (Sigma.ι K))
      (isColimitOfPreserves F (coproductIsCoproduct K))
  let ec : Cofan (fun j => F.obj (K j)) :=
    Cofan.mk (∐ E) (fun j => (e j).hom ≫ Sigma.ι E j)
  have hec : IsColimit ec :=
    (IsColimit.precomposeHomEquiv (Discrete.natIso
        (F := Discrete.functor (fun j => F.obj (K j)))
        (G := Discrete.functor E) (fun j => e j.as)) _).2
      (coproductIsCoproduct E)
  let t := hc.coconePointUniqueUpToIso hec
  have ht (j : J) : F.map (Sigma.ι K j) ≫ t.hom = (e j).hom ≫ Sigma.ι E j :=
    hc.comp_coconePointUniqueUpToIso_hom hec ⟨j⟩
  obtain ⟨g, hg⟩ := F.map_surjective (f ≫ t.inv)
  obtain ⟨s, a, ha⟩ := StacksDraft.Perfect.exists_sum_cofan_of_isCompactObject P (Sigma.ι K)
    (coproductIsCoproduct K) g
  refine ⟨∑ j ∈ s, DirectSum.of _ j (F.map (a j) ≫ (e j).hom), ?_⟩
  simp only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Category.assoc]
  calc
    ∑ j ∈ s, F.map (a j) ≫ (e j).hom ≫ Sigma.ι E j =
        F.map (∑ j ∈ s, a j ≫ Sigma.ι K j) ≫ t.hom := by
      simp only [Functor.map_sum, Functor.map_comp, Preadditive.sum_comp,
        Category.assoc, ht]
    _ = f := by rw [ha, hg]; simp


private theorem isPerfect_of_iso {M N : DerivedCategory (ModuleCat.{v} R)}
    (e : M ≅ N) (hM : StacksDraft.Perfect.IsPerfect M) : StacksDraft.Perfect.IsPerfect N := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨i⟩⟩ := hM
  exact ⟨P, a, b, ha, hb, hf, hp, ⟨e.symm ≪≫ i⟩⟩

private theorem isPerfect_singleFunctor_obj (N : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Projective R N] (n : ℤ) :
    StacksDraft.Perfect.IsPerfect ((DerivedCategory.singleFunctor (ModuleCat.{v} R) n).obj N) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj N
  have h (i : ℤ) : Module.Finite R (P.X i) ∧ Module.Projective R (P.X i) := by
    by_cases hi : i = n
    · subst i
      let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n N).toLinearEquiv
      exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
    · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n N i hi
      have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp hz
      exact ⟨inferInstance, Module.Projective.of_free⟩
  exact ⟨P, n, n, inferInstance, inferInstance, fun i => (h i).1,
    fun i => (h i).2, ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) n).app N⟩⟩

private theorem isPerfect_of_isInvertible (M : DerivedCategory (ModuleCat.{u} R)) :
    let m := (derivedCategory_symmetricMonoidalCategory R).choose
    letI := m
    MonoidalCategory.IsInvertible M → StacksDraft.Perfect.IsPerfect M := by
  intro m
  let := m
  intro ⟨h⟩
  let D := DerivedCategory (ModuleCat.{u} R)
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let j := CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj R
  have : IsCompactObject.{u} U :=
    (StacksDraft.Perfect.isPerfect_iff_isCompactObject U).mp
      (isPerfect_singleFunctor_obj (ModuleCat.of R R) 0)
  have : IsCompactObject.{u} (𝟙_ D) :=
    StacksDraft.Perfect.isCompactObject_of_iso_of_preadditive j.symm
  let E := h.tensorLeftEquivalence
  have : E.functor.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits _; infer_instance)
  have : IsCompactObject.{u} (M ⊗ (𝟙_ D)) :=
    isCompactObject_map_equivalence E (𝟙_ D)
  have : IsCompactObject.{u} M :=
    StacksDraft.Perfect.isCompactObject_of_iso_of_preadditive (MonoidalCategory.rightUnitor M)
  exact (StacksDraft.Perfect.isPerfect_iff_isCompactObject M).mpr this

private theorem exists_finite_principal_cover {P : R → Prop}
    (hP : ∀ p : Ideal R, p.IsPrime → ∃ f, f ∉ p ∧ P f) :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧ ∀ f ∈ s, P f := by
  classical
  have hspan : Ideal.span {f : R | P f} = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hPf⟩ := hP p hp.isPrime
    exact hf (hle (Ideal.subset_span hPf))
  obtain ⟨s, hs, htop⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  exact ⟨s, htop, fun f hf => hs hf⟩

private def localizationAwayIso (f : R) :
    (totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.Away f))).functor ≅
      StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, v} f := by
  let F := CochainComplex.DerivedTensor.extensionScalars.{u, u, v}
    (algebraMap R (Localization.Away f))
  let D := totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.Away f))
  have : F.PreservesHomology := CochainComplex.DerivedTensor.extensionScalars_preservesHomology _
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) (by
        intro X Y g hg
        have : QuasiIso g := hg
        change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
        infer_instance)
  change D.functor ≅ F.mapDerivedCategory
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

private theorem isPerfect_of_isLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) :
    StacksDraft.Perfect.IsPerfect M := by
  obtain ⟨s, hs, hlocal⟩ := exists_finite_principal_cover hM
  apply StacksDraft.Perfect.isPerfect_of_localizationSpan (fun f : s => (f : R))
    (by convert hs using 1; congr 1; ext x; simp) M
  intro f
  obtain ⟨n, ⟨e⟩⟩ := hlocal f f.property
  exact isPerfect_of_iso (e.symm ≪≫ (localizationAwayIso.{u, u} (f : R)).app M)
    (isPerfect_singleFunctor_obj (ModuleCat.of (Localization.Away (f : R))
      (Localization.Away (f : R))) n)

private def localizedHomologyLinearEquiv
    (M : DerivedCategory (ModuleCat.{u} R)) (f : R) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R (Localization.Away f))).functor.obj M)) ≃ₗ[Localization.Away f]
      LocalizedModule.Away f
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) := by
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
    ((totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R (Localization.Away f))).functor.obj M)
  let N' := (ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).obj N
  letI : Module (Localization.Away f) N' := inferInstanceAs (Module (Localization.Away f) N)
  let e : N' ≃ₗ[R] LocalizedModule.Away f
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) :=
    ((CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso.{u, u} f n).app
      M).toLinearEquiv
  have : IsScalarTower R (Localization.Away f) N' :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact e.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)

/-- The homology of a single-degree object vanishes away from that degree. -/
private theorem isZero_homology_singleFunctor_obj_of_ne {S : Type u} [CommRing S]
    (N : ModuleCat.{u} S) {n i : ℤ} (hi : i ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj N)) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact DerivedCategory.isZero_of_isGE _ n i hi
  · exact DerivedCategory.isZero_of_isLE _ n i hi

private theorem finite_free_homology_singleFunctor_obj (N : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Free R N] (n i : ℤ) :
    let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj N)
    Module.Finite R H ∧ Module.Free R H := by
  dsimp only
  by_cases hi : i = n
  · subst i
    let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj N)) ≃ₗ[R] N :=
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} R) n).app N).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_homology_singleFunctor_obj_of_ne N hi)
    exact ⟨inferInstance, inferInstance⟩

private theorem finite_projective_homology_of_isLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (i : ℤ) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) ∧
      Module.Projective R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) := by
  obtain ⟨s, hs, hlocal⟩ := exists_finite_principal_cover hM
  apply ((Module.finite_projective_tfae R
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)).out 7 2).mp
  refine ⟨s, hs, ?_⟩
  intro f hf
  obtain ⟨n, ⟨e⟩⟩ := hlocal f hf
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) i
  let j := ((H.mapIso e).toLinearEquiv).symm.trans (localizedHomologyLinearEquiv M f i)
  obtain ⟨hfin, hfree⟩ := finite_free_homology_singleFunctor_obj
    (ModuleCat.of (Localization.Away f) (Localization.Away f)) n i
  have := hfin
  have := hfree
  exact ⟨Module.Free.of_equiv j, Module.Finite.equiv j⟩

/-- A bounded derived object with projective cohomology is the coproduct of its shifted
cohomology modules. -/
private theorem nonempty_iso_coproduct_singleFunctor_obj_homology
    (M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) [M.IsGE a] [M.IsLE b]
    (hproj : ∀ n : ℤ, Module.Projective R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) :
    Nonempty (M ≅ ∐ fun n : Set.Icc a b =>
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n.1).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n.1).obj M)) := by
  obtain ⟨j⟩ :=
    DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero
      M a b (fun i _ p _ hp x => by
        have := hproj i
        have : Projective ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) :=
          inferInstance
        exact x.eq_zero_of_hasProjectiveDimensionLT 1 (by omega))
  let q : (Finset.Icc a b : Finset ℤ) ≃ Set.Icc a b :=
    { toFun := fun i => ⟨i, Finset.mem_Icc.mp i.property⟩
      invFun := fun i => ⟨i, Finset.mem_Icc.mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := fun n : Set.Icc a b =>
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) n.1).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n.1).obj M)
  exact ⟨j ≪≫ biproduct.whiskerEquiv (g := G) q (fun _ => Iso.refl _) ≪≫
    biproduct.isoCoproduct G⟩

private theorem splitsAsCohomology_of_isPerfect_of_projective_homology
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : StacksDraft.Perfect.IsPerfect M)
    (hproj : ∀ n : ℤ, Module.Projective R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) :
    SplitsAsCohomology M := by
  obtain ⟨P, a, b, ha, hb, _, _, ⟨e⟩⟩ := hM
  have := ha
  have := hb
  have : M.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have : M.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have hvan (n : ℤ) (hn : n ∉ Set.Icc a b) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · exact M.isZero_of_isGE a n hn
    · exact M.isZero_of_isLE b n hn
  exact ⟨a, b, hvan, nonempty_iso_coproduct_singleFunctor_obj_homology M a b hproj⟩

private theorem splitsAsCohomology_of_isLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) :
    SplitsAsCohomology M :=
  splitsAsCohomology_of_isPerfect_of_projective_homology M
    (isPerfect_of_isLocallyShiftedUnit M hM)
    (fun n => (finite_projective_homology_of_isLocallyShiftedUnit M hM n).2)

/-- The object of a complex isomorphic to a single-degree one is isomorphic to any
isomorphic copy of the term in that degree. -/
private def singleObjIsoOfXIso {S : Type u} [CommRing S] {P : CochainComplex (ModuleCat.{u} S) ℤ}
    {n : ℤ} {N B : ModuleCat.{u} S} (q : P ≅ (CochainComplex.singleFunctor _ n).obj N)
    (j : P.X n ≅ B) : N ≅ B :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n N).symm ≪≫
    (HomologicalComplex.eval _ _ n).mapIso q.symm ≪≫ j

/-- **A perfect complex whose derived fibre at every maximal ideal has a single cohomology
module, of rank one, is locally a shift of the ring.** For a given prime, choose a maximal ideal
above it: the bounded free representative near that maximal ideal has terms of the ranks read off
from its residue field, and the principal neighbourhood it provides still contains the prime. -/
public theorem isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : StacksDraft.Perfect.IsPerfect M)
    (hrank : ∀ (m : Ideal R) (_ : m.IsMaximal), ∃ n : ℤ, ∀ i : ℤ,
      Module.finrank m.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap R m.ResidueField)).functor.obj M)) = if i = n then 1 else 0) :
    IsLocallyShiftedUnit M := by
  intro p hp
  have := hp
  obtain ⟨m, hmMax, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have : m.IsMaximal := hmMax
  have : m.IsPrime := hmMax.isPrime
  obtain ⟨n, hn⟩ := hrank m hmMax
  obtain ⟨_, _, f, hf, P, a, b, _, _, hterms, ⟨e⟩⟩ :=
    StacksDraft.Perfect.exists_away_bounded_free_complex_representing m M hM
  have hzero (i : ℤ) (hi : i ≠ n) : IsZero (P.X i) := by
    obtain ⟨j⟩ := hterms i
    rw [hn i, ite_eq_right hi] at j
    exact (ModuleCat.isZero_of_subsingleton _).of_iso j
  have : P.IsStrictlyGE n := (CochainComplex.isStrictlyGE_iff P n).mpr
    (fun i hi => hzero i (by omega))
  have : P.IsStrictlyLE n := (CochainComplex.isStrictlyLE_iff P n).mpr
    (fun i hi => hzero i (by omega))
  obtain ⟨j⟩ := hterms n
  rw [hn n, ite_eq_left rfl] at j
  let jn : P.X n ≅ ModuleCat.of (Localization.Away f) (Localization.Away f) :=
    j ≪≫ (ULift.moduleEquiv.trans
      (LinearEquiv.funUnique (Fin 1) (Localization.Away f) (Localization.Away f))).toModuleIso
  obtain ⟨N, ⟨q⟩⟩ := P.exists_iso_single n
  let qn := singleObjIsoOfXIso q jn
  exact ⟨f, fun hfp => hf (hpm hfp), n, ⟨e.symm ≪≫ DerivedCategory.Q.mapIso q ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ n).app N).symm ≪≫
    (DerivedCategory.singleFunctor _ n).mapIso qn⟩⟩

private def derivedExtensionScalarsUnitIso {A : Type u} [CommRing A] (f : R →+* A) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) := by
  letI := f.toAlgebra
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let F := CochainComplex.DerivedTensor.extensionScalars.{u, u, u} f
  let P : CochainComplex (ModuleCat.{u} R) ℤ := 𝟙_ _
  have hP : P.KFlat := by
    intro K hK
    exact HomologicalComplex.Acyclic.of_iso (rightUnitor K).symm hK
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  exact D.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (ModuleCat.of R R)) ≪≫
    asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app
        (ModuleCat.of R R)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj (ModuleCat.of R R))).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (TensorProduct.AlgebraTensorModule.rid R A A).toModuleIso

private theorem isInvertible_derivedExtensionScalars {A : Type u} [CommRing A]
    (f : R →+* A) (M : DerivedCategory (ModuleCat.{u} R)) :
    letI := (derivedCategory_symmetricMonoidalCategory R).choose
    letI := (derivedCategory_symmetricMonoidalCategory A).choose
    IsInvertible M → IsInvertible ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj M) := by
  let := (derivedCategory_symmetricMonoidalCategory R).choose
  let := (derivedCategory_symmetricMonoidalCategory A).choose
  intro ⟨h⟩
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let TR := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let TA := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨_, eR, _⟩ := (derivedCategory_symmetricMonoidalCategory R).choose_spec
  obtain ⟨_, eA, _⟩ := (derivedCategory_symmetricMonoidalCategory A).choose_spec
  let t := CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso f TR.toGeneral
    TA.toGeneral D
  let unitIso := D.functor.mapIso
      (CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj R) ≪≫
    derivedExtensionScalarsUnitIso f ≪≫
      (CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj A).symm
  let tensorIso (X Y : DerivedCategory (ModuleCat.{u} R)) :
      D.functor.obj X ⊗ D.functor.obj Y ≅ D.functor.obj (X ⊗ Y) :=
    (eA.app (D.functor.obj X)).app (D.functor.obj Y) ≪≫ t.iso.app (X, Y) ≪≫
      D.functor.mapIso ((eR.app X).app Y).symm
  exact ⟨⟨D.functor.obj h.inv,
    tensorIso M h.inv ≪≫ D.functor.mapIso h.isoLeft ≪≫ unitIso,
    tensorIso h.inv M ≪≫ D.functor.mapIso h.isoRight ≪≫ unitIso⟩⟩

/-- An object with a nonzero identity all of whose endomorphisms are zero or invertible is
simple. -/
public theorem simple_of_endomorphism_eq_zero_or_isIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [SplitMonoCategory C]
    (X : C) (hX : 𝟙 X ≠ 0) (h : ∀ f : X ⟶ X, f = 0 ∨ IsIso f) : Simple X := by
  constructor
  intro Y f hf
  constructor
  · intro hi
    have := hi
    intro hz
    apply hX
    calc
      𝟙 X = inv f ≫ f := (IsIso.inv_hom_id f).symm
      _ = 0 := by simp only [hz, comp_zero]
  · intro hne
    have : IsSplitMono f := isSplitMono_of_mono f
    let r := retraction f
    have hfr : f ≫ r = 𝟙 Y := IsSplitMono.id f
    rcases h (r ≫ f) with hz | hi
    · apply False.elim
      apply hne
      calc
        f = f ≫ (r ≫ f) := by rw [← Category.assoc, hfr, Category.id_comp]
        _ = 0 := by rw [hz, comp_zero]
    · have := hi
      have : Epi f := epi_of_epi r f
      exact ⟨⟨r, hfr, (cancel_epi f).mp (by simp [← Category.assoc, hfr])⟩⟩

private theorem simple_singleFunctor_obj_field (k : Type u) [Field k] (n : ℤ) :
    Simple ((DerivedCategory.singleFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} k) n
  let U := ModuleCat.of k k
  apply simple_of_endomorphism_eq_zero_or_isIso
  · intro hz
    have : (𝟙 U : U ⟶ U) = 0 := F.map_injective (by simpa using hz)
    exact CategoryTheory.id_nonzero U this
  · intro f
    obtain ⟨g, rfl⟩ := F.map_surjective f
    by_cases hg : g = 0
    · exact Or.inl (by simp [hg])
    · have : IsIso g := (CategoryTheory.isIso_iff_nonzero g).mpr hg
      exact Or.inr inferInstance

private theorem simple_of_isInvertible_field (k : Type u) [Field k]
    (M : DerivedCategory (ModuleCat.{u} k)) :
    letI := (derivedCategory_symmetricMonoidalCategory k).choose
    IsInvertible M → Simple M := by
  let := (derivedCategory_symmetricMonoidalCategory k).choose
  intro ⟨h⟩
  have := simple_singleFunctor_obj_field k 0
  have : Simple (𝟙_ (DerivedCategory (ModuleCat.{u} k))) :=
    Simple.of_iso (CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj k)
  have : Simple (M ⊗ 𝟙_ (DerivedCategory (ModuleCat.{u} k))) :=
    CategoryTheory.simple_obj h.tensorLeftEquivalence.functor _
  exact Simple.of_iso (rightUnitor M).symm

private theorem exists_finrank_homology_eq_ite_of_isInvertible_field
    (k : Type u) [Field k] (M : DerivedCategory (ModuleCat.{u} k)) :
    letI := (derivedCategory_symmetricMonoidalCategory k).choose
    IsInvertible M → ∃ n : ℤ, ∀ i : ℤ,
      Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj M) =
        if i = n then 1 else 0 := by
  let := (derivedCategory_symmetricMonoidalCategory k).choose
  intro hM
  have : Simple M := simple_of_isInvertible_field k M hM
  obtain ⟨a, b, _, ⟨e⟩⟩ := splitsAsCohomology_of_isPerfect_of_projective_homology M
    (isPerfect_of_isInvertible M hM) (fun _ => inferInstance)
  let G := fun n : Set.Icc a b =>
    (DerivedCategory.singleFunctor (ModuleCat.{u} k) n.1).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n.1).obj M)
  have : Simple (∐ G) := Simple.of_iso e.symm
  have hex : ∃ n, Sigma.ι G n ≠ 0 := by
    by_contra! h
    apply Simple.not_isZero (∐ G)
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro n
    simp [h]
  obtain ⟨n, hn⟩ := hex
  have : IsSplitMono (Sigma.ι G n) := IsSplitMono.mk'
    ⟨Sigma.desc (Pi.single n (𝟙 (G n))), by simp⟩
  have : IsIso (Sigma.ι G n) := isIso_of_mono_of_nonzero hn
  let j : M ≅ G n := e ≪≫ (asIso (Sigma.ι G n)).symm
  have : Simple (G n) := Simple.of_iso j.symm
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n.1).obj M
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} k) n.1
  have : F.PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    have hk : f.hom.ker = ⊥ := LinearMap.ker_eq_bot.mpr
      ((ModuleCat.mono_iff_injective f).mp hf)
    have : IsSplitMono f := IsSplitMono.mk'
      ⟨ModuleCat.ofHom f.hom.leftInverse,
        ModuleCat.hom_ext (LinearMap.leftInverse_comp_of_inj hk)⟩
    infer_instance
  have : Simple H := F.simple_of_simple_obj H
  have hrank : Module.finrank k H = 1 := isSimpleModule_iff_finrank_eq_one.mp inferInstance
  refine ⟨n.1, fun i => ?_⟩
  by_cases hi : i = n.1
  · subst i
    rw [ite_eq_left rfl]
    exact hrank
  · rw [ite_eq_right hi]
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((isZero_homology_singleFunctor_obj_of_ne _ hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso j))
    exact Module.finrank_zero_of_subsingleton

private theorem isLocallyShiftedUnit_of_isInvertible
    (M : DerivedCategory (ModuleCat.{u} R)) :
    letI := (derivedCategory_symmetricMonoidalCategory R).choose
    IsInvertible M → IsLocallyShiftedUnit M := by
  let := (derivedCategory_symmetricMonoidalCategory R).choose
  intro hM
  apply isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank M
    (isPerfect_of_isInvertible M hM)
  intro m hm
  have : m.IsPrime := hm.isPrime
  exact exists_finrank_homology_eq_ite_of_isInvertible_field m.ResidueField _
    (isInvertible_derivedExtensionScalars (algebraMap R m.ResidueField) M hM)

private theorem bijective_localized_contractLeft
    {A X Y : Type*} [CommRing A] [Algebra R A] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [Module A Y] [IsScalarTower R A Y]
    [Module.FinitePresentation R X] (S : Submonoid R) [IsLocalization S A]
    (f : X →ₗ[R] Y) [IsLocalizedModule S f] [Module.Invertible A Y] :
    Function.Bijective (LocalizedModule.map S (contractLeft R X)) := by
  let d := IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R A) A
  let g := TensorProduct.map d f
  let j := IsLocalization.moduleTensorEquiv S A (Module.Dual A Y) Y
  let c : (Module.Dual A Y ⊗[R] Y) →ₗ[R] A :=
    ((contractLeft A Y).comp j.symm.toLinearMap).restrictScalars R
  have hc : IsLocalizedModule.map S g (Algebra.linearMap R A) (contractLeft R X) = c := by
    apply IsLocalizedModule.linearMap_ext S g (Algebra.linearMap R A)
    rw [IsLocalizedModule.map_comp]
    ext l x
    simp [g, c, j, d, IsLocalization.moduleTensorEquiv,
      TensorProduct.equivOfCompatibleSMul,
      IsLocalizedModule.mapExtendScalars_apply_apply,
      IsLocalizedModule.map_apply]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective g
    (Algebra.linearMap R A), hc]
  exact Module.Invertible.bijective.comp j.symm.bijective

private theorem module_invertible_of_rankAtStalk_eq_one
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.Projective R X] (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk X p = 1) :
    Module.Invertible R X := by
  have : Module.FinitePresentation R X := Module.finitePresentation_of_projective R X
  constructor
  apply bijective_of_localized_maximal
  intro p hp
  let A := Localization.AtPrime p
  let Y := LocalizedModule p.primeCompl X
  have : Module.Free A Y := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (hrank ⟨p, hp.isPrime⟩)
  have : Module.Invertible A Y := Module.Invertible.congr e
  exact bijective_localized_contractLeft (A := A) p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl X)

private theorem idempotent_smul_eq_self_of_support_subset
    (X : Type*) [AddCommGroup X] [Module R X] {e : R} (he : IsIdempotentElem e)
    (hsupp : Module.support R X ⊆ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)))
    (x : X) : e • x = x := by
  have hz : Subsingleton (LocalizedModule.Away (1 - e) X) :=
    LocalizedModule.subsingleton_iff_support_subset.mpr
      (hsupp.trans_eq (PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he))
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := LocalizedModule.subsingleton_iff.mp hz x
  have hx : (1 - e) • x = 0 := by
    cases n with
    | zero =>
        have hx : x = 0 := by simpa using hn
        simp [hx]
    | succ n => simpa [he.one_sub.pow_succ_eq n] using hn
  simpa only [sub_smul, one_smul, sub_eq_zero, eq_comm] using hx

private theorem isLocalizedModule_id_of_idempotent_support
    (X : Type*) [AddCommGroup X] [Module R X] {e : R} (he : IsIdempotentElem e)
    (hsupp : Module.support R X ⊆ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))) :
    IsLocalizedModule.Away e (LinearMap.id : X →ₗ[R] X) := by
  apply IsLocalizedModule.Away.mk
  · have h : algebraMap R (Module.End R X) e = 1 := by
      ext x
      exact idempotent_smul_eq_self_of_support_subset X he hsupp x
    rw [h]
    exact isUnit_one
  · intro x
    exact ⟨0, x, by simp⟩
  · intro x y h
    exact ⟨0, by simpa using h⟩

private theorem invertible_baseChange_of_idempotent_support
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.Projective R X] {e : R} (he : IsIdempotentElem e)
    (hsupp : Module.support R X ⊆ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)))
    (hrank : ∀ p : PrimeSpectrum R, e ∉ p.asIdeal → Module.rankAtStalk X p = 1)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away e A] :
    Module.Invertible A (A ⊗[R] X) ∧ Nonempty (X ≃ₗ[R] A ⊗[R] X) := by
  have : IsLocalizedModule.Away e (LinearMap.id : X →ₗ[R] X) :=
    isLocalizedModule_id_of_idempotent_support X he hsupp
  refine ⟨module_invertible_of_rankAtStalk_eq_one _ (fun p => ?_),
    ⟨IsLocalizedModule.linearEquiv (Submonoid.powers e) LinearMap.id
      (TensorProduct.mk R A X 1)⟩⟩
  rw [Module.rankAtStalk_baseChange]
  exact hrank _ ((PrimeSpectrum.localization_away_comap_range A e).le ⟨p, rfl⟩)

private theorem exists_completeOrthogonalIdempotents_of_clopen_partition
    {I : Type*} [Fintype I] (U : I → Set (PrimeSpectrum R))
    (hU : ∀ i, IsClopen (U i)) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : ∀ p, ∃ i, p ∈ U i) :
    ∃ e : I → R, CompleteOrthogonalIdempotents e ∧
      ∀ i, U i = (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R)) := by
  classical
  choose e he hUe using fun i =>
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hU i)
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => ?_⟩
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j))
      IsIdempotentElem.zero
    apply TopologicalSpace.Opens.ext
    rw [PrimeSpectrum.basicOpen_mul]
    show (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum R)) ∩
      (PrimeSpectrum.basicOpen (e j) : Set (PrimeSpectrum R)) = _
    rw [← hUe i, ← hUe j, Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)]
    simp
  refine ⟨e, ⟨hortho, ?_⟩, hUe⟩
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hortho.isIdempotentElem_sum
    IsIdempotentElem.one
  apply TopologicalSpace.Opens.ext
  ext p
  show (∑ i, e i) ∉ p.asIdeal ↔ (1 : R) ∉ p.asIdeal
  simp only [Ideal.one_notMem, not_false_eq_true, iff_true]
  obtain ⟨i, hi⟩ := hcover p
  have hei : e i ∉ p.asIdeal := by
    rw [hUe i] at hi
    exact hi
  intro hs
  apply hei
  rw [← hortho.mul_sum_of_mem (Finset.mem_univ i)]
  exact p.asIdeal.mul_mem_left (e i) hs

private theorem exists_rankAtStalk_homology_eq_ite_of_isLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M)
    (p : PrimeSpectrum R) :
    ∃ n : ℤ, ∀ i : ℤ,
      Module.rankAtStalk ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) p =
        if i = n then 1 else 0 := by
  classical
  obtain ⟨f, hf, n, ⟨e⟩⟩ := hM p.asIdeal p.isPrime
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (Localization.Away f),
      q.comap (algebraMap R (Localization.Away f)) = p :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm.le hf
  refine ⟨n, fun i => ?_⟩
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M
  have := (finite_projective_homology_of_isLocallyShiftedUnit M hM i).1
  have := (finite_projective_homology_of_isLocallyShiftedUnit M hM i).2
  rw [← hq, ← Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers f) H) q]
  let j := (localizedHomologyLinearEquiv M f i).symm.trans
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) i).mapIso
      e).toLinearEquiv)
  rw [Module.rankAtStalk_eq_of_equiv j]
  by_cases hi : i = n
  · subst i
    rw [ite_eq_left rfl]
    have : Nontrivial (Localization.Away f) := q.nontrivial
    have h := congrFun (Module.rankAtStalk_eq_of_equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (Localization.Away f)) n).app
          (ModuleCat.of (Localization.Away f) (Localization.Away f))).toLinearEquiv) q
    exact h.trans (congrFun Module.rankAtStalk_self q)
  · rw [ite_eq_right hi]
    have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_homology_singleFunctor_obj_of_ne
        (ModuleCat.of (Localization.Away f) (Localization.Away f)) hi)
    exact congrFun Module.rankAtStalk_eq_zero_of_subsingleton q

private theorem exists_rankAtStalk_homology_eq_ite_in_Icc
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M))
    (p : PrimeSpectrum R) :
    ∃ n : Set.Icc a b, ∀ i : ℤ,
      Module.rankAtStalk ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M) p =
        if i = n.1 then 1 else 0 := by
  obtain ⟨n, hn⟩ := exists_rankAtStalk_homology_eq_ite_of_isLocallyShiftedUnit M hM p
  have hnI : n ∈ Set.Icc a b := by
    by_contra h
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) :=
      ModuleCat.isZero_iff_subsingleton.mp (hvan n h)
    have hz := congrFun (Module.rankAtStalk_eq_zero_of_subsingleton (R := R)
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) p
    have ho : Module.rankAtStalk
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) p = 1 := by
      simpa using hn n
    exact Nat.zero_ne_one (hz.symm.trans ho)
  exact ⟨⟨n, hnI⟩, hn⟩

private theorem hasInvertibleCohomologyDecomposition_of_isLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) :
    HasInvertibleCohomologyDecomposition M := by
  classical
  obtain ⟨a, b, hvan, _⟩ := splitsAsCohomology_of_isLocallyShiftedUnit M hM
  let I := Set.Icc a b
  let H (i : ℤ) := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M
  have hfin (i : ℤ) : Module.Finite R (H i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).1
  have hproj (i : ℤ) : Module.Projective R (H i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).2
  have hpres (i : ℤ) : Module.FinitePresentation R (H i) :=
    Module.finitePresentation_of_projective R (H i)
  have hrank (p : PrimeSpectrum R) : ∃ n : I, ∀ i : ℤ,
      Module.rankAtStalk (H i) p = if i = n.1 then 1 else 0 :=
    exists_rankAtStalk_homology_eq_ite_in_Icc M hM a b hvan p
  let U (i : I) := {p : PrimeSpectrum R | Module.rankAtStalk (H i.1) p = 1}
  have hU (i : I) : IsClopen (U i) :=
    Module.isLocallyConstant_rankAtStalk.isClopen_fiber 1
  have hdisj : Pairwise (fun i j : I => Disjoint (U i) (U j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    obtain ⟨n, hn⟩ := hrank p
    have huniq (k : I) (hk : p ∈ U k) : k = n := by
      apply Subtype.ext
      by_contra h
      have := hn k.1
      simp only [ite_eq_right h] at this
      exact Nat.zero_ne_one (this.symm.trans hk)
    exact hij ((huniq i hi).trans (huniq j hj).symm)
  have hcover (p : PrimeSpectrum R) : ∃ i, p ∈ U i := by
    obtain ⟨i, hi⟩ := hrank p
    exact ⟨i, by simpa [U] using hi i.1⟩
  obtain ⟨e, he, hUe⟩ :=
    exists_completeOrthogonalIdempotents_of_clopen_partition U hU hdisj hcover
  let A (i : I) := R ⧸ Ideal.span {1 - e i}
  have hloc (i : I) : IsLocalization.Away (e i) (A i) :=
    IsLocalization.Away.quotient_of_isIdempotentElem (he.idem i)
  let E : R ≃+* ∀ i, A i := RingEquiv.ofBijective
    (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - e i})) he.bijective_pi
  have hfac (i : I) : Module.Invertible (A i) (A i ⊗[R] H i.1) ∧
      Nonempty (H i.1 ≃ₗ[R] A i ⊗[R] H i.1) := by
    apply invertible_baseChange_of_idempotent_support (H i.1) (he.idem i)
    · rw [← hUe i]
      intro p hp
      have hp' : Module.rankAtStalk (H i.1) p ≠ 0 :=
        Nat.ne_of_gt ((Module.rankAtStalk_pos_iff_mem_support p).mpr hp)
      obtain ⟨n, hn⟩ := hrank p
      have hi : i.1 = n.1 := by
        by_contra h
        exact hp' ((hn i.1).trans (ite_eq_right h))
      exact (hn i.1).trans (ite_eq_left hi)
    · intro p hp
      exact ((hUe i).symm ▸ hp : p ∈ U i)
  refine ⟨a, b, A, inferInstance, E,
    (fun i => ModuleCat.of (A i) (A i ⊗[R] H i.1)),
    (fun i => (hfac i).1), (fun i => ?_), hvan⟩
  obtain ⟨j⟩ := (hfac i).2
  exact ⟨j.toModuleIso⟩

private theorem linearMap_eq_zero_of_disjoint_support
    {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (h : Disjoint (Module.support R X) (Module.support R Y)) (f : X →ₗ[R] Y) : f = 0 := by
  ext x
  apply Module.eq_of_localization_maximal
    (fun p : Ideal R => LocalizedModule p.primeCompl Y)
    (fun p _ => LocalizedModule.mkLinearMap p.primeCompl Y)
  intro p hp
  have hzero : Subsingleton (LocalizedModule p.primeCompl X) ∨
      Subsingleton (LocalizedModule p.primeCompl Y) := by
    by_cases hx : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R X
    · exact Or.inr (Module.notMem_support_iff.mp
        (fun hy => Set.disjoint_left.mp h hx hy))
    · exact Or.inl (Module.notMem_support_iff.mp hx)
  rcases hzero with hx | hy
  · have := hx
    simpa only [LocalizedModule.mkLinearMap_apply, LinearMap.zero_apply,
      LocalizedModule.map_mk, map_zero, LocalizedModule.zero_mk] using
      congrArg (LocalizedModule.map p.primeCompl f)
        (Subsingleton.elim (LocalizedModule.mk x 1) 0)
  · have := hy
    exact Subsingleton.elim _ _

private def piEndEquiv {I : Type*} [Fintype I] (X : I → Type*)
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]
    (h : ∀ i j, i ≠ j → ∀ f : X i →ₗ[R] X j, f = 0) :
    (∀ i, Module.End R (X i)) ≃ₗ[R] Module.End R (∀ i, X i) := by
  classical
  refine
    { toFun := fun f => LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))
      invFun := fun f i => (LinearMap.proj i).comp (f.comp (LinearMap.single R X i))
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · intro f
    funext i
    ext x
    simp
  · intro f
    apply LinearMap.ext
    intro x
    funext i
    change f (Pi.single i (x i)) i = f x i
    calc
      f (Pi.single i (x i)) i = ∑ j, f (Pi.single j (x j)) i := by
        symm
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact LinearMap.congr_fun (h j i hji
            ((LinearMap.proj i).comp (f.comp (LinearMap.single R X j)))) (x j)
        · simp
      _ = f x i := by rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single]

private def endEquivSelf_of_invertible (X : Type*) [AddCommGroup X] [Module R X]
    [Module.Invertible R X] : Module.End R X ≃ₗ[R] R :=
  (TensorProduct.lid R X).conj.symm ≪≫ₗ
    (Module.Invertible.rTensorEquiv R R
      (TensorProduct.comm R X (Module.Dual R X) ≪≫ₗ Module.Invertible.linearEquiv R X)).symm ≪≫ₗ
    LinearMap.ringLmapEquivSelf R R R

private abbrev cohomologyComplex (M : DerivedCategory (ModuleCat.{u} R)) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X n := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

private theorem cohomologyComplex_isStrictlyGE (M : DerivedCategory (ModuleCat.{u} R))
    (a b : ℤ) (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    (cohomologyComplex M).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ a).mpr
    (fun i hi => hvan i (by simp only [Set.mem_Icc]; omega))

private theorem cohomologyComplex_isStrictlyLE (M : DerivedCategory (ModuleCat.{u} R))
    (a b : ℤ) (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    (cohomologyComplex M).IsStrictlyLE b :=
  (CochainComplex.isStrictlyLE_iff _ b).mpr
    (fun i hi => hvan i (by simp only [Set.mem_Icc]; omega))

private theorem nonempty_iso_cohomologyComplex
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) :
    Nonempty (M ≅ DerivedCategory.Q.obj (cohomologyComplex M)) := by
  classical
  obtain ⟨a, b, hvan, ⟨eM⟩⟩ := splitsAsCohomology_of_isLocallyShiftedUnit M hM
  let K := cohomologyComplex M
  have := cohomologyComplex_isStrictlyGE M a b hvan
  have := cohomologyComplex_isStrictlyLE M a b hvan
  let qH (i : ℤ) :
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (DerivedCategory.Q.obj K) ≅
        K.X i :=
    (DerivedCategory.homologyFunctorFactors _ i).app K ≪≫
      (ShortComplex.HomologyData.ofZeros (K.sc i) rfl rfl).left.homologyIso
  have hp (i : ℤ) : Module.Projective R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (DerivedCategory.Q.obj K)) := by
    have := (finite_projective_homology_of_isLocallyShiftedUnit M hM i).2
    exact Module.Projective.of_equiv' (qH i).toLinearEquiv.symm
  obtain ⟨j⟩ := nonempty_iso_coproduct_singleFunctor_obj_homology (DerivedCategory.Q.obj K) a b hp
  exact ⟨eM ≪≫ (j ≪≫ Sigma.mapIso
    (fun i => (DerivedCategory.singleFunctor _ i.1).mapIso (qH i.1))).symm⟩

private def cochainZeroEquivPiEnd (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hvan : ∀ i, i ∉ Set.Icc a b → IsZero (K.X i)) :
    CochainComplex.HomComplex.Cochain K K 0 ≃ₗ[R]
      ∀ i : Set.Icc a b, Module.End R (K.X i.1) := by
  classical
  let f : CochainComplex.HomComplex.Cochain K K 0 →ₗ[R]
      ∀ i : Set.Icc a b, Module.End R (K.X i.1) :=
    { toFun := fun z i => (z.v i.1 i.1 (add_zero _)).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearEquiv.ofBijective f ⟨fun z z' h => ?_, fun z => ?_⟩
  · apply CochainComplex.HomComplex.Cochain.ext₀
    intro i
    by_cases hi : i ∈ Set.Icc a b
    · exact ModuleCat.hom_ext (congrFun h ⟨i, hi⟩)
    · exact (hvan i hi).eq_of_src _ _
  · refine ⟨CochainComplex.HomComplex.Cochain.ofHoms
      (fun i => if hi : i ∈ Set.Icc a b then ModuleCat.ofHom (z ⟨i, hi⟩) else 0), ?_⟩
    funext i
    change ((CochainComplex.HomComplex.Cochain.ofHoms
      (fun j => if hj : j ∈ Set.Icc a b then ModuleCat.ofHom (z ⟨j, hj⟩) else 0)).v
        i.1 i.1 (add_zero _)).hom = z i
    rw [CochainComplex.HomComplex.Cochain.ofHoms_v, dite_eq_left i.property]
    rfl

private theorem cohomologyComplex_linearMap_eq_zero
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M))
    (i j : ℤ) (hij : i ≠ j) (f : (cohomologyComplex M).X i →ₗ[R] (cohomologyComplex M).X j) :
    f = 0 := by
  have (i : ℤ) : Module.Finite R ((cohomologyComplex M).X i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).1
  have (i : ℤ) : Module.Projective R ((cohomologyComplex M).X i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).2
  apply linearMap_eq_zero_of_disjoint_support
  refine Set.disjoint_left.mpr fun p hi hj => ?_
  have hi' := (Module.rankAtStalk_pos_iff_mem_support p).mpr hi
  have hj' := (Module.rankAtStalk_pos_iff_mem_support p).mpr hj
  have hrank : ∃ n : Set.Icc a b, ∀ i : ℤ,
      Module.rankAtStalk ((cohomologyComplex M).X i) p = if i = n.1 then 1 else 0 :=
    exists_rankAtStalk_homology_eq_ite_in_Icc M hM a b hvan p
  obtain ⟨n, hn⟩ := hrank
  rw [hn i] at hi'
  rw [hn j] at hj'
  have hin : i = n.1 := by split_ifs at hi' with h <;> omega
  have hjn : j = n.1 := by split_ifs at hj' with h <;> omega
  exact hij (hin.trans hjn.symm)

private theorem module_invertible_pi_cohomologyComplex
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    Module.Invertible R (∀ i : Set.Icc a b, (cohomologyComplex M).X i.1) := by
  classical
  have (i : ℤ) : Module.Finite R ((cohomologyComplex M).X i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).1
  have (i : ℤ) : Module.Projective R ((cohomologyComplex M).X i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).2
  have : Module.Projective R (∀ i : Set.Icc a b, (cohomologyComplex M).X i.1) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := R))
  apply module_invertible_of_rankAtStalk_eq_one
  intro p
  have hrank : ∃ n : Set.Icc a b, ∀ i : ℤ,
      Module.rankAtStalk ((cohomologyComplex M).X i) p = if i = n.1 then 1 else 0 :=
    exists_rankAtStalk_homology_eq_ite_in_Icc M hM a b hvan p
  obtain ⟨n, hn⟩ := hrank
  rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype, Finset.sum_eq_single n]
  · simpa using hn n.1
  · intro i _ hin
    rw [hn i.1, ite_eq_right (fun h => hin (Subtype.ext h))]
  · simp

private theorem isZero_homComplexR_cohomologyComplex
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M))
    {n : ℤ} (hn : n ≠ 0) :
    IsZero ((CochainComplex.HomComplexR R (cohomologyComplex M) (cohomologyComplex M)).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro z z'
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  exact (cohomologyComplex_linearMap_eq_zero M hM a b hvan i j (by omega) _).trans
    (cohomologyComplex_linearMap_eq_zero M hM a b hvan i j (by omega) _).symm

private theorem homComplexR_cohomologyComplex_isStrictlyGE
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    (CochainComplex.HomComplexR R (cohomologyComplex M) (cohomologyComplex M)).IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ 0).mpr
    (fun _ _ => isZero_homComplexR_cohomologyComplex M hM a b hvan (by omega))

private theorem homComplexR_cohomologyComplex_isStrictlyLE
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    (CochainComplex.HomComplexR R (cohomologyComplex M) (cohomologyComplex M)).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).mpr
    (fun _ _ => isZero_homComplexR_cohomologyComplex M hM a b hvan (by omega))

private theorem nonempty_homComplexR_cohomologyComplex_iso_unit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) (a b : ℤ)
    (hvan : ∀ i, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M)) :
    Nonempty (CochainComplex.HomComplexR R (cohomologyComplex M) (cohomologyComplex M) ≅
      𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) := by
  classical
  let K := cohomologyComplex M
  let V := ∀ i : Set.Icc a b, K.X i.1
  have : Module.Invertible R V := module_invertible_pi_cohomologyComplex M hM a b hvan
  let S := CochainComplex.HomComplexR R K K
  have := homComplexR_cohomologyComplex_isStrictlyGE M hM a b hvan
  have := homComplexR_cohomologyComplex_isStrictlyLE M hM a b hvan
  let e0 : S.X 0 ≅ ModuleCat.of R R :=
    ((cochainZeroEquivPiEnd K a b hvan) ≪≫ₗ
      piEndEquiv (fun i : Set.Icc a b => K.X i.1)
        (fun i j hij => cohomologyComplex_linearMap_eq_zero M hM a b hvan i.1 j.1
          (fun h => hij (Subtype.ext h))) ≪≫ₗ
      endEquivSelf_of_invertible V).toModuleIso
  obtain ⟨L, ⟨eS⟩⟩ := S.exists_iso_single 0
  let eL := singleObjIsoOfXIso eS e0
  exact ⟨eS ≪≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).mapIso eL⟩

private theorem isInvertible_of_isLocallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) (hM : IsLocallyShiftedUnit M) :
    letI := (derivedCategory_symmetricMonoidalCategory R).choose
    IsInvertible M := by
  classical
  let := (derivedCategory_symmetricMonoidalCategory R).choose
  let := (derivedCategory_symmetricMonoidalCategory R).choose_spec.choose
  obtain ⟨a, b, hvan, _⟩ := splitsAsCohomology_of_isLocallyShiftedUnit M hM
  let K := cohomologyComplex M
  have hfin (i : ℤ) : Module.Finite R (K.X i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).1
  have hproj (i : ℤ) : Module.Projective R (K.X i) :=
    (finite_projective_homology_of_isLocallyShiftedUnit M hM i).2
  have := cohomologyComplex_isStrictlyGE M a b hvan
  have := cohomologyComplex_isStrictlyLE M a b hvan
  obtain ⟨eSU⟩ := nonempty_homComplexR_cohomologyComplex_iso_unit M hM a b hvan
  obtain ⟨N, p, ⟨aN, bN, hNa, hNb⟩, _⟩ :=
    (CochainComplex.LeftDual.exactPairing_iff_bounded_finiteProjective R).2 K
      ⟨a, b, inferInstance, inferInstance⟩ (fun i => ⟨hfin i, hproj i⟩)
  have := hNa
  have := hNb
  have hNproj (i : ℤ) : Module.Projective R (N.X i) :=
    ((CochainComplex.LeftDual.exactPairing_iff_bounded_finiteProjective R).1 K N p).2.2.2.1 i |>.2
  have hKflat : K.KFlat := CochainComplex.KFlat.kFlat_of_flat K b
  have hNflat : N.KFlat := CochainComplex.KFlat.kFlat_of_flat N bN
  obtain ⟨eH, _, _⟩ := CochainComplex.LeftDual.tensorLeftDualIsoHomComplex K N p
  obtain ⟨eM⟩ := nonempty_iso_cohomologyComplex M hM
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let t := (derivedCategory_symmetricMonoidalCategory R).choose_spec.choose_spec.choose
  let e : M ⊗ DerivedCategory.Q.obj N ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} R)) :=
    tensorIso eM (Iso.refl _) ≪≫
      ((t.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj N)) ≪≫
      T.comparison K N hKflat hNflat ≪≫
      DerivedCategory.Q.mapIso (eH K ≪≫ eSU) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
        (ModuleCat.of R R)).symm ≪≫
      (CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj R).symm
  exact ⟨⟨DerivedCategory.Q.obj N, e, (β_ (DerivedCategory.Q.obj N) M) ≪≫ e⟩⟩

/-- **Stacks 0FNT.** A derived object is invertible if and only if it is locally a shift of the
ring. In that case it is perfect, is the direct sum of its cohomology modules, every cohomology
module is finite projective, and those modules are invertible on the factors of a finite product
decomposition of the ring. -/
@[stacks 0FNT]
public theorem isInvertible_iff_locallyShiftedUnit
    (M : DerivedCategory (ModuleCat.{u} R)) :
    let derivedMonoidal := (derivedCategory_symmetricMonoidalCategory R).choose
    letI := derivedMonoidal
    (MonoidalCategory.IsInvertible M ↔ IsLocallyShiftedUnit M) ∧
      (MonoidalCategory.IsInvertible M →
        StacksDraft.Perfect.IsPerfect M ∧
          SplitsAsCohomology M ∧
          (∀ n : ℤ,
            Module.Finite R
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M) ∧
              Module.Projective R
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) ∧
          HasInvertibleCohomologyDecomposition M) := by
  intro derivedMonoidal
  let := derivedMonoidal
  refine ⟨⟨isLocallyShiftedUnit_of_isInvertible M,
    isInvertible_of_isLocallyShiftedUnit M⟩, fun hM => ?_⟩
  have hlocal := isLocallyShiftedUnit_of_isInvertible M hM
  exact ⟨isPerfect_of_isInvertible M hM,
    splitsAsCohomology_of_isLocallyShiftedUnit M hlocal,
    finite_projective_homology_of_isLocallyShiftedUnit M hlocal,
    hasInvertibleCohomologyDecomposition_of_isLocallyShiftedUnit M hlocal⟩

end DerivedCategory.Invertible

end
