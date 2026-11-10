module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Tactic.TFAE
import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.TorsionFreeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.EtaleFlatUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Generic étaleness of a morphism of smooth curves

A morphism of smooth curves over a field has nonzero differential exactly when its sheaf of
relative differentials is supported on a proper closed subset, exactly when it is unramified or
étale on a nonempty open, and exactly when it induces a finite separable extension of function
fields.

## Main results

* `AlgebraicGeometry.unramifiedAt_iff_notMem_supp_relativeDifferentials`: a morphism locally of
  finite type is unramified at a point precisely when that point misses the support of its sheaf
  of relative differentials.
* `AlgebraicGeometry.genericallyEtale_tfae`: the five equivalent conditions.

## Implementation notes

The extension of function fields is written as the residue-field extension at the generic point
of the source, the generic point of the target being its image because the morphism is dominant;
dominance is part of the condition rather than a hypothesis, since a constant morphism of curves
satisfies none of the other four conditions.

Unramifiedness at a point is compared with the vanishing of the stalk of relative differentials
through the identification of that stalk with the Kähler differentials of the local rings, which
turns the statement into formal unramifiedness of the stalk map. That comparison is what makes
the support condition, which is about stalks, and the unramifiedness conditions, which are about
open neighbourhoods, two readings of the same locus.

The condition on the differential `df : f^*Ω_{Y/k} ⟶ Ω_{X/k}` rests on the exact sequence
`f^*Ω_{Y/k} ⟶ Ω_{X/k} ⟶ Ω_{X/Y} ⟶ 0`, which exhibits `Ω_{X/Y}` as the cokernel of `df`, and on
the invertibility of `Ω_{X/k}`: the stalk of `Ω_{X/k}` at the generic point is one-dimensional
over the function field, so the stalk of `df` there is surjective as soon as it is nonzero, and
a morphism into `Ω_{X/k}` vanishes as soon as its stalk at the generic point does, `Ω_{X/k}`
being torsion free and the germ maps of a torsion-free module at the generic point therefore
injective.

## References

* [Stacks Project, Tag 0C1C](https://stacks.math.columbia.edu/tag/0C1C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeDifferentialStalkMap

universe u

namespace AlgebraicGeometry

/-! ### Unramifiedness at a point and the stalk of relative differentials -/

/-- A point misses the support of a module on a scheme exactly when the stalk there vanishes. -/
private theorem notMem_supp_iff_subsingleton_stalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    x ∉ SheafOfModules.supp F ↔ Subsingleton (F.presheaf.stalk x) :=
  (not_congr (SheafOfModules.mem_supp_iff_nontrivial_stalk F x)).trans
    not_nontrivial_iff_subsingleton

/-- Isomorphic modules on a scheme have the same support. -/
private theorem notMem_supp_congr {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) [IsIso φ]
    (x : X) : x ∉ SheafOfModules.supp F ↔ x ∉ SheafOfModules.supp G := by
  rw [notMem_supp_iff_subsingleton_stalk, notMem_supp_iff_subsingleton_stalk]
  exact Equiv.subsingleton_congr (stalkLinearEquiv F G φ x).toEquiv

/-- A morphism of schemes locally of finite type is unramified at a point exactly when that point
misses the support of its sheaf of relative differentials. -/
theorem unramifiedAt_iff_notMem_supp_relativeDifferentials {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    UnramifiedAt f x ↔ x ∉ SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) := by
  classical
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  let := algebraStalkMap f x
  rw [notMem_supp_iff_subsingleton_stalk, unramifiedAt_iff_formallyUnramified_stalkMap f x]
  refine Iff.trans ?_ (Equiv.subsingleton_congr
    (relativeDifferentialsStalkKaehlerEquiv f x).toEquiv).symm
  exact @Algebra.formallyUnramified_iff _ _ _ _ (f.stalkMap x).hom.toAlgebra

/-! ### The residue-field extension at a point of formal unramifiedness -/

/-- The algebra structure on residue fields given by `residueFieldMap` is the one induced by the
local stalk map. -/
private theorem toAlgebra_residueFieldMap_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
    (f.residueFieldMap x).hom.toAlgebra =
      (inferInstance : Algebra (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
        (IsLocalRing.ResidueField <| X.presheaf.stalk x)) :=
  Algebra.algebra_ext _ _ fun y : Y.residueField (f x) ↦ by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    rfl

/-- If the stalk map of a morphism locally of finite type is formally unramified at a point, the
residue-field extension at that point is finite. -/
private theorem finite_residueField_of_formallyUnramified_stalkMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (h : (f.stalkMap x).hom.FormallyUnramified) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  suffices hfin : Module.Finite
      (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    rw [toAlgebra_residueFieldMap_eq f x]
    exact hfin
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.formallyUnramified_algebraMap.mpr h
  infer_instance

/-- If the stalk map of a morphism locally of finite type is formally unramified at a point, the
residue-field extension at that point is separable. -/
private theorem isSeparable_residueField_of_formallyUnramified_stalkMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (h : (f.stalkMap x).hom.FormallyUnramified) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  suffices hsep : Algebra.IsSeparable
      (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    rw [toAlgebra_residueFieldMap_eq f x]
    exact hsep
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.formallyUnramified_algebraMap.mpr h
  infer_instance

/-- Conversely, a separable residue-field extension at a point whose two local rings are fields
makes the stalk map there formally unramified. -/
private theorem formallyUnramified_stalkMap_of_isSeparable_residueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hX : IsField (X.presheaf.stalk x)) (hY : IsField (Y.presheaf.stalk (f x)))
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)) :
    (f.stalkMap x).hom.FormallyUnramified := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f x)
  let : Field (X.presheaf.stalk x) := hX.toField
  let : Field (Y.presheaf.stalk (f x)) := hY.toField
  have hsep : Algebra.IsSeparable (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) := by
    convert! h
    exact (toAlgebra_residueFieldMap_eq f x).symm
  have hmax : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.maximalIdeal_eq_bot, IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  rw [← RingHom.algebraMap_toAlgebra (f.stalkMap x).hom, RingHom.formallyUnramified_algebraMap]
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmax

/-! ### Separability of field extensions -/

/-- A separable algebraic field extension is separable in the sense of transcendence bases. -/
private theorem isSeparableExtension_of_isSeparable
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (hsep : Algebra.IsSeparable k K) : Algebra.IsSeparableExtension k K := by
  constructor
  intro K' hfinite
  have hsep' : Algebra.IsSeparable k K' := Algebra.IsSeparable.of_algHom k K K'.val
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K'
  exact ⟨s, hs, Algebra.isSeparable_tower_top_of_isSeparable k _ _⟩

/-- Separable generation is carried along an isomorphism of field extensions. -/
private theorem separablyGenerated_of_algEquiv
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (e : K ≃ₐ[k] L) [Algebra.IsSeparablyGenerated k K] :
    Algebra.IsSeparablyGenerated k L := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := K)
  let t : Set L := e '' s
  let es : s ≃ t := Equiv.Set.image e.toEquiv s e.toEquiv.injective
  have hcomp : (fun x : t => (x : L)) ∘ es = fun x : s => e x := rfl
  have ht' : IsTranscendenceBasis k (fun x : t => (x : L)) :=
    (isTranscendenceBasis_equiv' es hcomp).mp (e.isTranscendenceBasis hs)
  let F : IntermediateField k K := IntermediateField.adjoin k s
  let F' : IntermediateField k L := IntermediateField.adjoin k t
  let eF : F ≃ₐ[k] F.map e.toAlgHom := IntermediateField.intermediateFieldMap e F
  have hF : F.map e.toAlgHom = F' := by
    change (IntermediateField.adjoin k s).map e.toAlgHom = IntermediateField.adjoin k (e '' s)
    exact IntermediateField.adjoin_map k s (e : K →ₐ[k] L)
  let e1 : F ≃ₐ[k] F' := eF.trans (IntermediateField.equivOfEq hF)
  have he : (algebraMap F' L).comp (e1 : F →ₐ[k] F') =
      (e : K →+* L).comp (algebraMap F K) := by
    ext x
    change ((e1 x : F') : L) = e (x : K)
    rfl
  have : Algebra.IsSeparable F K := hsep
  exact ⟨t, ht', Algebra.IsSeparable.of_equiv_equiv e1.toRingEquiv e.toRingEquiv he⟩

/-- A finite separable field extension is separable algebraic. -/
private theorem isSeparable_of_finite_isSeparableExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [Algebra.IsSeparableExtension k K] : Algebra.IsSeparable k K := by
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let : Algebra.EssFiniteType k (⊤ : IntermediateField k K) := by infer_instance
  let : Algebra.IsSeparablyGenerated k (⊤ : IntermediateField k K) := inferInstance
  have hsg : Algebra.IsSeparablyGenerated k K :=
    separablyGenerated_of_algEquiv (IntermediateField.topEquiv :
      (⊤ : IntermediateField k K) ≃ₐ[k] K)
  obtain ⟨s, hs, hsep⟩ := hsg.isSeparable
  have hsempty : IsEmpty s := hs.isEmpty_iff_isAlgebraic.mpr inferInstance
  rw [Set.isEmpty_coe_sort.mp hsempty, IntermediateField.adjoin_empty] at hsep
  let e₁ : k ≃+* (⊥ : IntermediateField k K) :=
    (IntermediateField.botEquiv k K).symm.toRingEquiv
  let e₂ : K ≃+* K := RingEquiv.refl K
  have he : (algebraMap (⊥ : IntermediateField k K) K).comp e₁ =
      e₂.toRingHom.comp (algebraMap k K) := by
    ext x
    simp [e₁, e₂, IntermediateField.botEquiv_symm]
  exact (Algebra.IsSeparable.iff_of_equiv_equiv e₁ e₂ he).2 hsep

/-! ### The generic point of the target is the image of the generic point of the source -/

/-- The residue field at a closed point of a scheme locally of finite type over a field is
algebraic over that field. -/
private theorem residueField_algebraic_of_closed_point
    {k : Type u} [Field k] {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pY] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Algebra.IsAlgebraic k (Y.residueField y) := by
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have : LocallyOfFiniteType (Y.fromSpecResidueField y) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hy
    infer_instance
  have hcomp : LocallyOfFiniteType (Y.fromSpecResidueField y ≫ pY) := inferInstance
  rw [← pY.SpecMap_residueFieldMap_fromSpecResidueField y] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (Y.residueField y) := by
    change RingHom.FiniteType (algebraMap k (Y.residueField y))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  have : Module.Finite k (Y.residueField y) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Algebra.IsAlgebraic.of_finite k (Y.residueField y)

/-- A morphism of curves over a field whose residue-field extension at the generic point of the
source is finite takes that generic point to the generic point of the target. -/
private theorem genericPoint_map_of_finiteResidueExtension
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X))]
    [Module.Finite (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X))]
    (hAlgebra : algebraMap (Y.residueField (f (genericPoint X)))
        (X.residueField (genericPoint X)) =
      (f.residueFieldMap (genericPoint X)).hom) :
    f (genericPoint X) = genericPoint Y := by
  let ηX := genericPoint X
  let y := f ηX
  by_contra hyη
  have hyclosed : IsClosed ({y} : Set Y) := by
    by_contra hn
    have : T0Space Y := inferInstance
    have : QuasiSober Y := inferInstance
    have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace pY
    have hdim := IsCurve.topologicalKrullDim_eq_one (k := k) (f := pY)
    let Z : TopologicalSpace.IrreducibleCloseds Y :=
      ⟨closure ({y} : Set Y), IsIrreducible.closure isIrreducible_singleton, isClosed_closure⟩
    have hZ : Z.carrier = Set.univ := by
      by_contra h
      have heq : Z.carrier = {y} := by
        classical
        obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints
          ⟨y, subset_closure (Set.mem_singleton y)⟩ Z.isClosed'.isLocallyClosed
        have hzc : IsClosed ({z} : Set Y) := (mem_closedPoints_iff).mp hzclosed
        let W : TopologicalSpace.IrreducibleCloseds Y :=
          ⟨{z}, isIrreducible_singleton, hzc⟩
        have hWZ : W ≤ Z := Set.singleton_subset_iff.mpr hz
        let T : TopologicalSpace.IrreducibleCloseds Y :=
          ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
        have hZT : Z < T := by
          refine lt_of_le_of_ne (by exact Set.subset_univ _) ?_
          intro heq'
          exact h (congrArg TopologicalSpace.IrreducibleCloseds.carrier heq')
        have hdim' : Order.krullDim (TopologicalSpace.IrreducibleCloseds Y) ≤ 1 := by
          change topologicalKrullDim Y ≤ 1
          rw [hdim]
        rcases (Order.krullDim_le_one_iff.mp hdim') Z with hmin | hmax
        · have hWZ' : W = Z := le_antisymm hWZ (hmin hWZ)
          have hyW : y ∈ W.carrier := by simpa [hWZ'] using subset_closure (Set.mem_singleton y)
          have hyz : y = z := Set.mem_singleton_iff.mp hyW
          simpa [hyz] using congrArg TopologicalSpace.IrreducibleCloseds.carrier hWZ'.symm
        · exact False.elim ((not_lt_of_ge (hmax (le_of_lt hZT))) hZT)
      exact hn (heq ▸ Z.isClosed')
    exact hyη ((show IsGenericPoint y Set.univ from hZ).eq (genericPoint_spec Y))
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have hyalg : Algebra.IsAlgebraic k (Y.residueField y) :=
    residueField_algebraic_of_closed_point pY y hyclosed
  let : Algebra.IsAlgebraic (Y.residueField y) (X.residueField ηX) :=
    Algebra.IsAlgebraic.of_finite _ _
  let : Algebra k (X.residueField ηX) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation ηX).hom.toAlgebra
  have hcanonical : (algebraMap k (X.residueField ηX)) =
      (f.residueFieldMap ηX).hom.comp (algebraMap k (Y.residueField y)) := by
    ext a
    calc
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation ηX).hom a =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ f.appTop ≫
            X.Γevaluation ηX).hom a := by
              rw [← hf, Scheme.Hom.comp_appTop, Category.assoc]
      _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫
            Y.Γevaluation y ≫ f.residueFieldMap ηX).hom a := by
              rw [Scheme.Γevaluation_naturality f ηX]
      _ = ((f.residueFieldMap ηX).hom.comp
            ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom) a := rfl
  have : IsScalarTower k (Y.residueField y) (X.residueField ηX) :=
    IsScalarTower.of_algebraMap_eq' (hcanonical.trans (by rw [← hAlgebra]))
  have : Algebra.IsAlgebraic k (X.residueField ηX) :=
    Algebra.IsAlgebraic.trans k (Y.residueField y) (X.residueField ηX)
  have hdim := AlgebraicGeometry.topologicalKrullDim_eq_trdeg_residueField
    k X pX ηX (genericPoint_spec X)
  have hdim1 : topologicalKrullDim X = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := pX)
  have htrdeg : Algebra.trdeg k (X.residueField ηX) = 0 := trdeg_eq_zero
  rw [hdim] at hdim1
  simp [htrdeg] at hdim1

/-! ### Vanishing of a morphism into a torsion-free module -/

/-- A torsion-free quasi-coherent module on an integral scheme has injective germ maps at the
generic point: a section whose germ there vanishes is a torsion section, hence zero. -/
private theorem generic_germ_injective_of_isTorsionFree {X : Scheme.{u}} [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree F) {U : X.Opens}
    (hη : genericPoint X ∈ U) :
    Function.Injective (F.presheaf.germ U (genericPoint X) hη) :=
  injective_generic_germ_of_isTorsionFree F hF hη

/-- A morphism into a torsion-free quasi-coherent module on an integral scheme whose stalk map at
the generic point vanishes is zero. -/
private theorem eq_zero_of_stalkLinearMap_genericPoint_eq_zero {X : Scheme.{u}} [IsIntegral X]
    {A F : X.Modules} [F.IsQuasicoherent]
    (hF : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree F)
    (φ : A ⟶ F) (h : stalkLinearMap A F φ (genericPoint X) = 0) : φ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro region
  apply ModuleCat.hom_ext
  ext value
  by_cases hregion : Nonempty region.unop
  · have hη : genericPoint X ∈ region.unop :=
      ((genericPoint_spec X).mem_open_set_iff region.unop.isOpen).mpr
        (by simpa using hregion)
    apply injective_generic_germ_of_isTorsionFree F hF hη
    have hgerm := stalkLinearMap_germ A F φ region.unop (genericPoint X) hη value
    rw [h, LinearMap.zero_apply] at hgerm
    change F.presheaf.germ region.unop (genericPoint X) hη
      ((φ.val.app (op region.unop)) value) =
        F.presheaf.germ region.unop (genericPoint X) hη 0
    rw [map_zero]
    exact hgerm.symm
  · apply TopCat.Presheaf.section_ext (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} X.toTopCat)
      region.unop
    intro point hpoint
    exact False.elim (hregion ⟨⟨point, hpoint⟩⟩)

/-- The stalks of the sheaf of relative differentials of a smooth curve over a field are free of
rank one. -/
theorem finrank_stalk_relativeDifferentials_eq_one {k : Type u} [Field k] {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX] (x : X) :
    Module.finrank (ToType (X.sheaf.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toTopCat)
        (Scheme.Hom.relativeDifferentials pX).val.presheaf x)) = 1 := by
  have heq : (pX ⁻¹' {pX x}) = (Set.univ : Set X) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  let e : pX.fiber (pX x) ≃ₜ X :=
    (pX.fiberHomeo (pX x)).trans
      ((Homeomorph.setCongr heq).trans (Homeomorph.Set.univ X))
  have hdim : topologicalKrullDimAt (pX.fiber (pX x)) (pX.asFiber x) = 1 := by
    rw [topologicalKrullDimAt_eq_of_homeomorph e,
      ← AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X pX]
    exact IsCurve.topologicalKrullDim_eq_one pX
  have hrank := AlgebraicGeometry.finrank_stalk_relativeDifferentials_eq_fiberDimensionAt pX x
  rw [hdim] at hrank
  exact_mod_cast hrank

private alias differential_finrank_one := finrank_stalk_relativeDifferentials_eq_one

/-! ### The support of the relative differentials -/

/-- On an irreducible space, a sheaf of modules of finite type is supported on a proper closed
subset exactly when its stalk at the generic point vanishes. -/
theorem exists_proper_closed_supset_supp_iff_genericPoint_notMem
    {X : Scheme.{u}} [IrreducibleSpace X]
    (F : SheafOfModules X.ringCatSheaf) [F.IsFiniteType] :
    (∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧ SheafOfModules.supp F ⊆ Z) ↔
      genericPoint X ∉ SheafOfModules.supp F := by
  refine ⟨fun ⟨Z, hZ, hproper, hsub⟩ hη => hproper (Set.eq_univ_of_univ_subset
      (((genericPoint_spec X).mem_closed_set_iff hZ).mp (hsub hη))),
    fun hη => ⟨_, SheafOfModules.isClosed_supp F, fun h => hη (h ▸ Set.mem_univ _),
      Set.Subset.rfl⟩⟩

private alias proper_support_iff_genericPoint_notMem :=
  exists_proper_closed_supset_supp_iff_genericPoint_notMem

/-! ### The five equivalent conditions -/

/-- The condition that a morphism of schemes induce a finite separable extension of residue
fields at the generic point of its source. -/
private abbrev GenericFiniteSeparable {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Y) :
    Prop :=
  letI : Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) :=
    (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  Module.Finite (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) ∧
    Algebra.IsSeparableExtension (Y.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X))

/-- A morphism of curves over a field which is unramified at the generic point of its source is
dominant and induces a finite separable extension of function fields. -/
private theorem isDominant_and_genericFiniteSeparable_of_unramifiedAt
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] (f : X ⟶ Y) (hf : f ≫ pY = pX) [LocallyOfFiniteType f]
    (hUnr : UnramifiedAt f (genericPoint X)) :
    IsDominant f ∧ GenericFiniteSeparable f := by
  let η := genericPoint X
  have hformal : (f.stalkMap η).hom.FormallyUnramified :=
    (unramifiedAt_iff_formallyUnramified_stalkMap f η).mp hUnr
  let : Algebra (Y.residueField (f η)) (X.residueField η) :=
    (f.residueFieldMap η).hom.toAlgebra
  have hfin : Module.Finite (Y.residueField (f η)) (X.residueField η) :=
    finite_residueField_of_formallyUnramified_stalkMap f η hformal
  have hsep : Algebra.IsSeparable (Y.residueField (f η)) (X.residueField η) :=
    isSeparable_residueField_of_formallyUnramified_stalkMap f η hformal
  have hη : f η = genericPoint Y :=
    genericPoint_map_of_finiteResidueExtension pX pY f hf rfl
  refine ⟨(isDominant_iff f).2 ?_, hfin, isSeparableExtension_of_isSeparable _ _ hsep⟩
  exact dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset
    (((genericPoint_spec Y).mem_closed_set_iff isClosed_closure).mp (subset_closure ⟨η, hη⟩)))

/-- **Stacks Project, Tag 0C1C.** For a morphism `f : X ⟶ Y` of smooth curves over a field `k`
the following are equivalent: the differential `f^*Ω_{Y/k} ⟶ Ω_{X/k}` is nonzero; the sheaf
`Ω_{X/Y}` is supported on a proper closed subset of `X`; `f` is unramified on a nonempty open;
`f` is étale on a nonempty open; `f` is dominant and the extension of function fields it induces
is finite separable. -/
@[stacks 0C1C]
theorem genericallyEtale_tfae
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY] [Smooth pX] [Smooth pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) :
    List.TFAE [
      Scheme.Hom.relativeDifferentialsMap f pY pX (𝟙 (Spec (.of k)))
        (by simpa using hf) ≠ 0,
      ∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧
        SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) ⊆ Z,
      ∃ U : X.Opens, Nonempty U ∧ Unramified (U.ι ≫ f),
      ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f),
      IsDominant f ∧
        (letI : Algebra (Y.residueField (f (genericPoint X)))
            (X.residueField (genericPoint X)) :=
          (f.residueFieldMap (genericPoint X)).hom.toAlgebra
         Module.Finite (Y.residueField (f (genericPoint X)))
            (X.residueField (genericPoint X)) ∧
         Algebra.IsSeparableExtension (Y.residueField (f (genericPoint X)))
            (X.residueField (genericPoint X)))] := by
  subst pX
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  let η := genericPoint X
  have hηmem (U : X.Opens) (hU : Nonempty U) : η ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hopen : UnramifiedAt f η ↔ ∃ U : X.Opens, Nonempty U ∧ Unramified (U.ι ≫ f) :=
    ⟨fun h => ⟨⟨{x : X | UnramifiedAt f x}, isOpen_setOf_unramifiedAt f⟩, ⟨⟨η, h⟩⟩,
        unramified_ι_comp_of_forall_unramifiedAt f _ fun x hx => hx⟩,
      fun ⟨U, hU, hUnr⟩ => unramifiedAt_comp_ι f hUnr ⟨η, hηmem U hU⟩⟩
  have hfield : IsDominant f → IsField (Y.presheaf.stalk (f η)) := fun hdom => by
    rw [AlgebraicGeometry.map_genericPoint_of_isDominant f]
    exact Field.toIsField Y.functionField
  tfae_have 2 ↔ 3 := by
    rw [proper_support_iff_genericPoint_notMem (Scheme.Hom.relativeDifferentials f),
      ← unramifiedAt_iff_notMem_supp_relativeDifferentials f η]
    exact hopen
  tfae_have 3 → 5 := fun h =>
    isDominant_and_genericFiniteSeparable_of_unramifiedAt (f ≫ pY) pY f rfl (hopen.mpr h)
  tfae_have 5 → 3 := by
    rintro ⟨hdom, hfin, hsepext⟩
    let : Algebra (Y.residueField (f η)) (X.residueField η) :=
      (f.residueFieldMap η).hom.toAlgebra
    let : Module.Finite (Y.residueField (f η)) (X.residueField η) := hfin
    let : Algebra.IsSeparableExtension (Y.residueField (f η)) (X.residueField η) := hsepext
    have hXfield : IsField (X.presheaf.stalk η) := Field.toIsField X.functionField
    exact hopen.mp ((unramifiedAt_iff_formallyUnramified_stalkMap f η).mpr
      (formallyUnramified_stalkMap_of_isSeparable_residueField f η hXfield (hfield hdom)
        (isSeparable_of_finite_isSeparableExtension _ _)))
  tfae_have 4 → 3 := by
    rintro ⟨U, hU, hEtale⟩
    exact ⟨U, hU, (unramified_iff_locallyOfFiniteType_and_formallyUnramified
      (U.ι ≫ f)).mpr ⟨inferInstance, inferInstance⟩⟩
  tfae_have 3 → 4 := by
    rintro ⟨U, hU, hUnr⟩
    have hUnrAt : UnramifiedAt f η := hopen.mpr ⟨U, hU, hUnr⟩
    have hYfield : IsField (Y.presheaf.stalk (f η)) :=
      hfield (isDominant_and_genericFiniteSeparable_of_unramifiedAt (f ≫ pY) pY f rfl hUnrAt).1
    have hGU : GUnramifiedAt f η := by
      obtain ⟨U₀, hU₀, hηU₀, V₀, hV₀, e, halg⟩ := hUnrAt
      refine ⟨U₀, hU₀, hηU₀, V₀, hV₀, e, ?_⟩
      let : Algebra Γ(Y, V₀) Γ(X, U₀) := (f.appLE V₀ U₀ e).hom.toAlgebra
      let : Algebra.Unramified Γ(Y, V₀) Γ(X, U₀) := halg
      have : IsNoetherianRing Γ(Y, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
      exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    have hEtaleAt : EtaleAt f η :=
      (etaleAt_iff_isFlatAt_and_gUnramifiedAt f η).mpr
        ⟨RingHom.Flat.of_isField hYfield _, hGU⟩
    obtain ⟨V, _, hηV, hEt⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt f η hEtaleAt
    exact ⟨V, ⟨⟨η, hηV⟩⟩, hEt⟩
  tfae_have 1 ↔ 2 := by
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ pY)
    obtain ⟨hzero, hexact⟩ := AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_exact f pY
    let : Epi (Scheme.Hom.toRelativeDifferentials f pY) :=
      AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_epi f pY
    let df := Scheme.Hom.relativeDifferentialsMap f pY (f ≫ pY) (𝟙 (Spec (.of k)))
      (Category.comp_id (f ≫ pY)).symm
    let S : ShortComplex X.Modules :=
      ShortComplex.mk df (Scheme.Hom.toRelativeDifferentials f pY) hzero
    have hS : S.Exact := hexact
    let : Epi S.g := AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_epi f pY
    let cok : cokernel df ≅ Scheme.Hom.relativeDifferentials f :=
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hS.gIsCokernel
    have hFLF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (Scheme.Hom.relativeDifferentials (f ≫ pY)) :=
      AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (f ≫ pY)
    have : _root_.SheafOfModules.IsCoherent (Scheme.Hom.relativeDifferentials (f ≫ pY)) :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent'_of_isQuasicoherent_of_isFiniteType _
    have htf : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree
        (Scheme.Hom.relativeDifferentials (f ≫ pY)) :=
      (isTorsionFree_iff_isFiniteLocallyFree (isRegular_of_smooth_over_field (f ≫ pY))
        (le_of_eq (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f ≫ pY))) _).mpr hFLF
    have hrank : Module.finrank (X.presheaf.stalk η)
        ((Scheme.Hom.relativeDifferentials (f ≫ pY)).presheaf.stalk η) = 1 :=
      differential_finrank_one (f ≫ pY) η
    let : Field (X.presheaf.stalk η) := inferInstanceAs (Field X.functionField)
    have h1 : (∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧
        SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) ⊆ Z) ↔
          η ∉ SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) :=
      proper_support_iff_genericPoint_notMem _
    have h2 : η ∉ SheafOfModules.supp (cokernel df) ↔
        η ∉ SheafOfModules.supp (Scheme.Hom.relativeDifferentials f) :=
      notMem_supp_congr cok.hom η
    have h3 : Function.Surjective (stalkLinearMap _ _ df η) ↔
        η ∉ SheafOfModules.supp (cokernel df) :=
      Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel df η
    have h4 : df ≠ 0 ↔ Function.Surjective (stalkLinearMap _ _ df η) := by
      constructor
      · intro hne
        refine surjective_of_nonzero_of_finrank_eq_one (K := X.presheaf.stalk η) hrank ?_
        intro h0
        exact hne (eq_zero_of_stalkLinearMap_genericPoint_eq_zero htf df h0)
      · intro hsurj hdf
        have : Nontrivial ((Scheme.Hom.relativeDifferentials (f ≫ pY)).presheaf.stalk η) :=
          Module.nontrivial_of_finrank_pos (R := X.presheaf.stalk η) (by rw [hrank]; norm_num)
        have hzero' : stalkLinearMap _ _ df η = 0 := by
          rw [hdf]
          refine (Scheme.Modules.stalkLinearMap_eq_zero_iff (0 : _ ⟶ _) η).mpr ?_
          have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesZeroMorphisms
            X.ringCatSheaf η
          exact Functor.map_zero _ _ _
        obtain ⟨w, hw⟩ :=
          exists_ne (0 : (Scheme.Hom.relativeDifferentials (f ≫ pY)).presheaf.stalk η)
        obtain ⟨z, hz⟩ := hsurj w
        rw [hzero'] at hz
        exact hw (hz.symm.trans (LinearMap.zero_apply z))
    exact (show df ≠ 0 ↔ _ from h4.trans (h3.trans (h2.trans h1.symm)))
  tfae_finish

end AlgebraicGeometry

end
