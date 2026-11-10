module

public import Mathlib.FieldTheory.FinTrdeg
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# The diagonal of a nonsingular variety

The diagonal `Δ : X ⟶ X ×ₖ X` of a nonsingular variety `X` over a perfect field `k` is a regular
immersion, and its codimension is the dimension of `X`. Nonsingularity is
`AlgebraicGeometry.IsRegular`. The codimension is expressed in two ways: as the rank of the
conormal sheaf of `Δ`, and as the codimension in `X ×ₖ X` of the closure of the image under `Δ` of
the generic point of `X`.

## Main results

* `Stacks.Intersection.isRegularImmersion_diagonal`: the diagonal of a nonsingular variety over a
  perfect field is a regular immersion.
* `Stacks.Intersection.isFiniteLocallyFreeOfRank_conormalSheaf_diagonal`: the conormal sheaf of
  that diagonal is finite locally free of rank the dimension of the variety.
* `Stacks.Intersection.codimension_diagonal_eq_topologicalKrullDim`: for any variety, the closure
  of the image of the generic point under the diagonal has codimension the dimension of the
  variety in the product.
* `Stacks.Intersection.isFiniteLocallyFreeOfRank_relativeDifferentials`: the sheaf of relative
  differentials of a nonsingular variety over a perfect field is finite locally free of rank its
  dimension.
* `Stacks.Intersection.exists_topologicalKrullDim_eq_natCast`: the dimension of a variety is a
  natural number.
* `Stacks.Intersection.trdeg_residueField_eq_of_isClosedImmersion_of_eq`: a closed immersion
  does not change the transcendence degree of the residue field, read at any point of the target
  equal to the image of the given one.
* `Stacks.Intersection.trdeg_residueField_lt_aleph0_of_locallyOfFiniteType`: on a scheme locally
  of finite type over a field the residue field at any point has finite transcendence degree.

## References

* [Stacks Project, Lemma 43.13.3 (Tag 0B0Q)](https://stacks.math.columbia.edu/tag/0B0Q)
* [Stacks Project, Lemma 31.22.7 (Tag 067U)](https://stacks.math.columbia.edu/tag/067U)
* [Stacks Project, Lemma 25.16.1 (Tag 08S2)](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.Intersection

universe u

section Nonsingular

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The diagonal `X ⟶ X ×ₖ X` of a nonsingular variety over a perfect field is a regular
immersion. -/
@[stacks 0B0Q "the diagonal is a regular immersion", sga "1 II 4.18" "variety over perfect fld"]
theorem isRegularImmersion_diagonal [IsVariety k f] (hX : IsRegular X) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion (pullback.diagonal f) := by
  have hf : Smooth f := smooth_of_isRegular_over_perfectField f hX
  have hp : Smooth (pullback.fst f f ≫ f) := smooth_pullback_of_isRegular f f hX hX
  have : Smooth (pullback.diagonal f ≫ (pullback.fst f f ≫ f)) := by
    rwa [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  exact Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth
    (pullback.diagonal f) (pullback.fst f f ≫ f)

/-- The sheaf of relative differentials of a nonsingular variety over a perfect field is finite
locally free of rank the dimension of the variety. -/
theorem isFiniteLocallyFreeOfRank_relativeDifferentials [IsVariety k f] (hX : IsRegular X)
    (n : ℕ) (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f) n := by
  have hf : Smooth f := smooth_of_isRegular_over_perfectField f hX
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  have hft : (Scheme.Hom.relativeDifferentials f).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree
      (R := X.ringCatSheaf) (Scheme.Hom.relativeDifferentials f)
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq _ n (genericPoint X) ?_
  have hcast : ((Scheme.Modules.fiberRank (Scheme.Hom.relativeDifferentials f)
      (genericPoint X) : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    rw [← hdim, topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f (genericPoint X),
      topologicalKrullDimAt_eq_fiber_of_subsingleton f (genericPoint X),
      ← finrank_stalk_relativeDifferentials_eq_fiberDimensionAt f (genericPoint X),
      Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (Scheme.Hom.relativeDifferentials f)]
    rfl
  exact_mod_cast hcast

/-- The conormal sheaf of the diagonal of a nonsingular variety over a perfect field is finite
locally free of rank the dimension of the variety: the diagonal is a regular immersion of
codimension `dim X`. -/
@[stacks 0B0Q "the codimension of the diagonal is the dimension of the variety"]
theorem isFiniteLocallyFreeOfRank_conormalSheaf_diagonal [IsVariety k f] (hX : IsRegular X)
    (n : ℕ) (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) n :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f)
    (isFiniteLocallyFreeOfRank_relativeDifferentials f hX n hdim)

end Nonsingular

section Codimension

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The codimension of the closure of a point is its coheight in the specialisation order. -/
private lemma codimension_closureSingleton_eq_coheight {Y : Scheme.{u}} (y : Y) :
    codimension (IrreducibleCloseds.closureSingleton y) = Order.coheight y := by
  rw [codimension_eq_coheight]
  let e := irreducibleSetEquivPoints (α := Y)
  have heq : e (IrreducibleCloseds.closureSingleton y) = y :=
    ((IrreducibleCloseds.closureSingleton y).isIrreducible.isGenericPoint_genericPoint
      (IrreducibleCloseds.closureSingleton y).isClosed).eq
      (show IsGenericPoint y (IrreducibleCloseds.closureSingleton y : Set Y) from rfl)
  rw [← Order.coheight_orderIso e, heq]

/-- A closed immersion preserves the transcendence degree over the base field of the residue
fields. -/
public theorem trdeg_residueField_of_isClosedImmersion {Y Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) (i : Y ⟶ Z) [IsClosedImmersion i] (y : Y) :
    letI : Algebra k (Z.residueField (i y)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation (i y)).hom.toAlgebra
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ g).appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Algebra.trdeg k (Z.residueField (i y)) = Algebra.trdeg k (Y.residueField y) := by
  let : Algebra k (Z.residueField (i y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation (i y)).hom.toAlgebra
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ g).appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have hs : Function.Surjective (i.residueFieldMap y).hom := by
    have h := (Y.residue_surjective y).comp (i.stalkMap_surjective y)
    change Function.Surjective (i.stalkMap y ≫ Y.residue y).hom at h
    rw [← Scheme.residue_residueFieldMap i y] at h
    exact .of_comp (g := (Z.residue (i y)).hom) h
  let e : Z.residueField (i y) ≃ₐ[k] Y.residueField y :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (i.residueFieldMap y).hom
      ⟨RingHom.injective _, hs⟩) (by
        intro a
        change (i.residueFieldMap y).hom
          (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation (i y)).hom a) =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ g).appTop ≫ Y.Γevaluation y).hom a
        rw [Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply i y
          (g.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)))
  exact e.trdeg_eq

/-- For a closed immersion `i : Y ⟶ Z` over a field `k`, a point `y` of `Y` and a point `z` of `Z`
with `i y = z`, the residue fields at `z` and at `y` have the same transcendence degree over
`k`. -/
public theorem trdeg_residueField_eq_of_isClosedImmersion_of_eq {Y Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) (i : Y ⟶ Z) [IsClosedImmersion i] (y : Y) {z : Z} (hz : i y = z) :
    letI : Algebra k (Z.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ g).appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Algebra.trdeg k (Z.residueField z) = Algebra.trdeg k (Y.residueField y) := by
  subst hz
  exact trdeg_residueField_of_isClosedImmersion g i y

/-- On a scheme locally of finite type over a field the residue field at any point has finite
transcendence degree. -/
private theorem trdeg_residueField_lt_aleph0 [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let p : PrimeSpectrum k := f x
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hbase : (((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).Γevaluation (f x)).hom).EssFiniteType := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (f x) trivial ≫
      (Spec (.of k)).residue (f x)).hom).EssFiniteType
    rw [← Scheme.Spec.algebraMap_residueFieldIso_inv]
    exact (show (algebraMap k p.asIdeal.ResidueField).EssFiniteType from
        RingHom.essFiniteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.essFiniteType
        (RingHom.FiniteType.of_surjective _
          (Scheme.Spec.residueFieldIso (.of k) (f x)).symm.commRingCatIsoToRingEquiv.surjective))
  let : Algebra.EssFiniteType k (X.residueField x) := by
    rw [← RingHom.essFiniteType_algebraMap]
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom).EssFiniteType
    rw [← Scheme.Γevaluation_naturality]
    exact hbase.comp (RingHom.EssFiniteType.residueFieldMap
      (LocallyOfFiniteType.stalkMap f x))
  exact trdeg_lt_aleph0 k (X.residueField x)

/-- **On a scheme locally of finite type over a field the residue field at any point has finite
transcendence degree.** This is `trdeg_residueField_lt_aleph0` above, made available to other
modules: the transcendence degrees that the dimension computations at the diagonal add and
subtract have to be known finite, and that happens outside this file. -/
public alias trdeg_residueField_lt_aleph0_of_locallyOfFiniteType := trdeg_residueField_lt_aleph0

/-- The dimension of a variety is a natural number. -/
theorem exists_topologicalKrullDim_eq_natCast [IsVariety k f] :
    ∃ n : ℕ, topologicalKrullDim X = (n : WithBot ℕ∞) := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  have hne : Cardinal.toENat (Algebra.trdeg k (X.residueField (genericPoint X))) ≠ ⊤ :=
    (Cardinal.toENat_lt_top.2 (trdeg_residueField_lt_aleph0 f (genericPoint X))).ne
  refine ⟨(Cardinal.toENat (Algebra.trdeg k (X.residueField (genericPoint X)))).toNat, ?_⟩
  rw [topologicalKrullDim_eq_trdeg_residueField k X f (genericPoint X) (genericPoint_spec X)]
  exact_mod_cast (ENat.natCast_toNat hne).symm

/-- The image of the diagonal of a variety has codimension the dimension of the variety inside
the product `X ×ₖ X`: the codimension of the closure of the image of the generic point is
`dim X`. -/
@[stacks 0B0Q "the codimension of the image of the diagonal is the dimension of the variety"]
theorem codimension_diagonal_eq_topologicalKrullDim [IsVariety k f] :
    (codimension (IrreducibleCloseds.closureSingleton
      (pullback.diagonal f (genericPoint X))) : WithBot ℕ∞) = topologicalKrullDim X := by
  set η : X := genericPoint X
  set Z := (pullback f f : Scheme.{u})
  set p : Z ⟶ Spec (.of k) := pullback.fst f f ≫ f with hp
  set z : Z := pullback.diagonal f η
  let : IsClosedImmersion (pullback.diagonal f) := inferInstance
  set g : X ⟶ Spec (.of k) := pullback.diagonal f ≫ p with hg
  let : LocallyOfFiniteType g := by
    rw [hg, hp, ← Category.assoc, pullback.diagonal_fst, Category.id_comp]
    infer_instance
  let : Algebra k (X.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation η).hom.toAlgebra
  let : Algebra k (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  have htrZ : Algebra.trdeg k (Z.residueField z) = Algebra.trdeg k (X.residueField η) :=
    trdeg_residueField_of_isClosedImmersion p (pullback.diagonal f) η
  have hz {π : Z ⟶ X} (h : pullback.diagonal f ≫ π = 𝟙 X) : π z = η := by
    change (pullback.diagonal f ≫ π) η = η
    rw [h]
    rfl
  have hzfst : (pullback.fst f f) z = η := hz (pullback.diagonal_fst f)
  have hzsnd : (pullback.snd f f) z = η := hz (pullback.diagonal_snd f)
  have hsum : topologicalKrullDim X + topologicalKrullDim X =
      (Cardinal.toENat (Algebra.trdeg k (Z.residueField z)) : WithBot ℕ∞) +
        ringKrullDim (Z.presheaf.stalk z) :=
    (show topologicalKrullDimAt Z z = _ by
      rw [topologicalKrullDimAt_pullback k f f z, hzfst, hzsnd,
        ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f η]).symm.trans
      (topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Z p z)
  have hdimGeneric := topologicalKrullDim_eq_trdeg_residueField k X g η (genericPoint_spec X)
  rw [htrZ, ← hdimGeneric, ringKrullDim_stalk_eq_coheight z] at hsum
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast f
  rw [hn] at hsum
  have hsum' : (n : ℕ∞) + (n : ℕ∞) = (n : ℕ∞) + Order.coheight z := by exact_mod_cast hsum
  rw [codimension_closureSingleton_eq_coheight z,
    ← WithTop.add_left_cancel (WithTop.coe_ne_top (a := n)) hsum', hn]
  rfl

end Codimension

end Stacks.Intersection

end
