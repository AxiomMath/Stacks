module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# Derived internal Hom out of a bounded-above complex into a bounded-below one

Let `X` be a ringed space, let `K` be an object of `D(𝒪_X)` vanishing in degrees above `d` and
let `L` be an object of `D(𝒪_X)` vanishing in degrees below `b`. Then `RSheafHom(K, L)` vanishes
in degrees below `b - d`.

The bound is read on models: `K` is represented by a complex `P` concentrated in degrees `≤ d`
and `L` by a K-injective complex `J` concentrated in degrees `≥ b`, and on those representatives
the derived internal Hom is the internal Hom complex `SheafHom^•(P, J)`. Over any open `U` the
degree-`n` sections of that complex are the degree-`n` morphisms from `P|_U` to `J|_U` in the
derived category of the slice site, and those vanish for `n < b - d` by the two bounds; so the
internal Hom complex has no cohomology below `b - d`.

## Main results

* `Stacks.SheafOfModules.isGE_derivedSheafHom`: the bound `b - d`.
* `Stacks.SheafOfModules.isBoundedBelow_derivedSheafHom`: the unquantified form, that
  `RSheafHom(K, L)` is cohomologically bounded below when `K` is bounded above and `L` is
  bounded below.

## References

* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  DerivedCategory

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- A cohomologically bounded-below object of `D(𝒪_X)` has a K-injective representative which
vanishes in every degree below the same bound. -/
private theorem exists_isStrictlyGE_isKInjective_model
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : DerivedCategory (StructureSheafModules Rc)) (b : ℤ) (hL : L.IsGE b) :
    ∃ J : CochainComplex (StructureSheafModules Rc) ℤ,
      J.IsStrictlyGE b ∧ J.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj J ≅ L) := by
  have := hL
  obtain ⟨C, hC, ⟨iC⟩⟩ := L.exists_iso_Q_obj_of_isGE b
  have := hC
  obtain ⟨J, -, hJ⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE b C
  have := hJ
  exact ⟨J.cocomplex, hJ, CochainComplex.isKInjective_of_injective J.cocomplex b,
    ⟨(asIso (DerivedCategory.Q.map J.ι)).symm ≪≫ iC.symm⟩⟩

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The internal Hom complex out of a complex vanishing above `d` into a K-injective complex
vanishing below `b` has no cohomology below `b - d`: over every open the degree-`n` sections
compute the degree-`n` morphisms between the restrictions, and these vanish for `n < b - d`. -/
private theorem isGE_sheafHomComplex_of_isStrictlyLE_of_isStrictlyGE
    (P J : CochainComplex (StructureSheafModules Rc) ℤ) (d b : ℤ)
    [P.IsStrictlyLE d] [J.IsStrictlyGE b] [J.IsKInjective] :
    (sheafHomComplex Rc P J).obj.IsGE (b - d) := by
  refine isGE_sheafHomComplex_of_locally_subsingleton Rc P J (b - d) (fun _ => True)
    (fun _ U hU => ⟨U, hU, le_rfl, trivial⟩) fun U _ n hn => ?_
  have hP : (restrictComplex Rc P U).IsStrictlyLE d :=
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
      Functor.map_isZero (_root_.SheafOfModules.overFunctor (structureSheaf Rc) U)
        (P.isZero_of_isStrictlyLE d i hi)
  have hJ : (restrictComplex Rc J U).IsStrictlyGE b :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
      Functor.map_isZero (_root_.SheafOfModules.overFunctor (structureSheaf Rc) U)
        (J.isZero_of_isStrictlyGE b i hi)
  have hA : (DerivedCategory.Q.obj (restrictComplex Rc P U)).IsLE d := inferInstance
  have hB : (DerivedCategory.Q.obj (restrictComplex Rc J U)).IsGE b := inferInstance
  have hBn : ((DerivedCategory.Q.obj (restrictComplex Rc J U))⟦n⟧).IsGE (b - n) :=
    DerivedCategory.TStructure.t.isGE_shift _ b n (b - n) (by omega)
  exact ⟨fun f g => (DerivedCategory.TStructure.t.zero f d (b - n) (by omega)).trans
    (DerivedCategory.TStructure.t.zero g d (b - n) (by omega)).symm⟩

/-- **The derived internal Hom of a bounded-above complex into a bounded-below complex is
bounded below.** If `K` vanishes in degrees above `d` and `L` vanishes in degrees below `b`,
then `RSheafHom(K, L)` vanishes in degrees below `b - d`. -/
public theorem isGE_derivedSheafHom
    (K L : DerivedCategory (StructureSheafModules Rc)) (d b : ℤ)
    (hK : K.IsLE d) (hL : L.IsGE b) :
    (((derivedSheafHom Rc).obj (op K)).obj L).IsGE (b - d) := by
  have := hK
  obtain ⟨P, hP, ⟨eP⟩⟩ := K.exists_iso_Q_obj_of_isLE d
  obtain ⟨J, hJ, hJinj, ⟨eJ⟩⟩ := exists_isStrictlyGE_isKInjective_model Rc L b hL
  have := hP
  have := hJ
  have := hJinj
  have hmodel : (DerivedCategory.Q.obj (sheafHomComplex Rc P J).obj).IsGE (b - d) := by
    have := isGE_sheafHomComplex_of_isStrictlyLE_of_isStrictlyGE Rc P J d b
    infer_instance
  refine DerivedCategory.TStructure.t.isGE_of_iso (X := DerivedCategory.Q.obj
    (sheafHomComplex Rc P J).obj) ?_ (b - d)
  exact (derivedSheafHomComparison Rc P J).symm ≪≫
    ((derivedSheafHom Rc).mapIso eP.op).app (DerivedCategory.Q.obj J) ≪≫
      ((derivedSheafHom Rc).obj (op K)).mapIso eJ

/-- **The derived internal Hom of a bounded-above complex into a bounded-below complex is
cohomologically bounded below.** If `K` is bounded above and `L` is bounded below, then
`RSheafHom(K, L)` is bounded below, on an arbitrary ringed space. -/
@[stacks 0D0C "the boundedness clause, on an arbitrary ringed space and with no coherence or \
Noetherian hypothesis; the coherence clause is not carried"]
public theorem isBoundedBelow_derivedSheafHom
    (K L : DerivedCategory (StructureSheafModules Rc))
    (hK : DerivedCategoryB.IsBoundedAbove K) (hL : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.IsBoundedBelow (((derivedSheafHom Rc).obj (op K)).obj L) := by
  obtain ⟨d, hd⟩ := hK
  obtain ⟨b, hb⟩ := hL
  have hK' : K.IsLE (d + 1) := (DerivedCategory.isLE_iff K (d + 1)).mpr fun i hi =>
    hd i (by omega)
  have hL' : L.IsGE b := (DerivedCategory.isGE_iff L b).mpr hb
  exact ⟨b - (d + 1), fun i hi =>
    (DerivedCategory.isGE_iff _ (b - (d + 1))).1
      (isGE_derivedSheafHom Rc K L (d + 1) b hK' hL') i hi⟩

end Stacks.SheafOfModules

end
