module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InvertibleHomRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafHomDegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplit

/-!
# The derived dual of an invertible sheaf on a ringed space

Let `(X, O_X)` be a ringed space and `L` an invertible sheaf of `O_X`-modules. This file
identifies the derived internal Hom out of `L` placed in degree zero into the structure sheaf
placed in degree zero with the ordinary dual sheaf `L^∨ = ℰom(L, O_X)`, again in degree zero:

`RSheafHom(L[0], O_X[0]) ≅ L^∨[0]` in `D(O_X)`.

Two known inputs make this immediate. The comparison from the class of the internal Hom complex
`SheafHom(L[0], O_X[0])` of Stacks 0A8Z to the derived internal Hom is an isomorphism, because
an invertible sheaf is rank-one locally free ([Stacks, Tag 0B8M]) and so locally a direct
summand of a finite free module, which is all the representation theorem of [Stacks, Tag 08JH]
needs: that is
`Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_isInvertible`. And the internal Hom
complex itself is concentrated in degree zero, where it is `ℰom(L, O_X)`: its degree-`n` term is
`ℰom(L[0]^{-n}, O_X)` by the degreewise collapse
`Stacks.SheafOfModules.homStructureSheafDegreeIso`, and `L[0]^{-n}` vanishes for `n ≠ 0`.

## Main definitions

* `Stacks.SheafOfModules.homSingleStructureSheafComplexIso`: the internal Hom complex
  `SheafHom(M[0], O_X[0])` of **any** sheaf of modules `M` placed in degree zero is the dual
  sheaf `ℰom(M, O_X)` placed in degree zero. No invertibility is used.
* `Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso`: for `L` invertible, the
  derived internal Hom `RSheafHom(L[0], O_X[0])` is `L^∨[0]`.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso_eq`: the identification is the
  inverse of the representation comparison of [Stacks, Tag 08JH] followed by the degreewise
  collapse, which is what pins it down.
* `Stacks.SheafOfModules.homSingleStructureSheafDegreeZeroIso_naturality`,
  `Stacks.SheafOfModules.homSingleStructureSheafComplexIso_naturality` and
  `Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso_naturality`: **all three
  identifications are natural in `M`**, a morphism `f : A ⟶ B` being carried to the dual map
  `ℰom(B, O_X) ⟶ ℰom(A, O_X)`. The derived statement is the complex-level one together with the
  naturality of the representation comparison, the two copies of whose inverse cancel.

## Implementation notes

The complex-level identification is built with `HomologicalComplex.mkHomToSingle` from the
degree-zero component of the collapse, and is an isomorphism because every other degree has
both sides zero. The degree index of the collapse is `-n`, so the degree-zero component lands on
the term `L[0]^{-0}` rather than on `L[0]^0`; the two differ by
`HomologicalComplex.singleObjXIsoOfEq` at `(-0 : ℤ) = 0`, carried into the contravariant
variable of the internal Hom sheaf by `internalHomSheafPreIso`.

For an invertible source the representation comparison is invertible for *every* target, so the
statement below is the special case of the target `O_X[0]`; it is the case that computes the
dual, and the one that the local computation of [Stacks, Tag 0B4B] uses for the ideal sheaf of
an effective Cartier divisor, which is invertible by definition.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

universe u

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An isomorphism of the source induces an isomorphism of internal Hom sheaves: the
contravariant counterpart of `AlgebraicGeometry.RingedSite.internalHomSheafPostIso`. -/
def internalHomSheafPreIso {A B : StructureSheafModules Rc}
    (e : A ≅ B) (C : StructureSheafModules Rc) :
    RingedSite.internalHomSheaf (ringedSite Rc) B C ≅
      RingedSite.internalHomSheaf (ringedSite Rc) A C where
  hom := RingedSite.internalHomPre (ringedSite Rc) e.hom
  inv := RingedSite.internalHomPre (ringedSite Rc) e.inv
  hom_inv_id :=
    (RingedSite.internalHomPre_comp (ringedSite Rc) e.inv e.hom).trans
      ((congrArg (fun g : B ⟶ B => RingedSite.internalHomPre (ringedSite Rc) (C := C) g)
          e.inv_hom_id).trans (RingedSite.internalHomPre_id (ringedSite Rc)))
  inv_hom_id :=
    (RingedSite.internalHomPre_comp (ringedSite Rc) e.hom e.inv).trans
      ((congrArg (fun g : A ⟶ A => RingedSite.internalHomPre (ringedSite Rc) (C := C) g)
          e.hom_inv_id).trans (RingedSite.internalHomPre_id (ringedSite Rc)))

/-- A complex concentrated in one degree has finite support. -/
theorem finite_support_single (M : StructureSheafModules Rc) (k : ℤ) :
    {i : ℤ | ¬ IsZero (((HomologicalComplex.single (StructureSheafModules Rc)
      (ComplexShape.up ℤ) k).obj M).X i)}.Finite := by
  refine (Set.finite_singleton k).subset fun i hi => ?_
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hi (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k M i h)

/-- The degree-zero term of the internal Hom complex `SheafHom(M[0], O_X[0])` is the dual sheaf
`ℰom(M, O_X)`: the degreewise collapse of Stacks 08DM at `n = 0`, read through the
identification of `M[0]^{-0}` with `M`. -/
def homSingleStructureSheafDegreeZeroIso (M : StructureSheafModules Rc) :
    (RingedSite.sheafHomComplex (ringedSite Rc)
        ((HomologicalComplex.single (StructureSheafModules Rc)
          (ComplexShape.up ℤ) 0).obj M)
        (RingedSite.structureSheafComplex (ringedSite Rc))).obj.X 0 ≅
      RingedSite.internalHomSheaf (ringedSite Rc) M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)) :=
  homStructureSheafDegreeIso Rc _ (finite_support_single Rc M 0) 0 ≪≫
    internalHomSheafPreIso Rc
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (-0) neg_zero).symm _

/-- Away from degree zero the internal Hom complex `SheafHom(M[0], O_X[0])` vanishes: its
degree-`n` term is the dual of `M[0]^{-n}`, which is zero for `n ≠ 0`. -/
theorem isZero_homSingleStructureSheafDegree (M : StructureSheafModules Rc) {n : ℤ}
    (hn : n ≠ 0) :
    IsZero ((RingedSite.sheafHomComplex (ringedSite Rc)
      ((HomologicalComplex.single (StructureSheafModules Rc)
        (ComplexShape.up ℤ) 0).obj M)
      (RingedSite.structureSheafComplex (ringedSite Rc))).obj.X n) :=
  isZero_homStructureSheafDegree Rc _ (finite_support_single Rc M 0) n
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M (-n)
      (fun h => hn (by omega)))

/-- The comparison `SheafHom(M[0], O_X[0]) ⟶ ℰom(M, O_X)[0]` of complexes given by the
degreewise collapse in degree zero. Its only nontrivial clause is that the differential into
degree zero kills it, which holds because the degree-`(-1)` term of the source vanishes. -/
def homSingleToSingleStructureSheaf (M : StructureSheafModules Rc) :
    (RingedSite.sheafHomComplex (ringedSite Rc)
        ((HomologicalComplex.single (StructureSheafModules Rc)
          (ComplexShape.up ℤ) 0).obj M)
        (RingedSite.structureSheafComplex (ringedSite Rc))).obj ⟶
      (HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
        (RingedSite.internalHomSheaf (ringedSite Rc) M
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc))) :=
  HomologicalComplex.mkHomToSingle (homSingleStructureSheafDegreeZeroIso Rc M).hom
    (fun i hi => (isZero_homSingleStructureSheafDegree Rc M
      (n := i) (by have h : i + 1 = 0 := hi; omega)).eq_of_src _ _)

/-- The degree-zero component of `homSingleToSingleStructureSheaf` is the degreewise collapse,
read through the identification of the degree-zero term of the single complex with its object. -/
private theorem homSingleToSingleStructureSheaf_f_zero (M : StructureSheafModules Rc) :
    (homSingleToSingleStructureSheaf Rc M).f 0 =
      (homSingleStructureSheafDegreeZeroIso Rc M).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (RingedSite.internalHomSheaf (ringedSite Rc) M
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- Every component of the comparison above is invertible: in degree zero it is the degreewise
collapse, and in every other degree both sides are zero. -/
instance isIso_homSingleToSingleStructureSheaf_f (M : StructureSheafModules Rc) (n : ℤ) :
    IsIso ((homSingleToSingleStructureSheaf Rc M).f n) := by
  by_cases hn : n = 0
  · subst hn
    have h : (homSingleToSingleStructureSheaf Rc M).f 0 =
        (homSingleStructureSheafDegreeZeroIso Rc M ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (RingedSite.internalHomSheaf (ringedSite Rc) M
              (_root_.SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).symm).hom :=
      HomologicalComplex.mkHomToSingle_f _ _
    have hiso : IsIso (homSingleStructureSheafDegreeZeroIso Rc M ≪≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (RingedSite.internalHomSheaf (ringedSite Rc) M
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).symm).hom := inferInstance
    rw [h]
    exact hiso
  · exact ⟨0, (isZero_homSingleStructureSheafDegree Rc M hn).eq_of_src _ _,
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn).eq_of_src _ _⟩

/-- **The internal Hom complex of a sheaf of modules placed in degree zero into the structure
sheaf is its dual sheaf, placed in degree zero.** -/
def homSingleStructureSheafComplexIso (M : StructureSheafModules Rc) :
    (RingedSite.sheafHomComplex (ringedSite Rc)
        ((HomologicalComplex.single (StructureSheafModules Rc)
          (ComplexShape.up ℤ) 0).obj M)
        (RingedSite.structureSheafComplex (ringedSite Rc))).obj ≅
      (HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
        (RingedSite.internalHomSheaf (ringedSite Rc) M
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc))) :=
  haveI : IsIso (homSingleToSingleStructureSheaf Rc M) :=
    HomologicalComplex.Hom.isIso_of_components _
  asIso (homSingleToSingleStructureSheaf Rc M)

/-- **The derived dual of an invertible sheaf on a ringed space is its dual sheaf:**

`RSheafHom(L[0], O_X[0]) ≅ L^∨[0]` in `D(O_X)`.

The comparison from the class of the internal Hom complex to the derived internal Hom is an
isomorphism for an invertible source ([Stacks, Tag 08JH] through [Stacks, Tag 0B8M], as
`Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_isInvertible`), and that complex is
the dual sheaf in degree zero. -/
def derivedSheafHomSingleStructureSheafIso (L : StructureSheafModules Rc)
    [IsInvertible Rc.obj (structureSheaf Rc).property L] :
    ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj
          ((HomologicalComplex.single (StructureSheafModules Rc)
            (ComplexShape.up ℤ) 0).obj L)))).obj
        (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite Rc))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj
          (RingedSite.internalHomSheaf (ringedSite Rc) L
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))) :=
  haveI := strictlyPerfectHomComparison_isIso_of_isInvertible Rc 0 L
    (RingedSite.structureSheafComplex (ringedSite Rc))
  (asIso (strictlyPerfectHomComparison Rc
      ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj L)
      (RingedSite.structureSheafComplex (ringedSite Rc)))).symm ≪≫
    DerivedCategory.Q.mapIso (homSingleStructureSheafComplexIso Rc L)

/-- The identification of the derived dual of an invertible sheaf with its dual sheaf is the
inverse of the representation comparison of [Stacks, Tag 08JH] followed by the degreewise
collapse of the internal Hom complex. This is what pins it down. -/
theorem derivedSheafHomSingleStructureSheafIso_eq (L : StructureSheafModules Rc)
    [IsInvertible Rc.obj (structureSheaf Rc).property L] :
    (derivedSheafHomSingleStructureSheafIso Rc L).inv =
      DerivedCategory.Q.map (homSingleStructureSheafComplexIso Rc L).inv ≫
        strictlyPerfectHomComparison Rc
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj L)
          (RingedSite.structureSheafComplex (ringedSite Rc)) :=
  rfl

/-- The component of `(single 0).map f` at a degree *presented as* equal to `0`, read through
`HomologicalComplex.singleObjXIsoOfEq`. This is `HomologicalComplex.single_map_f_self` with the
degree not syntactically `0`, which is what the collapse of the internal Hom complex forces: it
indexes the surviving term of `SheafHom(M[0], O_X[0])^0` as `M[0]^{-0}`. -/
private theorem single_map_f_of_eq {J : Type*} {V : Type*} [Category V]
    [CategoryTheory.Limits.HasZeroMorphisms V] [CategoryTheory.Limits.HasZeroObject V]
    (c : ComplexShape J) [DecidableEq J] (j : J) {A B : V} (f : A ⟶ B) (i : J) (hi : i = j) :
    ((HomologicalComplex.single V c j).map f).f i =
      (HomologicalComplex.singleObjXIsoOfEq c j A i hi).hom ≫ f ≫
        (HomologicalComplex.singleObjXIsoOfEq c j B i hi).inv := by
  subst hi
  exact HomologicalComplex.single_map_f_self c _ f

/-- **The degree-zero collapse `SheafHom(M[0], O_X[0])^0 ≅ ℰom(M, O_X)` is natural in `M`.** A
morphism `f : A ⟶ B` induces the map of internal Hom complexes in the other direction, and
through the collapse its degree-zero component is precomposition with `f`.

This is `Stacks.SheafOfModules.homStructureSheafDegreeIso_naturality` together with the
naturality of `HomologicalComplex.singleObjXIsoOfEq`, which is what reconciles the index `-0` of
the surviving term with the degree `0` of the source. -/
theorem homSingleStructureSheafDegreeZeroIso_naturality {A B : StructureSheafModules Rc}
    (f : A ⟶ B) :
    (RingedSite.homMap (ringedSite Rc)
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f)
          (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))).f 0 ≫
        (homSingleStructureSheafDegreeZeroIso Rc A).hom =
      (homSingleStructureSheafDegreeZeroIso Rc B).hom ≫
        RingedSite.internalHomPre (ringedSite Rc) f := by
  have hnat := homStructureSheafDegreeIso_naturality Rc
    ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
    ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj A)
    (finite_support_single Rc B 0) (finite_support_single Rc A 0)
    ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f) 0
  have hsq : (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 A (-0) neg_zero).inv ≫
      ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f).f
        (-0) =
      f ≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 B (-0) neg_zero).inv := by
    rw [single_map_f_of_eq (ComplexShape.up ℤ) 0 f (-0) neg_zero, Iso.inv_hom_id_assoc]
  show _ ≫ (homStructureSheafDegreeIso Rc _ (finite_support_single Rc A 0) 0).hom ≫
      RingedSite.internalHomPre (ringedSite Rc)
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 A (-0) neg_zero).inv =
    ((homStructureSheafDegreeIso Rc _ (finite_support_single Rc B 0) 0).hom ≫
      RingedSite.internalHomPre (ringedSite Rc)
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 B (-0) neg_zero).inv) ≫ _
  rw [← Category.assoc, hnat, Category.assoc, Category.assoc]
  exact congrArg
    ((homStructureSheafDegreeIso Rc
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
        (finite_support_single Rc B 0) 0).hom ≫ ·)
    (((RingedSite.internalHomPre_comp (ringedSite Rc)
            (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 A (-0) neg_zero).inv
            (((HomologicalComplex.single (StructureSheafModules Rc)
              (ComplexShape.up ℤ) 0).map f).f (-0))).trans
        (congrArg (fun g : A ⟶ ((HomologicalComplex.single (StructureSheafModules Rc)
              (ComplexShape.up ℤ) 0).obj B).X (-0) =>
            RingedSite.internalHomPre (ringedSite Rc)
              (C := _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)) g)
          hsq)).trans
      (RingedSite.internalHomPre_comp (ringedSite Rc) f
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 B (-0) neg_zero).inv).symm)

/-- **The identification `SheafHom(M[0], O_X[0]) ≅ ℰom(M, O_X)[0]` of complexes is natural in
`M`.** A morphism `f : A ⟶ B` induces the map of internal Hom complexes in the other direction,
and through the identification it is the single complex on precomposition with `f`.

A morphism into a complex concentrated in degree zero is determined by its degree-zero
component, where this is
`Stacks.SheafOfModules.homSingleStructureSheafDegreeZeroIso_naturality`; in every other degree
the target vanishes. -/
theorem homSingleStructureSheafComplexIso_naturality {A B : StructureSheafModules Rc}
    (f : A ⟶ B) :
    RingedSite.homMap (ringedSite Rc)
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f)
          (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc))) ≫
        (homSingleStructureSheafComplexIso Rc A).hom =
      (homSingleStructureSheafComplexIso Rc B).hom ≫
        (HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
          (RingedSite.internalHomPre (ringedSite Rc) f) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have hmid : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (RingedSite.internalHomSheaf (ringedSite Rc) B
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).inv ≫
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
            (RingedSite.internalHomPre (ringedSite Rc) f)).f 0 =
        RingedSite.internalHomPre (ringedSite Rc) f ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (RingedSite.internalHomSheaf (ringedSite Rc) A
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).inv :=
      (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (RingedSite.internalHomSheaf (ringedSite Rc) B
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).inv ≫ ·)
          (HomologicalComplex.single_map_f_self (V := StructureSheafModules Rc)
            (ComplexShape.up ℤ) 0 (RingedSite.internalHomPre (ringedSite Rc) f))).trans
        (Iso.inv_hom_id_assoc _ _)
    show _ ≫ (homSingleToSingleStructureSheaf Rc A).f 0 =
      (homSingleToSingleStructureSheaf Rc B).f 0 ≫ _
    refine (congrArg ((RingedSite.homMap (ringedSite Rc)
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f)
        (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))).f 0 ≫ ·)
      (homSingleToSingleStructureSheaf_f_zero Rc A)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (RingedSite.internalHomSheaf (ringedSite Rc) A
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)))).inv)
      (homSingleStructureSheafDegreeZeroIso_naturality Rc f)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((homSingleStructureSheafDegreeZeroIso Rc B).hom ≫ ·) hmid.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ ((HomologicalComplex.single (StructureSheafModules Rc)
        (ComplexShape.up ℤ) 0).map (RingedSite.internalHomPre (ringedSite Rc) f)).f 0)
      (homSingleToSingleStructureSheaf_f_zero Rc B).symm
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn).eq_of_tgt _ _

/-- **The derived dual of an invertible sheaf is natural in the sheaf.** For `f : A ⟶ B` a
morphism of invertible sheaves of modules, the map `R ℰom(B[0], O_X) ⟶ R ℰom(A[0], O_X)` induced
in the contravariant variable of the derived internal Hom is, under the identifications of both
sides with the dual sheaves in degree zero, the dual map `ℰom(B, O_X) ⟶ ℰom(A, O_X)`.

Each identification is the inverse of the representation comparison of [Stacks, Tag 08JH]
followed by the degreewise collapse
(`Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso_eq`). The comparison is natural
in both variables, by
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality` at `e := (single 0).map f`
and `g := 𝟙`, so the two copies of its inverse cancel against each other and what remains is
the complex-level naturality
`Stacks.SheafOfModules.homSingleStructureSheafComplexIso_naturality`. -/
theorem derivedSheafHomSingleStructureSheafIso_naturality {A B : StructureSheafModules Rc}
    [IsInvertible Rc.obj (structureSheaf Rc).property A]
    [IsInvertible Rc.obj (structureSheaf Rc).property B] (f : A ⟶ B) :
    ((derivedSheafHom Rc).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite Rc)))).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
              f)).op ≫
        (derivedSheafHomSingleStructureSheafIso Rc A).hom =
      (derivedSheafHomSingleStructureSheafIso Rc B).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
            (RingedSite.internalHomPre (ringedSite Rc) f)) := by
  have := strictlyPerfectHomComparison_isIso_of_isInvertible Rc 0 A
    (RingedSite.structureSheafComplex (ringedSite Rc))
  have := strictlyPerfectHomComparison_isIso_of_isInvertible Rc 0 B
    (RingedSite.structureSheafComplex (ringedSite Rc))
  have hA : (derivedSheafHomSingleStructureSheafIso Rc A).hom =
      inv (strictlyPerfectHomComparison Rc
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj A)
          (RingedSite.structureSheafComplex (ringedSite Rc))) ≫
        DerivedCategory.Q.map (homSingleStructureSheafComplexIso Rc A).hom := rfl
  have hB : (derivedSheafHomSingleStructureSheafIso Rc B).hom =
      inv (strictlyPerfectHomComparison Rc
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
          (RingedSite.structureSheafComplex (ringedSite Rc))) ≫
        DerivedCategory.Q.map (homSingleStructureSheafComplexIso Rc B).hom := rfl
  have hid : ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj
          ((HomologicalComplex.single (StructureSheafModules Rc)
            (ComplexShape.up ℤ) 0).obj A)))).map
        (DerivedCategory.Q.map (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))) =
      𝟙 (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj
          ((HomologicalComplex.single (StructureSheafModules Rc)
            (ComplexShape.up ℤ) 0).obj A)))).obj
        (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite Rc)))) :=
    (congrArg (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj
            ((HomologicalComplex.single (StructureSheafModules Rc)
              (ComplexShape.up ℤ) 0).obj A)))).map)
        (CategoryTheory.Functor.map_id DerivedCategory.Q
          (RingedSite.structureSheafComplex (ringedSite Rc)))).trans
      (CategoryTheory.Functor.map_id _ _)
  have hc : DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
            ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f)
            (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))) ≫
          strictlyPerfectHomComparison Rc
            ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj A)
            (RingedSite.structureSheafComplex (ringedSite Rc)) =
        strictlyPerfectHomComparison Rc
            ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
            (RingedSite.structureSheafComplex (ringedSite Rc)) ≫
          ((derivedSheafHom Rc).map (DerivedCategory.Q.map
                ((HomologicalComplex.single (StructureSheafModules Rc)
                  (ComplexShape.up ℤ) 0).map f)).op).app
              (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite Rc))) :=
    (RingedSite.strictlyPerfectHomComparison_naturality (ringedSite Rc)
        (derivedInternalHom Rc)
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj A)
        (RingedSite.structureSheafComplex (ringedSite Rc))
        (RingedSite.structureSheafComplex (ringedSite Rc))
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f)
        (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))).trans
      (congrArg (strictlyPerfectHomComparison Rc
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
          (RingedSite.structureSheafComplex (ringedSite Rc)) ≫ ·)
        ((congrArg (((derivedSheafHom Rc).map (DerivedCategory.Q.map
                  ((HomologicalComplex.single (StructureSheafModules Rc)
                    (ComplexShape.up ℤ) 0).map f)).op).app
                (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite Rc))) ≫ ·)
            hid).trans (Category.comp_id _)))
  have hF : inv (strictlyPerfectHomComparison Rc
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
          (RingedSite.structureSheafComplex (ringedSite Rc))) ≫
        DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
            ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map f)
            (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))) ≫
          strictlyPerfectHomComparison Rc
            ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj A)
            (RingedSite.structureSheafComplex (ringedSite Rc)) =
      ((derivedSheafHom Rc).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite Rc)))).map
        (DerivedCategory.Q.map
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
            f)).op :=
    (congrArg (inv (strictlyPerfectHomComparison Rc
          ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
          (RingedSite.structureSheafComplex (ringedSite Rc))) ≫ ·) hc).trans
      (IsIso.inv_hom_id_assoc _ _)
  have hmain : (DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
              ((HomologicalComplex.single (StructureSheafModules Rc)
                (ComplexShape.up ℤ) 0).map f)
              (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))) ≫
            strictlyPerfectHomComparison Rc
              ((HomologicalComplex.single (StructureSheafModules Rc)
                (ComplexShape.up ℤ) 0).obj A)
              (RingedSite.structureSheafComplex (ringedSite Rc))) ≫
          (inv (strictlyPerfectHomComparison Rc
              ((HomologicalComplex.single (StructureSheafModules Rc)
                (ComplexShape.up ℤ) 0).obj A)
              (RingedSite.structureSheafComplex (ringedSite Rc))) ≫
            DerivedCategory.Q.map (homSingleStructureSheafComplexIso Rc A).hom) =
        DerivedCategory.Q.map (homSingleStructureSheafComplexIso Rc B).hom ≫
          DerivedCategory.Q.map ((HomologicalComplex.single (StructureSheafModules Rc)
            (ComplexShape.up ℤ) 0).map (RingedSite.internalHomPre (ringedSite Rc) f)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (DerivedCategory.Q.map (RingedSite.homMap (ringedSite Rc)
              ((HomologicalComplex.single (StructureSheafModules Rc)
                (ComplexShape.up ℤ) 0).map f)
              (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))) ≫ ·)
            (IsIso.hom_inv_id_assoc _ _)).trans
        ((DerivedCategory.Q.map_comp (RingedSite.homMap (ringedSite Rc)
                ((HomologicalComplex.single (StructureSheafModules Rc)
                  (ComplexShape.up ℤ) 0).map f)
                (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc))))
              (homSingleStructureSheafComplexIso Rc A).hom).symm.trans
          ((congrArg DerivedCategory.Q.map
                (homSingleStructureSheafComplexIso_naturality Rc f)).trans
            (DerivedCategory.Q.map_comp (homSingleStructureSheafComplexIso Rc B).hom
              ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map
                (RingedSite.internalHomPre (ringedSite Rc) f))))))
  rw [hA, hB, ← hF]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (inv (strictlyPerfectHomComparison Rc
        ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj B)
        (RingedSite.structureSheafComplex (ringedSite Rc))) ≫ ·) hmain).trans ?_
  exact (Category.assoc _ _ _).symm

end Stacks.SheafOfModules

end
