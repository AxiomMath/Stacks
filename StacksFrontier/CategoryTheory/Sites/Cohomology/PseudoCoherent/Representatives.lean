module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of a representative of a pseudo-coherent derived object

Let `(C, O)` be a ringed site and let `E` be an object of `D(O)` which is `m`-pseudo-coherent,
that is, isomorphic to the image of some `m`-pseudo-coherent complex of `O`-modules. Then
*every* complex of `O`-modules representing `E` is `m`-pseudo-coherent. This is part (2) of
Stacks 08FU.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictCochainAlong`: restriction of cochain complexes of
  `O|_V`-modules along an arrow `W ⟶ V` of the site.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_lift_of_quasiIso`: the special case of
  Stacks 08FQ in which the map lifted through is a quasi-isomorphism, with the restriction
  expressed by `SheafOfModules.overMap` rather than by passage to an iterated slice. It is
  stated separately from the use made of it here because it is also what turns a *derived*
  strictly perfect approximation over a slice into the chain-level approximations on a covering
  that the definition of pseudo-coherence asks for.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_iso`: Stacks 08FU, part (2).

## Implementation notes

The proof follows the source. Write `K₀` for an `m`-pseudo-coherent complex representing `E`
and `K` for the complex at hand. The isomorphism `Q(K₀) ≅ Q(K)` of `D(O)` is written as a left
fraction `Q(u) ≫ (Q s)⁻¹` with `u : K₀ ⟶ Y` and `s : K ⟶ Y` morphisms of complexes
(`DerivedCategory.left_fac`); both are quasi-isomorphisms since the fraction is invertible. Over
any object `V` of the site carrying a strictly perfect approximation `α : P ⟶ K₀|_V`, the
composite `α ≫ u|_V : P ⟶ Y|_V` has the same behaviour on cohomology as `α`, and it lifts
through the quasi-isomorphism `s|_V : K|_V ⟶ Y|_V` after restriction along the arrows of a
covering sieve of `V` — this is the lifting lemma below, the special case of Stacks 08FQ in
which the map lifted through is a quasi-isomorphism, deduced from Stacks 08FP (1) as in the
source. Binding those sieves over a covering of an arbitrary object `U` gives the covering of
`U` required by the definition of `m`-pseudo-coherence of `K`.

Two pieces of bookkeeping are needed, both forced by the shape of Stacks 08FP (1).

* That lemma restricts along an arrow `g : W ⟶ V` by `SheafOfModules.overFunctor` on the slice
  `C/V`, landing in sheaves of modules over the *iterated* slice `(C/V)/(W → V)`, whereas the
  definition of pseudo-coherence speaks of the slice `C/W`. The two are compared by
  `Stacks.SheafOfModules.sliceBackward`, the pushforward of sheaves of modules along
  `Over.iteratedSliceBackward`; the point is that restricting to the iterated slice and then
  transporting is *equal*, not merely isomorphic, to `SheafOfModules.overMap` along `g`
  (`Stacks.SheafOfModules.overFunctor_comp_sliceBackward`), so all of the development below is
  phrased with `overMap`, for which exactness and the comparison
  `overFunctor V ⋙ overMap g ≅ overFunctor W` are already available. That comparison and its
  degreewise forms are in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/IteratedSlice.lean`.
* Restriction along `g` must be known to carry strictly perfect complexes to strictly perfect
  complexes, and to preserve the two cohomological conditions. Both follow from exactness of
  `overMap` together with `SheafOfModules.mapFreeIso`.

Stacks 08FU (2) is stated twice: `isPseudoCoherentComplexFrom_of_iso_general` has the objects
of the site, its morphisms and the sections of the structure sheaf at independent universes,
and `isPseudoCoherentComplexFrom_of_iso` is its instance at `RingedSite.{u, u, 0}`.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

/-- A null-homotopy of the image of a morphism under one functor between categories of
complexes gives a null-homotopy of its image under any isomorphic functor. -/
private def homotopyZeroOfNatIso {ι : Type} {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {c : ComplexShape ι}
    {F G : HomologicalComplex A c ⥤ HomologicalComplex B c} (e : F ≅ G)
    {X Y : HomologicalComplex A c} (α : X ⟶ Y) (h : Homotopy (F.map α) 0) :
    Homotopy (G.map α) 0 :=
  (Homotopy.ofEq (by simp)).trans
    (((h.compLeft (e.inv.app X)).compRight (e.hom.app Y)).trans (Homotopy.ofEq (by simp)))

/-- Restriction of cochain complexes of `O`-modules to the slice over an object of the site. -/
private noncomputable abbrev restrictTo (X : RingedSite.{u, v, w}) (V : X.C) :
    CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ :=
  (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Restriction of cochain complexes of `O|_V`-modules along an arrow `W ⟶ V` of the site. -/
noncomputable abbrev restrictCochainAlong (X : RingedSite.{u, v, w}) {V W : X.C} (g : W ⟶ V) :
    CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ ⥤
      CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ :=
  (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
    (ComplexShape.up ℤ)

section Lifting

variable (X : RingedSite.{u, v, w}) (W : X.C)
variable [HasSheafify (X.J.over W) AddCommGrpCat.{w}]
variable [(X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 08FP (1)**, with the restriction to the slice over an arrow `V → W` of the covering
sieve expressed by `SheafOfModules.overMap` rather than by restriction to an iterated slice. -/
private theorem exists_coveringSieve_homotopy_zero_of_acyclic_overMap
    {E F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ}
    (α : E ⟶ F)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) E)
    (hF : F.Acyclic) :
    ∃ S : Sieve W, S ∈ X.J W ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ W), S g →
        Nonempty (Homotopy ((restrictCochainAlong X g).map α) 0) := by
  obtain ⟨S, hS, hnull⟩ := exists_coveringSieve_homotopy_zero_of_acyclic_general X W α hE hF
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨h⟩ := hnull g hg
  exact ⟨homotopyZeroOfNatIso
    (Stacks.SheafOfModules.sliceBackwardComplexIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) α
    (((Stacks.SheafOfModules.sliceBackward
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomotopy h).trans
      (Homotopy.ofEq (Functor.map_zero _ _ _)))⟩

/-- The mapping cone of a quasi-isomorphism of complexes in an abelian category is acyclic: the
cone sits in a distinguished triangle of the derived category whose first map is invertible. -/
private theorem acyclic_mappingCone_of_quasiIso {A : Type*} [Category A] [Abelian A]
    {G F : CochainComplex A ℤ} (f : G ⟶ F) [QuasiIso f] :
    (CochainComplex.mappingCone f).Acyclic := by
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  have hf : IsIso (DerivedCategory.Q.map f) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have hzero : IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      (DerivedCategory.mappingCone_triangle_distinguished f) hf
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine ((DerivedCategory.homologyFunctorFactors A i).app
    (CochainComplex.mappingCone f)).isZero_iff.mp ?_
  exact Functor.map_isZero (DerivedCategory.homologyFunctor A i) hzero

/-- The special case of **Stacks 08FQ** in which the map lifted through is a quasi-isomorphism:
a morphism `α : E ⟶ F` of complexes of `O|_W`-modules whose source is strictly perfect lifts,
up to homotopy, through a quasi-isomorphism `f : G ⟶ F` after restriction along the arrows of a
covering sieve of `W`.

The cone of `f` is acyclic, so Stacks 08FP (1) makes `α ≫ inr f` null-homotopic on a covering
sieve; over each of its arrows the lift is then produced from the distinguished triangle
`G|_V ⟶ F|_V ⟶ C(f|_V) ⟶ G|_V[1]` of the homotopy category. -/
theorem exists_coveringSieve_lift_of_quasiIso
    {E F G : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ}
    (α : E ⟶ F) (f : G ⟶ F)
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) E) [QuasiIso f] :
    ∃ S : Sieve W, S ∈ X.J W ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ W), S g →
        ∃ β : (restrictCochainAlong X g).obj E ⟶ (restrictCochainAlong X g).obj G,
          Nonempty (Homotopy (β ≫ (restrictCochainAlong X g).map f)
            ((restrictCochainAlong X g).map α)) := by
  obtain ⟨S, hS, hnull⟩ := exists_coveringSieve_homotopy_zero_of_acyclic_overMap X W
    (α ≫ CochainComplex.mappingCone.inr f) hE (acyclic_mappingCone_of_quasiIso f)
  refine ⟨S, hS, fun V g hg => ?_⟩
  set Rg := SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g with hRg
  set Rc := Rg.mapHomologicalComplex (ComplexShape.up ℤ) with hRc
  have : HasFiniteBiproducts
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : HomologicalComplex.HasHomotopyCofiber (Rc.map f) := ⟨fun i j _ => inferInstance⟩
  let Quo := HomotopyCategory.quotient
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) (ComplexShape.up ℤ)
  let coneIso := CochainComplex.mappingCone.mapHomologicalComplexIso f Rg
  have hnull' : Quo.map (Rc.map α ≫ Rc.map (CochainComplex.mappingCone.inr f)) = 0 := by
    rw [← Functor.map_comp]
    exact (HomotopyCategory.quotient_map_eq_zero_iff _).2 (hnull g hg)
  have hcomp : Quo.map (Rc.map α) ≫
      Quo.map (CochainComplex.mappingCone.inr (Rc.map f)) = 0 := by
    rw [← Functor.map_comp, show Rc.map α ≫ CochainComplex.mappingCone.inr (Rc.map f) =
      (Rc.map α ≫ Rc.map (CochainComplex.mappingCone.inr f)) ≫ coneIso.hom from by
        rw [Category.assoc, CochainComplex.mappingCone.map_inr f Rg], Functor.map_comp,
      hnull', zero_comp]
  obtain ⟨βq, hβq⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂
    (CochainComplex.mappingCone.triangleh (Rc.map f))
    (HomotopyCategory.mappingCone_triangleh_distinguished (Rc.map f)) (Quo.map (Rc.map α)) hcomp
  obtain ⟨β, hβ⟩ := Quo.map_surjective βq
  change Rc.obj E ⟶ Rc.obj G at β
  have hzero : Quo.map (β ≫ Rc.map f - Rc.map α) = 0 := by
    rw [Functor.map_sub, Functor.map_comp]
    exact sub_eq_zero.mpr (hβ.symm ▸ hβq.symm)
  obtain ⟨hK⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).1 hzero
  exact ⟨β, ⟨Homotopy.equivSubZero.symm hK⟩⟩

end Lifting

section Transfer

/-- An isomorphism of functors transfers epimorphy of an image. -/
theorem epi_map_iff_of_natIso {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (e : F ≅ G) {P Q : A} (f : P ⟶ Q) : Epi (F.map f) ↔ Epi (G.map f) := by
  constructor <;> intro hf
  · rw [show G.map f = e.inv.app P ≫ F.map f ≫ e.hom.app Q by simp]
    exact epi_comp _ _
  · rw [show F.map f = e.hom.app P ≫ G.map f ≫ e.inv.app Q by simp]
    exact epi_comp _ _

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- An exact functor carries a morphism of complexes which is epic on cohomology in a degree to
one which is again epic on cohomology in that degree. -/
public theorem epi_homologyMap_map [F.PreservesEpimorphisms]
    {P Q : CochainComplex A ℤ} (φ : P ⟶ Q) (i : ℤ)
    (hφ : Epi (HomologicalComplex.homologyMap φ i)) :
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i) := by
  have : Epi (HomologicalComplex.homologyMap φ i) := hφ
  exact (epi_map_iff_of_natIso (ShortComplex.homologyFunctorIso F)
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map φ)).mpr
    (inferInstanceAs (Epi (F.map (HomologicalComplex.homologyMap φ i))))

/-- An exact functor carries a morphism of complexes which is invertible on cohomology in a
degree to one which is again invertible on cohomology in that degree. -/
public theorem isIso_homologyMap_map {P Q : CochainComplex A ℤ} (φ : P ⟶ Q) (i : ℤ)
    (hφ : IsIso (HomologicalComplex.homologyMap φ i)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i) := by
  have : IsIso (HomologicalComplex.homologyMap φ i) := hφ
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso F)
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map φ)).mpr
    (inferInstanceAs (IsIso (F.map (HomologicalComplex.homologyMap φ i))))

end Transfer

section StrictlyPerfect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
variable {U V : C} (g : V ⟶ U)
variable [HasSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify (J.over V) AddCommGrpCat.{w}]
variable [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction along an arrow of the site carries strictly perfect complexes to strictly
perfect complexes: it preserves zero objects, and being exact it preserves the finite
coproducts which present a finite free module, so a direct summand of a finite free module
restricts to one. -/
theorem isStrictlyPerfect_overMap
    {P : CochainComplex (SheafOfModules.{w} (R.over U)) ℤ}
    (hP : IsStrictlyPerfect (R.over U) P) :
    IsStrictlyPerfect (R.over V)
      (((SheafOfModules.overMap R g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits (R := R) g
  refine ⟨hP.bounded.subset ?_, fun i => ?_⟩
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi (Functor.map_isZero (SheafOfModules.overMap R g) hz)
  · obtain ⟨n, j, r, hjr⟩ :=
      (isDirectSummandOfFiniteFree_iff_free (R.over U) (P.X i)).mp (hP.termDirectSummand i)
    let eFree := SheafOfModules.mapFreeIso (SheafOfModules.overMap R g) (ULift.{w} (Fin n))
      (SheafOfModules.overMapUnitIso (R := R) g).symm
    refine (isDirectSummandOfFiniteFree_iff_free (R.over V) _).mpr
      ⟨n, (SheafOfModules.overMap R g).map j ≫ eFree.inv,
        eFree.hom ≫ (SheafOfModules.overMap R g).map r, ?_⟩
    rw [Category.assoc, ← Category.assoc eFree.inv, eFree.inv_hom_id, Category.id_comp,
      ← Functor.map_comp, hjr, CategoryTheory.Functor.map_id]
    rfl

end StrictlyPerfect

section SliceRestriction

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The restriction of a complex of `O`-modules to a slice, read along an arrow of the
site**: for an arrow `g : W ⟶ V`, the complex `(M|_V)|_W` is `M|_W`, and restriction between
slices is exact, so the class of the restriction of the restriction is the image under
`overMap g` of the class of the restriction. -/
noncomputable def restrictComplexOverMapIso
    (M : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V)
    [HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))]
    [(SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)]
    [PreservesFiniteColimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)] :
    (SheafOfModules.overMap.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (X.restrictComplex M V)) ≅
      DerivedCategory.Q.obj (X.restrictComplex M W) :=
  ((SheafOfModules.overMap.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategoryFactors.app
      (X.restrictComplex M V)) ≪≫
    DerivedCategory.Q.mapIso
      ((Stacks.SheafOfModules.overFunctorMapComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app M)

end SliceRestriction

section Main

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C,
  (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive]
variable [∀ U : X.C,
  PreservesFiniteLimits
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
variable [∀ U : X.C,
  PreservesFiniteColimits
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- One object's worth of Stacks 08FU (2). Given a strictly perfect approximation `α` of the
restriction of `K₀` to `V`, and quasi-isomorphisms `u : K₀ ⟶ Y` and `s : K ⟶ Y`, there is a
covering sieve of `V` over each arrow of which `K` admits a strictly perfect approximation in
the same two degrees. -/
private theorem exists_coveringSieve_strictlyPerfect_approximation (V : X.C)
    {K₀ Y K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : K₀ ⟶ Y) (s : K ⟶ Y) [QuasiIso u] [QuasiIso s] (m : ℤ)
    (P : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (α : P ⟶ (restrictTo X V).obj K₀)
    (hgt : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hm : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ T : Sieve V, T ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ P' : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
          ∃ α' : P' ⟶ X.restrictComplex K W,
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
            Epi (HomologicalComplex.homologyMap α' m) := by
  have hiso (j : ℤ) : IsIso (HomologicalComplex.homologyMap ((restrictTo X V).map u) j) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  -- The approximation of `K₀|_V`, pushed into `Y|_V` along the quasi-isomorphism `u`.
  have hα₁gt : ∀ j : ℤ, m < j →
      IsIso (HomologicalComplex.homologyMap (α ≫ (restrictTo X V).map u) j) := by
    intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := hgt j hj
    have := hiso j
    infer_instance
  have hα₁m : Epi (HomologicalComplex.homologyMap (α ≫ (restrictTo X V).map u) m) := by
    rw [HomologicalComplex.homologyMap_comp]
    have := hiso m
    exact epi_comp' hm (IsIso.epi_of_iso _)
  obtain ⟨T, hT, hlift⟩ := exists_coveringSieve_lift_of_quasiIso X V
    (α ≫ (restrictTo X V).map u) ((restrictTo X V).map s) hP
  refine ⟨T, hT, fun W g hg => ?_⟩
  obtain ⟨β, ⟨hβ⟩⟩ := hlift g hg
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g
  -- Restricting `K` to `V` and then along `g` is restricting it to `W`.
  have hcmp : (restrictCochainAlong X g).obj ((restrictTo X V).obj K) ≅ X.restrictComplex K W :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app K
  have hcmpIso : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap hcmp.hom j) := by
    intro j
    have : IsIso hcmp.hom := hcmp.isIso_hom
    show IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map hcmp.hom)
    infer_instance
  have hs' : ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap
      ((restrictCochainAlong X g).map ((restrictTo X V).map s)) j) := by
    intro j
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  refine ⟨(restrictCochainAlong X g).obj P,
    isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP,
    β ≫ hcmp.hom, ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have hcomm := Homotopy.homologyMap_eq hβ j
    rw [HomologicalComplex.homologyMap_comp] at hcomm
    have h₃ : IsIso (HomologicalComplex.homologyMap
        ((restrictCochainAlong X g).map (α ≫ (restrictTo X V).map u)) j) :=
      isIso_homologyMap_map
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
        (α ≫ (restrictTo X V).map u) j (hα₁gt j hj)
    rw [← hcomm] at h₃
    have := hs' j
    have := h₃
    have hβj : IsIso (HomologicalComplex.homologyMap β j) := by
      rw [show HomologicalComplex.homologyMap β j =
        (HomologicalComplex.homologyMap β j ≫ HomologicalComplex.homologyMap
            ((restrictCochainAlong X g).map ((restrictTo X V).map s)) j) ≫
          inv (HomologicalComplex.homologyMap
            ((restrictCochainAlong X g).map ((restrictTo X V).map s)) j) by simp]
      infer_instance
    have := hβj
    have := hcmpIso j
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have hcomm := Homotopy.homologyMap_eq hβ m
    rw [HomologicalComplex.homologyMap_comp] at hcomm
    have h₃ : Epi (HomologicalComplex.homologyMap
        ((restrictCochainAlong X g).map (α ≫ (restrictTo X V).map u)) m) :=
      epi_homologyMap_map
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
        (α ≫ (restrictTo X V).map u) m hα₁m
    rw [← hcomm] at h₃
    have := hs' m
    have hβm : Epi (HomologicalComplex.homologyMap β m) :=
      (epi_comp_iff_of_isIso (HomologicalComplex.homologyMap β m)
        (HomologicalComplex.homologyMap
          ((restrictCochainAlong X g).map ((restrictTo X V).map s)) m)).mp h₃
    have := hcmpIso m
    exact epi_comp' hβm (IsIso.epi_of_iso _)

/-- **Stacks 08FU, part (2)**, with the site, its morphisms and the sections of the structure
sheaf at independent universes. Let `(C, O)` be a ringed site and let `E` be an object of `D(O)`
which is `m`-pseudo-coherent. Then every complex of `O`-modules representing `E` is
`m`-pseudo-coherent. -/
theorem isPseudoCoherentComplexFrom_of_iso_general
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hE : X.IsPseudoCoherentFrom E m)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) :
    X.IsPseudoCoherentComplexFrom K m := by
  classical
  obtain ⟨K₀, hK₀, ⟨e₀⟩⟩ := hE
  obtain ⟨Y, u, s, hs, hfac⟩ := DerivedCategory.left_fac (e₀.hom ≫ e.inv)
  have := hs
  have hu : IsIso (DerivedCategory.Q.map u) := by
    rw [show DerivedCategory.Q.map u = (e₀.hom ≫ e.inv) ≫ DerivedCategory.Q.map s by
      rw [hfac]; simp]
    infer_instance
  have : QuasiIso u := by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : QuasiIso s := by rwa [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  intro U
  obtain ⟨S₀, hS₀, hdata⟩ := hK₀ U
  have key : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S₀ f →
      ∃ T : Sieve V, T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
          ∃ P' : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
            ∃ α' : P' ⟶ X.restrictComplex K W,
              (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
              Epi (HomologicalComplex.homologyMap α' m) := by
    intro V f hf
    obtain ⟨P, hP, α, hgt, hm⟩ := hdata f hf
    exact exists_coveringSieve_strictlyPerfect_approximation X V u s m P hP α hgt hm
  set T : ∀ ⦃V : X.C⦄ ⦃f : V ⟶ U⦄, S₀ f → Sieve V := fun _ f hf => (key f hf).choose with hT
  have hTmem : ∀ ⦃V : X.C⦄ ⦃f : V ⟶ U⦄ (hf : S₀ f), T hf ∈ X.J V :=
    fun _ f hf => (key f hf).choose_spec.1
  have hbind : Sieve.bind S₀ T ∈ X.J U := by
    refine X.J.transitive hS₀ _ ?_
    rintro Z h ⟨V, g, f, hf, rfl⟩
    refine X.J.superset_covering ?_
      (X.J.pullback_stable g (hTmem (V := V) (f := f) hf))
    rw [Sieve.pullback_comp]
    exact Sieve.pullback_monotone g (Sieve.le_pullback_bind S₀ T f hf)
  refine ⟨(Sieve.bind S₀ T).arrows, ?_, fun W h hh => ?_⟩
  · rw [Sieve.generate_sieve]
    exact hbind
  · obtain ⟨V, g, f, hf, hg, rfl⟩ := hh
    exact (key f hf).choose_spec.2 g hg

section DiagonalUniverses

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C,
  (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive]
variable [∀ U : X.C,
  PreservesFiniteLimits
    (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
variable [∀ U : X.C,
  PreservesFiniteColimits
    (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- **Stacks 08FU, part (2).** Let `(C, O)` be a ringed site and let `E` be an object of `D(O)`
which is `m`-pseudo-coherent. Then every complex of `O`-modules representing `E` is
`m`-pseudo-coherent. -/
@[stacks 08FU "part (2)", sga "6 I 2.2" "a)"]
theorem isPseudoCoherentComplexFrom_of_iso
    [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hE : X.IsPseudoCoherentFrom E m)
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) :
    X.IsPseudoCoherentComplexFrom K m := by
  exact isPseudoCoherentComplexFrom_of_iso_general X E m hE K e

end DiagonalUniverses

end Main

end AlgebraicGeometry.RingedSite

end
