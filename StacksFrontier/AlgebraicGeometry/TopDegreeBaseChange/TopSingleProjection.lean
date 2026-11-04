module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.MapHomologyCycles

/-!
# The canonical projection of a bounded-above complex onto its top cohomology

A cochain complex `K` with no terms above degree `d` has a canonical map to the complex with
`Hᵈ(K)` in degree `d` and zero elsewhere: in degree `d` it is the projection
`K.X d ⟶ Hᵈ(K)`, which exists because the differential out of degree `d` is zero, and it
annihilates the differential into degree `d`. This file constructs that map, computes its
effect on `Hᵈ`, and transports both facts along an additive functor and into the derived
category.

Mathlib has the two ingredients and not the map: `HomologicalComplex.mkHomToSingle` builds a
morphism into a single complex out of one component, and
`CochainComplex.exists_iso_single` produces an isomorphism with a single complex — but only for
a complex concentrated in **one** degree, and only as an **existential**. For a complex that is
merely bounded above, the canonical map onto the top cohomology is not named.

## Main definitions

* `Stacks.TopSingleProjection.topProjection`: the projection `K.X d ⟶ Hᵈ(K)`.
* `Stacks.TopSingleProjection.toSingleTop`: the canonical map `K ⟶ Hᵈ(K)[-d]`.
* `Stacks.TopSingleProjection.mapToSingleTop`: its image under an additive functor `G`,
  landing at `G(Hᵈ K)[-d]` through
  `HomologicalComplex.singleMapHomologicalComplex`.
* `Stacks.TopSingleProjection.QToSingle`: a morphism into a single complex, read in the derived
  category. Nothing has to be transported: `DerivedCategory.singleFunctor C d` **is**
  `CochainComplex.singleFunctor C d ⋙ DerivedCategory.Q`, by
  `DerivedCategory.singleFunctorIsoCompQ`, which is `Iso.refl`.

## Main results

* `Stacks.TopSingleProjection.homologyMap_toSingleTop`: `toSingleTop` induces the **identity**
  on `Hᵈ`, read through `HomologicalComplex.singleObjHomologySelfIso`.
* `Stacks.TopSingleProjection.homologyMap_mapToSingleTop`: for `G` additive and right exact,
  `mapToSingleTop` induces on `Hᵈ` the **inverse** of the canonical comparison
  `Stacks.MapHomologyCycles.mapHomology`. In particular that comparison is an isomorphism at
  the top degree of a complex with no terms above `d`.
* `Stacks.TopSingleProjection.homologyMap_QToSingle`: the master identity in the derived
  category — `Hᵈ` of `Q u`, followed by the canonical identification
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`, is the factorization of `Hᵈ` through
  the derived category followed by `Hᵈ(u)`. Together with the two results above this computes
  the derived-category map induced by `toSingleTop` and by `mapToSingleTop`.
* `Stacks.TopSingleProjection.singleFunctorIsoCompQh_hom_app` and
  `Stacks.TopSingleProjection.singleFunctorCompHomologyFunctorIso_hom_app`: the two
  identifications of the single functor on the derived category, unfolded. Mathlib defines both
  through the `SingleFunctors` bundle and states neither on components, and they are what lets a
  statement written with `DerivedCategory.singleFunctor` meet one written with
  `DerivedCategory.Q` or `DerivedCategory.Qh`.

## Implementation notes

*Every identity here mixes two `rfl`-equal spellings, and that is what dictates the proofs.*
`DerivedCategory.singleFunctor C d` and `CochainComplex.singleFunctor C d ⋙ Q` are definitionally
equal but not interchangeable while a rewrite motive is being formed, so `rw`, `simp only` and
even `Category.assoc` refuse goals that contain both — `Category.assoc` reporting that it *"did
not find an occurrence of the pattern `(?f ≫ ?g) ≫ ?h`"* on a goal which visibly contains one.
Two cures are used throughout and no transparency option is:

* a **declared return type** (`QToSingle`, and the `have`s inside the proofs) fixes the spelling
  of a term before it is composed with anything, which is what makes the composite's implicit
  arguments agree;
* **term mode forms no motive**, so the associativity and unit steps that `rw` refuses go
  through as `Category.assoc`, `Category.comp_id` and `congrArg` applied as terms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category HomologicalComplex

namespace Stacks.TopSingleProjection

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B]

section Complex

/-- **The projection of a bounded-above complex onto its top cohomology.** For `K` with no
terms above degree `d` the differential out of degree `d` vanishes, so `Hᵈ(K)` is the opcycles
in degree `d`, and this is the projection onto them read backwards through that
identification. -/
def topProjection (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    K.X d ⟶ K.homology d :=
  K.pOpcycles d ≫
    (K.isoHomologyι d (d + 1) (by simp)
      ((K.isZero_of_isStrictlyLE d (d + 1) (by lia)).eq_of_tgt _ _)).inv

/-- **`topProjection` is the homology projection on cycles.** This is the only property of it
that is ever used, and it is what makes it canonical. -/
@[reassoc]
theorem iCycles_comp_topProjection (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    K.iCycles d ≫ topProjection K d = K.homologyπ d := by
  rw [topProjection, ← assoc, ← HomologicalComplex.homology_π_ι, assoc,
    HomologicalComplex.isoHomologyι_hom_inv_id, comp_id]

/-- **`topProjection` annihilates the differentials into degree `d`**, which is what makes it a
morphism of complexes into the single complex. -/
@[reassoc]
theorem d_comp_topProjection (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d] (i : ℤ) :
    K.d i d ≫ topProjection K d = 0 := by
  rw [topProjection, ← assoc, HomologicalComplex.d_pOpcycles, zero_comp]

/-- **The canonical map from a complex with no terms above `d` to the single complex on its
degree-`d` cohomology.** -/
def toSingleTop (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    K ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) d).obj (K.homology d) :=
  HomologicalComplex.mkHomToSingle (topProjection K d)
    (fun i _ => d_comp_topProjection K d i)

/-- In degree `d`, `toSingleTop` is `topProjection` followed by the identification of the
degree-`d` term of the single complex with `Hᵈ K`. -/
@[simp]
theorem toSingleTop_f (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    (toSingleTop K d).f d =
      topProjection K d ≫ (singleObjXSelf (ComplexShape.up ℤ) d (K.homology d)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- **`toSingleTop` induces the identity on degree-`d` cohomology.** Both sides are determined
by their composite with the epimorphism `K.homologyπ d`, and there the claim is
`iCycles_comp_topProjection`. -/
theorem homologyMap_toSingleTop (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    HomologicalComplex.homologyMap (toSingleTop K d) d ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) d (K.homology d)).hom =
      𝟙 (K.homology d) := by
  rw [← cancel_epi (K.homologyπ d), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom,
    HomologicalComplex.cyclesMap_i_assoc, toSingleTop_f, assoc,
    Iso.inv_hom_id, comp_id, iCycles_comp_topProjection, comp_id]

end Complex

section Functor

variable (G : A ⥤ B) [G.Additive] (K : CochainComplex A ℤ) (d : ℤ) [K.IsStrictlyLE d]

omit [K.IsStrictlyLE d] in
/-- The cycles of the image complex in the top degree are the whole of degree `d`, because the
differential out of it is the image of a zero differential. -/
theorem isIso_iCycles_mapHomologicalComplex_obj (hd : K.d d (d + 1) = 0) :
    IsIso (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles d) :=
  ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).isIso_iCycles d (d + 1) (by simp)
    (by
      rw [show ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d d (d + 1) =
        G.map (K.d d (d + 1)) from rfl, hd, G.map_zero])

/-- **The cycles comparison is invertible in the top degree of a complex with no terms above
`d`**: both sides are then the whole of degree `d`. -/
theorem isIso_mapCycles_of_isStrictlyLE :
    IsIso (Stacks.MapHomologyCycles.mapCycles G K d) := by
  have hd : K.d d (d + 1) = 0 :=
    (K.isZero_of_isStrictlyLE d (d + 1) (by lia)).eq_of_tgt _ _
  have h1 : IsIso (K.iCycles d) := K.isIso_iCycles d (d + 1) (by simp) hd
  have h2 := isIso_iCycles_mapHomologicalComplex_obj G K d hd
  have h3 : IsIso (G.map (K.iCycles d)) := inferInstance
  exact IsIso.of_isIso_fac_right (Stacks.MapHomologyCycles.mapCycles_i G K d)

/-- **The image of `toSingleTop` under `G`**, landing at the single complex on `G(Hᵈ K)`
through `HomologicalComplex.singleMapHomologicalComplex`. -/
def mapToSingleTop :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      (HomologicalComplex.single B (ComplexShape.up ℤ) d).obj (G.obj (K.homology d)) :=
  (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (toSingleTop K d) ≫
    (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app (K.homology d)

/-- In degree `d`, `mapToSingleTop` is the image of `topProjection` under `G` followed by the
identification of the degree-`d` term of the single complex with `G(Hᵈ K)`. -/
@[simp]
theorem mapToSingleTop_f :
    (mapToSingleTop G K d).f d =
      G.map (topProjection K d) ≫
        (singleObjXSelf (ComplexShape.up ℤ) d (G.obj (K.homology d))).inv := by
  rw [mapToSingleTop, HomologicalComplex.comp_f,
    singleMapHomologicalComplex_hom_app_self,
    show ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map (toSingleTop K d)).f d =
      G.map ((toSingleTop K d).f d) from rfl,
    toSingleTop_f, ← assoc, ← G.map_comp, assoc, Iso.inv_hom_id, comp_id]

/-- **For a right exact functor, `mapToSingleTop` induces on `Hᵈ` the inverse of the canonical
comparison `Stacks.MapHomologyCycles.mapHomology`.**

Both sides are determined by their composite with the cycles comparison followed by the
homology projection, which is an epimorphism because the cycles comparison is invertible here
(`isIso_mapCycles_of_isStrictlyLE`); and there the claim is the defining cycle-class equation of
`mapHomology` together with `iCycles_comp_topProjection`.

In particular `Stacks.MapHomologyCycles.mapHomology G K d` is an **isomorphism** when `K` has no
terms above `d`. -/
theorem homologyMap_mapToSingleTop [PreservesFiniteColimits G] :
    HomologicalComplex.homologyMap (mapToSingleTop G K d) d ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) d (G.obj (K.homology d))).hom ≫
        Stacks.MapHomologyCycles.mapHomology G K d =
      𝟙 (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology d) := by
  have hiso := isIso_mapCycles_of_isStrictlyLE G K d
  have hepi : Epi (Stacks.MapHomologyCycles.mapCycles G K d ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ d) := inferInstance
  rw [← cancel_epi (Stacks.MapHomologyCycles.mapCycles G K d ≫
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ d), comp_id, assoc,
    HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom_assoc, singleObjCyclesSelfIso_hom, assoc,
    HomologicalComplex.cyclesMap_i_assoc, Stacks.MapHomologyCycles.mapCycles_i_assoc,
    mapToSingleTop_f, assoc, Iso.inv_hom_id_assoc, ← assoc, ← G.map_comp,
    iCycles_comp_topProjection, Stacks.MapHomologyCycles.homologyπ_comp_mapHomology]

/-- **`G` applied to a representative-level projection into a single complex.** The image of
`toSingleTop` followed by the single complex on a map `g` is `mapToSingleTop` followed by the
single complex on `G g`; this is the compatibility of
`HomologicalComplex.singleMapHomologicalComplex` with `g`. -/
theorem map_toSingleTop_comp_singleMap {M : A} (g : K.homology d ⟶ M) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (toSingleTop K d ≫ (HomologicalComplex.single A (ComplexShape.up ℤ) d).map g) ≫
        (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app M =
      mapToSingleTop G K d ≫
        (HomologicalComplex.single B (ComplexShape.up ℤ) d).map (G.map g) := by
  have hnat : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single A (ComplexShape.up ℤ) d).map g) ≫
      (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app M =
      (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.app (K.homology d) ≫
        (HomologicalComplex.single B (ComplexShape.up ℤ) d).map (G.map g) :=
    (singleMapHomologicalComplex G (ComplexShape.up ℤ) d).hom.naturality g
  rw [CategoryTheory.Functor.map_comp, assoc, hnat, mapToSingleTop, assoc]

end Functor

section Derived

open DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **Mathlib's `DerivedCategory.singleFunctorIsoCompQh` on components.** It is the
identification of `Q` with `Qh` after the homotopy-category quotient, at the single complex.
Mathlib builds it inside the `SingleFunctors` bundle and states no component formula. -/
theorem singleFunctorIsoCompQh_hom_app (M : C) (d : ℤ) :
    (singleFunctorIsoCompQh C d).hom.app M =
      (quotientCompQhIso C).inv.app ((CochainComplex.singleFunctor C d).obj M) := by
  have h1 : (singleFunctorIsoCompQh C d).hom.app M =
      ((SingleFunctors.postcompIsoOfIso (CochainComplex.singleFunctors C)
          (quotientCompQhIso C).symm).hom.hom d).app M ≫
        ((SingleFunctors.postcompPostcompIso (CochainComplex.singleFunctors C)
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)) Qh).inv.hom d).app M := rfl
  rw [h1, SingleFunctors.postcompIsoOfIso_hom_hom_app,
    SingleFunctors.postcompPostcompIso_inv_hom_app]
  exact (comp_id _).trans rfl

/-- **Mathlib's `DerivedCategory.singleFunctorCompHomologyFunctorIso` on components.** It is the
factorization of `Hᵈ` through the derived category at the single complex, followed by
`HomologicalComplex.singleObjHomologySelfIso`. Mathlib builds it by whiskering and states no
component formula; without one, nothing about `Hᵈ` of a single object of the derived category
can be connected to the complex-level statements. -/
theorem singleFunctorCompHomologyFunctorIso_hom_app (M : C) (d : ℤ) :
    (singleFunctorCompHomologyFunctorIso C d).hom.app M =
      (homologyFunctorFactors C d).hom.app ((CochainComplex.singleFunctor C d).obj M) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d M).hom := by
  have hα : ((SingleFunctors.evaluation C (DerivedCategory C) d).mapIso
      (singleFunctorsPostcompQIso C)).hom.app M = 𝟙 ((singleFunctor C d).obj M) := rfl
  have hA : (homologyFunctor C d).map
        (((SingleFunctors.evaluation C (DerivedCategory C) d).mapIso
          (singleFunctorsPostcompQIso C)).hom.app M) =
      𝟙 ((singleFunctor C d ⋙ homologyFunctor C d).obj M) := by
    rw [hα]; exact (homologyFunctor C d).map_id _
  have h1 : (singleFunctorCompHomologyFunctorIso C d).hom.app M =
      (homologyFunctor C d).map
          (((SingleFunctors.evaluation C (DerivedCategory C) d).mapIso
            (singleFunctorsPostcompQIso C)).hom.app M) ≫
        𝟙 ((((CochainComplex.singleFunctors C).functor d ⋙ Q) ⋙ homologyFunctor C d).obj M) ≫
          ((homologyFunctorFactors C d).hom.app ((CochainComplex.singleFunctor C d).obj M) ≫
            (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d M).hom) := rfl
  rw [h1, hA]
  exact (id_comp _).trans (id_comp _)

/-- **A morphism into a single complex, read in the derived category.** The declared return
type is the point: `DerivedCategory.singleFunctor C d` is definitionally
`CochainComplex.singleFunctor C d ⋙ Q`, and fixing the spelling here is what lets the result be
composed with the statements written in terms of `DerivedCategory.singleFunctor`. -/
def QToSingle {X : CochainComplex C ℤ} {M : C} {d : ℤ}
    (u : X ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M) :
    Q.obj X ⟶ (singleFunctor C d).obj M :=
  Q.map u

/-- **What a morphism into a single complex does on `Hᵈ` in the derived category.** The
identification `DerivedCategory.singleFunctorCompHomologyFunctorIso` turns `Hᵈ(Q u)` into
`Hᵈ(u)`, through the factorization of `Hᵈ` over the derived category.

This is the master identity of the file: its two instances, at `toSingleTop` and at
`mapToSingleTop`, are `homologyMap_QToSingle_toSingleTop` and
`homologyMap_QToSingle_mapToSingleTop`. -/
theorem homologyMap_QToSingle {X : CochainComplex C ℤ} {M : C} {d : ℤ}
    (u : X ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M) :
    (homologyFunctor C d).map (QToSingle u) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app M =
      (homologyFunctorFactors C d).hom.app X ≫
        HomologicalComplex.homologyMap u d ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d M).hom := by
  have hnat : (homologyFunctor C d).map (QToSingle u) ≫
      (homologyFunctorFactors C d).hom.app
        ((CochainComplex.singleFunctor C d).obj M) =
      (homologyFunctorFactors C d).hom.app X ≫ HomologicalComplex.homologyMap u d :=
    homologyFunctorFactors_hom_naturality u d
  rw [singleFunctorCompHomologyFunctorIso_hom_app]
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d M).hom) hnat).trans
      (assoc _ _ _))

/-- **`homologyMap_QToSingle` with the target single complex changed along a map.** A morphism
into the single complex on `M` followed by the single complex on a map `M ⟶ M'` is how a
representative-level projection reaches the single complex on the cohomology of the object it
represents. -/
theorem homologyMap_QToSingle_comp {X : CochainComplex C ℤ} {M M' : C} {d : ℤ}
    (u : X ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) d).obj M) (g : M ⟶ M') :
    (homologyFunctor C d).map
          (QToSingle (u ≫ (HomologicalComplex.single C (ComplexShape.up ℤ) d).map g)) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app M' =
      (homologyFunctorFactors C d).hom.app X ≫
        HomologicalComplex.homologyMap u d ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) d M).hom ≫ g := by
  rw [homologyMap_QToSingle, HomologicalComplex.homologyMap_comp]
  exact congrArg (fun t => (homologyFunctorFactors C d).hom.app X ≫ t)
    ((assoc _ _ _).trans (congrArg (fun t => HomologicalComplex.homologyMap u d ≫ t)
      (singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) d g)))

/-- **The derived-category map induced by `toSingleTop` computes the identification of `Hᵈ(K)`
with `Hᵈ` of the class of `K`.** -/
theorem homologyMap_QToSingle_toSingleTop (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] :
    (homologyFunctor C d).map (QToSingle (toSingleTop K d)) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app (K.homology d) =
      (homologyFunctorFactors C d).hom.app K := by
  rw [homologyMap_QToSingle]
  exact (congrArg (fun t => (homologyFunctorFactors C d).hom.app K ≫ t)
    (homologyMap_toSingleTop K d)).trans (comp_id _)

end Derived

section DerivedFunctor

open DerivedCategory

variable {C : Type*} [Category C] [Abelian C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]

/-- **The derived-category map induced by `mapToSingleTop` is inverse to the canonical
comparison `mapHomology`.** This is the form in which the cycle-class identity of a top-degree
base-change comparison is discharged: it says that the canonical projection of a bounded-above
complex onto its top cohomology, pushed through a right exact functor and read in the derived
category, *is* the comparison `G(Hᵈ K) ⟶ Hᵈ(G K)` inverted. -/
theorem homologyMap_QToSingle_mapToSingleTop (G : C ⥤ D) [G.Additive]
    [PreservesFiniteColimits G] (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d] :
    (homologyFunctor D d).map (QToSingle (mapToSingleTop G K d)) ≫
        (singleFunctorCompHomologyFunctorIso D d).hom.app (G.obj (K.homology d)) ≫
        Stacks.MapHomologyCycles.mapHomology G K d =
      (homologyFunctorFactors D d).hom.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have h := homologyMap_QToSingle (mapToSingleTop G K d)
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ Stacks.MapHomologyCycles.mapHomology G K d) h).trans
      ((assoc _ _ _).trans ((congrArg (fun t =>
          (homologyFunctorFactors D d).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ t)
        ((assoc _ _ _).trans (homologyMap_mapToSingleTop G K d))).trans (comp_id _))))

end DerivedFunctor

end Stacks.TopSingleProjection

end
