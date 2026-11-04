module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The comparison of a complex with the single complex on its top cohomology

Let `K` be a complex in an abelian category and let `r` be a degree out of which the differential
vanishes — for a complex concentrated in the degrees `≤ r`, the top degree. Then the cocycles in
degree `r` are all of `K.X r`, so there is a canonical map `K.X r ⟶ K.homology r`, and it kills the
image of the differential into degree `r`. By `HomologicalComplex.mkHomToSingle` it therefore
assembles into a map of complexes

  `K ⟶ (single _ _ r).obj (K.homology r)`,

`HomologicalComplex.toSingleTopCohomology`, and this map is an isomorphism on cohomology in degree
`r`, `HomologicalComplex.isIso_homologyMap_toSingleTopCohomology`.

## Main definitions

* `HomologicalComplex.toSingleTopCohomology`: the comparison map.

## Main results

* `HomologicalComplex.isIso_homologyMap_toSingleTopCohomology`: the comparison is an isomorphism on
  cohomology in the top degree.
* `HomologicalComplex.topToHomology_naturality` and
  `HomologicalComplex.toSingleTopCohomology_naturality`: the comparison is natural in the
  complex.
* `HomologicalComplex.homologyMap_toSingleTopCohomology`: the induced map on cohomology is the
  inverse of `HomologicalComplex.singleObjHomologySelfIso`.
* `HomologicalComplex.isColimitCokernelCoforkTopToHomology`: in such a degree the cohomology object
  is a cokernel of the incoming differential, with the comparison map as its projection.
* `HomologicalComplex.singleObjHomologySelfIso_inv`: the description through the cocycles of the
  inverse of the identification of the cohomology of a single complex with its value.

## References

* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [Abelian V] {ι : Type*} [DecidableEq ι]
  {c : ComplexShape ι}

/-- The inverse of the isomorphism `homology_j ≅ A` of a single complex, through the cocycles. -/
theorem singleObjHomologySelfIso_inv (A : V) (r : ι) :
    (singleObjHomologySelfIso c r A).inv =
      (singleObjCyclesSelfIso c r A).inv ≫ ((single V c r).obj A).homologyπ r := by
  simp only [singleObjHomologySelfIso, Iso.trans_inv, Iso.symm_inv]
  congr 1

section Top

variable (K : HomologicalComplex V c) {r j : ι} (hrj : c.next r = j) (hz : K.d r j = 0)

/-- With the differential out of degree `r` zero, the identity of `K.X r` factors through the
cocycles, so there is a canonical map `K.X r ⟶ K.homology r`. -/
def topToHomology : K.X r ⟶ K.homology r :=
  K.liftCycles (𝟙 (K.X r)) j hrj (by rw [hz, comp_zero]) ≫ K.homologyπ r

/-- The canonical map from the cocycles in degree `r` to `K.X r`, followed by the lift of the
identity of `K.X r` to the cocycles, is the identity. -/
theorem iCycles_comp_liftCycles_id :
    K.iCycles r ≫ K.liftCycles (𝟙 (K.X r)) j hrj (by rw [hz, comp_zero]) = 𝟙 (K.cycles r) := by
  rw [← cancel_mono (K.iCycles r), Category.assoc, K.liftCycles_i, Category.comp_id,
    Category.id_comp]

/-- The canonical map `K.X r ⟶ K.homology r` kills the differential into degree `r`. -/
theorem d_comp_topToHomology (i : ι) : K.d i r ≫ topToHomology K hrj hz = 0 := by
  rw [topToHomology, ← Category.assoc,
    show K.d i r ≫ K.liftCycles (𝟙 (K.X r)) j hrj (by rw [hz, comp_zero]) = K.toCycles i r from by
      rw [← cancel_mono (K.iCycles r), Category.assoc, K.liftCycles_i, Category.comp_id,
        K.toCycles_i]]
  exact K.toCycles_comp_homologyπ i r

/-- **The comparison of a complex with the single complex on its cohomology in a degree out of
which the differential vanishes.** -/
def toSingleTopCohomology : K ⟶ (single V c r).obj (K.homology r) :=
  mkHomToSingle (topToHomology K hrj hz) (fun i _ => d_comp_topToHomology K hrj hz i)

/-- In degree `r`, the comparison map is the canonical map `K.X r ⟶ K.homology r` followed by the
identification of the degree-`r` term of the single complex with `K.homology r`. -/
@[simp]
theorem toSingleTopCohomology_f :
    (toSingleTopCohomology K hrj hz).f r =
      topToHomology K hrj hz ≫ (singleObjXSelf c r (K.homology r)).inv :=
  mkHomToSingle_f _ _

/-- **The canonical map to the top cohomology is natural**: a map of complexes commutes with it and
with the induced map on cohomology. -/
theorem topToHomology_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {r j : ι}
    (hrj : c.next r = j) (hzK : K.d r j = 0) (hzL : L.d r j = 0) :
    φ.f r ≫ topToHomology L hrj hzL = topToHomology K hrj hzK ≫ homologyMap φ r := by
  rw [topToHomology, topToHomology, Category.assoc, homologyπ_naturality, ← Category.assoc,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles r), Category.assoc, liftCycles_i, Category.comp_id,
    Category.assoc, cyclesMap_i, ← Category.assoc, liftCycles_i, Category.id_comp]

/-- **The comparison is natural in the complex**: a map of complexes `φ : K ⟶ L` commutes with the
comparisons and with the map induced by `φ` on cohomology in degree `r`. -/
theorem toSingleTopCohomology_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {r j : ι}
    (hrj : c.next r = j) (hzK : K.d r j = 0) (hzL : L.d r j = 0) :
    φ ≫ toSingleTopCohomology L hrj hzL =
      toSingleTopCohomology K hrj hzK ≫ (single V c r).map (homologyMap φ r) := by
  refine to_single_hom_ext ?_
  rw [comp_f, comp_f, toSingleTopCohomology_f, toSingleTopCohomology_f, single_map_f_self]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  exact topToHomology_naturality φ hrj hzK hzL

/-- **The comparison induces on cohomology in degree `r` the inverse of Mathlib's
identification of the cohomology of a single complex with its value.** -/
theorem homologyMap_toSingleTopCohomology :
    homologyMap (toSingleTopCohomology K hrj hz) r =
      (singleObjHomologySelfIso c r (K.homology r)).inv := by
  rw [← cancel_epi (K.homologyπ r), homologyπ_naturality,
    singleObjHomologySelfIso_inv, ← Category.assoc]
  congr 1
  rw [← cancel_mono (((single V c r).obj (K.homology r)).iCycles r), cyclesMap_i,
    toSingleTopCohomology, mkHomToSingle_f, topToHomology]
  simp only [Category.assoc]
  rw [show (singleObjCyclesSelfIso c r (K.homology r)).inv ≫
        ((single V c r).obj (K.homology r)).iCycles r =
      (singleObjXSelf c r (K.homology r)).inv from by
        rw [← cancel_epi (singleObjCyclesSelfIso c r (K.homology r)).hom,
          Iso.hom_inv_id_assoc, singleObjCyclesSelfIso_hom, Category.assoc, Iso.hom_inv_id,
          Category.comp_id],
    ← Category.assoc, iCycles_comp_liftCycles_id K hrj hz, Category.id_comp]

/-- **The comparison is an isomorphism on cohomology in degree `r`.** -/
instance isIso_homologyMap_toSingleTopCohomology :
    IsIso (homologyMap (toSingleTopCohomology K hrj hz) r) := by
  rw [homologyMap_toSingleTopCohomology]
  infer_instance

/-- **The canonical map to the top cohomology is the projection to the opcycles**, read through
Mathlib's identification of the cohomology with the opcycles in a degree out of which the
differential vanishes. -/
theorem topToHomology_comp_isoHomologyι :
    topToHomology K hrj hz ≫ (K.isoHomologyι r j hrj hz).hom = K.pOpcycles r := by
  rw [topToHomology, Category.assoc, isoHomologyι_hom, homology_π_ι, ← Category.assoc,
    liftCycles_i, Category.id_comp]

/-- The canonical map `K.X r ⟶ K.homology r` is the projection to the opcycles followed by the
identification of the opcycles with the cohomology. -/
theorem topToHomology_eq_pOpcycles_comp :
    topToHomology K hrj hz = K.pOpcycles r ≫ (K.isoHomologyι r j hrj hz).inv :=
  (Iso.eq_comp_inv _).2 (topToHomology_comp_isoHomologyι K hrj hz)

/-- **In a degree out of which the differential vanishes, the cohomology object is a cokernel of
the differential into that degree**, with `HomologicalComplex.topToHomology` as the projection: a
map out of the degree-`r` term killing the incoming differential factors uniquely through
`topToHomology`. -/
def isColimitCokernelCoforkTopToHomology (i : ι) (hir : c.prev r = i) :
    IsColimit (CokernelCofork.ofπ (topToHomology K hrj hz)
      (d_comp_topToHomology K hrj hz i)) :=
  IsColimit.ofIsoColimit (K.opcyclesIsCokernel (i := i) (j := r) hir)
    (Cofork.ext (K.isoHomologyι r j hrj hz).symm
      (topToHomology_eq_pOpcycles_comp K hrj hz).symm)

/-- The canonical map `K.X r ⟶ K.homology r` is an epimorphism. -/
instance epi_topToHomology : Epi (topToHomology K hrj hz) := by
  rw [topToHomology_eq_pOpcycles_comp]
  infer_instance

/-- Two maps out of the top cohomology agreeing on the degree-`r` term are equal. -/
theorem hom_ext_topToHomology {A : V} {u v : K.homology r ⟶ A}
    (h : topToHomology K hrj hz ≫ u = topToHomology K hrj hz ≫ v) : u = v :=
  (cancel_epi (topToHomology K hrj hz)).1 h

/-- **A map out of the degree-`r` term killing the incoming differential, read as a map out of the
top cohomology.** -/
def descTopHomology (i : ι) (hir : c.prev r = i) {A : V} (θ : K.X r ⟶ A)
    (hθ : K.d i r ≫ θ = 0) : K.homology r ⟶ A :=
  (isColimitCokernelCoforkTopToHomology K hrj hz i hir).desc (CokernelCofork.ofπ θ hθ)

/-- The map `descTopHomology K hrj hz i hir θ hθ` composed after the canonical map
`K.X r ⟶ K.homology r` is `θ`. -/
@[reassoc]
theorem topToHomology_comp_descTopHomology (i : ι) (hir : c.prev r = i) {A : V} (θ : K.X r ⟶ A)
    (hθ : K.d i r ≫ θ = 0) :
    topToHomology K hrj hz ≫ descTopHomology K hrj hz i hir θ hθ = θ :=
  (isColimitCokernelCoforkTopToHomology K hrj hz i hir).fac (CokernelCofork.ofπ θ hθ)
    WalkingParallelPair.one

/-! ### Comparing a complex with the single complex on an arbitrary presentation of its top
cohomology -/

section Desc

variable {A : V} (g : K.homology r ⟶ A)

/-- The canonical map `K.X r ⟶ K.homology r` followed by any map `g` kills the differential into
degree `r`. -/
theorem d_comp_topToHomology_comp (i : ι) : K.d i r ≫ topToHomology K hrj hz ≫ g = 0 := by
  rw [← Category.assoc, d_comp_topToHomology, zero_comp]

/-- **The comparison of a complex with the single complex on any object receiving its top
cohomology** factors through the comparison with the single complex on the cohomology itself. -/
theorem mkHomToSingle_topToHomology_comp :
    mkHomToSingle (topToHomology K hrj hz ≫ g)
        (fun i _ => d_comp_topToHomology_comp K hrj hz g i) =
      toSingleTopCohomology K hrj hz ≫ (single V c r).map g := by
  refine to_single_hom_ext ?_
  rw [mkHomToSingle_f, comp_f, toSingleTopCohomology_f, single_map_f_self]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

/-- **The comparison with the single complex on an object isomorphic to the top cohomology is an
isomorphism on cohomology in degree `r`.** -/
theorem isIso_homologyMap_mkHomToSingle [IsIso g] :
    IsIso (homologyMap (mkHomToSingle (topToHomology K hrj hz ≫ g)
      (fun i _ => d_comp_topToHomology_comp K hrj hz g i)) r) := by
  rw [mkHomToSingle_topToHomology_comp, homologyMap_comp]
  have : IsIso ((single V c r).map g) := ((single V c r).mapIso (asIso g)).isIso_hom
  infer_instance

end Desc

end Top

end HomologicalComplex

end
