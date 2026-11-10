module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso
public import StacksFrontier.Algebra.Homology.MappingConeTriangleDegreewiseIso

/-!
# Splicing a complex in degrees `< m` onto a complex in degrees `≥ m`

Let `𝒜` be an abelian category, let `m` be an integer, let `ℰ` be a complex with `ℰ^i = 0` for
`i < m` and let `ℒ` be a complex with `ℒ^i = 0` for `i ≥ m`. A morphism `ℒ ⟶ ℰ⟦1⟧` of complexes
is then concentrated in the single degree `m - 1`, where it is a map `ℒ^{m-1} ⟶ ℰ^m`, and the
complex

`… ⟶ ℒ^{m-2} ⟶ ℒ^{m-1} ⟶ ℰ^m ⟶ ℰ^{m+1} ⟶ …`

obtained by using that map as the differential out of degree `m - 1` sits in a distinguished
triangle `ℰ ⟶ 𝓜 ⟶ ℒ ⟶ ℰ⟦1⟧` of `D(𝒜)`. This file constructs that complex and proves that
*every* morphism `Q(ℒ) ⟶ Q(ℰ)⟦1⟧` of the derived category is realized by it.

This is the step of the proof of [Stacks, Tag 0FPV] which replaces the representative of an
`m`-pseudo-coherent object by one whose terms in degrees `≥ m` are those of a strictly perfect
approximation: there `ℰ` is the approximating strictly perfect complex, `ℒ` represents the third
vertex of the cocone triangle of the approximation, and `𝓜` is the new representative. The
source attributes the single-degree description of the morphism `ℒ ⟶ ℰ⟦1⟧` to
[Stacks, Tag 06XS], which is
`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE`, and that is how it is proved
here.

## Main results

* `CochainComplex.homOfDegreeComponent`: the morphism `F ⟶ E` of complexes determined by a map
  `F^m ⟶ E^m` annihilated by the differentials on both sides, when `F` is concentrated in
  degrees `≤ m` and `E` in degrees `≥ m`; `CochainComplex.homOfHomologyMap` is the instance of
  it realizing a prescribed map `H^m(F) ⟶ H^m(E)`, and
  `CochainComplex.homologyMap_homOfHomologyMap` says that it does.
* `CochainComplex.exists_hom_Q_map_eq`: **every** morphism `Q(F) ⟶ Q(E)` of `D(𝒜)` between such
  a pair is the image of a morphism of complexes. This is the complex-level form of
  [Stacks, Tag 06XS].
* `CochainComplex.exists_splice_triangle`: **the splice complex.** For every
  `g : Q(ℒ) ⟶ Q(ℰ)⟦1⟧` there are a complex `𝓜`, a morphism `ι : ℰ ⟶ 𝓜` of complexes which is an
  isomorphism in every degree `≥ m`, and a morphism `π : 𝓜 ⟶ ℒ` of complexes which is an
  isomorphism in every degree `< m`, such that `Q(ℰ) ⟶ Q(𝓜) ⟶ Q(ℒ) ⟶ Q(ℰ)⟦1⟧`, with the
  given `g` as its third morphism, is a distinguished triangle.

## Implementation notes

**The splice is the mapping cone, and nothing else.** With `ℱ := ℒ⟦-1⟧` the complex displayed
above is `CochainComplex.mappingCone ψ` for the morphism `ψ : ℱ ⟶ ℰ` with component the given
`ℒ^{m-1} ⟶ ℰ^m`: the mapping cone has `ℱ^{i+1} ⊞ ℰ^i = ℒ^i ⊞ ℰ^i` in degree `i`, which is
`ℒ^i` for `i < m` and `ℰ^i` for `i ≥ m` because the other summand vanishes there. No complex is
defined by cases on the degree and no `eqToHom` appears; the identifications in the two ranges
of degrees are `CochainComplex.mappingCone.inr` and `CochainComplex.mappingCone.inl`, and that
they are isomorphisms in the relevant degrees is
`CochainComplex.mappingCone.isIso_inr_f` and `CochainComplex.mappingCone.isIso_inl_v` of
`StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso`; that the connecting morphism of the
cone triangle is an isomorphism in those degrees, which is what makes `π` one, is
`CochainComplex.mappingCone.isIso_triangle_mor₃_f` of
`StacksFrontier.Algebra.Homology.MappingConeTriangleDegreewiseIso`. The distinguished
triangle is Mathlib's `DerivedCategory.mappingCone_triangle_distinguished`, rotated once.

**Why the realization statement needs no sign bookkeeping.** The third morphism of the rotated
cone triangle is `e ≫ -(Q(ψ)⟦1⟧)` for a fixed isomorphism `e`, so the assignment
`Q(ψ) ↦ (third morphism)` is a bijection; a given `g` is hit by applying fullness of the shift
functor to `-(e⁻¹ ≫ g)`, which is where the sign is absorbed. Nothing about the comparison
isomorphisms of `DerivedCategory.Q` with the shift beyond their naturality is used.

**Morphisms of complexes versus morphisms of `D(𝒜)`.** A morphism `F ⟶ E` of complexes with `F`
concentrated in degrees `≤ m` and `E` in degrees `≥ m` has a single possibly nonzero component,
and `CochainComplex.homOfDegreeComponent` builds it by factoring through the complex
`ℰ^m`-of-cycles placed in degree `m`, using `HomologicalComplex.mkHomToSingle` and
`HomologicalComplex.mkHomFromSingle`. Its effect on cohomology in degree `m` is computed in
`CochainComplex.homologyMap_homOfHomologyMap`; combined with the bijectivity of
[Stacks, Tag 06XS] on the derived side, that is the whole of
`CochainComplex.exists_hom_Q_map_eq`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Lemma 13.27.3 (Tag 06XS)](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

namespace CochainComplex

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-! ### Morphisms of complexes concentrated on either side of a degree -/

section Component

variable {F E : CochainComplex A ℤ} {m : ℤ}

/-- The differential of `F` out of degree `m` vanishes when `F` is concentrated in degrees
`≤ m`. -/
lemma d_eq_zero_of_isStrictlyLE [F.IsStrictlyLE m] : F.d m (m + 1) = 0 :=
  (F.isZero_of_isStrictlyLE m (m + 1) (by lia)).eq_of_tgt _ _

/-- The differential of `E` into degree `m` vanishes when `E` is concentrated in degrees
`≥ m`. -/
lemma d_eq_zero_of_isStrictlyGE [E.IsStrictlyGE m] : E.d (m - 1) m = 0 :=
  (E.isZero_of_isStrictlyGE m (m - 1) (by lia)).eq_of_src _ _

/-- **The morphism of complexes with a prescribed degree-`m` component.** If `F` is concentrated
in degrees `≤ m` and `E` in degrees `≥ m`, a map `φ : F^m ⟶ E^m` killed by the differential of
`F` into degree `m` and by the differential of `E` out of degree `m` is the degree-`m`
component of a morphism `F ⟶ E`, all of whose other components are zero. -/
def homOfDegreeComponent (φ : F.X m ⟶ E.X m)
    (h₁ : F.d (m - 1) m ≫ φ = 0) (h₂ : φ ≫ E.d m (m + 1) = 0) : F ⟶ E :=
  HomologicalComplex.mkHomToSingle (K := F) (j := m) (A := E.cycles m)
      (E.liftCycles φ (m + 1) (by simp) h₂)
      (fun i hi => by
        obtain rfl : i = m - 1 := by
          simp only [ComplexShape.up_Rel] at hi; lia
        rw [← cancel_mono (E.iCycles m), zero_comp, assoc,
          HomologicalComplex.liftCycles_i, h₁]) ≫
    HomologicalComplex.mkHomFromSingle (K := E) (j := m) (A := E.cycles m)
      (E.iCycles m) (fun i hi => by
        obtain rfl : i = m + 1 := by
          simp only [ComplexShape.up_Rel] at hi; lia
        exact E.iCycles_d m (m + 1))

/-- The degree-`m` component of `CochainComplex.homOfDegreeComponent φ h₁ h₂` is `φ`. -/
@[simp]
lemma homOfDegreeComponent_f_self (φ : F.X m ⟶ E.X m)
    (h₁ : F.d (m - 1) m ≫ φ = 0) (h₂ : φ ≫ E.d m (m + 1) = 0) :
    (homOfDegreeComponent φ h₁ h₂).f m = φ := by
  rw [homOfDegreeComponent, HomologicalComplex.comp_f,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomFromSingle_f, assoc,
    Iso.inv_hom_id_assoc, HomologicalComplex.liftCycles_i]

variable [F.IsStrictlyLE m] [E.IsStrictlyGE m]

/-- The degree-`m` component attached to a map `H^m(F) ⟶ H^m(E)`: read `F^m` as the cycles of
`F` in degree `m`, project to `H^m(F)`, apply the map, and read `H^m(E)` back as the cycles of
`E` in degree `m`. Both identifications are isomorphisms because `F` has no term in degree
`m + 1` and `E` has none in degree `m - 1`. -/
def componentOfHomologyMap (h : F.homology m ⟶ E.homology m) : F.X m ⟶ E.X m :=
  (F.iCyclesIso m (m + 1) (by simp) d_eq_zero_of_isStrictlyLE).inv ≫ F.homologyπ m ≫ h ≫
    (E.isoHomologyπ (m - 1) m (by simp) d_eq_zero_of_isStrictlyGE).inv ≫ E.iCycles m

/-- The differential of `F` into degree `m` composed with `componentOfHomologyMap h` is zero. -/
lemma d_comp_componentOfHomologyMap (h : F.homology m ⟶ E.homology m) :
    F.d (m - 1) m ≫ componentOfHomologyMap h = 0 := by
  have key : F.d (m - 1) m ≫
      (F.iCyclesIso m (m + 1) (by simp) d_eq_zero_of_isStrictlyLE).inv =
      F.toCycles (m - 1) m := by
    rw [← cancel_mono (F.iCycles m), assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      comp_id, HomologicalComplex.toCycles_i]
  rw [componentOfHomologyMap, ← assoc, key, ← assoc, F.toCycles_comp_homologyπ,
    zero_comp]

/-- `componentOfHomologyMap h` composed with the differential of `E` out of degree `m` is zero. -/
lemma componentOfHomologyMap_comp_d (h : F.homology m ⟶ E.homology m) :
    componentOfHomologyMap h ≫ E.d m (m + 1) = 0 := by
  rw [componentOfHomologyMap]
  simp

/-- **The morphism of complexes realizing a prescribed map on degree-`m` cohomology.** -/
def homOfHomologyMap (h : F.homology m ⟶ E.homology m) : F ⟶ E :=
  homOfDegreeComponent (componentOfHomologyMap h) (d_comp_componentOfHomologyMap h)
    (componentOfHomologyMap_comp_d h)

/-- **The degree-`m` cohomology of `CochainComplex.homOfHomologyMap h` is `h`.** -/
lemma homologyMap_homOfHomologyMap (h : F.homology m ⟶ E.homology m) :
    HomologicalComplex.homologyMap (homOfHomologyMap h) m = h := by
  have hπE : IsIso (E.homologyπ m) :=
    E.isIso_homologyπ (m - 1) m (by simp) d_eq_zero_of_isStrictlyGE
  have hcm : HomologicalComplex.cyclesMap (homOfHomologyMap h) m =
      F.homologyπ m ≫ h ≫
        (E.isoHomologyπ (m - 1) m (by simp) d_eq_zero_of_isStrictlyGE).inv := by
    rw [← cancel_mono (E.iCycles m), HomologicalComplex.cyclesMap_i, homOfHomologyMap,
      homOfDegreeComponent_f_self, componentOfHomologyMap, ← assoc,
      HomologicalComplex.iCyclesIso_hom_inv_id, id_comp, assoc, assoc]
  apply (cancel_epi (F.homologyπ m)).mp
  rw [HomologicalComplex.homologyπ_naturality, hcm, assoc, assoc,
    HomologicalComplex.isoHomologyπ_inv_hom_id, comp_id]

end Component

/-! ### Realizing a morphism of the derived category by a morphism of complexes -/

section Realize

variable [HasDerivedCategory.{w} A]

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor
  HomologicalComplex.homology

/-- **[Stacks, Tag 06XS] at the level of complexes.** Let `F` be a complex concentrated in
degrees `≤ m` and `E` a complex concentrated in degrees `≥ m`. Then every morphism
`Q(F) ⟶ Q(E)` of the derived category is the image of a morphism of complexes `F ⟶ E`.

Both `Hom_{D(𝒜)}(Q(F), Q(E))` and `Hom_𝒜(H^m(F), H^m(E))` are computed by taking `H^m`, the
latter because a morphism of complexes between such a pair is its single degree-`m`
component. -/
theorem exists_hom_Q_map_eq (F E : CochainComplex A ℤ) (m : ℤ)
    [F.IsStrictlyLE m] [E.IsStrictlyGE m]
    (γ : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj E) :
    ∃ ψ : F ⟶ E, DerivedCategory.Q.map ψ = γ := by
  refine ⟨homOfHomologyMap ((DerivedCategory.homologyFunctorFactors A m).inv.app F ≫
    (DerivedCategory.homologyFunctor A m).map γ ≫
    (DerivedCategory.homologyFunctorFactors A m).hom.app E), ?_⟩
  refine (DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj E) m).1 ?_
  change (DerivedCategory.homologyFunctor A m).map (DerivedCategory.Q.map
      (homOfHomologyMap _)) = (DerivedCategory.homologyFunctor A m).map γ
  apply (cancel_mono ((DerivedCategory.homologyFunctorFactors A m).hom.app E)).mp
  rw [DerivedCategory.homologyFunctorFactors_hom_naturality,
    homologyMap_homOfHomologyMap]
  simp

end Realize

/-! ### The splice complex -/

section Splice

variable [HasDerivedCategory.{w} A]

/-- **The splice complex of [Stacks, Tag 0FPV].** Let `m` be an integer, let `E` be a complex
concentrated in degrees `≥ m` and let `L` be a complex concentrated in degrees `≤ m - 1`. Then
every morphism `g : Q(L) ⟶ Q(E)⟦1⟧` of the derived category is the connecting morphism of a
distinguished triangle `Q(E) ⟶ Q(M) ⟶ Q(L) ⟶ Q(E)⟦1⟧` in which `M` is a complex carrying
morphisms of complexes `ι : E ⟶ M` and `π : M ⟶ L` which are isomorphisms in every degree
`≥ m`, resp. in every degree `< m`. So `M` is the complex

`… ⟶ L^{m-2} ⟶ L^{m-1} ⟶ E^m ⟶ E^{m+1} ⟶ …`

of the source, with the differential out of degree `m - 1` the degree-`m-1` component of `g`. -/
theorem exists_splice_triangle (E L : CochainComplex A ℤ) (m : ℤ)
    [E.IsStrictlyGE m] [L.IsStrictlyLE (m - 1)]
    (g : DerivedCategory.Q.obj L ⟶ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧) :
    ∃ (M : CochainComplex A ℤ) (ι : E ⟶ M) (π : M ⟶ L),
      (∀ i : ℤ, m ≤ i → IsIso (ι.f i)) ∧ (∀ i : ℤ, i < m → IsIso (π.f i)) ∧
      Triangle.mk (DerivedCategory.Q.map ι) (DerivedCategory.Q.map π) g ∈
        distTriang (DerivedCategory A) := by
  -- the shifted source, concentrated in degrees `≤ m`
  have hFLE : (L⟦(-1 : ℤ)⟧).IsStrictlyLE m := L.isStrictlyLE_shift (m - 1) (-1) m (by lia)
  -- the chain-level identification `(L⟦-1⟧)⟦1⟧ ≅ L`
  have eC : ((L⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) ≅ L :=
    (shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) (1 : ℤ) (by lia)).app L
  -- the derived identification `Q(L) ≅ Q(L⟦-1⟧)⟦1⟧`
  obtain ⟨e, he⟩ :
      ∃ e : DerivedCategory.Q.obj L ≅ (DerivedCategory.Q.obj (L⟦(-1 : ℤ)⟧))⟦(1 : ℤ)⟧,
        e.hom = DerivedCategory.Q.map eC.inv ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (L⟦(-1 : ℤ)⟧) :=
    ⟨(DerivedCategory.Q.mapIso eC).symm ≪≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).app (L⟦(-1 : ℤ)⟧), rfl⟩
  obtain ⟨γ, hγ⟩ :=
    (CategoryTheory.shiftFunctor (DerivedCategory A) (1 : ℤ)).map_surjective (-(e.inv ≫ g))
  obtain ⟨ψ, hψ⟩ := exists_hom_Q_map_eq (L⟦(-1 : ℤ)⟧) E m γ
  -- the connecting morphism of the cone triangle, with its codomain spelled out
  obtain ⟨p₃, hp₃⟩ : ∃ p₃ : mappingCone ψ ⟶ (L⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧,
      p₃ = (mappingCone.triangle ψ).mor₃ := ⟨_, rfl⟩
  -- the image of the cone triangle, rotated once
  have hdist : (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle ψ)).rotate ∈
      distTriang (DerivedCategory A) :=
    rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished ψ)
  refine ⟨mappingCone ψ, mappingCone.inr ψ, p₃ ≫ eC.hom, ?_, ?_, ?_⟩
  · intro i hi
    refine mappingCone.isIso_inr_f ψ i ?_
    exact (L.isZero_of_isStrictlyLE (m - 1) i (by lia)).of_iso
      (L.shiftFunctorObjXIso (-1) (i + 1) i (by lia))
  · intro i hi
    have h₂ : IsIso (p₃.f i) := by
      rw [hp₃]
      exact mappingCone.isIso_triangle_mor₃_f ψ i (E.isZero_of_isStrictlyGE m i (by lia))
    have h₃ : IsIso (eC.hom.f i) := by
      have hev : IsIso ((HomologicalComplex.eval A (ComplexShape.up ℤ) i).map eC.hom) :=
        inferInstance
      exact hev
    exact IsIso.comp_isIso' h₂ h₃
  · refine isomorphic_distinguished _ hdist _ ?_
    refine Triangle.isoMk _ _ (Iso.refl (DerivedCategory.Q.obj E))
      (Iso.refl (DerivedCategory.Q.obj (mappingCone ψ))) e ?_ ?_ ?_
    · exact (comp_id (DerivedCategory.Q.map (mappingCone.inr ψ))).trans (id_comp _).symm
    · have hcancel : DerivedCategory.Q.map eC.hom ≫ DerivedCategory.Q.map eC.inv =
          𝟙 (DerivedCategory.Q.obj ((L⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧)) := by
        rw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id, DerivedCategory.Q.map_id]
      have key : DerivedCategory.Q.map (p₃ ≫ eC.hom) ≫ e.hom =
          DerivedCategory.Q.map (mappingCone.triangle ψ).mor₃ ≫
            (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (L⟦(-1 : ℤ)⟧) := by
        rw [DerivedCategory.Q.map_comp, he]
        simp only [assoc]
        rw [← assoc (DerivedCategory.Q.map eC.hom), hcancel, id_comp, hp₃]
        rfl
      exact key.trans (id_comp _).symm
    · have key : e.hom ≫ (-((DerivedCategory.Q.map ψ)⟦(1 : ℤ)⟧')) = g := by
        rw [hψ, hγ, neg_neg, Iso.hom_inv_id_assoc]
      have key₂ : g ≫ ((𝟙 (DerivedCategory.Q.obj E))⟦(1 : ℤ)⟧') = g := by simp
      exact key₂.trans key.symm

end Splice

end CochainComplex

end
