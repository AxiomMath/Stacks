module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A negative object annihilating a map of bounded derived objects

In an abelian category with enough negative objects, a morphism `f : X ⟶ X'` between bounded
derived objects whose target has no cohomology in degree `b` admits a lift `N[-b] ⟶ X` from a
negative object `N`, epimorphic on degree-`b` cohomology and annihilated by `f`.

## Main results

* `AlgebraicGeometry.exists_negative_epimorphic_lift_comp_eq_zero`: the negative object and the
  annihilated lift.

## Implementation notes

Having enough negative objects is expressed by its defining property: every object receives an
epimorphism from an object to which it has no nonzero morphisms. This avoids a dependency on the
later siblings proposition. The map `N[-b] ⟶ X` is expressed using the derived-category
single-object functor in degree `b`, and the induced map on degree-`b` cohomology uses the inverse
of the canonical isomorphism `H^b(N[-b]) ≅ N`. The bounded objects are regarded in the ambient
derived category through the fully faithful inclusion. Only the vanishing of degree-`b` cohomology
of the target is used; no cohomological bound on the source is needed.

## References

* [Stacks Project, Tag 0GWG](https://stacks.math.columbia.edu/tag/0GWG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-- The map from an object placed in degree `b` into a complex, given by a map into the
degree-`b` cycles. -/
private noncomputable def mapFromCycles
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (b : ℤ) (N : A) (q : N ⟶ K.cycles b) :
    (CochainComplex.singleFunctor A b).obj N ⟶ K :=
  HomologicalComplex.mkHomFromSingle (q ≫ K.iCycles b) (by simp)

/-- If the chosen map onto the cycles is epimorphic, the induced map on degree-`b` homology of
complexes is epimorphic. -/
private lemma epi_homology_mapFromCycles_chain
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (b : ℤ) (N : A) (q : N ⟶ K.cycles b) [Epi q] :
    Epi ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) b N).inv ≫
      HomologicalComplex.homologyMap (mapFromCycles K b N q) b) := by
  let u := mapFromCycles K b N q
  have hcycles :
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) b N).inv ≫
        HomologicalComplex.cyclesMap u b = q := by
    apply (cancel_mono (K.iCycles b)).1
    simp only [HomologicalComplex.cyclesMap_i, u, mapFromCycles,
      HomologicalComplex.mkHomFromSingle_f, Category.assoc]
    show ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) b N).inv ≫
      ((HomologicalComplex.single A (ComplexShape.up ℤ) b).obj N).iCycles b ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b N).hom ≫
          q ≫ K.iCycles b) = q ≫ K.iCycles b
    rw [← Category.assoc, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
    simp
  have hfac :
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) b N).inv ≫
        HomologicalComplex.homologyMap u b = q ≫ K.homologyπ b := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcycles]
  rw [hfac]
  exact epi_comp q (K.homologyπ b)

/-- If the chosen map onto the cycles is epimorphic, the induced map on degree-`b` cohomology in
the derived category is epimorphic. -/
private lemma epi_homology_mapFromCycles
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : CochainComplex A ℤ) (b : ℤ) (N : A) (q : N ⟶ K.cycles b) [Epi q] :
    Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
      (DerivedCategory.homologyFunctor A b).map
        (DerivedCategory.Q.map (mapFromCycles K b N q))) := by
  have hmap : Epi (HomologicalComplex.homologyMap (mapFromCycles K b N q) b) :=
    (epi_comp_iff_of_epi _ _).1 (epi_homology_mapFromCycles_chain K b N q)
  refine (epi_comp_iff_of_isIso _ ((DerivedCategory.homologyFunctorFactors A b).hom.app K)).1 ?_
  rw [Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality (mapFromCycles K b N q) b]
  exact epi_comp' inferInstance (epi_comp' inferInstance hmap)

/-- Truncation above `n` does not change cohomology in degrees `≤ n`. -/
private lemma isIso_homology_truncLEι
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (n j : ℤ) (hj : j ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor A j).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K)) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLEGE n (n + 1) rfl).obj K
  have hT := t.triangleLEGE_distinguished n (n + 1) rfl K
  have hz (i : ℤ) (hi : i < n + 1) :
      IsZero ((DerivedCategory.homologyFunctor A i).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE ((t.truncGE (n + 1)).obj K) (n + 1) i hi
  have : Epi ((DerivedCategory.homologyFunctor A j).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT j).mpr
      ((hz j (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor A j).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (j - 1) j
      (by omega)).mpr ((hz (j - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor A j).map T.mor₁)

/-- **Stacks Project, Tag 0GWG.** A map of bounded derived objects whose target has zero
cohomology in degree `b` can be killed by a map from a negative object in degree `b` which
surjects onto the degree-`b` cohomology. -/
@[stacks 0GWG, stacks 0GWF "the case `X' = 0`, with no condition on the composition"]
public theorem exists_negative_epimorphic_lift_comp_eq_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (hA : ∀ Y : A, ∃ (N : A) (p : N ⟶ Y), Epi p ∧ Subsingleton (Y ⟶ N))
    (X X' : DerivedCategory.Bounded A) (f : X ⟶ X') (b : ℤ)
    (hX' : IsZero ((DerivedCategory.homologyFunctor A b).obj X'.obj)) :
    ∃ (N : A) (g : (DerivedCategory.singleFunctor A b).obj N ⟶ X.obj),
      Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
        (DerivedCategory.homologyFunctor A b).map g) ∧
      Subsingleton (((DerivedCategory.homologyFunctor A b).obj X.obj) ⟶ N) ∧
      g ≫ (DerivedCategory.Bounded.ι.map f) = 0 := by
  let t := DerivedCategory.TStructure.t (C := A)
  let f₀ := f.hom
  obtain ⟨C, v, w, hC⟩ := Pretriangulated.distinguished_cocone_triangle f₀
  let T := (Pretriangulated.Triangle.mk f₀ v w).invRotate
  have hT : T ∈ distTriang _ := Pretriangulated.inv_rot_of_distTriang _ hC
  let F := (shiftFunctor (DerivedCategory A) (-1 : ℤ)).obj C
  let α : F ⟶ X.obj :=
    -(shiftFunctor (DerivedCategory A) (-1 : ℤ)).map w ≫
      (shiftEquiv (DerivedCategory A) (1 : ℤ)).unitIso.inv.app X.obj
  let H := DerivedCategory.homologyFunctor A b
  have hαepi : Epi (H.map α) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT b).mpr
      (hX'.eq_of_tgt _ _)
  have := isIso_homology_truncLEι F b b le_rfl
  let L := (t.truncLE b).obj F
  have : L.IsLE b := by
    dsimp [L]
    infer_instance
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE L b
  obtain ⟨N, q, hq, hqsub⟩ := hA (K.cycles b)
  let u := mapFromCycles K b N q
  let g : (DerivedCategory.singleFunctor A b).obj N ⟶ X.obj :=
    DerivedCategory.Q.map u ≫ e.inv ≫ ((t.truncLEι b).app F ≫ α)
  have hbase : Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
      H.map (DerivedCategory.Q.map u)) :=
    epi_homology_mapFromCycles K b N q
  have htail : Epi (H.map e.inv ≫ H.map ((t.truncLEι b).app F ≫ α)) := by
    rw [Functor.map_comp]
    infer_instance
  have h_epi : Epi ((DerivedCategory.singleFunctorCompHomologyFunctorIso A b).inv.app N ≫
      H.map g) := by
    dsimp [g]
    rw [Functor.map_comp, Functor.map_comp]
    simpa using epi_comp' hbase htail
  let hfactorMap := eqToHom (HomologicalComplex.homologyFunctor_obj A
      (ComplexShape.up ℤ) b K).symm ≫
        (DerivedCategory.homologyFunctorFactors A b).inv.app K
  let p : K.cycles b ⟶ H.obj X.obj :=
    K.homologyπ b ≫ hfactorMap ≫ H.map e.inv ≫
      H.map ((t.truncLEι b).app F) ≫ H.map α
  have hp : Epi p := by
    dsimp [p, hfactorMap]
    infer_instance
  have hsub : Subsingleton (H.obj X.obj ⟶ N) :=
    ⟨fun a a' => (cancel_epi p).1 (hqsub.elim (p ≫ a) (p ≫ a'))⟩
  refine ⟨N, g, h_epi, hsub, ?_⟩
  show g ≫ f₀ = 0
  have hkill : α ≫ f₀ = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
  simp [g, hkill]

end AlgebraicGeometry

end
