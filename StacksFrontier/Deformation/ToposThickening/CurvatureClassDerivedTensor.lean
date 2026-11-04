module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.BaseChangeLocallySurjective
public import StacksFrontier.Deformation.ToposThickening.FlatTensorAmplitude
public import StacksFrontier.Deformation.ToposThickening.IdealKernelExistence
import StacksCore.Tactic.StacksAttribute

/-!
# The curvature class with values in the derived tensor product

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site whose kernel is an
ideal sheaf `I` of square zero. For every `K₀` in `D⁻(O₀)` there is a canonical map

`ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]`

in `D(O₀)`, natural in `K₀` (Tag 0DIU). Here `- ⊗^L_{O₀} I` is
`Deformation.ComplexLift.derivedTensorRight I`, the total left derived functor of the degreewise
tensor product with `I`, constructed by Stacks 0794 from flat resolutions; by
`Deformation.ComplexLift.singleTensorIsoDerivedTensorRight` it is the partial functor of the
derived tensor product of the ringed site (Tag 06YU).

The map is the one of the proof of Tag 0DIU: choose a bounded above flat lift `F` of `K₀`
(Tag 0DIT), with reduction `F₀ ⟶ K₀` a quasi-isomorphism; the square of the lifted differential
is a map of complexes `F₀ ⟶ (F₀ ⊗_{O₀} I)[2]`; and since `F₀` is a bounded above complex of flat
modules, the canonical comparison `F₀ ⊗^L_{O₀} I ⟶ F₀ ⊗_{O₀} I` is invertible, so the target
represents `(K₀ ⊗^L_{O₀} I)[2]`.

## Main definitions

* `Deformation.ComplexLift.tensorCurvature`: the curvature of a flat lift, read in
  `(F₀ ⊗^L_{O₀} I)[2]`.
* `Deformation.ComplexLift.tensorObstruction`: the map `K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` computed from a
  given flat lift and kernel identification.
* `Deformation.ComplexLift.tensorOmega`: the map for a bounded above complex.
* `Deformation.ComplexLift.tensorOmegaObj`: the map for an object of `D(O₀)` with bounded above
  cohomology.
* `Deformation.ComplexLift.tensorOmegaMinus`: **Tag 0DIU**, the map `ω(K₀)` for an object `K₀`
  of `D⁻(O₀)`.

## Main results

* `Deformation.ComplexLift.FlatLift.isFlat_baseChange_X`: the reduction of a flat lift has flat
  terms (Tag 05V4).
* `Deformation.ComplexLift.isIso_derivedTensorRightCounit_app_of_isFlat`: the derived tensor
  product with a module is computed by the degreewise one on a bounded above complex of flat
  modules.
* `Deformation.ComplexLift.tensorObstruction_eq_of_lift`: the map does not depend on the lift.
* `Deformation.ComplexLift.tensorOmega_natural_derived`: naturality along every morphism of
  `D(O₀)` between bounded above complexes.
* `Deformation.ComplexLift.tensorOmegaMinus_natural`: **Tag 0DIU**, naturality of `ω` along
  every morphism of `D⁻(O₀)`.

## Implementation notes

The comparison of a left derived functor runs from the derived functor to the underived one,
`K ⊗^L_{O₀} I ⟶ K ⊗_{O₀} I`, and is invertible on bounded above complexes of flat modules; the
curvature is read through its inverse at the reduction of the lift only, which is such a
complex. `Deformation.ComplexLift.DerivedIdealTensor` asks instead for a comparison
`K ⊗_{O₀} I ⟶ K ⊗^L_{O₀} I` natural on *all* complexes. Applied to a flat resolution `P ⟶ K` of
a module, its naturality makes `P ⊗ I ⟶ K ⊗ I` a split monomorphism in `D(O₀)`, which forces
`Tor₁(K, I) = 0`; so such a datum exists only when `I` is flat over `O₀`, and the map here is
not obtained from one.

## References

* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.UnboundedLeftDerivedFunctor
open Stacks.SheafOfModules.ComplexLifting (IsExtensionOfScalars extensionOfScalarsUnit
  extensionOfScalarsUnit_isExtension)

universe v u w d

namespace Deformation.ComplexLift

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

section Flat

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {K₀ : CochainComplex (SheafMod O₀) ℤ}

/-- **The reduction of a flat lift has flat terms**: each term is an extension of scalars of a
flat module, hence flat by Tag 05V4. -/
theorem FlatLift.isFlat_baseChange_X (L : FlatLift f K₀) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat (L.baseChange.complex.X n) := by
  have := IsExtensionOfScalars.isIso_desc.{v, u, w, w} f (L.baseChange.isExtension n)
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso O₀
    (asIso (IsExtensionOfScalars.desc f (extensionOfScalarsUnit_isExtension f (L.F.X n))
      (L.baseChange.unit n)))
    (Stacks.FlatChangeOfRings.isFlat_extendScalars f (L.F.X n) (L.flat n))

/-- The reduction of a flat lift is bounded above. -/
theorem FlatLift.isStrictlyLE_baseChange (L : FlatLift f K₀) :
    ∃ a : ℤ, L.baseChange.complex.IsStrictlyLE a := by
  obtain ⟨N, hN⟩ := L.boundedAbove
  refine ⟨N, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Stacks.SheafOfModules.ComplexLifting.isZero_of_isExtensionOfScalars f
    (L.baseChange.isExtension i) (hN i hi.le)

end Flat

section Counit

variable (R : Sheaf J CommRingCat.{w}) [HasDerivedCategory.{d} (SheafMod R)] (M : SheafMod R)

/-- **The derived tensor product is computed by the degreewise one on a bounded above complex of
flat modules**: such a complex is cellular for the flat modules, and the comparison of a left
derived functor constructed by Stacks 0794 is invertible on cellular complexes. -/
theorem isIso_derivedTensorRightCounit_app_of_isFlat (P : CochainComplex (SheafMod R) ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (P.X n)) (a : ℤ) [P.IsStrictlyLE a] :
    IsIso ((derivedTensorRightCounit.{d} M).app P) := by
  have hc := isFlatCellular_of_isStrictlyLE R P a hflat
  have : IsIso ((derivedTensorRightCounitHomotopy.{d} M).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
    CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions
      (HomotopyCategory.quasiIso (SheafMod R) (ComplexShape.up ℤ))
      (cellular (flatObjects R)) (exists_cellular_quasiIso R) (tensorRightHomotopy M)
      (fun s hs hA hB ↦ isIso_map_tensorRightHomotopy_of_cellular R M s hs hA hB)
      DerivedCategory.Qh (derivedTensorRight M) (derivedTensorRightCounitHomotopy M) _
      (cellular_quotient_obj R hc)
  dsimp only [derivedTensorRightCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

end Counit

section Derived

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [HasDerivedCategory.{d} (SheafMod O₀)] {S : SquareZeroIdeal f I}
  {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}

/-- The comparison `F₀ ⊗^L_{O₀} I ⟶ F₀ ⊗_{O₀} I` at the reduction of a flat lift is invertible:
the reduction is a bounded above complex of flat modules. -/
instance FlatLift.isIso_derivedTensorRightCounit_app (L : FlatLift f K₀) :
    IsIso ((derivedTensorRightCounit.{d} I).app L.baseChange.complex) := by
  obtain ⟨a, ha⟩ := L.isStrictlyLE_baseChange
  exact isIso_derivedTensorRightCounit_app_of_isFlat O₀ I _ L.isFlat_baseChange_X a

/-- **The curvature class of a flat lift with values in the derived tensor product**: the map of
complexes `F₀ ⟶ (F₀ ⊗_{O₀} I)[2]` given by the square of the lifted differential, read in
`D(O₀)` and followed by the inverse of the comparison `F₀ ⊗^L_{O₀} I ≅ F₀ ⊗_{O₀} I`. -/
def tensorCurvature {L : FlatLift f K₀} (T : IdealKernel S L) :
    DerivedCategory.Q.obj L.baseChange.complex ⟶
      ((derivedTensorRight.{d} I).obj (DerivedCategory.Q.obj L.baseChange.complex))⟦(2 : ℤ)⟧ :=
  DerivedCategory.Q.map (curvatureMap T) ≫
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (L.idealTensor (I := I)) ≫
    (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
      (inv ((derivedTensorRightCounit.{d} I).app L.baseChange.complex))

/-- **The map `K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` computed from a flat lift**: the curvature class of the
lift, transported along the quasi-isomorphism `F₀ ⟶ K₀`. -/
def tensorObstruction {L : FlatLift f K₀} (T : IdealKernel S L) :
    DerivedCategory.Q.obj K₀ ⟶
      ((derivedTensorRight.{d} I).obj (DerivedCategory.Q.obj K₀))⟦(2 : ℤ)⟧ :=
  inv (DerivedCategory.Q.map L.baseChange.map) ≫ tensorCurvature T ≫
    (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
      ((derivedTensorRight.{d} I).map (DerivedCategory.Q.map L.baseChange.map))

variable {L : FlatLift f K₀} {M : FlatLift f L₀} {φ : K₀ ⟶ L₀} (h : FlatLiftHom L M φ)
  (TL : IdealKernel S L) (TM : IdealKernel S M)
  (hemb : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n =
    TL.emb n ≫ h.hom n)

/-- The inverse comparison is natural along the map of reductions of a morphism of flat
lifts. -/
theorem inv_derivedTensorRightCounit_naturality :
    inv ((derivedTensorRightCounit.{d} I).app L.baseChange.complex) ≫
        (derivedTensorRight.{d} I).map (DerivedCategory.Q.map h.red) =
      DerivedCategory.Q.map ((idealTensorFunctor O₀ I).map h.red) ≫
        inv ((derivedTensorRightCounit.{d} I).app M.baseChange.complex) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact (derivedTensorRightCounit.{d} I).naturality h.red

include hemb in
/-- Naturality of the curvature class along a morphism of flat lifts. -/
theorem tensorCurvature_natural :
    tensorCurvature TL ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d} I).map (DerivedCategory.Q.map h.red)) =
      DerivedCategory.Q.map h.red ≫ tensorCurvature TM := by
  have hcomp := inv_derivedTensorRightCounit_naturality (I := I) h
  have hshift := (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.naturality
    ((idealTensorFunctor O₀ I).map h.red)
  simp only [Functor.comp_map] at hshift
  simp only [tensorCurvature, Category.assoc, ← Functor.map_comp]
  rw [hcomp, Functor.map_comp]
  slice_lhs 2 3 => rw [← hshift]
  slice_lhs 1 2 =>
    rw [← Functor.map_comp, curvatureMap_natural h TL TM hemb, Functor.map_comp]
  simp only [Category.assoc]

include hemb in
/-- Naturality of the map along a map of complexes covered by a morphism of flat lifts. -/
theorem tensorObstruction_natural :
    DerivedCategory.Q.map φ ≫ tensorObstruction TM =
      tensorObstruction TL ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d} I).map (DerivedCategory.Q.map φ)) := by
  have hred : DerivedCategory.Q.map L.baseChange.map ≫ DerivedCategory.Q.map φ =
      DerivedCategory.Q.map h.red ≫ DerivedCategory.Q.map M.baseChange.map := by
    rw [← Functor.map_comp, ← Functor.map_comp, h.red_map]
  have hinv : DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map M.baseChange.map) =
      inv (DerivedCategory.Q.map L.baseChange.map) ≫ DerivedCategory.Q.map h.red := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hred
  simp only [tensorObstruction, Category.assoc]
  slice_lhs 1 2 => rw [hinv]
  simp only [Category.assoc, ← Functor.map_comp]
  slice_lhs 2 3 => rw [← tensorCurvature_natural h TL TM hemb]
  simp only [Category.assoc, ← Functor.map_comp, h.red_map]

/-- Two flat lifts of one complex joined by a morphism of lifts over the identity give the same
map. -/
theorem tensorObstruction_eq_of_hom {L M : FlatLift f K₀} (h : FlatLiftHom L M (𝟙 K₀))
    (TL : IdealKernel S L) (TM : IdealKernel S M)
    (hemb : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫
      TM.emb n = TL.emb n ≫ h.hom n) :
    tensorObstruction TL = tensorObstruction TM := by
  have hn := tensorObstruction_natural h TL TM hemb
  simpa using hn.symm

end Derived

end General

section Canonical

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [HasDerivedCategory.{d} (SheafMod O₀)]

/-- The map computed from any two bounded above flat lifts of `K₀`, with any kernel
identifications on them, is the same. -/
theorem tensorObstruction_eq_of_lift (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) {K₀ : CochainComplex (SheafMod O₀) ℤ}
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    {L L' : FlatLift f K₀} (T : IdealKernel S L) (T' : IdealKernel S L') :
    tensorObstruction.{v, u, max u v w, d} T = tensorObstruction.{v, u, max u v w, d} T' := by
  obtain ⟨M, ⟨h⟩, ⟨h'⟩⟩ := exists_flatLiftHom_pair L L' hf hK
  obtain ⟨TM⟩ := nonempty_idealKernel hf S M
  rw [tensorObstruction_eq_of_hom h T TM (emb_natural hf h T TM),
    tensorObstruction_eq_of_hom h' T' TM (emb_natural hf h' T' TM)]

/-- **The map `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` of a bounded above complex.** It is the curvature
class of a bounded above flat lift of `K₀` (Tag 0DIT), read through the canonical identification
of the ideal part of the lift with the kernel of its reduction; by
`Deformation.ComplexLift.tensorObstruction_eq_of_lift` it does not depend on the lift. -/
@[stacks 0DIU "the canonical map ω(K₀) : K₀ ⟶ (K₀ ⊗^L I)[2], on a bounded above complex"]
def tensorOmega (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n)) :
    DerivedCategory.Q.obj K₀ ⟶
      ((derivedTensorRight.{d} I).obj (DerivedCategory.Q.obj K₀))⟦(2 : ℤ)⟧ :=
  tensorObstruction (idealKernel hf S (Classical.choice (exists_flatLift hf K₀ hK)))

/-- `ω(K₀)` is computed by any bounded above flat lift and any kernel identification on it. -/
theorem tensorOmega_eq (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    {K₀ : CochainComplex (SheafMod O₀) ℤ}
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    {L : FlatLift f K₀} (T : IdealKernel S L) :
    tensorOmega.{v, u, w, d} hf S K₀ hK = tensorObstruction T :=
  tensorObstruction_eq_of_lift hf S hK _ T

/-- Naturality of `ω` along a map of bounded above complexes. -/
theorem tensorOmega_natural (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ} (φ : K₀ ⟶ L₀)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (hL : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (L₀.homology n)) :
    DerivedCategory.Q.map φ ≫ tensorOmega.{v, u, w, d} hf S L₀ hL =
      tensorOmega.{v, u, w, d} hf S K₀ hK ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d} I).map (DerivedCategory.Q.map φ)) := by
  obtain ⟨L⟩ := exists_flatLift hf K₀ hK
  obtain ⟨M, ⟨h⟩⟩ := exists_flatLiftHom hf L φ hL
  obtain ⟨TL⟩ := nonempty_idealKernel hf S L
  obtain ⟨TM⟩ := nonempty_idealKernel hf S M
  rw [tensorOmega_eq hf S hK TL, tensorOmega_eq hf S hL TM]
  exact tensorObstruction_natural h TL TM (emb_natural hf h TL TM)

/-- **Naturality of `ω` along an arbitrary morphism of `D(O₀)`** between bounded above
complexes: such a morphism is a roof `K₀ ⟶ M ⟵ L₀` of maps of complexes with the second leg a
quasi-isomorphism, and `ω` is natural along both legs. -/
@[stacks 0DIU "naturality of ω, on bounded above complexes"]
theorem tensorOmega_natural_derived (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (hL : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (L₀.homology n))
    (ψ : DerivedCategory.Q.obj K₀ ⟶ DerivedCategory.Q.obj L₀) :
    ψ ≫ tensorOmega.{v, u, w, d} hf S L₀ hL =
      tensorOmega.{v, u, w, d} hf S K₀ hK ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d} I).map ψ) := by
  obtain ⟨M, g, t, ht, hgt⟩ := exists_roof_of_derived_hom ψ
  have : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso (SheafMod O₀) t).mp ht
  obtain ⟨N, hN⟩ := hL
  have hM : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (M.homology n) :=
    ⟨N, fun n hn =>
      IsZero.of_iso (hN n hn) (asIso (HomologicalComplex.homologyMap t n)).symm⟩
  have hnt := tensorOmega_natural hf S t ⟨N, hN⟩ hM
  have hng := tensorOmega_natural hf S g hK hM
  rw [← cancel_mono ((CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀))
    (2 : ℤ)).map ((derivedTensorRight.{d} I).map (DerivedCategory.Q.map t)))]
  simp only [Category.assoc]
  rw [← hnt, ← Category.assoc, hgt, hng]
  simp only [← Functor.map_comp, hgt]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- An object of `D⁻(O₀)` is represented by a complex with bounded above cohomology. -/
theorem homology_objPreimage_isZero {X : DerivedCategory (SheafMod O₀)}
    (hX : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (SheafMod O₀) n).obj X)) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((DerivedCategory.Q.objPreimage X).homology n) := by
  obtain ⟨N, hN⟩ := hX
  refine ⟨N, fun n hn => IsZero.of_iso (hN n hn) ?_⟩
  exact ((DerivedCategory.homologyFunctorFactors (SheafMod O₀) n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (SheafMod O₀) n).mapIso
      (DerivedCategory.Q.objObjPreimageIso X)

/-- **Stacks 0DIU.** Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site
whose kernel is an ideal sheaf `I` of square zero (`S`). For every object `K₀` of `D⁻(O₀)` --
an object of `D(O₀)` whose cohomology vanishes in all sufficiently large degrees -- this is the
canonical map

`ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]`

in `D(O₀)`: it is `Deformation.ComplexLift.tensorOmega` on a complex representing `K₀`, the
curvature of the lifted differential of a bounded above flat lift. -/
@[stacks 0DIU "the canonical map ω(K₀) : K₀ ⟶ (K₀ ⊗^L I)[2], on an object with bounded above
cohomology"]
def tensorOmegaObj (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (X : DerivedCategory (SheafMod O₀))
    (hX : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (SheafMod O₀) n).obj X)) :
    X ⟶ ((derivedTensorRight.{d} I).obj X)⟦(2 : ℤ)⟧ :=
  (DerivedCategory.Q.objObjPreimageIso X).inv ≫
    tensorOmega.{v, u, w, d} hf S _ (homology_objPreimage_isZero hX) ≫
    (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
      ((derivedTensorRight.{d} I).map (DerivedCategory.Q.objObjPreimageIso X).hom)

/-- **Stacks 0DIU, naturality of `ω`.** For every map `ψ : K₀ ⟶ L₀` in `D⁻(O₀)` the square

`ω(L₀) ∘ ψ = (ψ ⊗^L I)[2] ∘ ω(K₀)`

commutes. -/
@[stacks 0DIU "naturality of ω, on objects with bounded above cohomology"]
theorem tensorOmegaObj_natural (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    {X Y : DerivedCategory (SheafMod O₀)}
    (hX : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (SheafMod O₀) n).obj X))
    (hY : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (SheafMod O₀) n).obj Y))
    (ψ : X ⟶ Y) :
    ψ ≫ tensorOmegaObj.{v, u, w, d} hf S Y hY =
      tensorOmegaObj.{v, u, w, d} hf S X hX ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d} I).map ψ) := by
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let eY := DerivedCategory.Q.objObjPreimageIso Y
  have hn := tensorOmega_natural_derived.{v, u, w, d} hf S (homology_objPreimage_isZero hX)
    (homology_objPreimage_isZero hY) (eX.hom ≫ ψ ≫ eY.inv)
  have hψ : eX.hom ≫ ψ = (eX.hom ≫ ψ ≫ eY.inv) ≫ eY.hom := by simp
  simp only [tensorOmegaObj, Category.assoc]
  change _ = eX.inv ≫ _ ≫ _ ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp, hψ, Functor.map_comp, Functor.map_comp,
    ← Category.assoc (tensorOmega _ _ _ _), ← hn]
  simp [eX, eY]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- An object of the bounded above derived category has cohomology vanishing in all sufficiently
large degrees. -/
theorem homology_isZero_of_minus (E : DerivedCategory.Minus (SheafMod O₀)) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (SheafMod O₀) n).obj E.obj) := by
  obtain ⟨b, hb⟩ := E.property
  have : E.obj.IsLE b := hb
  exact ⟨b + 1, fun n hn => (DerivedCategory.isLE_iff E.obj b).1 this n (by omega)⟩

/-- **Stacks 0DIU.** Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site
whose kernel is an ideal sheaf `I` of square zero (`S`). For every object `K₀` of `D⁻(O₀)` there
is a canonical map

`ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]`

in `D(O₀)`, where `- ⊗^L_{O₀} I` is `Deformation.ComplexLift.derivedTensorRight I`. On a complex
representing `K₀` it is the curvature `d ∘ d` of the lifted differential of a bounded above flat
lift; its naturality is `Deformation.ComplexLift.tensorOmegaMinus_natural`. -/
@[stacks 0DIU "the canonical map ω(K₀) : K₀ ⟶ (K₀ ⊗^L I)[2] for every K₀ in D⁻(O₀)"]
def tensorOmegaMinus (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    (K₀ : DerivedCategory.Minus (SheafMod O₀)) :
    K₀.obj ⟶ ((derivedTensorRight.{d} I).obj K₀.obj)⟦(2 : ℤ)⟧ :=
  tensorOmegaObj.{v, u, w, d} hf S K₀.obj (homology_isZero_of_minus K₀)

/-- **Stacks 0DIU, naturality of `ω`.** For every map `ψ : K₀ ⟶ L₀` in `D⁻(O₀)` the square

`ω(L₀) ∘ ψ = (ψ ⊗^L I)[2] ∘ ω(K₀)`

in `D(O₀)` commutes. -/
@[stacks 0DIU "naturality of ω along every map K₀ ⟶ L₀ in D⁻(O₀)"]
theorem tensorOmegaMinus_natural (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    {K₀ L₀ : DerivedCategory.Minus (SheafMod O₀)} (ψ : K₀.obj ⟶ L₀.obj) :
    ψ ≫ tensorOmegaMinus.{v, u, w, d} hf S L₀ =
      tensorOmegaMinus.{v, u, w, d} hf S K₀ ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d} I).map ψ) :=
  tensorOmegaObj_natural hf S _ _ ψ

end Canonical

end Deformation.ComplexLift

end
