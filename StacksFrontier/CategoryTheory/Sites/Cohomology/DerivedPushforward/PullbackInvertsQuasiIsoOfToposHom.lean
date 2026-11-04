module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.Homology.CyclesShortComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Degreewise pullback along a morphism of ringed topoi is exact on the K-flat class

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi.  The exactness clause of
**Stacks 06YY** is that degreewise pullback carries a quasi-isomorphism between K-flat complexes
of `O`-modules with flat terms to an isomorphism of `D(O')`; it is what the derived pullback
`Lf^*` is built from.  This file proves it with the geometric datum an
`AlgebraicGeometry.RingedToposHom` — a morphism of the underlying topoi together with the
structure map — so that no functor between the underlying sites is asked for.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.acyclic_pullbackComplex_of_kFlat_of_acyclic`:
  degreewise pullback carries an acyclic K-flat complex with flat terms to an acyclic complex.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat`: **the exactness
  clause of Stacks 06YY**, in the shape
  `Stacks.Cohomology.DerivedPullbackOfToposHom.PullbackInvertsQuasiIso` that the derived pullback
  of a morphism of ringed topoi consumes.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`: hence
  `Lf^*` exists along every morphism of ringed topoi, the resolving half of the datum being
  Stacks 06YS.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general`: `Lf^*` is
  an exact functor of triangulated categories, the exactness assertion of Stacks 06YY.

## Implementation notes

*The argument for a single complex.*  An acyclic complex splices out of its cycles sequences
`0 ⟶ Z^n ⟶ K^n ⟶ Z^{n+1} ⟶ 0`, which are short exact exactly because the complex is acyclic.
Their third terms are the cycles, flat by Stacks 0G7C, so Stacks 0G6R keeps each of them short
exact after pulling back, and a complex whose cycles sequences stay short exact has acyclic image
(`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`).  Neither exactness of `f^*`
nor K-flatness of the pulled-back complex is used.  Stacks 0G6R is available unconditionally for
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, which is why no
morphism-of-sites hypothesis appears; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/KFlatPullbackOfToposHom.lean`.

*From one complex to a morphism.*  The cone of a quasi-isomorphism between complexes of the class
is acyclic and is again K-flat with flat terms, so its degreewise pullback is acyclic; reading
`CategoryTheory.ObjectProperty.trW_iff_of_distinguished` on the image of the mapping-cone triangle
under the triangulated functor `K(f^*)` turns that into the conclusion.  The third vertex must be
the mapping cone of a representative and **not** the abstract vertex of a distinguished triangle:
flatness of the *terms* is not invariant under homotopy equivalence, so the abstract vertex need
not lie in the class even though the cone does.

*Why this is not in the Stacks 06YY module.*
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean`,
which carries the 06YY attributes, is imported by
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfRingedTopoi.lean`,
from which the mapping-cone closure `isKFlat_mappingCone` used below comes, and by
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfToposHom.lean`,
which states `PullbackInvertsQuasiIso` for a morphism of the underlying topoi.  Putting the
discharge there would close an import cycle, exactly as it does for the ringed-site discharge in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom

noncomputable section

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]

/-- **Degreewise pullback carries an acyclic complex with flat cycles to an acyclic complex.**
The cycles sequences of an acyclic complex are short exact with the cycles as third term, so
Stacks 0G6R keeps each of them short exact after pulling back, and a complex whose cycles
sequences stay short exact has acyclic image. -/
theorem acyclic_pullbackComplex_of_isFlat_cycles (f : RingedToposHom X Y)
    (K : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hKac : K.Acyclic)
    (hcyc : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O)
      (K.cycles n)) :
    ((pullbackComplex f).obj K).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact
    f.toModulesHom.pullbackModules K
    fun _ j hij ↦ shortExact_map_pullbackModules f _
      (HomologicalComplex.cyclesShortComplex_shortExact K hij (hKac j)) (hcyc j)

/-- **Degreewise pullback carries an acyclic K-flat complex with flat terms to an acyclic
complex.**  The three hypotheses on the complex enter only through Stacks 0G7C, which makes its
cycles flat; flat cycles are all the splicing argument needs. -/
theorem acyclic_pullbackComplex_of_kFlat_of_acyclic (f : RingedToposHom X Y)
    (K : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) (K.X i))
    (hKac : K.Acyclic) :
    ((pullbackComplex f).obj K).Acyclic :=
  acyclic_pullbackComplex_of_isFlat_cycles f K hKac
    (Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat Y K hKac
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).2 hK) hflat)

/-- In a distinguished triangle of the homotopy category, the first map is a quasi-isomorphism
exactly when the third vertex is acyclic. -/
private theorem quasiIso_iff_subcategoryAcyclic_of_distinguished {B : Type*} [Category B]
    [Abelian B] {T : Triangle (HomotopyCategory B (ComplexShape.up ℤ))} (hT : T ∈ distTriang _) :
    HomotopyCategory.quasiIso B (ComplexShape.up ℤ) T.mor₁ ↔
      HomotopyCategory.subcategoryAcyclic B T.obj₃ := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ObjectProperty.trW_iff_of_distinguished _ _ hT

/-- **The exactness clause of Stacks 06YY for an arbitrary morphism of ringed topoi.**
Degreewise pullback along `f` carries a quasi-isomorphism between K-flat complexes of
`O`-modules with flat terms to an isomorphism of `D(O')`.

The cone of such a quasi-isomorphism is acyclic and is again K-flat with flat terms, so its
degreewise pullback is acyclic; the conclusion is then read off the image of the mapping-cone
triangle under the triangulated functor `K(f^*)`. -/
@[stacks 06YY "exactness on K-flat complexes with flat terms, for an arbitrary morphism of
ringed topoi"]
theorem pullbackInvertsQuasiIso_isKFlat (f : RingedToposHom X Y) :
    PullbackInvertsQuasiIso f (IsKFlat (Y := Y)) := by
  intro K M s hs hK hM
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨M₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨s₀, rfl⟩ : ∃ s₀ : K₀ ⟶ M₀,
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s₀ = s :=
    ⟨Quot.out s, HomotopyCategory.quotient_map_out s⟩
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished s₀
  have hacyc : (CochainComplex.mappingCone s₀).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
    exact (quasiIso_iff_subcategoryAcyclic_of_distinguished hT).1 hs
  have hcone := Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone s₀ hK hM
  have hpull : ((pullbackComplex f).obj (CochainComplex.mappingCone s₀)).Acyclic :=
    acyclic_pullbackComplex_of_kFlat_of_acyclic f _ hcone.1 hcone.2 hacyc
  have hFT := ((f.toModulesHom.pullbackModules).mapHomotopyCategory
    (ComplexShape.up ℤ)).map_distinguished _ hT
  have h3 : HomotopyCategory.subcategoryAcyclic
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
      (((f.toModulesHom.pullbackModules).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone s₀))) :=
    ObjectProperty.prop_of_iso _
      ((((f.toModulesHom.pullbackModules).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
        (CochainComplex.mappingCone s₀)).symm)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hpull)
  have hq := (quasiIso_iff_subcategoryAcyclic_of_distinguished hFT).2 h3
  exact Localization.inverts DerivedCategory.Qh _ _ hq

/-- **The derived pullback exists along every morphism of ringed topoi.**  The resolving half of
the datum is Stacks 06YS and the exactness half is `pullbackInvertsQuasiIso_isKFlat`, so
degreewise pullback followed by localization has an everywhere-defined left derived functor. -/
theorem hasLeftDerivedFunctor_pullbackOnHomotopy (f : RingedToposHom X Y) :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f (IsKFlat (Y := Y))
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y))
    (pullbackInvertsQuasiIso_isKFlat f)

section Triangulated

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

/-- The canonical comparison `Lf^* ⟶ f^*` commutes with the shifts. -/
instance derivedPullbackComparison_commShift_general (f : RingedToposHom X Y) :
    NatTrans.CommShift (derivedPullbackComparison f) ℤ :=
  Functor.IsLeftDerivedFunctor.natTrans_commShift (derivedPullback f)
    (derivedPullbackComparison f) (quasiIsoTarget (Y := Y)) ℤ

/-- **Tag 06YY, exactness, for an arbitrary morphism of ringed topoi.**  The derived pullback is
an exact functor of triangulated categories: every morphism of `D(𝒪')` is, up to isomorphism,
the image of a morphism between K-flat complexes with flat terms, the mapping cone of such a
morphism is again K-flat with flat terms, and the canonical comparison is invertible there. -/
theorem derivedPullback_isTriangulated_general (f : RingedToposHom X Y) :
    (derivedPullback f).IsTriangulated := by
  let W := quasiIsoTarget (Y := Y)
  let P : ObjectProperty (HomotopyCategory
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ)) := IsKFlat (Y := Y)
  have hres : HasResolutions (Y := Y) P :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat (Y := Y)
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun M => by
      obtain ⟨K, hK, s, hs⟩ := hres M
      exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) DerivedCategory.Qh
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ DerivedCategory.Qh) (W.inverseImage P.ι)
  have hiso : ∀ K, P K → IsIso ((derivedPullbackComparison f).app K) := fun K hK =>
    isIso_derivedPullbackComparison_app f P hres (pullbackInvertsQuasiIso_isKFlat f) K hK
  apply Functor.isTriangulated_of_rightExtension (derivedPullback f) (derivedPullbackComparison f)
  intro K L g
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ DerivedCategory.Qh).mapArrow) (Arrow.mk g)
  refine ⟨CochainComplex.mappingCone.triangleh (P.ι.map a.hom).out,
    HomotopyCategory.mappingCone_triangleh_distinguished _, hiso _ a.left.property,
    hiso _ a.right.property, hiso _ ?_, ?_⟩
  · exact Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone _
      a.left.property a.right.property
  · exact ⟨eqToIso (congrArg (fun m => Arrow.mk (DerivedCategory.Qh.map m))
      (HomotopyCategory.quotient_map_out (P.ι.map a.hom))) ≪≫ ea⟩

end Triangulated

end Stacks.Cohomology.DerivedPullbackOfToposHom

end

end
