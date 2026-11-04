module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.PullbackOfApproximations

/-!
# Degreewise pullback along a morphism of ringed topoi preserves an approximation

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi, with the object, morphism
and section universes of the two sites free.  A map `α : R ⟶ P` of complexes of `𝒪_D`-modules
is an *approximation in degrees `> m`* when it is an isomorphism on cohomology in every degree
`> m` and an epimorphism on cohomology in degree `m`.  If `R` and `P` are K-flat with flat
terms, then the degreewise pullback `f^*α` is again an approximation in degrees `> m`.

This is the step of Stacks 08H4 at which the derived pullback is pushed through a strictly
perfect approximation, at the generality of a morphism of ringed topoi whose geometric datum is
a morphism of the underlying topoi.  It applies in particular to the morphism of small étale
ringed topoi of a morphism of algebraic spaces, Stacks 03G8, whose sites have their objects one
universe above their morphisms and sections.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.isKFlat_of_isStrictlyLE`: a strictly bounded
  above complex with flat terms is K-flat with flat terms (Stacks 06YQ).
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackComplex_approximation`: degreewise
  pullback preserves an approximation between K-flat complexes with flat terms.

## Implementation notes

The argument is the one of
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.homologyBounds_modulePullback` for ringed
spaces.  The cone `C` of `α` is K-flat with flat terms, and the hypotheses on `α` say that `C`
has vanishing cohomology in degrees `≥ m`; the ladder of Stacks 077J resolves it by a complex
strictly bounded above by `m - 1` with flat terms, which is K-flat by Stacks 06YQ; degreewise
pullback inverts that resolution, both ends being K-flat with flat terms (the exactness clause of
Stacks 06YY, `pullbackInvertsQuasiIso_isKFlat`), and keeps the bound; and the pullback of the
cone is the cone of the pullback.  The two derived categories are used only inside the proof,
at an arbitrary model, to read the cohomology of a cone off a distinguished triangle.

## References

* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (isIso_homologyFunctor_map_Q_map_iff
  epi_homologyFunctor_map_Q_map_iff)

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

section Bounded

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

omit [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **Stacks 06YQ, in the resolving class of the derived pullback.**  A strictly bounded above
complex of flat `𝒪`-modules is K-flat with flat terms. -/
theorem isKFlat_of_isStrictlyLE
    (K : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (b : ℤ)
    (hb : K.IsStrictlyLE b)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O)
      (K.X i)) :
    IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
  have := hb
  ⟨CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ K b
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor_ofSize Y.O)
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules_ofSize Y.O)
    (fun q => Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize Y.O _
      (hflat q) q), hflat⟩

omit [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- **K-flatness with flat terms is invariant under isomorphism of complexes.** -/
theorem isKFlat_of_iso
    {K K' : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (e : K ≅ K') (hK : IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K') := by
  let := Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u', v', w', w', w'} Y.O
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u', v', w', w', w'} Y.O
  refine ⟨fun G hG i => (hK.1 G hG i).of_iso
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).mapIso e),
    fun i => Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize Y.O
      ((HomologicalComplex.eval _ _ i).mapIso e) (hK.2 i)⟩

end Bounded

section Approximation

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]

omit [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] in
/-- Degreewise pullback along a morphism of ringed topoi preserves strict boundedness above. -/
theorem isStrictlyLE_pullbackComplex (f : RingedToposHom X Y)
    (F : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) (n : ℤ)
    [F.IsStrictlyLE n] : ((pullbackComplex f).obj F).IsStrictlyLE n :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
    (f.toModulesHom.pullbackModules).map_isZero (F.isZero_of_isStrictlyLE n i hi)

/-- **Degreewise pullback along a morphism of ringed topoi preserves an approximation between
K-flat complexes with flat terms.**  Let `α : R ⟶ P` be a map of complexes of `𝒪_D`-modules,
both K-flat with flat terms, which is an isomorphism on cohomology in degrees `> m` and an
epimorphism on cohomology in degree `m`.  Then `f^*α` has the same two properties. -/
theorem pullbackComplex_approximation (f : RingedToposHom X Y)
    {R P : CochainComplex (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (α : R ⟶ P)
    (hR : IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R))
    (hP : IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap ((pullbackComplex f).map α) j)) ∧
      Epi (HomologicalComplex.homologyMap ((pullbackComplex f).map α) m) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))
  have hQC : (DerivedCategory.Q.obj (CochainComplex.mappingCone α)).IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α))
      (DerivedCategory.mappingCone_triangle_distinguished α) m
      (fun i hi => (isIso_homologyFunctor_map_Q_map_iff α i).2 (hiso i hi))
      ((epi_homologyFunctor_map_Q_map_iff α m).2 hepi)
  have hCLE : (CochainComplex.mappingCone α).IsLE (m - 1) :=
    (DerivedCategory.isLE_Q_obj_iff _ _).1 hQC
  have := Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize Y.O
  obtain ⟨F, s, hs, hFflat, hFLE⟩ :=
    (CochainComplex.exists_quasiIso_prop
      ((fun M => AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w', w'} (O := Y.O) M) :
        ObjectProperty (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)))
      (fun M => by
        obtain ⟨N, p, hN, hp⟩ :=
          Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize Y.O M
        exact ⟨N, hN, p, hp⟩) (m - 1)).2 (CochainComplex.mappingCone α)
  have hinv := pullbackInvertsQuasiIso_isKFlat f
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).mpr hs)
    (isKFlat_of_isStrictlyLE F (m - 1) hFLE hFflat)
    (Stacks.Sheaves.RingedToposDerivedPullback.isKFlat_mappingCone α hR hP)
  have hqis : IsIso (DerivedCategory.Q.map ((pullbackComplex f).map s)) := by
    let N : HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ pullbackOnHomotopy f ≅
        pullbackComplex f ⋙ DerivedCategory.Q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((f.toModulesHom.pullbackModules).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (pullbackComplex f) (DerivedCategory.quotientCompQhIso _)
    exact (NatIso.isIso_map_iff N s).1 hinv
  have := isStrictlyLE_pullbackComplex f F (m - 1)
  have hQpC : (DerivedCategory.Q.obj ((pullbackComplex f).obj
      (CochainComplex.mappingCone α))).IsLE (m - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (asIso (DerivedCategory.Q.map ((pullbackComplex f).map s))) (m - 1)
  have e : (pullbackComplex f).obj (CochainComplex.mappingCone α) ≅
      CochainComplex.mappingCone ((pullbackComplex f).map α) :=
    CochainComplex.mappingCone.mapHomologicalComplexIso α (f.toModulesHom.pullbackModules)
  have hcone : (DerivedCategory.Q.obj (CochainComplex.mappingCone
      ((pullbackComplex f).map α))).IsLE (m - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Q.mapIso e) (m - 1)
  obtain ⟨h₁, h₂⟩ := DerivedCategory.approximation_of_triangle_isLE
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      ((pullbackComplex f).map α)))
    (DerivedCategory.mappingCone_triangle_distinguished _) m hcone
  exact ⟨fun j hj => (isIso_homologyFunctor_map_Q_map_iff _ j).1 (h₁ j hj),
    (epi_homologyFunctor_map_Q_map_iff _ m).1 h₂⟩

end Approximation

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
