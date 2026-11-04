module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesUniversalProperty
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationProjectiveLine
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataAxioms
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Stacks 0FHL: the functor on Chow motives attached to Weil cohomology data

Let `k` be a field and `F` a field of characteristic zero. Given data (D0), (D1), (D2), (D3)
satisfying (A), (B) and (C) (`Stacks.WeilCohomology.WeilDataAxioms`), Stacks 0FHL constructs a
`ℚ`-linear functor of symmetric monoidal categories

  `G : M_k ⟶ graded F-vector spaces`

with `H^*(X) = G(h(X))`. This file assembles the construction:

* the functor `G` on smooth projective schemes with correspondences of degree zero
  (`WeilData.corrFunctor`, `G(c)(a) = pr₂,*(γ(c) ∪ pr₁^*a)`), ℚ-linear, additive and a functor of
  symmetric monoidal categories for the Koszul-signed symmetry of graded vector spaces
  (`WeilData.corrFunctorBraided`);
* the image of `G(c₂)` on `G(P¹_k)` is invertible
  (`WeilData.exists_isInvertible_image_corrFunctor_map_projectiveLineFibrePoint`);
* hence, by the universal property of `M_k` (Stacks 0FGH), `G` factors through a functor
  `WeilData.motiveFunctor : M_k ⥤ GradedObject ℤ (ModuleCat F)` of symmetric monoidal categories,
  with a monoidal isomorphism `WeilData.motiveFunctorIso : untwistedOfObj ⋙ G ≅ corrFunctor`;
* the graph `[Γ_f]` acting by `f^*`, `h(X) ↦ G(h(X))` is identified with `X ↦ H^*(X)` as functors
  (`WeilData.motiveFunctorCohomologyIso : h ⋙ G ≅ W.cohomologyFunctor`).

## Main results

* `Stacks.WeilCohomology.WeilDataAxioms.exists_motiveFunctor`: **Stacks 0FHL**.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FGH](https://stacks.math.columbia.edu/tag/0FGH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow MonoidalCategory
  CategoryTheory.GradedCategory

universe u w

namespace CategoryTheory.GradedCategory.TwistedKaroubi

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [GradedCategory R C]
  {D : Type*} [Category D] (G : D ⥤ C)
  (hG : ∀ {X Y : D} (f : X ⟶ Y), G.map f ∈ grade (R := R) (G.obj X) (G.obj Y) 0)

/-- A functor whose maps are homogeneous of degree zero, as a functor into the degree-zero
category. -/
def degreeZeroLift : D ⥤ DegreeZero R C where
  obj X := G.obj X
  map f := DegreeZero.homMk (G.map f) (hG f)
  map_id X := DegreeZero.hom_ext (G.map_id X)
  map_comp f g := DegreeZero.hom_ext (G.map_comp f g)

/-- `X ↦ (G X, 1, 0)` factors through the degree-zero category. -/
def functorOfGradeIsoDegreeZeroLift :
    functorOfGrade G hG ≅
      degreeZeroLift G hG ⋙ Idempotents.toKaroubi (DegreeZero R C) ⋙ untwisted R C :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) fun f ↦ by
    refine hom_ext ?_
    rw [comp_val, comp_val]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end CategoryTheory.GradedCategory.TwistedKaroubi

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- **The cohomology functor** `X ↦ H^*(X)`, `f ↦ f^*`, from smooth projective schemes over `k`
to graded `F`-vector spaces. -/
def cohomologyFunctor :
    ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ ⥤ GradedObject ℤ (ModuleCat.{w} F) where
  obj X := W.cohomologyGraded X.unop
  map f n := ModuleCat.ofHom (W.pullDeg f.unop n)
  map_id X := funext fun _ ↦ congrArg ModuleCat.ofHom
    (LinearMap.ext fun x ↦ Subtype.ext (DFunLike.congr_fun (W.pull_id X.unop) x.1))
  map_comp f g := funext fun _ ↦ congrArg ModuleCat.ofHom
    (LinearMap.ext fun x ↦ Subtype.ext (DFunLike.congr_fun (W.pull_comp g.unop f.unop) x.1))

/-! ### The realization of Chow motives -/

variable {W} [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)

/-- Smooth projective schemes as objects of the category of correspondences of degree zero, with
`f ↦ [Γ_f]`. -/
def graphDegreeZero :
    ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ ⥤ DegreeZero ℚ (CorrespondenceCategory k) :=
  GradedCategory.TwistedKaroubi.degreeZeroLift (canonicalGraphFunctor k)
    fun f ↦ graphHom_mem_grade f.unop

/-- `h(X) = (X, 1, 0)` is the image of `X` in the category of correspondences of degree zero. -/
def hIsoGraphDegreeZero :
    ChowMotiveCat.h k ≅
      graphDegreeZero ⋙ TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) :=
  GradedCategory.TwistedKaroubi.functorOfGradeIsoDegreeZeroLift (canonicalGraphFunctor k)
    fun f ↦ graphHom_mem_grade f.unop

/-- On graphs, the realization of degree-zero correspondences is the cohomology functor:
`G([Γ_f]) = f^*`. -/
def graphDegreeZeroCompCorrFunctorIso :
    graphDegreeZero ⋙ corrFunctor hA hB hC ≅ W.cohomologyFunctor :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) fun f ↦ by
    funext n
    ext x
    simp only [Functor.comp_map, Iso.refl_hom]
    exact congrArg (fun φ : W.grade _ n →ₗ[F] W.grade _ n ↦ φ x)
      (corrHomMap_of_val_eq_graphHom hA hB hC (graphDegreeZero.map f) f.unop rfl n)

section Braided

attribute [local instance 10000] GradedObject.koszulBraidedCategory
  GradedObject.koszulSymmetricCategory

attribute [local instance] corrFunctorBraided

/-- The universal property of `M_k` (Stacks 0FGH) applied to the realization `G` of degree-zero
correspondences. -/
theorem exists_motiveFunctor_aux :
    ∃ (G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F)) (_ : G.Braided) (_ : G.Additive)
      (_ : Functor.Linear ℚ G)
      (φ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G ≅ corrFunctor hA hB hC),
      NatTrans.IsMonoidal φ.hom :=
  (ChowMotiveCat.universalProperty (ChowMotiveCat.projectiveLineZero k)
    ChowMotiveCat.projectiveLineZero_comp (corrFunctor hA hB hC)
    (exists_isInvertible_image_corrFunctor_map_projectiveLineFibrePoint hA hB hC _ _)).1

/-- **The functor `G : M_k ⥤ graded F-vector spaces` of Stacks 0FHL**, the extension of the
realization of degree-zero correspondences along `M_k`'s universal property (Stacks 0FGH). -/
def motiveFunctor : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F) :=
  (exists_motiveFunctor_aux hA hB hC).choose

/-- `G` is a functor of symmetric monoidal categories, for the Koszul-signed symmetry. -/
abbrev motiveFunctorBraided : (motiveFunctor hA hB hC).Braided :=
  (exists_motiveFunctor_aux hA hB hC).choose_spec.choose

attribute [local instance] motiveFunctorBraided

/-- The functor `G` is additive. -/
instance motiveFunctor_additive : (motiveFunctor hA hB hC).Additive :=
  (exists_motiveFunctor_aux hA hB hC).choose_spec.choose_spec.choose

/-- The functor `G` is `ℚ`-linear. -/
instance motiveFunctor_linear : Functor.Linear ℚ (motiveFunctor hA hB hC) :=
  (exists_motiveFunctor_aux hA hB hC).choose_spec.choose_spec.choose_spec.choose

/-- `G` restricted to degree-zero correspondences is the realization `c ↦ pr₂,*(γ(c) ∪ pr₁^*-)`. -/
def motiveFunctorIso :
    TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ motiveFunctor hA hB hC ≅
      corrFunctor hA hB hC :=
  (exists_motiveFunctor_aux hA hB hC).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The isomorphism `motiveFunctorIso` between `G` on degree-zero correspondences and the
realization `corrFunctor` is a monoidal natural transformation. -/
instance motiveFunctorIso_isMonoidal : NatTrans.IsMonoidal (motiveFunctorIso hA hB hC).hom :=
  (exists_motiveFunctor_aux hA hB hC).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end Braided

/-- **`H^*(X) = G(h(X))`**, naturally in `X`: `h ⋙ G ≅ (X ↦ H^*(X), f ↦ f^*)`. -/
def motiveFunctorCohomologyIso : ChowMotiveCat.h k ⋙ motiveFunctor hA hB hC ≅ W.cohomologyFunctor :=
  Functor.isoWhiskerRight (hIsoGraphDegreeZero (k := k)) (motiveFunctor hA hB hC) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft graphDegreeZero (motiveFunctorIso hA hB hC) ≪≫
    graphDegreeZeroCompCorrFunctorIso hA hB hC

end Stacks.WeilCohomology.WeilData

namespace Stacks.WeilCohomology.WeilDataAxioms

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F]

/-- The functor `G : M_k ⥤ graded F-vector spaces` attached to data (D0)–(D3) satisfying (A),
(B) and (C) (Stacks 0FHL). -/
abbrev motiveFunctor (T : WeilDataAxioms k F) :
    ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F) :=
  WeilData.motiveFunctor T.poincareDuality T.kunneth T.cycleClassAxiom

/-- **Stacks Project, Tag 0FHL.** Data (D0), (D1), (D2), (D3) satisfying (A), (B) and (C) give a
`ℚ`-linear functor `G : M_k ⥤ graded F-vector spaces` of symmetric monoidal categories (for the
Koszul-signed symmetry of Stacks, Homology, Example 0FFX) with `H^*(X) = G(h(X))`, naturally in `X`
(pullbacks `f^*` corresponding to `G(h(f))`). -/
@[stacks 0FHL "data (D0)-(D3) satisfying (A), (B), (C) give a Q-linear symmetric monoidal functor
G : M_k -> graded F-vector spaces with H^*(X) = G(h(X))"]
theorem exists_motiveFunctor (T : WeilDataAxioms k F) :
    ∃ (G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F))
      (_ : @Functor.Braided (ChowMotiveCat k) _ _ _ (GradedObject ℤ (ModuleCat.{w} F)) _ _
        GradedObject.koszulBraidedCategory G) (_ : G.Additive) (_ : Functor.Linear ℚ G),
      Nonempty (ChowMotiveCat.h k ⋙ G ≅ T.cohomologyFunctor) :=
  ⟨T.motiveFunctor, WeilData.motiveFunctorBraided _ _ _, inferInstance, inferInstance,
    ⟨WeilData.motiveFunctorCohomologyIso _ _ _⟩⟩

end Stacks.WeilCohomology.WeilDataAxioms

end
