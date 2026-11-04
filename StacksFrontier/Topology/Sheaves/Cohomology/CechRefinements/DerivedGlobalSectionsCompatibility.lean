module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.ModuleComplexRefinementMap
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.DerivedSectionsScalarComparison

/-!
# The Čech refinement map and the Čech augmentation

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `U` be an open covering of `X`, let `V` be
an open covering of `Y` and let `c` be a refinement function, so that `U i ⊆ f⁻¹(V (c i))` for
every `i`.  For a sheaf of modules `F` on `X` the counit `f^* f_* F ⟶ F` of the adjunction is
an `f`-map, so it induces a Čech refinement map

`Č•(V, f_* F) ⟶ Č•(U, F)`

of complexes of `Γ(Y, 𝒪_Y)`-modules.  This file records that this map is compatible with the
Čech augmentations: the section of `f_* F` over `Y`, restricted to the opens `V j`, is carried
to the section of `F` over `X`, restricted to the opens `U i`.  This is the first commutative
square in the proof of [Stacks, Tag 01FD].

## Main results

* `Stacks.Cohomology.CechRefinement.cechDegreeZeroRestriction_pushforwardCounit`: the square in
  natural degrees, at degree zero.
* `Stacks.Cohomology.CechRefinement.cechAugmentationInt_pushforwardCounit`: the same square
  read in integer degrees.

## Implementation notes

Both squares are proved degreewise, against the projections of the defining product of the
degree-zero term of the Čech complex.  Because restriction of scalars has to be applied to the
Čech complex on `X`, those projections appear in the image of
`Stacks.Cohomology.restrictGlobalScalars`, and
`Stacks.CategoryTheory.CechComplex.hom_ext_map` is the resulting extensionality principle: it
is `Stacks.CategoryTheory.CechComplex.hom_ext` transported along
`Stacks.CategoryTheory.CechComplex.coefficientsIsoX`.

After the two degreewise formulas are applied, both sides are a section of `F` over the whole
of `X` restricted to a refined intersection, along the two routes through the slice over
`⊤`.  The slice over an open subset is thin, so the two routes are the same morphism and
functoriality of the sections presheaf finishes the square; the only genuine input is that the
counit acts on sections as the identity, which is
`Stacks.Cohomology.CechRefinement.sectionsRefinement_pushforwardCounit`.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf
  sectionsPresheafFunctor sectionsTerminalFunctorIso)
open Stacks.Cohomology.CechDerived (cechComplexNatFunctor cechComplexIntFunctor
  cechDegreeZeroRestriction cechDegreeZeroRestriction_comp_π cechAugmentationInt)
open RingedSpaceModuleAdjunction (modulePushforward modulePullback homEquiv)

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local implicit_reducible] structureSheafRing
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.sectionsPresheaf
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover
attribute [local implicit_reducible] Stacks.Cohomology.CechDerived.cechComplexNatFunctor
attribute [local implicit_reducible] Stacks.Cohomology.CechDerived.cechComplexIntFunctor
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.sectionsTerminalFunctor
attribute [local implicit_reducible] ComplexShape.Embedding.extendFunctor
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe vA vB vC uA uB uC uI u

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  {I : Type uI} [HasProducts.{uI} A] [HasProducts.{uI} B]
  (U : I → C) (P : Cᵒᵖ ⥤ A) (H : A ⥤ B) [H.Additive]
  [∀ n : ℕ, PreservesLimit
    (Discrete.functor fun x : Fin (n + 1) → I ↦ P.obj (op (inter U x))) H]

omit [H.Additive] in
/-- Two morphisms into the image under an additive functor `H` of a degree of a Čech complex
agree as soon as they agree after composing with the image under `H` of every projection.  This
is `Stacks.CategoryTheory.CechComplex.hom_ext` transported along
`Stacks.CategoryTheory.CechComplex.coefficientsIsoX`, and is what lets the squares of
[Stacks, Tag 01FD] be checked componentwise even though one side of them has had scalars
restricted. -/
theorem hom_ext_map {n : ℕ} {T : B}
    {u v : T ⟶ H.obj (((cechComplexFunctor U).obj P).X n)}
    (h : ∀ x, u ≫ H.map (π U P n x) = v ≫ H.map (π U P n x)) : u = v := by
  rw [← cancel_mono (coefficientsIsoX U P H n).hom]
  refine hom_ext U (P ⋙ H) fun x ↦ ?_
  rw [Category.assoc, Category.assoc, coefficientsIsoX_hom_comp_π]
  exact h x

end

end Stacks.CategoryTheory.CechComplex

namespace Stacks.Cohomology.CechRefinement

open Stacks.CategoryTheory.CechComplex

noncomputable section

attribute [local instance] ModuleCat.hasLimitsOfSize

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (F : Modules X)

/-- **The counit of the adjunction `f^* ⊣ f_*` as an `f`-map.**  This is the `f`-map
`f^* f_* F ⟶ F` to which the Čech refinement map of [Stacks, Tag 01FD] is applied when the
sheaf on the target is the pushforward of the sheaf on the source. -/
def pushforwardCounit : (modulePullback f).obj ((modulePushforward f).obj F) ⟶ F :=
  (homEquiv f F ((modulePushforward f).obj F)).symm (𝟙 _)

/-- **The counit acts on sections as the identity.**  The map on sections attached to an
`f`-map is the adjoint `f`-map followed by the identification of the sections of a pushforward,
and the adjoint of the counit is the identity, so for the counit only the identification
remains.  This is the one computational input to the squares of [Stacks, Tag 01FD] in which
the pushforward appears. -/
theorem sectionsRefinement_pushforwardCounit :
    sectionsRefinement f F ((modulePushforward f).obj F) (pushforwardCounit f F) =
      (pushforwardSectionsIso f F).hom := by
  dsimp only [sectionsRefinement, pushforwardCounit]
  rw [Equiv.apply_symm_apply, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- **Sections over the whole space agree with sections of the pushforward over the whole
space**, compatibly with the two identifications of sections at the terminal object of the
slice: all three maps are the identity on underlying sections.  This is the degenerate case of
`Stacks.Cohomology.CechRefinement.pushforwardSectionsIso` that the augmentation square of
[Stacks, Tag 01FD] needs. -/
theorem sectionsTerminalFunctorIso_inv_comp_pushforwardSectionsIso :
    (sectionsTerminalFunctorIso (R := ringCatSheaf Y) ⊤).inv.app
          ((modulePushforward f).obj F) ≫
        (pushforwardSectionsIso f F).hom.app
          (op (Over.mk (𝟙 (⊤ : Opens Y.carrier)))) =
      (restrictGlobalScalars f).map
        ((sectionsTerminalFunctorIso (R := ringCatSheaf X) ⊤).inv.app F) := by
  ext s
  rfl

variable {I J : Type u} (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
  (hU : ⊤ = ⨆ i, U i) (hV : ⊤ = ⨆ j, V j)
  (c : I → J) (hc : ∀ i, U i ≤ (Opens.map f.hom.base).obj (V (c i)))

/-- **The Čech refinement map of the counit is compatible with the degree-zero Čech
augmentations.**  Restricting a section of `f_* F` over `Y` to the opens `V j` and then
applying the refinement map gives the restrictions of the corresponding section of `F` over `X`
to the opens `U i`.  This is the first commutative square in the proof of
[Stacks, Tag 01FD]. -/
theorem cechDegreeZeroRestriction_pushforwardCounit :
    cechDegreeZeroRestriction (ringCatSheaf Y) ⊤ V hV
          ((modulePushforward f).obj F) ≫
        (cechComplexRefinementMap f F ((modulePushforward f).obj F)
          (pushforwardCounit f F) U V hU hV c hc).f 0 =
      (restrictGlobalScalars f).map
        (cechDegreeZeroRestriction (ringCatSheaf X) ⊤ U hU F) := by
  refine hom_ext_map (coverObject U hU) (sectionsPresheaf (⊤ : Opens X.carrier) F)
    (restrictGlobalScalars f) fun x ↦ ?_
  refine Eq.trans ?_ ((restrictGlobalScalars f).map_comp
    (cechDegreeZeroRestriction (ringCatSheaf X) ⊤ U hU F)
    (π (coverObject U hU) (sectionsPresheaf (⊤ : Opens X.carrier) F) 0 x))
  rw [cechDegreeZeroRestriction_comp_π (ringCatSheaf X) ⊤ U hU F x]
  conv_lhs => rw [Category.assoc, cechComplexRefinementMap_comp_map_π, ← Category.assoc,
    cechDegreeZeroRestriction_comp_π, sectionsRefinement_pushforwardCounit]
  have hthin : refinementInclusion f U V hU hV c hc 0 x ≫
      (sliceMap f).map (Over.mkIdTerminal.from (inter (coverObject V hV) (c ∘ x))) =
      Over.mkIdTerminal.from (inter (coverObject U hU) x) := Subsingleton.elim _ _
  have hcomp : ((sliceMap f).op ⋙ sectionsPresheaf (⊤ : Opens X.carrier) F ⋙
        restrictGlobalScalars f).map
        (Over.mkIdTerminal.from (inter (coverObject V hV) (c ∘ x))).op ≫
      (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙ restrictGlobalScalars f).map
        (refinementInclusion f U V hU hV c hc 0 x).op =
      (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙ restrictGlobalScalars f).map
        (Over.mkIdTerminal.from (inter (coverObject U hU) x)).op := by
    rw [show ((sliceMap f).op ⋙ sectionsPresheaf (⊤ : Opens X.carrier) F ⋙
          restrictGlobalScalars f).map
          (Over.mkIdTerminal.from (inter (coverObject V hV) (c ∘ x))).op =
        (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙ restrictGlobalScalars f).map
          ((sliceMap f).map
            (Over.mkIdTerminal.from (inter (coverObject V hV) (c ∘ x)))).op from rfl,
      ← CategoryTheory.Functor.map_comp, ← op_comp, hthin]
    rfl
  rw [Category.assoc,
    ← Category.assoc _ ((pushforwardSectionsIso f F).hom.app
      (op (inter (coverObject V hV) (c ∘ x)))) _,
    (pushforwardSectionsIso f F).hom.naturality
      (Over.mkIdTerminal.from (inter (coverObject V hV) (c ∘ x))).op,
    Category.assoc, hcomp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ (sectionsPresheaf (⊤ : Opens X.carrier) F ⋙
          restrictGlobalScalars f).map
          (Over.mkIdTerminal.from (inter (coverObject U hU) x)).op)
        (sectionsTerminalFunctorIso_inv_comp_pushforwardSectionsIso f F)).trans
      ((restrictGlobalScalars f).map_comp _ _).symm)

/-- **The Čech refinement map of the counit is compatible with the Čech augmentations, read in
integer degrees.**  This is `cechDegreeZeroRestriction_pushforwardCounit` after extension by
zero from natural to integer degrees, which is the form in which the first square of the proof
of [Stacks, Tag 01FD] is used. -/
theorem cechAugmentationInt_pushforwardCounit :
    cechAugmentationInt (ringCatSheaf Y) ⊤ V hV ((modulePushforward f).obj F) ≫
        (cechComplexRefinementMapInt f F ((modulePushforward f).obj F)
          (pushforwardCounit f F) U V hU hV c hc).f 0 =
      (restrictGlobalScalars f).map
        (cechAugmentationInt (ringCatSheaf X) ⊤ U hU F) := by
  have hmap : ((((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F)).extendXIso
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
        (Stacks.DerivedIndexing.mapExtendIso (restrictGlobalScalars f)
          ComplexShape.embeddingUpNat
          ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F)).hom.f 0 =
      (restrictGlobalScalars f).map
        (((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F).extendXIso
          ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv := by
    have key (o : Option ℕ) (ho : o = some 0) :
        (HomologicalComplex.extend.XIso
            (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F)) ho).inv ≫
          (Stacks.DerivedIndexing.mapExtendXIso (restrictGlobalScalars f)
            ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F) o).hom =
        (restrictGlobalScalars f).map
          (HomologicalComplex.extend.XIso
            ((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F) ho).inv := by
      subst ho
      simp only [Stacks.DerivedIndexing.mapExtendXIso, Iso.refl_hom,
        HomologicalComplex.extend.XIso, eqToIso.inv, eqToHom_map]
      rfl
    exact key _ (ComplexShape.embeddingUpNat.r_eq_some (i := 0) (i' := 0) rfl)
  dsimp only [cechAugmentationInt, cechComplexRefinementMapInt]
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl,
    Category.assoc, Category.assoc]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (cechDegreeZeroRestriction (ringCatSheaf Y) ⊤ V hV
    ((modulePushforward f).obj F) ≫ ·) (Iso.inv_hom_id_assoc _ _)).trans ?_
  refine (congrArg (cechDegreeZeroRestriction (ringCatSheaf Y) ⊤ V hV
    ((modulePushforward f).obj F) ≫ (cechComplexRefinementMap f F
      ((modulePushforward f).obj F) (pushforwardCounit f F) U V hU hV c hc).f 0 ≫ ·)
    hmap).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (restrictGlobalScalars f).map
    (((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj F).extendXIso
      ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv)
    (cechDegreeZeroRestriction_pushforwardCounit f F U V hU hV c hc)).trans ?_
  exact ((restrictGlobalScalars f).map_comp _ _).symm

end

end Stacks.Cohomology.CechRefinement

end
