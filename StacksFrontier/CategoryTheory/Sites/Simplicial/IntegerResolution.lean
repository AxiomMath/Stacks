module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Whiskering
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionBridgeCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentRestriction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormulaLegCocontinuous

/-!
# The integral resolution of the constant sheaf on a simplicial site

Let `S` be a simplicial-site situation. The lower shriek images `g_{n!} Z` of the constant sheaf
with value `Z` on the component site in simplicial degree `n` assemble into a simplicial abelian
sheaf on the total site, and the alternating-face complex
`… → g_{2!} Z → g_{1!} Z → g_{0!} Z` of that simplicial object is a resolution of the constant
sheaf with value `Z` on the total site.

The simplicial object is produced as the sheafification of the free abelian presheaf on the
presheaf of simplices: over an object of the total category lying in degree `k`, the degree-`n`
term has the simplex maps `[n] ⟶ [k]` as a basis. Mathlib's extra degeneracy on the free abelian
standard simplex gives exactness in every positive degree and at degree zero objectwise, and
sheafification preserves both. The degreewise identification with `g_{n!} Z` comes from the sum
formula of Stacks 09WG: restricted to degree `m`, both sides are the direct sum over the simplex
maps `[n] ⟶ [m]` of the constant sheaf, with matching summand inclusions.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentIntegerSheaf` and `.totalIntegerSheaf`: the
  lower shriek image of the constant integer sheaf of a component, and the constant integer sheaf
  of the total site.
* `CategoryTheory.constantIntegerRestriction` and `CategoryTheory.constantIntegerPullback`: the
  two canonical comparisons of constant integer sheaves along a site functor, induced by the
  sheafification unit.
* `CategoryTheory.SimplicialSiteSituation.transitionInverseImageForgetComparison`: the comparison
  of the inverse image along a simplicial transition with its abelian counterpart, on underlying
  sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.SummandForgetCompatibility`: the statement identifying
  the summand inclusions of the sum formula of Stacks 09WG on underlying sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.SimplicialIntegerResolution`: a simplicial abelian
  sheaf together with its degreewise identifications with the lower shriek images, its canonical
  transition comparisons, and its exact augmentation.

## Main results

* `CategoryTheory.SimplicialSiteSituation.summandForgetCompatibility`: the summand inclusions of
  the sum formula of Stacks 09WG on underlying sheaves of sets, in both cases of Stacks 09WE.
* `CategoryTheory.SimplicialSiteSituation.simplicialIntegerResolution`: **Stacks 09WI**, the
  resolution itself.
* `CategoryTheory.SimplicialSiteSituation.simplicialIntegerComplex`: its alternating-face chain
  complex.

## Implementation notes

The degreewise identification with `g_{n!} Z` uses the summand inclusions of the sum formula of
Stacks 09WG on underlying sheaves of sets, which is
`CategoryTheory.SimplicialSiteSituation.summandForgetCompatibility`. The sum formula
`CategoryTheory.SimplicialSiteSituation.componentLowerShriekRestrictionIsoCoproduct` is an opaque
isomorphism; its summand inclusions are identified with the canonical maps
`CategoryTheory.SimplicialSiteSituation.componentSumFormulaLeg` in each of the two cases of
Stacks 09WE. From there the underlying-set form follows by transposing along the morphism of topoi
of the transition in case (A), where both direct images are precomposition with the transition
functor, and by comparing after the sheafification unit in case (B), where both inverse images are
sheafified restrictions of presheaves.

The membership conditions on a `SimplicialIntegerResolution` — that the transition comparison is
the one induced by the sheafification unit, that the `i`th face map is the inclusion of the
summand labelled by the coface `δ i`, and that the augmentation is adjoint to restriction of the
integer generator to degree zero — pin down the integer generator and exclude sign-twisted
resolutions, which an unconstrained simplicial object with exact augmentation would not.

The integers are lifted to the universe of the component sites, so that the coefficients are
abelian groups in that universe and sheafification is available on every component and on the
total site with no extra hypothesis.

## References

* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory

/-- The constant sheaf of integers on a site: the sheafification of the constant presheaf with
value the integers, lifted to the universe of the site. -/
@[sga "4 IV 11.1.5"]
abbrev integerSheaf {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] : Sheaf J Ab.{u} :=
  (presheafToSheaf J Ab.{u}).obj
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- The constant sheaf of integers is the value of the constant sheaf functor at the
integers. -/
theorem integerSheaf_eq {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] :
    integerSheaf J = (constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  rfl

/-- Transposing a map of presheaves followed by the sheafification unit across the
sheafification adjunction gives the sheafification of that map. -/
theorem homEquiv_symm_comp_toSheafify {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u}] {P Q : Cᵒᵖ ⥤ Ab.{u}} (η : P ⟶ Q) :
    ((sheafificationAdjunction J Ab.{u}).homEquiv P ((presheafToSheaf J Ab.{u}).obj Q)).symm
        (η ≫ toSheafify J Q) = (presheafToSheaf J Ab.{u}).map η := by
  apply ((sheafificationAdjunction J Ab.{u}).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
  exact (sheafificationAdjunction J Ab.{u}).unit.naturality η

/-- The canonical restriction of a constant sheaf along a continuous functor. It is induced
by the sheafification unit of the constant presheaf, hence sends the integer generator to
the integer generator. -/
noncomputable def constantIntegerRestriction
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}] :
    integerSheaf J ⟶
      (F.sheafPushforwardContinuous Ab.{u} J K).obj
        (integerSheaf K) :=
  ((sheafificationAdjunction J Ab.{u}).homEquiv _ _).symm
    (((Functor.constCompWhiskeringLeftIso Cᵒᵖ F.op).app
      (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
      Functor.whiskerLeft F.op (toSheafify K
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))))

/-- The canonical map from the constant integer sheaf into the sheafification of the
restriction of a constant integer sheaf. -/
noncomputable def constantIntegerPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}] :
    integerSheaf J ⟶
      (presheafToSheaf J Ab.{u}).obj
        (F.op ⋙ (integerSheaf K).obj) :=
  ((sheafificationAdjunction J Ab.{u}).homEquiv _ _).symm
    (((Functor.constCompWhiskeringLeftIso Cᵒᵖ F.op).app
      (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
      Functor.whiskerLeft F.op (toSheafify K
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ≫
      toSheafify J
        (F.op ⋙ (integerSheaf K).obj))


namespace SimplicialSiteSituation

/-- Abelian sheaves on a component site have coproducts indexed by any type in the base
universe. -/
instance hasColimitsOfShape_discrete_sheafComponent {I : Type} (S : SimplicialSiteSituation.{u})
    (m : SimplexCategory) :
    HasColimitsOfShape (Discrete I) (Sheaf (S.componentTopology m) Ab.{u}) :=
  haveI : HasColimitsOfSize.{0, 0} Ab.{u} := inferInstance
  haveI : HasColimitsOfSize.{0, 0} (Sheaf (S.componentTopology m) Ab.{u}) := inferInstance
  HasColimitsOfSize.has_colimits_of_shape _

/-- Functors between the categories of abelian sheaves on two component sites have coproducts
indexed by any type in the base universe. -/
instance hasColimitsOfShape_discrete_sheafComponentFunctor {I : Type}
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) :
    HasColimitsOfShape (Discrete I)
      (Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf (S.componentTopology m) Ab.{u}) :=
  haveI : HasColimitsOfSize.{0, 0} Ab.{u} := inferInstance
  haveI : HasColimitsOfSize.{0, 0} (Sheaf (S.componentTopology m) Ab.{u}) := inferInstance
  haveI : HasColimitsOfSize.{0, 0}
      (Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf (S.componentTopology m) Ab.{u}) :=
    inferInstance
  HasColimitsOfSize.has_colimits_of_shape _

/-- The inverse images along the simplicial transitions from degree `n` to degree `m`, indexed by
the simplex maps `[n] ⟶ [m]`, admit a coproduct. -/
instance hasCoproduct_transitionInverseImageAb (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} :
    HasCoproduct (fun φ : n ⟶ m => transitionInverseImageAb S φ) :=
  HasColimitsOfShape.has_colimit _


/-- The inclusion of the degree-`n` component into the total category lands in degree `n`. -/
private theorem totalSimplexDegree_component (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    componentFunctor S n ⋙ totalSimplexDegree S = (Functor.const _).obj (Opposite.op n) := by
  cases S with
  | mk c => cases c with
    | inl C => exact Pseudofunctor.CoGrothendieck.comp_const C.totalPseudofunctor (Opposite.op n)
    | inr C => exact Functor.hext (fun _ => rfl) fun _ _ _ => HEq.rfl

/-- The inclusion of the degree-`n` component into the total category lands in degree `n`. -/
alias totalSimplexDegree_component' := totalSimplexDegree_component

/-- The presheaf of `n`-simplices on the total category: over an object lying in degree `k` its
sections are the simplex maps `[n] ⟶ [k]`. -/
def stdSimplexPresheaf' (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    S.totalCategoryᵒᵖ ⥤ Type u :=
  (totalSimplexDegree S).op ⋙ CategoryTheory.unopUnop SimplexCategory ⋙ SSet.stdSimplex ⋙
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op n)

/-- Restricted to the degree-`n` component, the presheaf of `k`-simplices is constant with value
the `k`-simplices of the standard `n`-simplex. -/
theorem stdSimplexPresheaf_restrict' (S : SimplicialSiteSituation.{u})
    (n k : SimplexCategory) :
    (componentFunctor S n).op ⋙ stdSimplexPresheaf' S k =
      (Functor.const _).obj ((SSet.stdSimplex.obj n).obj (Opposite.op k)) := by
  cases S with
  | mk c => cases c with
    | inl C =>
      show (((componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n ⋙
        totalSimplexDegree ⟨Sum.inl C⟩).op ⋙ CategoryTheory.unopUnop SimplexCategory) ⋙
        SSet.stdSimplex ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op k)) = _
      rw [totalSimplexDegree_component']
      apply Functor.hext
      · intro X
        simp [CategoryTheory.unopUnop]
      · intro X Y f
        simp [CategoryTheory.unopUnop]
    | inr C =>
      show (((componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⋙
        totalSimplexDegree ⟨Sum.inr C⟩).op ⋙ CategoryTheory.unopUnop SimplexCategory) ⋙
        SSet.stdSimplex ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op k)) = _
      rw [totalSimplexDegree_component']
      apply Functor.hext
      · intro X
        simp [CategoryTheory.unopUnop]
      · intro X Y f
        simp [CategoryTheory.unopUnop]

/-- The map of simplex presheaves induced by a simplex map, by precomposing simplices with it. -/
def stdSimplexPresheafMap' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    stdSimplexPresheaf' S m ⟶ stdSimplexPresheaf' S n :=
  Functor.whiskerLeft ((totalSimplexDegree S).op ⋙ CategoryTheory.unopUnop SimplexCategory ⋙
    SSet.stdSimplex) ((evaluation SimplexCategoryᵒᵖ (Type u)).map φ.op)

/-- The simplex presheaf map of an identity is the identity. -/
theorem stdSimplexPresheafMap_id' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : stdSimplexPresheafMap' S (𝟙 n) = 𝟙 _ := by
  ext X x
  simp [stdSimplexPresheafMap', stdSimplexPresheaf']

/-- The simplex presheaf map of a composite is the composite of the two maps in the reverse
order. -/
theorem stdSimplexPresheafMap_comp' (S : SimplicialSiteSituation.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    stdSimplexPresheafMap' S (φ ≫ ψ) =
      stdSimplexPresheafMap' S ψ ≫ stdSimplexPresheafMap' S φ := by
  ext X x
  simp [stdSimplexPresheafMap', stdSimplexPresheaf', ← Functor.map_comp]

/-- The free abelian presheaf on a presheaf of sets, formed objectwise. -/
def freeAbPresheaf' (C : Type u) [Category.{u} C] :
    (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free

/-- The free abelian presheaf on the presheaf of `n`-simplices. -/
def stdSimplexPresheafAb' (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (freeAbPresheaf' S.totalCategory).obj (stdSimplexPresheaf' S n)

/-- The map of free abelian simplex presheaves induced by a simplex map. -/
def stdSimplexPresheafAbMap' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    stdSimplexPresheafAb' S m ⟶ stdSimplexPresheafAb' S n :=
  (freeAbPresheaf' S.totalCategory).map (stdSimplexPresheafMap' S φ)

/-- On a basis element the free abelian simplex presheaf map is the simplex presheaf map. -/
theorem stdSimplexPresheafAbMap_generator' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (X : S.totalCategoryᵒᵖ)
    (x : (stdSimplexPresheaf' S m).obj X) :
    ((stdSimplexPresheafAbMap' S φ).app X).hom (FreeAbelianGroup.of x) =
      FreeAbelianGroup.of ((stdSimplexPresheafMap' S φ).app X x) := by
  show FreeAbelianGroup.map
    (fun y => (stdSimplexPresheafMap' S φ).app X y) (FreeAbelianGroup.of x) = _
  exact FreeAbelianGroup.map_of_apply x

/-- The free abelian simplex presheaf map of an identity is the identity. -/
theorem stdSimplexPresheafAbMap_id' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : stdSimplexPresheafAbMap' S (𝟙 n) = 𝟙 _ := by
  dsimp [stdSimplexPresheafAbMap', freeAbPresheaf', stdSimplexPresheafAb']
  rw [stdSimplexPresheafMap_id', Functor.whiskerRight_id']

/-- The free abelian simplex presheaf map of a composite is the composite in the reverse order. -/
theorem stdSimplexPresheafAbMap_comp' (S : SimplicialSiteSituation.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    stdSimplexPresheafAbMap' S (φ ≫ ψ) =
      stdSimplexPresheafAbMap' S ψ ≫ stdSimplexPresheafAbMap' S φ := by
  dsimp [stdSimplexPresheafAbMap', freeAbPresheaf', stdSimplexPresheafAb']
  rw [stdSimplexPresheafMap_comp', Functor.whiskerRight_comp]

/-- The simplicial abelian presheaf on the total category whose degree-`n` term is the free abelian
presheaf on the `n`-simplices. -/
noncomputable def presheafSimplicial' (S : SimplicialSiteSituation.{u}) :
    SimplicialObject (S.totalCategoryᵒᵖ ⥤ Ab.{u}) where
  obj n := stdSimplexPresheafAb' S n.unop
  map φ := stdSimplexPresheafAbMap' S φ.unop
  map_id n := stdSimplexPresheafAbMap_id' S n.unop
  map_comp φ ψ := stdSimplexPresheafAbMap_comp' S ψ.unop φ.unop

/-- The simplicial abelian sheaf on the total site obtained by sheafifying the simplicial abelian
presheaf of simplices degreewise. -/
noncomputable def resolutionSimplicial' (S : SimplicialSiteSituation.{u}) :
    SimplicialObject (Sheaf S.totalTopology Ab.{u}) :=
  presheafSimplicial' S ⋙ presheafToSheaf S.totalTopology Ab.{u}

/-- The degree-`n` term of the simplicial abelian sheaf of simplices is the sheafification of the
free abelian presheaf on the presheaf of `n`-simplices. -/
theorem resolutionSimplicial_obj (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    (resolutionSimplicial' S).obj (Opposite.op n) =
      (presheafToSheaf S.totalTopology Ab.{u}).obj (stdSimplexPresheafAb' S n) :=
  rfl

/-- The augmented simplicial abelian group freely generated by the augmented standard
`k`-simplex. -/
private noncomputable def freeStandardSimplexAug (k : SimplexCategory) :
    SimplicialObject.Augmented Ab.{u} :=
  (SimplicialObject.Augmented.whiskeringObj (Type u) Ab.{u}
    AddCommGrpCat.free).obj (SSet.Augmented.stdSimplex.obj k)

/-- The extra degeneracy of the free abelian augmented standard simplex, carried over from the
standard simplex itself. -/
private noncomputable def freeStandardSimplexExtra (k : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (freeStandardSimplexAug k) :=
  (SSet.Augmented.StandardSimplex.extraDegeneracy k).map AddCommGrpCat.free

/-- The alternating-face complex of the free abelian standard simplex is exact in every positive
degree. -/
private theorem freeStandardSimplex_exact_positive (k : SimplexCategory)
    (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (freeStandardSimplexAug k).left).ExactAt n := by
  let e := (freeStandardSimplexExtra k).homotopyEquiv
  have : QuasiIso e.hom := e.quasiIso_hom
  show (AlgebraicTopology.AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj (freeStandardSimplexAug k))).ExactAt n
  rw [exactAt_iff_of_quasiIsoAt e.hom n]
  exact HomologicalComplex.exactAt_single_obj _ 0 _ n (by omega)

/-- A short complex in an abelian category is exact as soon as the identity of its middle term is a
retraction of its first map plus a section of its second. -/
private theorem exact_of_contracting_identity
    {C : Type*} [Category* C] [Abelian C] (complex : ShortComplex C)
    (backward : complex.X₂ ⟶ complex.X₁) (sectionMap : complex.X₃ ⟶ complex.X₂)
    (identity : backward ≫ complex.f + complex.g ≫ sectionMap = 𝟙 complex.X₂) :
    complex.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  calc
    kernel.ι complex.g ≫ cokernel.π complex.f =
        kernel.ι complex.g ≫ (𝟙 complex.X₂) ≫ cokernel.π complex.f := by simp
    _ = kernel.ι complex.g ≫
        (backward ≫ complex.f + complex.g ≫ sectionMap) ≫ cokernel.π complex.f := by
      rw [identity]
    _ = 0 := by
      simp [Preadditive.add_comp, Category.assoc,
        ← Category.assoc (kernel.ι complex.g) complex.g]

/-- The alternating-face complex of the free abelian standard simplex is exact at degree zero
against its augmentation. -/
@[sga "4 Vbis 2.3.9" "partial"]
private theorem freeStandardSimplex_exact_zero (k : SimplexCategory) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (freeStandardSimplexAug k).left).d 1 0)
      ((freeStandardSimplexAug k).hom.app (Opposite.op ⦋0⦌))
      (by
        exact ((ChainComplex.toSingle₀Equiv _ _)
          (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
            (freeStandardSimplexAug k))).property)).Exact := by
  let extra := freeStandardSimplexExtra k
  let differential : (freeStandardSimplexAug k).left.obj (Opposite.op ⦋1⦌) ⟶
      (freeStandardSimplexAug k).left.obj (Opposite.op ⦋0⦌) :=
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (freeStandardSimplexAug k).left).d 1 0
  have identity :
      (extra.s 0 ≫ differential : (freeStandardSimplexAug k).left.obj (Opposite.op ⦋0⦌) ⟶
        (freeStandardSimplexAug k).left.obj (Opposite.op ⦋0⦌)) +
      ((freeStandardSimplexAug k).hom.app (Opposite.op ⦋0⦌) ≫ extra.s' :
        (freeStandardSimplexAug k).left.obj (Opposite.op ⦋0⦌) ⟶
          (freeStandardSimplexAug k).left.obj (Opposite.op ⦋0⦌)) = 𝟙 _ := by
    dsimp only [differential]
    rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
      AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
      Preadditive.comp_add, Preadditive.comp_neg]
    rw [extra.s_comp_δ₀, extra.s₀_comp_δ₁]
    simp
  exact exact_of_contracting_identity _ (extra.s 0) extra.s' identity

/-- The free abelian group on a one-point set is the group of integers. -/
noncomputable def freeUnitIntegerIso' :
    AddCommGrpCat.free.{u}.obj PUnit.{u + 1} ≅ AddCommGrpCat.of (ULift.{u} ℤ) := by
  let e : FreeAbelianGroup PUnit.{u + 1} ≃+ ULift.{u} ℤ :=
    (FreeAbelianGroup.uniqueEquiv PUnit.{u + 1}).trans AddEquiv.ulift.symm
  refine ⟨AddCommGrpCat.ofHom e.toAddMonoidHom,
    AddCommGrpCat.ofHom e.symm.toAddMonoidHom, ?_, ?_⟩
  · ext x
    exact e.symm_apply_apply x
  · ext x
    exact congrArg ULift.down (e.apply_symm_apply x)

/-- The identification of the free abelian group on a point with the integers carries the basis
element to `1`. -/
private theorem freeUnitIntegerIso_generator' :
    (freeUnitIntegerIso'.{u}).hom.hom (FreeAbelianGroup.of PUnit.unit) = ULift.up 1 := by
  show ((FreeAbelianGroup.uniqueEquiv PUnit.{u + 1}).trans AddEquiv.ulift.symm)
    (FreeAbelianGroup.of PUnit.unit) = _
  simp [FreeAbelianGroup.uniqueEquiv, FreeAbelianGroup.lift_apply_of]
  rfl

/-- The unique map from the presheaf of `n`-simplices to the constant presheaf with value a
point. -/
def stdSimplexPresheafToPoint' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
  stdSimplexPresheaf' S n ⟶ (Functor.const S.totalCategoryᵒᵖ).obj PUnit.{u + 1} :=
  { app := fun _ => ↾(fun _ : _ => (PUnit.unit : PUnit.{u + 1}))
    naturality := by intros; rfl }

/-- The free abelian presheaf on a constant presheaf is constant, with value the free abelian group
on its value. -/
noncomputable def freeAbPresheafConstIso' (C : Type u) [Category.{u} C] :
    (freeAbPresheaf' C).obj ((Functor.const Cᵒᵖ).obj PUnit.{u + 1}) ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.free.obj PUnit.{u + 1}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros X Y f
    ext x
    change FreeAbelianGroup.map (fun y : PUnit.{u + 1} => y) x = x
    exact FreeAbelianGroup.map_id_apply x)

/-- The augmentation of the free abelian `n`-simplex presheaf to the constant integer presheaf,
sending every simplex to `1`. -/
noncomputable def stdSimplexPresheafAbAugmentation'
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    stdSimplexPresheafAb' S n ⟶
      (Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (freeAbPresheaf' S.totalCategory).map (stdSimplexPresheafToPoint' S n) ≫
    (freeAbPresheafConstIso' S.totalCategory).hom ≫
    (Functor.const S.totalCategoryᵒᵖ).map (freeUnitIntegerIso'.{u}).hom

/-- The augmentation sends each basis element of the free abelian simplex presheaf to `1`. -/
private theorem stdSimplexPresheafAbAugmentation_generator'
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (X : S.totalCategoryᵒᵖ) (x : (stdSimplexPresheaf' S n).obj X) :
    ((stdSimplexPresheafAbAugmentation' S n).app X).hom (FreeAbelianGroup.of x) =
      ULift.up 1 := by
  show (freeUnitIntegerIso'.{u}).hom.hom (FreeAbelianGroup.of PUnit.unit) = _
  exact freeUnitIntegerIso_generator'

/-- The augmentation of the free abelian simplex presheaf is an epimorphism. -/
private theorem stdSimplexPresheafAbAugmentation_epi'
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    Epi (stdSimplexPresheafAbAugmentation' S n) := by
  let : ∀ X, Epi ((stdSimplexPresheafAbAugmentation' S n).app X) := by
    intro X
    apply ConcreteCategory.epi_of_surjective
    intro z
    let k : SimplexCategory := ((totalSimplexDegree S).obj X.unop).unop
    let x : (stdSimplexPresheaf' S n).obj X := by
      dsimp [stdSimplexPresheaf', k]
      exact SSet.stdSimplex.objEquiv.symm (SimplexCategory.const n k 0)
    refine ⟨z.down • FreeAbelianGroup.of x, ?_⟩
    apply ULift.ext
    show (((stdSimplexPresheafAbAugmentation' S n).app X).hom
      (z.down • FreeAbelianGroup.of x)).down = z.down
    exact (congrArg ULift.down (((stdSimplexPresheafAbAugmentation' S n).app X).hom.map_zsmul
      z.down (FreeAbelianGroup.of x))).trans
        (by rw [stdSimplexPresheafAbAugmentation_generator']; simp)
  exact NatTrans.epi_of_epi_app (stdSimplexPresheafAbAugmentation' S n)

/-- The simplicial maps of the free abelian simplex presheaves are compatible with their
augmentations. -/
private theorem stdSimplexPresheafAbMap_augmentation' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    stdSimplexPresheafAbMap' S φ ≫ stdSimplexPresheafAbAugmentation' S n =
      stdSimplexPresheafAbAugmentation' S m := by
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  show ((stdSimplexPresheafAbAugmentation' S n).app X).hom
      (((stdSimplexPresheafAbMap' S φ).app X).hom (FreeAbelianGroup.of x)) =
    ((stdSimplexPresheafAbAugmentation' S m).app X).hom (FreeAbelianGroup.of x)
  rw [stdSimplexPresheafAbMap_generator', stdSimplexPresheafAbAugmentation_generator',
    stdSimplexPresheafAbAugmentation_generator']

/-- The lower shriek image on the total site of the constant integer sheaf in degree `n`. -/
noncomputable abbrev componentIntegerSheaf (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : Sheaf S.totalTopology Ab.{u} :=
  (Functor.sheafPullbackConstruction.sheafPullback
      (componentFunctor S n) Ab.{u} (S.componentTopology n) S.totalTopology).obj
    (integerSheaf (S.componentTopology n))

/-- The constant integer sheaf on the total site. -/
noncomputable abbrev totalIntegerSheaf (S : SimplicialSiteSituation.{u}) :
    Sheaf S.totalTopology Ab.{u} :=
  integerSheaf S.totalTopology

/-- The augmentation of the degree-`n` term of the simplicial resolution to the constant integer
sheaf on the total site. -/
noncomputable def resolutionTermAugmentation' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : (resolutionSimplicial' S).obj (Opposite.op n) ⟶
      totalIntegerSheaf S := by
  change (presheafToSheaf S.totalTopology AddCommGrpCat.{u}).obj
      (stdSimplexPresheafAb' S n) ⟶
    (presheafToSheaf S.totalTopology AddCommGrpCat.{u}).obj
      ((Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
  exact (presheafToSheaf S.totalTopology AddCommGrpCat.{u}).map
    (stdSimplexPresheafAbAugmentation' S n)

/-- The simplicial maps of the resolution are compatible with the augmentations of its terms. -/
private theorem resolutionSimplicialMap_termAugmentation'
    (S : SimplicialSiteSituation.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    (resolutionSimplicial' S).map φ.op ≫ resolutionTermAugmentation' S n =
      resolutionTermAugmentation' S m := by
  show (presheafToSheaf S.totalTopology AddCommGrpCat.{u}).map
      (stdSimplexPresheafAbMap' S φ) ≫
      (presheafToSheaf S.totalTopology AddCommGrpCat.{u}).map
        (stdSimplexPresheafAbAugmentation' S n) =
    (presheafToSheaf S.totalTopology AddCommGrpCat.{u}).map
      (stdSimplexPresheafAbAugmentation' S m)
  rw [← Functor.map_comp, stdSimplexPresheafAbMap_augmentation']

/-- The augmentation of the alternating-face complex of the resolution, in degree zero. -/
noncomputable def resolutionAugmentation' (S : SimplicialSiteSituation.{u}) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (resolutionSimplicial' S)).X 0 ⟶ totalIntegerSheaf S := by
  change (resolutionSimplicial' S).obj (Opposite.op ⦋0⦌) ⟶ totalIntegerSheaf S
  exact resolutionTermAugmentation' S ⦋0⦌

/-- The augmentation of the resolution is an epimorphism. -/
theorem resolutionAugmentation_epi' (S : SimplicialSiteSituation.{u}) :
    Epi (resolutionAugmentation' S) := by
  show Epi ((presheafToSheaf S.totalTopology AddCommGrpCat.{u}).map
    (stdSimplexPresheafAbAugmentation' S ⦋0⦌))
  let : Epi (stdSimplexPresheafAbAugmentation' S ⦋0⦌) :=
    stdSimplexPresheafAbAugmentation_epi' S ⦋0⦌
  exact Functor.map_epi (presheafToSheaf S.totalTopology AddCommGrpCat.{u})
    (stdSimplexPresheafAbAugmentation' S ⦋0⦌)

/-- The augmentation of the resolution annihilates the first differential of the alternating-face
complex. -/
theorem resolutionAugmentation_comp' (S : SimplicialSiteSituation.{u}) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (resolutionSimplicial' S)).d 1 0 ≫ resolutionAugmentation' S = 0 := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  show ((resolutionSimplicial' S).map (SimplexCategory.δ (0 : Fin 2)).op +
      -((resolutionSimplicial' S).map (SimplexCategory.δ (1 : Fin 2)).op)) ≫
      resolutionTermAugmentation' S ⦋0⦌ = 0
  rw [CategoryTheory.Preadditive.add_comp, CategoryTheory.Preadditive.neg_comp]
  rw [resolutionSimplicialMap_termAugmentation' S (SimplexCategory.δ (0 : Fin 2)),
    resolutionSimplicialMap_termAugmentation' S (SimplexCategory.δ (1 : Fin 2))]
  simp

/-- Evaluated at an object of degree `k`, the simplicial abelian presheaf of simplices is the free
abelian simplicial group on the standard `k`-simplex. -/
private noncomputable def presheafSimplicialEvaluationIso'
    (S : SimplicialSiteSituation.{u}) (X : S.totalCategoryᵒᵖ) :
    presheafSimplicial' S ⋙ (evaluation _ Ab.{u}).obj X ≅
      (freeStandardSimplexAug (((totalSimplexDegree S).obj X.unop).unop)).left :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The augmentation of the simplicial abelian presheaf of simplices annihilates the first
differential. -/
private theorem presheafAugmentation_comp' (S : SimplicialSiteSituation.{u}) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (presheafSimplicial' S)).d 1 0 ≫ stdSimplexPresheafAbAugmentation' S ⦋0⦌ = 0 := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  show (stdSimplexPresheafAbMap' S (SimplexCategory.δ (0 : Fin 2)) +
      -(stdSimplexPresheafAbMap' S (SimplexCategory.δ (1 : Fin 2)))) ≫
      stdSimplexPresheafAbAugmentation' S ⦋0⦌ = 0
  rw [Preadditive.add_comp, Preadditive.neg_comp,
    stdSimplexPresheafAbMap_augmentation', stdSimplexPresheafAbMap_augmentation']
  simp

/-- The alternating-face complex of the simplicial abelian presheaf of simplices is exact at degree
zero against its augmentation. -/
private theorem presheafSimplicial_exact_zero' (S : SimplicialSiteSituation.{u}) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (presheafSimplicial' S)).d 1 0)
      (stdSimplexPresheafAbAugmentation' S ⦋0⦌)
      (presheafAugmentation_comp' S)).Exact := by
  let reflect : JointlyReflectIsomorphisms
      (fun X : S.totalCategoryᵒᵖ => (evaluation _ Ab.{u}).obj X) :=
    ⟨fun φ h => by
      let : ∀ X, IsIso (φ.app X) := h
      exact NatIso.isIso_of_isIso_app φ⟩
  apply (reflect.exact_iff _).2
  intro X
  let degree := (((totalSimplexDegree S).obj X.unop).unop)
  let comparison :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      ((evaluation _ Ab.{u}).obj X)).app (presheafSimplicial' S) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (presheafSimplicialEvaluationIso' S X)
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk
      (HomologicalComplex.Hom.isoApp comparison.symm 1)
      (HomologicalComplex.Hom.isoApp comparison.symm 0)
      (by
        show AddCommGrpCat.free.obj (⊤_ (Type u)) ≅ AddCommGrpCat.of (ULift.{u} ℤ)
        exact AddCommGrpCat.free.mapIso Types.terminalIso ≪≫ freeUnitIntegerIso')
      ?_ ?_) (freeStandardSimplex_exact_zero degree)
  · exact comparison.inv.comm 1 0
  · apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro simplex
    exact (stdSimplexPresheafAbAugmentation_generator' S ⦋0⦌ X simplex).symm

/-- The alternating-face complex of the simplicial abelian presheaf of simplices is exact in every
positive degree. -/
private theorem presheafSimplicial_exact_positive'
    (S : SimplicialSiteSituation.{u}) (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (presheafSimplicial' S)).ExactAt n := by
  let reflect : JointlyReflectIsomorphisms
      (fun X : S.totalCategoryᵒᵖ => (evaluation _ Ab.{u}).obj X) :=
    ⟨fun φ h => by
      let : ∀ X, IsIso (φ.app X) := h
      exact NatIso.isIso_of_isIso_app φ⟩
  apply (reflect.exactAt_iff _ n).2
  intro X
  let comparison :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      ((evaluation _ Ab.{u}).obj X)).app (presheafSimplicial' S) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (presheafSimplicialEvaluationIso' S X)
  exact (freeStandardSimplex_exact_positive _ n hn).of_iso comparison.symm

/-- The alternating-face complex of the simplicial abelian sheaf of simplices is exact in every
positive degree. -/
theorem resolutionSimplicial_exact_positive'
    (S : SimplicialSiteSituation.{u}) (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (resolutionSimplicial' S)).ExactAt n := by
  let comparison :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (presheafToSheaf S.totalTopology Ab.{u})).app (presheafSimplicial' S)
  apply HomologicalComplex.ExactAt.of_iso _ comparison
  exact (presheafSimplicial_exact_positive' S n hn).map
    (presheafToSheaf S.totalTopology Ab.{u})

/-- The alternating-face complex of the simplicial abelian sheaf of simplices is exact at degree
zero against its augmentation. -/
theorem resolutionSimplicial_exact_zero' (S : SimplicialSiteSituation.{u}) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (resolutionSimplicial' S)).d 1 0)
      (resolutionAugmentation' S) (resolutionAugmentation_comp' S)).Exact := by
  let comparison :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (presheafToSheaf S.totalTopology Ab.{u})).app (presheafSimplicial' S)
  show (ShortComplex.mk _
    ((presheafToSheaf S.totalTopology Ab.{u}).map
      (stdSimplexPresheafAbAugmentation' S ⦋0⦌)) _).Exact
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (presheafSimplicial' S)).d 1 0)
      (stdSimplexPresheafAbAugmentation' S ⦋0⦌)
      (presheafAugmentation_comp' S)).map
        (presheafToSheaf S.totalTopology Ab.{u}))
      (S₂ := ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (resolutionSimplicial' S)).d 1 0)
      (resolutionAugmentation' S) (resolutionAugmentation_comp' S))
      (HomologicalComplex.Hom.isoApp comparison 1)
      (HomologicalComplex.Hom.isoApp comparison 0)
      (Iso.refl _) ?_ ?_)
    ((presheafSimplicial_exact_zero' S).map (presheafToSheaf S.totalTopology Ab.{u}))
  · exact comparison.hom.comm 1 0
  · simp only [comparison, resolutionSimplicial', resolutionAugmentation',
      resolutionTermAugmentation', Category.comp_id, Iso.refl_hom]
    exact rfl

/-- Restriction along a cocontinuous functor carries a local isomorphism of abelian presheaves to a
local isomorphism. -/
private theorem localEquivalence_whiskerLeft
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsCocontinuous J K] {first second : Dᵒᵖ ⥤ Ab.{u}}
    (morphism : first ⟶ second) (localEquivalence : K.W morphism) :
    J.W (Functor.whiskerLeft F.op morphism) := by
  intro sheaf sheafCondition
  show Function.Bijective (fun transformation : F.op ⋙ second ⟶ sheaf =>
    Functor.whiskerLeft F.op morphism ≫ transformation)
  exact ((F.op.ranAdjunction Ab.{u}).map_comp_bijective_iff morphism sheaf).2
    (localEquivalence _
      (ran_isSheaf_of_isCocontinuous F K ⟨sheaf, sheafCondition⟩))

/-- Along a cocontinuous functor the canonical map of constant integer sheaves is an
isomorphism. -/
private theorem constantIntegerPullback_isIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsCocontinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}] :
    IsIso (constantIntegerPullback F J K) := by
  have localEquivalence := localEquivalence_whiskerLeft F J K
    (toSheafify K ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))))
    (K.W_toSheafify _)
  let : IsIso ((presheafToSheaf J Ab.{u}).map
      (Functor.whiskerLeft F.op
        (toSheafify K ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))))) :=
    (J.W_iff _).1 localEquivalence
  have equality : constantIntegerPullback F J K =
      (presheafToSheaf J Ab.{u}).map
        (((Functor.constCompWhiskeringLeftIso Cᵒᵖ F.op).app
          (AddCommGrpCat.of (ULift.{u} ℤ))).inv) ≫
      (presheafToSheaf J Ab.{u}).map
        (Functor.whiskerLeft F.op
          (toSheafify K ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))))) := by
    apply ((sheafificationAdjunction J Ab.{u}).homEquiv _ _).injective
    rw [constantIntegerPullback, Equiv.apply_symm_apply, ← Functor.map_comp,
      Adjunction.homEquiv_unit]
    simpa only [Functor.id_map, Functor.comp_map, Category.assoc,
      sheafificationAdjunction_unit_app, constantSheaf, sheafify,
      Functor.comp_obj] using
      ((sheafificationAdjunction J Ab.{u}).unit.naturality
        (((Functor.constCompWhiskeringLeftIso Cᵒᵖ F.op).app
          (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
          Functor.whiskerLeft F.op (toSheafify K
            ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))))))
  rw [equality]
  infer_instance

/-- Naturality of the unit of the adjunction between the free abelian sheaf and the underlying
sheaf of sets, with both functors spelled out. -/
private theorem freeSheafAdjunction_unit_naturality {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u}] [HasWeakSheafify J (Type u)]
    {X Y : Sheaf J (Type u)} (f : X ⟶ Y) :
    f ≫ (Sheaf.adjunction J AddCommGrpCat.adj).unit.app Y =
      (Sheaf.adjunction J AddCommGrpCat.adj).unit.app X ≫
        (sheafCompose J (forget Ab.{u})).map
          ((Sheaf.composeAndSheafify J AddCommGrpCat.free).map f) :=
  (Sheaf.adjunction J AddCommGrpCat.adj).unit.naturality f

/-- Transposition across the adjunction between the free abelian sheaf and the underlying sheaf
of sets, with both functors spelled out. -/
private theorem freeSheafAdjunction_homEquiv {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u}] [HasWeakSheafify J (Type u)]
    {X : Sheaf J (Type u)} {Y : Sheaf J Ab.{u}}
    (g : (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X ⟶ Y) :
    (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv X Y g =
      (Sheaf.adjunction J AddCommGrpCat.adj).unit.app X ≫
        (sheafCompose J (forget Ab.{u})).map g :=
  Adjunction.homEquiv_unit (Sheaf.adjunction J AddCommGrpCat.adj) X Y g

/-- Pullback along a continuous functor commutes with the free abelian sheaf functor: both
composites are left adjoint to the same functor. -/
private noncomputable def pullbackFreeAbelianIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}]
    [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)] :
    Sheaf.composeAndSheafify J AddCommGrpCat.free ⋙
        Functor.sheafPullbackConstruction.sheafPullback F Ab.{u} J K ≅
      Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K ⋙
        Sheaf.composeAndSheafify K AddCommGrpCat.free :=
  ((Sheaf.adjunction J AddCommGrpCat.adj).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u} J K)).leftAdjointUniq
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K).comp
      (Sheaf.adjunction K AddCommGrpCat.adj))

/-- The transpose of the comparison of free abelian pullbacks is the composite of the two
adjunction units. -/
private theorem pullbackFreeAbelianIso_adjacent
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}]
    [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)]
    (object : Sheaf J (Type u)) :
    (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv _ _
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u} J K).homEquiv
        _ _ ((pullbackFreeAbelianIso F J K).hom.app object)) =
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K).unit.app
        object ≫
      (F.sheafPushforwardContinuous (Type u) J K).map
        ((Sheaf.adjunction K AddCommGrpCat.adj).unit.app
          ((Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K).obj object)) := by
  have equality := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((Sheaf.adjunction J AddCommGrpCat.adj).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u} J K))
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K).comp
      (Sheaf.adjunction K AddCommGrpCat.adj)) object
  rw [Adjunction.comp_homEquiv] at equality
  rw [Adjunction.comp_unit_app] at equality
  exact equality

/-- The free abelian sheaf on the terminal sheaf of sets is the constant integer sheaf. -/
private noncomputable def freeTerminalIntegerIso
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] [HasWeakSheafify J (Type u)] :
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj
        (Sheaf.terminal J Types.isTerminalPUnit) ≅
      integerSheaf J :=
  (presheafToSheaf J Ab.{u}).mapIso
    (freeAbPresheafConstIso' C ≪≫ (Functor.const Cᵒᵖ).mapIso freeUnitIntegerIso')

/-- Along a continuous functor whose pullback of sheaves of sets preserves finite limits, the
pullback of the constant integer sheaf is the constant integer sheaf. -/
private noncomputable def continuousConstantIntegerIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}]
    [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)]
    [PreservesFiniteLimits (F.sheafPullback (Type u) J K)] :
    (Functor.sheafPullbackConstruction.sheafPullback F Ab.{u} J K).obj
        (integerSheaf J) ≅
      integerSheaf K := by
  let setPullback := Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K
  letI : PreservesFiniteLimits setPullback := preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K)
  let terminalComparison :=
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj
      setPullback _).uniqueUpToIso (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  exact (Functor.sheafPullbackConstruction.sheafPullback F Ab.{u} J K).mapIso
      (freeTerminalIntegerIso J).symm ≪≫
    (pullbackFreeAbelianIso F J K).app (Sheaf.terminal J Types.isTerminalPUnit) ≪≫
    (Sheaf.composeAndSheafify K AddCommGrpCat.free).mapIso terminalComparison ≪≫
    freeTerminalIntegerIso K

/-- The transpose of the identification of the free abelian sheaf on a point with the constant
integer sheaf carries the point to the integer generator. -/
private theorem freeTerminalIntegerIso_hom_generator
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] [HasWeakSheafify J (Type u)] (object : Cᵒᵖ) :
    (((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv _ _
      (freeTerminalIntegerIso J).hom).hom.app object) PUnit.unit =
    (toSheafify J ((Functor.const Cᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).app object (ULift.up 1) := by
  rw [Adjunction.homEquiv_unit]
  show (((Sheaf.adjunction J AddCommGrpCat.adj).unit.app
    (Sheaf.terminal J Types.isTerminalPUnit)).hom ≫
    Functor.whiskerRight (freeTerminalIntegerIso J).hom.hom
      (forget Ab.{u})).app object PUnit.unit = _
  rw [Sheaf.adjunction_unit_app_hom]
  show (toSheafify J _ ≫ ((presheafToSheaf J Ab.{u}).map
    (freeAbPresheafConstIso' C ≪≫
      (Functor.const Cᵒᵖ).mapIso freeUnitIntegerIso').hom).hom).app object
      (FreeAbelianGroup.of PUnit.unit) = _
  rw [← toSheafify_naturality]
  show (toSheafify J ((Functor.const Cᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))).app object
    ((freeUnitIntegerIso'.{u}).hom.hom (FreeAbelianGroup.of PUnit.unit)) = _
  rw [freeUnitIntegerIso_generator']

/-- The canonical restriction of constant integer sheaves carries the integer generator to the
integer generator. -/
private theorem constantIntegerRestriction_generator
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}]
    (object : Cᵒᵖ) :
    (constantIntegerRestriction F J K).hom.app object
      ((toSheafify J ((Functor.const Cᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))).app object (ULift.up 1)) =
      (toSheafify K ((Functor.const Dᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (F.op.obj object) (ULift.up 1) := by
  have equality := ((sheafificationAdjunction J Ab.{u}).homEquiv
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    ((F.sheafPushforwardContinuous Ab.{u} J K).obj
      (integerSheaf K))).apply_symm_apply
    (((Functor.constCompWhiskeringLeftIso Cᵒᵖ F.op).app
      (AddCommGrpCat.of (ULift.{u} ℤ))).inv ≫
      Functor.whiskerLeft F.op (toSheafify K
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))))
  rw [Adjunction.homEquiv_unit] at equality
  exact congrArg (fun morphism => morphism.hom (ULift.up 1))
    (congrArg (fun morphism => morphism.app object) equality)

/-- The transpose of the pullback comparison of constant integer sheaves is the canonical
restriction. -/
private theorem continuousConstantIntegerIso_adjacent
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [HasWeakSheafify J Ab.{u}] [HasWeakSheafify K Ab.{u}]
    [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)]
    [PreservesFiniteLimits (F.sheafPullback (Type u) J K)] :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u} J K).homEquiv
      _ _ (continuousConstantIntegerIso F J K).hom =
      constantIntegerRestriction F J K := by
  let : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K) :=
    preservesFiniteLimits_of_natIso
      (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) J K)
  let adjFree := Sheaf.adjunction J AddCommGrpCat.adj
  apply (cancel_epi (freeTerminalIntegerIso J).hom).1
  apply (adjFree.homEquiv _ _).injective
  simp only [continuousConstantIntegerIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Adjunction.homEquiv_naturality_left,
    Iso.symm_hom, Iso.hom_inv_id_assoc,
    Adjunction.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_naturality_right]
  show ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv _ _
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u} J K).homEquiv
      _ _ ((pullbackFreeAbelianIso F J K).hom.app
        (Sheaf.terminal J Types.isTerminalPUnit)))) ≫ _ = _
  rw [pullbackFreeAbelianIso_adjacent]
  simp only [Functor.map_comp]
  let terminalMap := ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj
      (Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K) _).uniqueUpToIso
        (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)
  show _ ≫ ((F.sheafPushforwardContinuous (Type u) J K).map
    ((Sheaf.adjunction K AddCommGrpCat.adj).unit.app _) ≫
    (F.sheafPushforwardContinuous (Type u) J K).map
      ((sheafCompose K (forget Ab.{u})).map
        ((Sheaf.composeAndSheafify K AddCommGrpCat.free).map terminalMap.hom) ≫
        (sheafCompose K (forget Ab.{u})).map (freeTerminalIntegerIso K).hom)) = _
  rw [← Functor.map_comp, ← Category.assoc]
  rw [← freeSheafAdjunction_unit_naturality K terminalMap.hom]
  rw [Category.assoc, Functor.map_comp, ← Category.assoc]
  rw [← freeSheafAdjunction_homEquiv K]
  rw [Adjunction.homEquiv_naturality_right]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext object
  apply ConcreteCategory.hom_ext
  intro point
  cases point
  show ((Sheaf.adjunction K AddCommGrpCat.adj).homEquiv _ _
      (freeTerminalIntegerIso K).hom).hom.app (F.op.obj object) PUnit.unit =
    (constantIntegerRestriction F J K).hom.app object
      (((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv _ _
        (freeTerminalIntegerIso J).hom).hom.app object PUnit.unit)
  rw [freeTerminalIntegerIso_hom_generator,
    freeTerminalIntegerIso_hom_generator, constantIntegerRestriction_generator]

/-- The map from the constant integer presheaf on the degree-`m` component to the restriction of
the free abelian `n`-simplex presheaf that picks out the simplex `φ`. -/
private noncomputable def stdSimplexPresheafGenerator' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (Functor.const (S.component m)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (componentFunctor S m).op ⋙ stdSimplexPresheafAb' S n := by
  refine (Functor.const _).map freeUnitIntegerIso'.inv ≫
    ((freeAbPresheafConstIso' _).inv) ≫
    (freeAbPresheaf' (S.component m)).map (Y :=
      (componentFunctor S m).op ⋙ stdSimplexPresheaf' S n) ?_
  refine { app := fun object => ↾(fun _ => ?_), naturality := ?_ }
  · rcases S with ⟨C | C⟩ <;> exact SSet.stdSimplex.objEquiv.symm φ
  · intro object other morphism
    apply ConcreteCategory.hom_ext
    intro point
    rcases S with ⟨C | C⟩ <;>
      simp only [stdSimplexPresheaf', totalSimplexDegree, componentFunctor,
        SimplicialSiteSituation.totalCategory, Functor.const_obj_obj, Functor.const_obj_map,
        unopUnop_obj, Category.id_comp, ConcreteCategory.hom_ofHom]
        <;> change SSet.stdSimplex.objEquiv.symm φ =
          (SSet.stdSimplex.map (𝟙 m)).app (Opposite.op n)
            (SSet.stdSimplex.objEquiv.symm φ)
        <;> exact congrArg (fun transformation : SSet.stdSimplex.obj m ⟶
          SSet.stdSimplex.obj m => transformation.app (Opposite.op n)
            (SSet.stdSimplex.objEquiv.symm φ)) (SSet.stdSimplex.map_id m) |>.symm

/-- The generator of the degree-`n` restriction of the free abelian `n`-simplex presheaf labelled
by the identity simplex. -/
private noncomputable def stdSimplexIdentityGenerator' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (Functor.const (S.component n)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (componentFunctor S n).op ⋙ stdSimplexPresheafAb' S n :=
  stdSimplexPresheafGenerator' S (𝟙 n)

/-- The comparison from the lower shriek image of the constant integer sheaf in degree `n` to the
degree-`n` term of the resolution, adjoint to the identity generator. -/
@[no_expose] noncomputable def resolutionDegreeMap' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : componentIntegerSheaf S n ⟶
      (resolutionSimplicial' S).obj (Opposite.op n) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentFunctor S n) Ab.{u} (S.componentTopology n) S.totalTopology).homEquiv
      _ _).symm
    (((sheafificationAdjunction (S.componentTopology n) Ab.{u}).homEquiv _ _).symm
      (stdSimplexIdentityGenerator' S n ≫
        Functor.whiskerLeft (componentFunctor S n).op
          (toSheafify S.totalTopology (stdSimplexPresheafAb' S n))))

/-- The cofan of copies of the integers indexed by a basis, with the free abelian group on that
basis as its point. -/
private noncomputable def freeAbelianIntegerCofan {index : Type*}
    (generators : Type u) (equivalence : index ≃ generators) :
    Cofan (fun _ : index => AddCommGrpCat.of (ULift.{u} ℤ)) :=
  Cofan.mk (AddCommGrpCat.free.obj generators) (fun entry =>
    AddCommGrpCat.ofHom ((zmultiplesHom (FreeAbelianGroup generators)
      (FreeAbelianGroup.of (equivalence entry))).comp AddEquiv.ulift.toAddMonoidHom))

/-- A free abelian group is the coproduct of copies of the integers indexed by its basis. -/
private noncomputable def freeAbelianIntegerCofanIsColimit {index : Type*}
    (generators : Type u) (equivalence : index ≃ generators) :
    IsColimit (freeAbelianIntegerCofan generators equivalence) := by
  refine Cofan.IsColimit.mk _ (fun cocone => AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun generator =>
      (cocone.inj (equivalence.symm generator)).hom (ULift.up 1)))) ?_ ?_
  · intro cocone entry
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro integer
    have equality := congrArg (fun morphism : ℤ →+ cocone.pt => morphism integer.down)
      (AddMonoidHom.ext_int (f :=
        (((freeAbelianIntegerCofan generators equivalence).inj entry ≫
          AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun generator =>
            (cocone.inj (equivalence.symm generator)).hom (ULift.up 1)))).hom.comp
            AddEquiv.ulift.symm.toAddMonoidHom))
        (g := (cocone.inj entry).hom.comp AddEquiv.ulift.symm.toAddMonoidHom) (by
          change FreeAbelianGroup.lift (fun generator =>
            (cocone.inj (equivalence.symm generator)).hom (ULift.up 1))
              (1 • FreeAbelianGroup.of (equivalence entry)) =
            (cocone.inj entry).hom (ULift.up 1)
          simp [FreeAbelianGroup.lift_apply_of]))
    exact equality
  · intro cocone morphism equations
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro generator
    have equality := congrArg (fun arrow => arrow.hom (ULift.up 1))
      (equations (equivalence.symm generator))
    change morphism.hom (FreeAbelianGroup.of generator) = _
    change morphism.hom (1 • FreeAbelianGroup.of (equivalence
      (equivalence.symm generator))) = _ at equality
    change morphism.hom (FreeAbelianGroup.of generator) =
      FreeAbelianGroup.lift (fun generator =>
        (cocone.inj (equivalence.symm generator)).hom (ULift.up 1))
        (FreeAbelianGroup.of generator)
    have scalar : (1 : ℤ) • FreeAbelianGroup.of generator =
        FreeAbelianGroup.of generator := one_zsmul _
    rw [Equiv.apply_symm_apply] at equality
    exact (congrArg morphism.hom scalar).symm.trans equality |>.trans
      (FreeAbelianGroup.lift_apply_of _ _).symm

/-- The comparison of constant integer sheaves along a simplicial transition is an isomorphism. -/
@[no_expose] noncomputable def transitionIntegerIso' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    integerSheaf (S.componentTopology m) ≅
    (transitionInverseImageAb S φ).obj
      (integerSheaf (S.componentTopology n)) := by
  rcases S with ⟨C | C⟩
  · letI := (C.isMorphismOfSites φ).isContinuous
    letI := (C.isMorphismOfSites φ).preservesFiniteLimits
    exact (continuousConstantIntegerIso (C.underlying.map φ).toFunctor
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).symm
  · letI : (C.underlying.map φ.op).toFunctor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op m)))
        (topologyOfCoverings (C.coverage (Opposite.op n))) :=
      C.isCocontinuous φ.op
    letI : IsIso (constantIntegerPullback (C.underlying.map φ.op).toFunctor
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (topologyOfCoverings (C.coverage (Opposite.op n)))) :=
      constantIntegerPullback_isIso (C.underlying.map φ.op).toFunctor
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (topologyOfCoverings (C.coverage (Opposite.op n)))
    exact @asIso _ _ _ _ (constantIntegerPullback (C.underlying.map φ.op).toFunctor
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (topologyOfCoverings (C.coverage (Opposite.op n))))
        (constantIntegerPullback_isIso _ _ _)

/-- A simplicial abelian sheaf whose alternating-face complex resolves the constant integer
sheaf, with its terms identified with the componentwise lower shriek images. -/
structure SimplicialIntegerResolution (S : SimplicialSiteSituation.{u}) where
  simplicial : SimplicialObject (Sheaf S.totalTopology Ab.{u})
  degreeIso (n : ℕ) : simplicial _⦋n⦌ ≅ componentIntegerSheaf S ⦋n⦌
  /-- The canonical identification of the pullback of the constant integer sheaf
  along a simplicial transition with the constant integer sheaf. -/
  transitionConstantIso {n m : SimplexCategory} (φ : n ⟶ m) :
    integerSheaf (S.componentTopology m) ≅
    (transitionInverseImageAb S φ).obj
      (integerSheaf (S.componentTopology n))
  /-- The comparison of constant sheaves is the one induced by the sheafification
  unit, equivalently the one preserving the integer generator. -/
  transitionConstantIso_canonical :
    match S with
    | ⟨Sum.inl C⟩ => ∀ {n m : SimplexCategory} (φ : n ⟶ m),
        letI : (C.underlying.map φ).toFunctor.IsContinuous
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
          (C.isMorphismOfSites φ).isContinuous
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (C.underlying.map φ).toFunctor Ab.{u}
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _
            (transitionConstantIso φ).inv =
          constantIntegerRestriction (C.underlying.map φ).toFunctor
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
    | ⟨Sum.inr C⟩ => ∀ {n m : SimplexCategory} (φ : n ⟶ m),
        (transitionConstantIso φ).hom =
          constantIntegerPullback (C.underlying.map φ.op).toFunctor
            (topologyOfCoverings (C.coverage (Opposite.op m)))
            (topologyOfCoverings (C.coverage (Opposite.op n)))
  /-- Under adjunction and the coproduct formula, the `i`th face map is the
  inclusion of the summand labelled by the coface `δ i`. -/
  face_adjacent (n : ℕ) (i : Fin (n + 2)) :
    let k := ⦋n + 1⦌
    let j := ⦋n⦌
    let F := componentFunctor S k
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{u}
      (S.componentTopology k) S.totalTopology).homEquiv _ _
      ((degreeIso (n + 1)).inv ≫ simplicial.δ i ≫ (degreeIso n).hom) =
    (transitionConstantIso (SimplexCategory.δ i)).hom ≫
      (Sigma.ι (fun φ : j ⟶ k =>
        transitionInverseImageAb S φ)
        (SimplexCategory.δ i)).app
          (integerSheaf (S.componentTopology j)) ≫
      (componentLowerShriekRestrictionIsoCoproduct
        S j k).inv.app
          (integerSheaf (S.componentTopology j))
  augmentation : ((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).X 0 ⟶
    totalIntegerSheaf S
  /-- The augmentation is adjoint to restriction of the integer generator to degree zero. -/
  augmentation_adjacent :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentFunctor S ⦋0⦌) Ab.{u}
      (S.componentTopology ⦋0⦌) S.totalTopology).homEquiv _ _
      ((degreeIso 0).inv ≫ augmentation) =
    constantIntegerRestriction (componentFunctor S ⦋0⦌)
      (S.componentTopology ⦋0⦌) S.totalTopology
  augmentation_comp :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).d 1 0 ≫
      augmentation = 0
  exact_positive (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).ExactAt n
  exact_zero :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).d 1 0)
      augmentation augmentation_comp).Exact
  augmentation_epi : Epi augmentation

/-- In case (A), the comparison of constant integer sheaves along a simplicial transition is the
canonical restriction induced by the sheafification unit. -/
private theorem transitionIntegerIso_canonical_inl' (C : SimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    [(C.underlying.map φ).toFunctor.IsContinuous
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck] :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (C.underlying.map φ).toFunctor Ab.{u}
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _
        (transitionIntegerIso' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).inv =
      constantIntegerRestriction (C.underlying.map φ).toFunctor
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck := by
  let := (C.isMorphismOfSites φ).preservesFiniteLimits
  show (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (C.underlying.map φ).toFunctor Ab.{u}
    (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _
      (continuousConstantIntegerIso (C.underlying.map φ).toFunctor
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).hom = _
  exact continuousConstantIntegerIso_adjacent (C.underlying.map φ).toFunctor
    (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck

/-- In case (B), the comparison of constant integer sheaves along a simplicial transition is the
canonical map into the sheafified restriction of a constant sheaf. -/
private theorem transitionIntegerIso_canonical_inr' (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (transitionIntegerIso' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).hom =
      constantIntegerPullback (C.underlying.map φ.op).toFunctor
        (topologyOfCoverings (C.coverage (Opposite.op m)))
        (topologyOfCoverings (C.coverage (Opposite.op n))) :=
  rfl

/-- The comparison of constant integer sheaves along a simplicial transition is canonical in
either case of the situation. -/
theorem transitionIntegerIso_canonical' (S : SimplicialSiteSituation.{u}) :
    match S with
    | ⟨Sum.inl C⟩ => ∀ {n m : SimplexCategory} (φ : n ⟶ m),
        letI : (C.underlying.map φ).toFunctor.IsContinuous
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
          (C.isMorphismOfSites φ).isContinuous
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (C.underlying.map φ).toFunctor Ab.{u}
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _
            (transitionIntegerIso' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).inv =
          constantIntegerRestriction (C.underlying.map φ).toFunctor
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
    | ⟨Sum.inr C⟩ => ∀ {n m : SimplexCategory} (φ : n ⟶ m),
        (transitionIntegerIso' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).hom =
          constantIntegerPullback (C.underlying.map φ.op).toFunctor
            (topologyOfCoverings (C.coverage (Opposite.op m)))
            (topologyOfCoverings (C.coverage (Opposite.op n))) := by
  rcases S with ⟨C | C⟩
  · intro n m φ
    let := (C.isMorphismOfSites φ).isContinuous
    exact transitionIntegerIso_canonical_inl' C φ
  · intro n m φ
    exact transitionIntegerIso_canonical_inr' C φ

/-- The generator labelled by `φ` carries `1` to the basis element of the simplex `φ`. -/
private theorem stdSimplexPresheafGenerator_generator' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (object : (S.component m)ᵒᵖ) :
    (stdSimplexPresheafGenerator' S φ).app object (ULift.up 1) =
      FreeAbelianGroup.of (show (stdSimplexPresheaf' S n).obj
        ((componentFunctor S m).op.obj object) from by
          rcases S with ⟨C | C⟩ <;> exact SSet.stdSimplex.objEquiv.symm φ) := by
  rcases S with ⟨C | C⟩ <;>
    show FreeAbelianGroup.map (fun _ : PUnit.{u + 1} =>
      SSet.stdSimplex.objEquiv.symm φ)
      (freeUnitIntegerIso'.inv.hom (ULift.up 1)) = _
    <;> rw [← freeUnitIntegerIso_generator']
    <;> have equality := congrArg
      (fun morphism : AddCommGrpCat.free.obj PUnit.{u + 1} ⟶
          AddCommGrpCat.free.obj PUnit.{u + 1} =>
        morphism.hom (FreeAbelianGroup.of PUnit.unit)) freeUnitIntegerIso'.hom_inv_id
    <;> change freeUnitIntegerIso'.inv.hom
      (freeUnitIntegerIso'.hom.hom (FreeAbelianGroup.of PUnit.unit)) =
        FreeAbelianGroup.of PUnit.unit at equality
    <;> rw [equality]
    <;> rfl

/-- The generator labelled by `ψ` followed by the simplicial map of `φ` is the generator labelled
by `φ ≫ ψ`. -/
private theorem stdSimplexPresheafGenerator_map' (S : SimplicialSiteSituation.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    stdSimplexPresheafGenerator' S ψ ≫
        Functor.whiskerLeft (componentFunctor S k).op (stdSimplexPresheafAbMap' S φ) =
      stdSimplexPresheafGenerator' S (φ ≫ ψ) := by
  apply NatTrans.ext
  funext object
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro integer
  have equality := AddMonoidHom.ext_int (f :=
    (((stdSimplexPresheafGenerator' S ψ ≫
      Functor.whiskerLeft (componentFunctor S k).op
        (stdSimplexPresheafAbMap' S φ)).app object).hom.comp
          AddEquiv.ulift.symm.toAddMonoidHom))
    (g := ((stdSimplexPresheafGenerator' S (φ ≫ ψ)).app object).hom.comp
      AddEquiv.ulift.symm.toAddMonoidHom) (by
      show ((stdSimplexPresheafAbMap' S φ).app _).hom
        ((stdSimplexPresheafGenerator' S ψ).app object (ULift.up 1)) =
        (stdSimplexPresheafGenerator' S (φ ≫ ψ)).app object (ULift.up 1)
      rw [stdSimplexPresheafGenerator_generator',
        stdSimplexPresheafGenerator_generator', stdSimplexPresheafAbMap_generator']
      rcases S with ⟨C | C⟩ <;> rfl)
  exact congrArg (fun morphism => morphism integer.down) equality

/-- The generator labelled by `φ` followed by the augmentation is the canonical identification of
the two constant presheaves. -/
private theorem stdSimplexPresheafGenerator_augmentation' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    stdSimplexPresheafGenerator' S φ ≫
        Functor.whiskerLeft (componentFunctor S m).op
          (stdSimplexPresheafAbAugmentation' S n) =
      ((Functor.constCompWhiskeringLeftIso (S.component m)ᵒᵖ
        (componentFunctor S m).op).app (AddCommGrpCat.of (ULift.{u} ℤ))).inv := by
  apply NatTrans.ext
  funext object
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro integer
  have equality := AddMonoidHom.ext_int (f :=
    (((stdSimplexPresheafGenerator' S φ ≫
      Functor.whiskerLeft (componentFunctor S m).op
        (stdSimplexPresheafAbAugmentation' S n)).app object).hom.comp
          AddEquiv.ulift.symm.toAddMonoidHom)) (g := AddEquiv.ulift.symm.toAddMonoidHom)
      (by
        show ((stdSimplexPresheafAbAugmentation' S n).app _).hom
          ((stdSimplexPresheafGenerator' S φ).app object (ULift.up 1)) = ULift.up 1
        rw [stdSimplexPresheafGenerator_generator',
          stdSimplexPresheafAbAugmentation_generator'])
  exact congrArg (fun morphism => morphism integer.down) equality

/-- The degree comparison followed by the augmentation of the resolution transposes to the
canonical restriction of constant integer sheaves. -/
private theorem resolutionDegreeMap_augmentation' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentFunctor S n) Ab.{u} (S.componentTopology n) S.totalTopology).homEquiv
      _ _ (resolutionDegreeMap' S n ≫ resolutionTermAugmentation' S n) =
        constantIntegerRestriction (componentFunctor S n)
          (S.componentTopology n) S.totalTopology := by
  rw [Adjunction.homEquiv_naturality_right]
  simp only [resolutionDegreeMap', Equiv.apply_symm_apply]
  apply ((sheafificationAdjunction (S.componentTopology n) Ab.{u}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    constantIntegerRestriction, Equiv.apply_symm_apply]
  show (stdSimplexIdentityGenerator' S n ≫
    Functor.whiskerLeft (componentFunctor S n).op
      (toSheafify S.totalTopology (stdSimplexPresheafAb' S n))) ≫
    Functor.whiskerLeft (componentFunctor S n).op
      ((presheafToSheaf S.totalTopology Ab.{u}).map
        (stdSimplexPresheafAbAugmentation' S n)).hom = _
  rw [Category.assoc, ← Functor.whiskerLeft_comp, ← toSheafify_naturality,
    Functor.whiskerLeft_comp, ← Category.assoc]
  exact congrArg (fun morphism => morphism ≫
    Functor.whiskerLeft (componentFunctor S n).op
      (toSheafify S.totalTopology
        ((Functor.const S.totalCategoryᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))))
    (stdSimplexPresheafGenerator_augmentation' S (𝟙 n))

/-- The map from the constant integer sheaf in degree `m` to the degree-`m` restriction of the
degree-`n` term of the resolution labelled by the simplex map `φ`. -/
private noncomputable def resolutionRestrictedGenerator' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    integerSheaf (S.componentTopology m) ⟶
      ((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology).obj
        ((resolutionSimplicial' S).obj (Opposite.op n)) :=
  ((sheafificationAdjunction (S.componentTopology m) Ab.{u}).homEquiv _ _).symm
    (stdSimplexPresheafGenerator' S φ ≫
      Functor.whiskerLeft (componentFunctor S m).op
        (toSheafify S.totalTopology (stdSimplexPresheafAb' S n)))

/-- Sheafification on the degree-`m` component commutes with restriction from the total site. -/
private noncomputable def resolutionRestrictionIso (S : SimplicialSiteSituation.{u})
    (n m : SimplexCategory) :
    (presheafToSheaf (S.componentTopology m) Ab.{u}).obj
        ((componentFunctor S m).op ⋙ stdSimplexPresheafAb' S n) ≅
      ((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology).obj
        ((resolutionSimplicial' S).obj (Opposite.op n)) :=
  ((componentFunctor S m).pushforwardContinuousSheafificationCompatibility
    Ab.{u} (S.componentTopology m) S.totalTopology).app (stdSimplexPresheafAb' S n)

/-- The cofan of copies of the constant integer sheaf in degree `m`, indexed by the simplex maps
`[n] ⟶ [m]`, whose inclusions are the restricted generators. -/
private noncomputable def resolutionRestrictionCofan (S : SimplicialSiteSituation.{u})
    (n m : SimplexCategory) :
    Cofan (fun _ : n ⟶ m => integerSheaf (S.componentTopology m)) :=
  Cofan.mk _ (resolutionRestrictedGenerator' S)

/-- Restricted to degree `m`, the free abelian `n`-simplex presheaf is the coproduct over the
simplex maps `[n] ⟶ [m]` of the constant integer presheaf. -/
private noncomputable def resolutionPresheafCofanIsColimit
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) :
    IsColimit (Cofan.mk ((componentFunctor S m).op ⋙ stdSimplexPresheafAb' S n)
      (fun φ : n ⟶ m => stdSimplexPresheafGenerator' S φ)) := by
  apply evaluationJointlyReflectsColimits
  intro object
  rcases S with ⟨C | C⟩
  all_goals
    let equivalence : (n ⟶ m) ≃
        (stdSimplexPresheaf' (⟨_⟩ : SimplicialSiteSituation.{u}) n).obj
          ((componentFunctor ⟨_⟩ m).op.obj object) := SSet.stdSimplex.objEquiv.symm
    refine IsColimit.ofIsoColimit (freeAbelianIntegerCofanIsColimit _ equivalence) ?_
    refine Cocone.ext (Iso.refl _) ?_
    intro entry
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro integer
    symm
    apply congrArg (fun morphism : ℤ →+ _ => morphism integer.down)
      (AddMonoidHom.ext_int (f :=
        ((stdSimplexPresheafGenerator' ⟨_⟩ entry.as).app object).hom.comp
          AddEquiv.ulift.symm.toAddMonoidHom)
        (g := ((freeAbelianIntegerCofan _ equivalence).inj entry.as).hom.comp
          AddEquiv.ulift.symm.toAddMonoidHom) ?_)
    change ((stdSimplexPresheafGenerator' ⟨_⟩ entry.as).app object).hom (ULift.up 1) = _
    rw [stdSimplexPresheafGenerator_generator']
    change _ = (1 : ℤ) • FreeAbelianGroup.of (equivalence entry.as)
    rw [one_zsmul]
    rfl

/-- Restricted to degree `m`, the degree-`n` term of the resolution is the coproduct over the
simplex maps `[n] ⟶ [m]` of the constant integer sheaf. -/
private noncomputable def resolutionRestrictionCofanIsColimit
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) :
    IsColimit (resolutionRestrictionCofan S n m) := by
  let cocone := Cofan.mk ((componentFunctor S m).op ⋙ stdSimplexPresheafAb' S n)
    (fun φ : n ⟶ m => stdSimplexPresheafGenerator' S φ)
  change IsColimit (Cofan.mk
    (((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
      (S.componentTopology m) S.totalTopology).obj
      ((resolutionSimplicial' S).obj (Opposite.op n)))
    (fun φ : n ⟶ m => resolutionRestrictedGenerator' S φ))
  refine IsColimit.ofIsoColimit
    ((Cofan.isColimitMapCoconeEquiv (presheafToSheaf (S.componentTopology m) Ab.{u})
      _ cocone) (isColimitOfPreserves (presheafToSheaf (S.componentTopology m) Ab.{u})
      (resolutionPresheafCofanIsColimit S n m))) ?_
  refine Cocone.ext (resolutionRestrictionIso S n m) ?_
  intro entry
  apply ((sheafificationAdjunction (S.componentTopology m) Ab.{u}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  change (toSheafify (S.componentTopology m) _ ≫
      ((presheafToSheaf (S.componentTopology m) Ab.{u}).map
        (stdSimplexPresheafGenerator' S entry.as)).hom) ≫ _ = _
  rw [← toSheafify_naturality, Category.assoc]
  change stdSimplexPresheafGenerator' S entry.as ≫
    (toSheafify (S.componentTopology m) ((componentFunctor S m).op ⋙ stdSimplexPresheafAb' S n) ≫
      (((componentFunctor S m).pushforwardContinuousSheafificationCompatibility
        Ab.{u} (S.componentTopology m) S.totalTopology).app
          (stdSimplexPresheafAb' S n)).hom.hom) = _
  refine (congrArg (fun arrow => stdSimplexPresheafGenerator' S entry.as ≫ arrow)
    ((componentFunctor S m).toSheafify_pullbackSheafificationCompatibility
      Ab.{u} (S.componentTopology m) S.totalTopology (stdSimplexPresheafAb' S n))).trans ?_
  change _ = ((sheafificationAdjunction (S.componentTopology m) Ab.{u}).homEquiv _
    (((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
      (S.componentTopology m) S.totalTopology).obj
      ((resolutionSimplicial' S).obj (Opposite.op n))))
    (resolutionRestrictedGenerator' S entry.as)
  exact ((sheafificationAdjunction (S.componentTopology m) Ab.{u}).homEquiv _
    (((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
      (S.componentTopology m) S.totalTopology).obj
      ((resolutionSimplicial' S).obj (Opposite.op n)))).apply_symm_apply
    (stdSimplexPresheafGenerator' S entry.as ≫
      Functor.whiskerLeft (componentFunctor S m).op
        (toSheafify S.totalTopology (stdSimplexPresheafAb' S n))) |>.symm

/-- The integer generator: the section of the constant integer sheaf obtained from `1`. -/
private noncomputable def integerGenerator
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] (object : Cᵒᵖ) :
    (integerSheaf J).obj.obj object :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))).app object (ULift.up 1)

/-- Two maps out of the constant integer sheaf agree as soon as they agree on the integer generator
over every object. -/
private theorem integerGenerator_hom_ext
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] {target : Sheaf J Ab.{u}}
    {first second : integerSheaf J ⟶ target}
    (equations : ∀ object, first.hom.app object (integerGenerator J object) =
      second.hom.app object (integerGenerator J object)) : first = second := by
  apply ((sheafificationAdjunction J Ab.{u}).homEquiv _ _).injective
  apply NatTrans.ext
  funext object
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro integer
  exact congrArg (fun morphism : ℤ →+ _ => morphism integer.down)
    (AddMonoidHom.ext_int (f :=
      ((((sheafificationAdjunction J Ab.{u}).homEquiv _ _) first).app object).hom.comp
        AddEquiv.ulift.symm.toAddMonoidHom)
      (g := ((((sheafificationAdjunction J Ab.{u}).homEquiv _ _) second).app object).hom.comp
        AddEquiv.ulift.symm.toAddMonoidHom) (by
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        exact equations object))

/-- The transpose of a map out of the constant integer presheaf carries the integer generator to
the image of `1`. -/
private theorem integerGenerator_sheafification
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] {target : Sheaf J Ab.{u}}
    (morphism : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ target.obj)
    (object : Cᵒᵖ) :
    ((((sheafificationAdjunction J Ab.{u}).homEquiv _ _).symm morphism).hom.app object)
        (integerGenerator J object) = morphism.app object (ULift.up 1) :=
  congrArg (fun arrow => arrow.hom (ULift.up 1))
    (congrArg (fun arrow => arrow.app object)
      (((sheafificationAdjunction J Ab.{u}).homEquiv _ _).apply_symm_apply morphism))

/-- The restricted generator labelled by `ψ` followed by the simplicial map of `φ` is the
restricted generator labelled by `φ ≫ ψ`. -/
private theorem resolutionRestrictedGenerator_map' (S : SimplicialSiteSituation.{u})
    {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k) :
    resolutionRestrictedGenerator' S ψ ≫
        ((componentFunctor S k).sheafPushforwardContinuous Ab.{u}
          (S.componentTopology k) S.totalTopology).map
          ((resolutionSimplicial' S).map φ.op) =
      resolutionRestrictedGenerator' S (φ ≫ ψ) := by
  apply ((sheafificationAdjunction (S.componentTopology k) Ab.{u}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show ((sheafificationAdjunction (S.componentTopology k) Ab.{u}).homEquiv _ _)
    (resolutionRestrictedGenerator' S ψ) = _ from Equiv.apply_symm_apply _ _]
  show (stdSimplexPresheafGenerator' S ψ ≫
    Functor.whiskerLeft (componentFunctor S k).op (toSheafify S.totalTopology _)) ≫
    Functor.whiskerLeft (componentFunctor S k).op
      ((presheafToSheaf S.totalTopology Ab.{u}).map (stdSimplexPresheafAbMap' S φ)).hom = _
  rw [Category.assoc, ← Functor.whiskerLeft_comp, ← toSheafify_naturality,
    Functor.whiskerLeft_comp, ← Category.assoc, stdSimplexPresheafGenerator_map']
  exact Equiv.apply_symm_apply _ _ |>.symm

/-- The restricted generator labelled by `φ` carries the integer generator to the simplex `φ`. -/
private theorem resolutionRestrictedGenerator_integerGenerator (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (object : (S.component m)ᵒᵖ) :
    (resolutionRestrictedGenerator' S φ).hom.app object
        (integerGenerator (S.componentTopology m) object) =
      (toSheafify S.totalTopology (stdSimplexPresheafAb' S n)).app
        ((componentFunctor S m).op.obj object)
        ((stdSimplexPresheafGenerator' S φ).app object (ULift.up 1)) :=
  integerGenerator_sheafification _ _ _

/-- The integer generator read as a map from the terminal sheaf of sets to the underlying sheaf of
sets of the constant integer sheaf. -/
private noncomputable def constantIntegerGenerator
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] [HasWeakSheafify J (Type u)] :
    Sheaf.terminal J Types.isTerminalPUnit ⟶
      (sheafCompose J (forget Ab.{u})).obj
        (integerSheaf J) :=
  (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv _ _ (freeTerminalIntegerIso J).hom

/-- On sections the generator map carries the point to the integer generator. -/
private theorem constantIntegerGenerator_app
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u}] [HasWeakSheafify J (Type u)] (object : Cᵒᵖ) :
    (constantIntegerGenerator J).hom.app object PUnit.unit = integerGenerator J object :=
  freeTerminalIntegerIso_hom_generator J object

/-- The comparison, on underlying sheaves of sets, between the inverse image along a simplicial
transition and `CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb`: the mate of the
abelian sheaf-pullback unit in case (A), and of the abelian sheafification unit in case (B). -/
noncomputable def transitionInverseImageForgetComparison (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (F : Sheaf (S.componentTopology n) Ab.{u}) :
    (S.transitionMorphism φ).inverseImage.obj
        ((sheafCompose (S.componentTopology n) (forget Ab.{u})).obj F) ⟶
      (sheafCompose (S.componentTopology m) (forget Ab.{u})).obj
        ((transitionInverseImageAb S φ).obj F) := by
  rcases S with ⟨C | C⟩
  · let f := (C.underlying.map φ).toFunctor
    letI : f.IsContinuous (C.coverage n).toGrothendieck
        (C.coverage m).toGrothendieck := (C.isMorphismOfSites φ).isContinuous
    exact ((f.sheafAdjunctionContinuous (Type u)
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _).symm
        ((sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f Ab.{u}
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).unit.app F))
  · let f := (C.underlying.map φ.op).toFunctor
    let J := topologyOfCoverings (C.coverage (Opposite.op m))
    exact ((sheafificationAdjunction J (Type u)).homEquiv _ _).symm
      (Functor.whiskerRight ((sheafificationAdjunction J Ab.{u}).unit.app (f.op ⋙ F.obj))
        (forget Ab.{u}))

/-- The statement that the summand inclusions of the sum formula of Stacks 09WG are, on underlying
sheaves of sets, the restriction of the lower-shriek unit followed by the transition of Stacks
09WF. It holds for every simplicial-site situation:
`CategoryTheory.SimplicialSiteSituation.summandForgetCompatibility`. -/
def SummandForgetCompatibility (S : SimplicialSiteSituation.{u}) : Prop :=
  ∀ {n m : SimplexCategory} (φ : n ⟶ m) (G : Sheaf (S.componentTopology n) Ab.{u}),
    transitionInverseImageForgetComparison S φ G ≫
        (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
          ((Sigma.ι (fun ψ : n ⟶ m => transitionInverseImageAb S ψ) φ).app G ≫
            (componentLowerShriekRestrictionIsoCoproduct S n m).inv.app G) =
      (S.transitionMorphism φ).inverseImage.map
          ((sheafCompose (S.componentTopology n) (forget Ab.{u})).map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentFunctor S n) Ab.{u}
                (S.componentTopology n) S.totalTopology).unit.app G)) ≫
        (fiberTransition S φ).app
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj
            ((Functor.sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
              (S.componentTopology n) S.totalTopology).obj G))

/-- The inverse image of the terminal sheaf of sets along a simplicial transition is terminal. -/
private noncomputable def transitionTerminalIso (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (S.transitionMorphism φ).inverseImage.obj
        (Sheaf.terminal (S.componentTopology n) Types.isTerminalPUnit) ≅
      Sheaf.terminal (S.componentTopology m) Types.isTerminalPUnit :=
  by
    letI := (S.transitionMorphism φ).preservesFiniteLimits
    exact ((Sheaf.isTerminalTerminal (S.componentTopology n) Types.isTerminalPUnit).isTerminalObj
      (S.transitionMorphism φ).inverseImage _).uniqueUpToIso
        (Sheaf.isTerminalTerminal (S.componentTopology m) Types.isTerminalPUnit)

/-- Transposition across the sheafification adjunction on sheaves of sets, with both functors
spelled out. -/
private theorem sheafificationAdjunctionType_homEquiv {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type u)]
    {P : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (g : (presheafToSheaf J (Type u)).obj P ⟶ X) :
    (sheafificationAdjunction J (Type u)).homEquiv P X g =
      toSheafify J P ≫ (sheafToPresheaf J (Type u)).map g :=
  Adjunction.homEquiv_unit (sheafificationAdjunction J (Type u)) P X g

/-- The inverse-image transition of a simplicial transition is the transpose of the
direct-image transition. -/
private theorem fiberTransition_app_eq (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf S.totalTopology (Type u)) :
    (fiberTransition S φ).app F =
      ((S.transitionMorphism φ).adj.homEquiv ((S.restrict m).obj F)
        ((S.restrict n).obj F)).symm ((S.restrictTransition φ).app F) :=
  rfl

/-- The inverse-image transition at the underlying sheaf of sets of an abelian sheaf, written
with the restrictions of that abelian sheaf as the source and target of the transposition. -/
private theorem fiberTransition_app_sheafCompose (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf S.totalTopology Ab.{u}) :
    (fiberTransition S φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj F) =
      ((S.transitionMorphism φ).adj.homEquiv
          ((sheafCompose (S.componentTopology m) (forget Ab.{u})).obj
            (((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
              (S.componentTopology m) S.totalTopology).obj F))
          ((sheafCompose (S.componentTopology n) (forget Ab.{u})).obj
            (((componentFunctor S n).sheafPushforwardContinuous Ab.{u}
              (S.componentTopology n) S.totalTopology).obj F))).symm
        ((S.restrictTransition φ).app
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj F)) :=
  rfl

/-- The transpose of the inverse-image transition at the underlying sheaf of sets of an abelian
sheaf is the direct-image transition, with the restrictions of that abelian sheaf as the source
and target of the transposition. -/
private theorem homEquiv_fiberTransition_app_sheafCompose (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf S.totalTopology Ab.{u}) :
    (S.transitionMorphism φ).adj.homEquiv
        ((sheafCompose (S.componentTopology m) (forget Ab.{u})).obj
          (((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
            (S.componentTopology m) S.totalTopology).obj F))
        ((sheafCompose (S.componentTopology n) (forget Ab.{u})).obj
          (((componentFunctor S n).sheafPushforwardContinuous Ab.{u}
            (S.componentTopology n) S.totalTopology).obj F))
        ((fiberTransition S φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj F)) =
      (S.restrictTransition φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj F) :=
  (congrArg _ (fiberTransition_app_sheafCompose S φ F)).trans (Equiv.apply_symm_apply _ _)

/-- In case (A), the summand inclusions of the sum formula of Stacks 09WG are, on underlying
sheaves of sets, the restricted lower-shriek unit followed by the transition of Stacks 09WF. -/
private theorem summandForgetCompatibility_inl (C : SimplicialSite.{u}) :
    SummandForgetCompatibility (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) := by
  intro n m φ G
  let := (C.isMorphismOfSites φ).isContinuous
  have leg : (Sigma.ι (fun ψ : n ⟶ m =>
        transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ) φ).app G ≫
      (componentLowerShriekRestrictionIsoCoproduct
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n m).inv.app G =
      (componentSumFormulaLeg (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).app G :=
    congrArg (fun t => t.app G)
      (SimplicialSite.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg
        C n m φ)
  rw [leg]
  apply (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.homEquiv
    _ _).injective
  have transpose :
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.homEquiv _ _
          (transitionInverseImageForgetComparison
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ G) =
        (sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (C.underlying.map φ).toFunctor Ab.{u}
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).unit.app G) :=
    Equiv.apply_symm_apply _ _
  have hleg := (Adjunction.homEquiv_unit _ _ _ _).symm.trans
    (homEquiv_componentSumFormulaLeg_app (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ G)
  refine Eq.trans (Adjunction.homEquiv_naturality_right _ _ _) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_left _ _ _).symm
  refine Eq.trans (congrArg (fun k => k ≫ _) transpose) ?_
  refine Eq.trans ?_ (congrArg (fun k => _ ≫ k)
    (homEquiv_fiberTransition_app_sheafCompose _ φ _).symm)
  exact ((sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map_comp _ _).symm.trans
    (congrArg (sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map hleg)

/-- In case (B), the summand inclusions of the sum formula of Stacks 09WG are, on underlying
sheaves of sets, the restricted lower-shriek unit followed by the transition of Stacks 09WF. -/
private theorem summandForgetCompatibility_inr (C : CocontinuousSimplicialSite.{u}) :
    SummandForgetCompatibility (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) := by
  intro n m φ G
  let : (C.underlying.map φ.op).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (topologyOfCoverings (C.coverage (Opposite.op n))) :=
    C.isCocontinuous φ.op
  have leg : (Sigma.ι (fun ψ : n ⟶ m =>
        transitionInverseImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) ψ) φ).app G ≫
      (componentLowerShriekRestrictionIsoCoproduct
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n m).inv.app G =
      (componentSumFormulaLeg (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app G :=
    congrArg (fun t => t.app G) <|
      CocontinuousSimplicialSite.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg
        C n m φ
  rw [leg]
  refine Sheaf.hom_ext_toSheafify _ _ ?_
  have comparison :
      toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (((C.underlying.map φ.op).toFunctor).op ⋙ G.obj ⋙ forget Ab.{u}) ≫
        (transitionInverseImageForgetComparison
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ G).hom =
      Functor.whiskerRight
        (toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (((C.underlying.map φ.op).toFunctor).op ⋙ G.obj)) (forget Ab.{u}) :=
    (sheafificationAdjunctionType_homEquiv
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      (P := ((C.underlying.map φ.op).toFunctor).op ⋙ G.obj ⋙ forget Ab.{u})
      (transitionInverseImageForgetComparison
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ G)).symm.trans
      (Equiv.apply_symm_apply _ _)
  have legSections := CocontinuousSimplicialSite.toSheafify_comp_componentSumFormulaLeg_inr_app
    C φ G
  have transition := CocontinuousSimplicialSite.toSheafify_comp_fiberTransition_inr_app C φ
    ((sheafCompose (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology (forget Ab.{u})).obj
      ((Functor.sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj G))
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ _) comparison).trans
      ((Functor.whiskerRight_comp _ _ _).symm.trans
        (congrArg (fun k => Functor.whiskerRight k (forget Ab.{u})) legSections)))) ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ _) (toSheafify_naturality _ _).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k) transition)))).symm
  exact Functor.whiskerRight_comp _ _ _

/-- The summand inclusions of the sum formula of Stacks 09WG are, on underlying sheaves of sets,
the restricted lower-shriek unit followed by the transition of Stacks 09WF. -/
theorem summandForgetCompatibility (S : SimplicialSiteSituation.{u}) :
    SummandForgetCompatibility S := by
  rcases S with ⟨C | C⟩
  · exact summandForgetCompatibility_inl C
  · exact summandForgetCompatibility_inr C

/-- In case (A) the underlying-set comparison is the mate of the abelian sheaf-pullback unit. -/
private theorem transitionInverseImageForgetComparison_inl (C : SimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    [(C.underlying.map φ).toFunctor.IsContinuous
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck]
    (F : Sheaf (C.coverage n).toGrothendieck Ab.{u}) :
    transitionInverseImageForgetComparison (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ F =
      (((C.underlying.map φ).toFunctor.sheafAdjunctionContinuous (Type u)
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _).symm
        ((sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (C.underlying.map φ).toFunctor Ab.{u}
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).unit.app F)) :=
  rfl

/-- In case (B) the underlying-set comparison is the transpose, across the sheafification
adjunction on sheaves of sets, of the abelian sheafification unit read through the forgetful
functor. -/
private theorem transitionInverseImageForgetComparison_inr (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (F : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :
    transitionInverseImageForgetComparison (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ F =
      ((sheafificationAdjunction
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          (Type u)).homEquiv _ _).symm
        (Functor.whiskerRight
          (toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
            ((C.underlying.map φ.op).toFunctor.op ⋙ F.obj))
          (forget Ab.{u})) :=
  rfl

/-- The sheafification unit followed by the inverse transpose along the sheafification
adjunction on sheaves of sets is the map that was transposed. -/
private theorem toSheafify_comp_homEquiv_symm {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type u)]
    (P : Cᵒᵖ ⥤ Type u) (X : Sheaf J (Type u)) (r : P ⟶ X.obj) :
    toSheafify J P ≫ (((sheafificationAdjunction J (Type u)).homEquiv P X).symm r).hom = r :=
  (sheafificationAdjunctionType_homEquiv J
      (((sheafificationAdjunction J (Type u)).homEquiv P X).symm r)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- In case (B), the sheafification unit followed by the underlying-set comparison is the
abelian sheafification unit read through the forgetful functor. -/
private theorem toSheafify_comp_transitionInverseImageForgetComparison_inr
    (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (F : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          ((C.underlying.map φ.op).toFunctor.op ⋙
            ((sheafCompose ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
              (forget Ab.{u})).obj F).obj) ≫
        (transitionInverseImageForgetComparison
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ F).hom =
      Functor.whiskerRight
        (toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          ((C.underlying.map φ.op).toFunctor.op ⋙ F.obj)) (forget Ab.{u}) := by
  rw [transitionInverseImageForgetComparison_inr]
  exact toSheafify_comp_homEquiv_symm
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m) _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- In case (B), the sheafification unit followed by the inverse-image transition of Stacks 09WF
is restriction of the total-site sheaf along the cross-fibre arrows. -/
private theorem toSheafify_comp_fiberTransition_inr_app (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (F : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u)) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
          ((C.underlying.map φ.op).toFunctor.op ⋙
            (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrict n).obj F).obj) ≫
        ((fiberTransition (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app F).hom =
      Functor.whiskerRight
        (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) F.obj := by
  have : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) :=
    C.isCocontinuous φ.op
  refine Eq.trans (Functor.toSheafify_comp_sheafAdjunctionPullbackCocontinuous_homEquiv_symm_hom
    ((C.underlying.map φ.op).toFunctor) (Type u) _ _ _) ?_
  exact Equiv.symm_apply_apply _ _

/-- In case (A) the transpose, across the adjunction of the simplicial transition on sheaves of
sets, of the underlying-set comparison is the abelian sheaf-pullback unit read through the
forgetful functor. -/
private theorem homEquiv_transitionInverseImageForgetComparison_inl (C : SimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (F : Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :
    (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.homEquiv _ _)
        (transitionInverseImageForgetComparison
          (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ F) =
      (sheafCompose ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
          (forget Ab.{u})).map
        ((transitionAdjunctionAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).unit.app F) :=
  Equiv.apply_symm_apply _ _

/-- In case (A) the underlying-set comparison along a simplicial transition carries the integer
generator in degree `n` to the one in degree `m`. -/
private theorem transitionIntegerGenerator_comparison_inl
    (C : SimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    let S : SimplicialSiteSituation.{u} := ⟨Sum.inl C⟩
    (S.transitionMorphism φ).inverseImage.map
        (constantIntegerGenerator (S.componentTopology n)) ≫
      transitionInverseImageForgetComparison S φ
        (integerSheaf (S.componentTopology n)) =
    (transitionTerminalIso S φ).hom ≫
      constantIntegerGenerator (S.componentTopology m) ≫
      (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
        (transitionIntegerIso' S φ).hom := by
  let := (C.isMorphismOfSites φ).isContinuous
  let := (C.isMorphismOfSites φ).preservesFiniteLimits
  dsimp only
  apply (cancel_mono ((sheafCompose
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) (forget Ab.{u})).map
    (transitionIntegerIso' ⟨Sum.inl C⟩ φ).inv)).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    Functor.map_id, Category.comp_id]
  apply (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism
    φ).adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  show constantIntegerGenerator (C.coverage n).toGrothendieck ≫
    ((Functor.sheafAdjunctionContinuous (C.underlying.map φ).toFunctor (Type u)
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv _ _
      (transitionInverseImageForgetComparison ⟨Sum.inl C⟩ φ
        (integerSheaf (C.coverage n).toGrothendieck))) ≫ _ = _
  have transpose :
      ((Functor.sheafAdjunctionContinuous (C.underlying.map φ).toFunctor (Type u)
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).homEquiv
          ((sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).obj
            (integerSheaf (C.coverage n).toGrothendieck)) _)
          (transitionInverseImageForgetComparison
            (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ
            (integerSheaf (C.coverage n).toGrothendieck)) =
        (sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (C.underlying.map φ).toFunctor Ab.{u}
            (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).unit.app
            (integerSheaf (C.coverage n).toGrothendieck)) := by
    rw [transitionInverseImageForgetComparison_inl]
    exact Equiv.apply_symm_apply _ _
  rw [transpose]
  show constantIntegerGenerator (C.coverage n).toGrothendieck ≫
    (sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (C.underlying.map φ).toFunctor Ab.{u} (C.coverage n).toGrothendieck
        (C.coverage m).toGrothendieck).unit.app _) ≫ _ = _
  show constantIntegerGenerator (C.coverage n).toGrothendieck ≫
    (sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (C.underlying.map φ).toFunctor Ab.{u} (C.coverage n).toGrothendieck
        (C.coverage m).toGrothendieck).unit.app _ ≫
        ((C.underlying.map φ).toFunctor.sheafPushforwardContinuous Ab.{u}
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).map
          (transitionIntegerIso' ⟨Sum.inl C⟩ φ).inv) = _
  show constantIntegerGenerator (C.coverage n).toGrothendieck ≫
    (sheafCompose (C.coverage n).toGrothendieck (forget Ab.{u})).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (C.underlying.map φ).toFunctor Ab.{u} (C.coverage n).toGrothendieck
        (C.coverage m).toGrothendieck).homEquiv
          (integerSheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n))
          (integerSheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m))
          (transitionIntegerIso' ⟨Sum.inl C⟩ φ).inv) = _
  rw [transitionIntegerIso_canonical_inl']
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext object
  apply ConcreteCategory.hom_ext
  intro point
  cases point
  show (constantIntegerRestriction (C.underlying.map φ).toFunctor
    (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).hom.app object
      ((constantIntegerGenerator (C.coverage n).toGrothendieck).hom.app object PUnit.unit) = _
  rw [constantIntegerGenerator_app]
  show (constantIntegerRestriction (C.underlying.map φ).toFunctor
    (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck).hom.app object
    ((toSheafify (C.coverage n).toGrothendieck ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).app object (ULift.up 1)) = _
  rw [constantIntegerRestriction_generator]
  rw [Adjunction.homEquiv_naturality_right]
  show _ = (constantIntegerGenerator (C.coverage m).toGrothendieck).hom.app
    ((C.underlying.map φ).toFunctor.op.obj object)
      ((((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.homEquiv _ _
        (transitionTerminalIso ⟨Sum.inl C⟩ φ).hom).hom.app object PUnit.unit)
  show _ = (constantIntegerGenerator (C.coverage m).toGrothendieck).hom.app _ PUnit.unit
  rw [constantIntegerGenerator_app]
  rfl

/-- In case (B) the underlying-set comparison along a simplicial transition carries the integer
generator in degree `n` to the one in degree `m`. -/
private theorem transitionIntegerGenerator_comparison_inr
    (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    let S : SimplicialSiteSituation.{u} := ⟨Sum.inr C⟩
    (S.transitionMorphism φ).inverseImage.map
        (constantIntegerGenerator (S.componentTopology n)) ≫
      transitionInverseImageForgetComparison S φ
        (integerSheaf (S.componentTopology n)) =
    (transitionTerminalIso S φ).hom ≫
      constantIntegerGenerator (S.componentTopology m) ≫
      (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
        (transitionIntegerIso' S φ).hom := by
  dsimp only
  let topology := (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m
  apply ((sheafificationAdjunction topology (Type u)).homEquiv _ _).injective
  refine ((Adjunction.homEquiv_naturality_right _ _ _).trans ?_).trans
    (Adjunction.homEquiv_naturality_right _ _ _).symm
  apply NatTrans.ext
  funext object
  apply ConcreteCategory.hom_ext
  intro point
  cases point
  show ((toSheafify topology _).app object ≫
    (((presheafToSheaf topology (Type u)).map
      (Functor.whiskerLeft (C.underlying.map φ.op).toFunctor.op
        (constantIntegerGenerator
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)).hom)).hom.app
      object) ≫
    (transitionInverseImageForgetComparison ⟨Sum.inr C⟩ φ
      (integerSheaf
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n))).hom.app object)
    PUnit.unit = _
  have unit_comparison := ((sheafificationAdjunction topology (Type u)).homEquiv _
    ((sheafCompose topology (forget Ab.{u})).obj
      ((transitionInverseImageAb ⟨Sum.inr C⟩ φ).obj
        (integerSheaf
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology
            n))))).apply_symm_apply
    (Functor.whiskerRight ((sheafificationAdjunction topology Ab.{u}).unit.app
      ((C.underlying.map φ.op).toFunctor.op ⋙
        (integerSheaf
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)).obj))
      (forget Ab.{u}))
  rw [Adjunction.homEquiv_unit] at unit_comparison
  have comparison_point := congrArg (fun arrow => arrow.app object
    (integerGenerator ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((C.underlying.map φ.op).toFunctor.op.obj object))) unit_comparison
  change (transitionInverseImageForgetComparison ⟨Sum.inr C⟩ φ
      (integerSheaf
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n))).hom.app object
    ((toSheafify (D := Type u) topology _).app object
      (integerGenerator ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        ((C.underlying.map φ.op).toFunctor.op.obj object))) = _ at comparison_point
  have move := congrArg (fun arrow => arrow.app object PUnit.unit)
    (toSheafify_naturality (J := topology)
      (Functor.whiskerLeft (C.underlying.map φ.op).toFunctor.op
        (constantIntegerGenerator
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)).hom))
  refine (Eq.trans (congrArg (fun element =>
      (transitionInverseImageForgetComparison ⟨Sum.inr C⟩ φ
          (integerSheaf
            ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n))).hom.app object
        element)
    (move.symm.trans (congrArg (fun element =>
        (toSheafify topology ((C.underlying.map φ.op).toFunctor.op ⋙
            ((sheafCompose ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
              (forget Ab.{u})).obj
              (integerSheaf
                ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n))).obj)).app
          object element)
      (constantIntegerGenerator_app
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        ((C.underlying.map φ.op).toFunctor.op.obj object))))) comparison_point).trans ?_
  have generator :
      (constantIntegerGenerator topology).hom.app object PUnit.unit =
        integerGenerator topology object :=
    constantIntegerGenerator_app topology object
  have canonical :
      (transitionIntegerIso' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).hom =
        constantIntegerPullback (C.underlying.map φ.op).toFunctor
          (topologyOfCoverings (C.coverage (Opposite.op m)))
          (topologyOfCoverings (C.coverage (Opposite.op n))) :=
    transitionIntegerIso_canonical_inr' C φ
  exact ((congrArg (fun element =>
        (transitionIntegerIso' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).hom.hom.app object
          element) generator).trans
      ((congrArg (fun arrow => arrow.hom.app object (integerGenerator topology object))
          canonical).trans
        (integerGenerator_sheafification _ _ _))).symm

/-- In case (A) the inverse-image transition carries the degree-`n` restricted generator of the
identity to the degree-`m` restricted generator labelled by `φ`. -/
private theorem resolutionFiberGenerator_inl
    (C : SimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    let S : SimplicialSiteSituation.{u} := ⟨Sum.inl C⟩
    let target := (sheafCompose S.totalTopology (forget Ab.{u})).obj
      ((resolutionSimplicial' S).obj (Opposite.op n))
    (S.transitionMorphism φ).inverseImage.map
        (constantIntegerGenerator (S.componentTopology n) ≫
          (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
            (resolutionRestrictedGenerator' S (𝟙 n))) ≫
      (fiberTransition S φ).app target =
    (transitionTerminalIso S φ).hom ≫
      constantIntegerGenerator (S.componentTopology m) ≫
      (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
        (resolutionRestrictedGenerator' S φ) := by
  let := (C.isMorphismOfSites φ).isContinuous
  dsimp only
  rw [fiberTransition_app_sheafCompose]
  refine (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans ?_
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _).symm
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext object
  apply ConcreteCategory.hom_ext
  intro point
  cases point
  show (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app
    ((sheafCompose _ (forget Ab.{u})).obj
      ((resolutionSimplicial' ⟨Sum.inl C⟩).obj (Opposite.op n)))).hom.app object
    ((resolutionRestrictedGenerator' ⟨Sum.inl C⟩ (𝟙 n)).hom.app object
      ((constantIntegerGenerator
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)).hom.app
          object PUnit.unit)) = _
  simp only [constantIntegerGenerator_app, resolutionRestrictedGenerator_integerGenerator,
    stdSimplexPresheafGenerator_generator']
  have naturality := (toSheafify
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology)
    (stdSimplexPresheafAb' ⟨Sum.inl C⟩ n)).naturality
      ((continuousInclusionTransition C φ).app object.unop).op
  have transported := congrArg (fun arrow => arrow.hom
    (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) naturality
  change (toSheafify (D := Ab.{u}) _ _).app _
    ((stdSimplexPresheafAb' ⟨Sum.inl C⟩ n).map
      ((continuousInclusionTransition C φ).app object.unop).op
      (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) =
    (((resolutionSimplicial' ⟨Sum.inl C⟩).obj (Opposite.op n)).obj.map
      ((continuousInclusionTransition C φ).app object.unop).op)
      ((toSheafify (D := Ab.{u}) _ _).app _
        (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) at transported
  have simplex :
      (stdSimplexPresheafGenerator' ⟨Sum.inl C⟩ φ).app
          ((C.underlying.map φ).toFunctor.op.obj object) (ULift.up 1) =
        (stdSimplexPresheafAb' ⟨Sum.inl C⟩ n).map
          ((continuousInclusionTransition C φ).app object.unop).op
          (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n))) :=
    (stdSimplexPresheafGenerator_generator' ⟨Sum.inl C⟩ φ
        ((C.underlying.map φ).toFunctor.op.obj object)).trans
      (congrArg FreeAbelianGroup.of (show _ =
          (stdSimplexPresheaf' ⟨Sum.inl C⟩ n).map
            ((continuousInclusionTransition C φ).app object.unop).op
            (SSet.stdSimplex.objEquiv.symm (𝟙 n)) from by
        show SSet.stdSimplex.objEquiv.symm φ = _
        show _ = (SSet.stdSimplex.map φ).app (Opposite.op n)
          (SSet.stdSimplex.objEquiv.symm (𝟙 n))
        rw [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp]))
  have target :
      (resolutionRestrictedGenerator' ⟨Sum.inl C⟩ φ).hom.app
          ((C.underlying.map φ).toFunctor.op.obj object)
          ((constantIntegerGenerator
            ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)).hom.app
              ((C.underlying.map φ).toFunctor.op.obj object) PUnit.unit) =
        (toSheafify ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology)
            (stdSimplexPresheafAb' ⟨Sum.inl C⟩ n)).app
          (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentFunctor m).op.obj
            ((C.underlying.map φ).toFunctor.op.obj object))
          ((stdSimplexPresheafGenerator' ⟨Sum.inl C⟩ φ).app
            ((C.underlying.map φ).toFunctor.op.obj object) (ULift.up 1)) :=
    (congrArg (fun element => (resolutionRestrictedGenerator' ⟨Sum.inl C⟩ φ).hom.app
        ((C.underlying.map φ).toFunctor.op.obj object) element)
      (constantIntegerGenerator_app
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        ((C.underlying.map φ).toFunctor.op.obj object))).trans
      (resolutionRestrictedGenerator_integerGenerator ⟨Sum.inl C⟩ φ
        ((C.underlying.map φ).toFunctor.op.obj object))
  exact transported.symm.trans
    ((congrArg (fun element => (toSheafify
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology)
        (stdSimplexPresheafAb' ⟨Sum.inl C⟩ n)).app
      (((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentFunctor m).op.obj
        ((C.underlying.map φ).toFunctor.op.obj object)) element) simplex).symm.trans target.symm)

/-- In case (B) the inverse-image transition carries the degree-`n` restricted generator of the
identity to the degree-`m` restricted generator labelled by `φ`. -/
private theorem resolutionFiberGenerator_inr
    (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m) :
    let S : SimplicialSiteSituation.{u} := ⟨Sum.inr C⟩
    let target := (sheafCompose S.totalTopology (forget Ab.{u})).obj
      ((resolutionSimplicial' S).obj (Opposite.op n))
    (S.transitionMorphism φ).inverseImage.map
        (constantIntegerGenerator (S.componentTopology n) ≫
          (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
            (resolutionRestrictedGenerator' S (𝟙 n))) ≫
      (fiberTransition S φ).app target =
    (transitionTerminalIso S φ).hom ≫
      constantIntegerGenerator (S.componentTopology m) ≫
      (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
        (resolutionRestrictedGenerator' S φ) := by
  dsimp only
  rw [fiberTransition_app_sheafCompose]
  refine (Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans ?_
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _).symm
  apply Sheaf.hom_ext
  apply (((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm.injective
  show (((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
    ((constantIntegerGenerator ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) ≫
      (sheafCompose _ (forget Ab.{u})).map
        (resolutionRestrictedGenerator' ⟨Sum.inr C⟩ (𝟙 n))).hom ≫
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app
        ((sheafCompose ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology)
          (forget Ab.{u})).obj
          ((resolutionSimplicial' ⟨Sum.inr C⟩).obj (Opposite.op n)))).hom) =
    (((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
      (((((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj.homEquiv _ _)
        (transitionTerminalIso ⟨Sum.inr C⟩ φ).hom).hom ≫
      (C.underlying.map φ.op).toFunctor.op.ran.map
        (constantIntegerGenerator
            ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m) ≫
          (sheafCompose _ (forget Ab.{u})).map
            (resolutionRestrictedGenerator' ⟨Sum.inr C⟩ φ)).hom)
  refine (Adjunction.homEquiv_naturality_left_symm _ _ _).trans
    (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm _ _ _).symm)
  apply NatTrans.ext
  funext object
  apply ConcreteCategory.hom_ext
  intro point
  cases point
  show ((((C.underlying.map φ.op).toFunctor.op.ranAdjunction (Type u)).homEquiv _ _).symm
    (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictTransition φ).app
      ((sheafCompose _ (forget Ab.{u})).obj
        ((resolutionSimplicial' ⟨Sum.inr C⟩).obj (Opposite.op n)))).hom).app object
    ((resolutionRestrictedGenerator' ⟨Sum.inr C⟩ (𝟙 n)).hom.app
      (Opposite.op ((C.underlying.map φ.op).toFunctor.obj object.unop) :
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ)
      ((constantIntegerGenerator
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)).hom.app
        (Opposite.op ((C.underlying.map φ.op).toFunctor.obj object.unop) :
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ)
        PUnit.unit)) = _
  simp only [constantIntegerGenerator_app, resolutionRestrictedGenerator_integerGenerator,
    stdSimplexPresheafGenerator_generator']
  have fibre := restrictTransition_inr_app C φ
    ((sheafCompose ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology)
      (forget Ab.{u})).obj ((resolutionSimplicial' ⟨Sum.inr C⟩).obj (Opposite.op n))) object.unop
  have naturality := (toSheafify
    ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology)
    (stdSimplexPresheafAb' ⟨Sum.inr C⟩ n)).naturality
      ((CategoryTheory.Grothendieck.ιNatTrans (F := C.underlying) φ.op).app object.unop).op
  have transported := congrArg (fun arrow => arrow.hom
    (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) naturality
  change (toSheafify (D := Ab.{u}) _ _).app _
    ((stdSimplexPresheafAb' ⟨Sum.inr C⟩ n).map
      ((CategoryTheory.Grothendieck.ιNatTrans (F := C.underlying) φ.op).app object.unop).op
      (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) =
    (((resolutionSimplicial' ⟨Sum.inr C⟩).obj (Opposite.op n)).obj.map
      ((CategoryTheory.Grothendieck.ιNatTrans (F := C.underlying) φ.op).app object.unop).op)
      ((toSheafify (D := Ab.{u}) _ _).app _
        (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n)))) at transported
  have simplex :
      (stdSimplexPresheafGenerator' ⟨Sum.inr C⟩ φ).app object (ULift.up 1) =
        (stdSimplexPresheafAb' ⟨Sum.inr C⟩ n).map
          ((CategoryTheory.Grothendieck.ιNatTrans (F := C.underlying) φ.op).app object.unop).op
          (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n))) :=
    (stdSimplexPresheafGenerator_generator' ⟨Sum.inr C⟩ φ object).trans
      (congrArg FreeAbelianGroup.of (show _ =
          (stdSimplexPresheaf' ⟨Sum.inr C⟩ n).map
            ((CategoryTheory.Grothendieck.ιNatTrans (F := C.underlying) φ.op).app object.unop).op
            (SSet.stdSimplex.objEquiv.symm (𝟙 n)) from by
        show SSet.stdSimplex.objEquiv.symm φ = _
        show _ = (SSet.stdSimplex.map φ).app (Opposite.op n)
          (SSet.stdSimplex.objEquiv.symm (𝟙 n))
        rw [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp]))
  have target :
      (resolutionRestrictedGenerator' ⟨Sum.inr C⟩ φ).hom.app object
          ((constantIntegerGenerator
            ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)).hom.app
              object PUnit.unit) =
        (toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology)
            (stdSimplexPresheafAb' ⟨Sum.inr C⟩ n)).app
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentFunctor m).op.obj object)
          ((stdSimplexPresheafGenerator' ⟨Sum.inr C⟩ φ).app object (ULift.up 1)) :=
    (congrArg (fun element => (resolutionRestrictedGenerator' ⟨Sum.inr C⟩ φ).hom.app object element)
      (constantIntegerGenerator_app
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m) object)).trans
      (resolutionRestrictedGenerator_integerGenerator ⟨Sum.inr C⟩ φ object)
  exact (congrArg (fun arrow => arrow
      ((toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology)
          (stdSimplexPresheafAb' ⟨Sum.inr C⟩ n)).app
        (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentFunctor n).op.obj
          (Opposite.op ((C.underlying.map φ.op).toFunctor.obj object.unop) :
            ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ))
        (FreeAbelianGroup.of (SSet.stdSimplex.objEquiv.symm (𝟙 n))))) fibre).trans
    (transported.symm.trans
      ((congrArg (fun element => (toSheafify
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology)
          (stdSimplexPresheafAb' ⟨Sum.inr C⟩ n)).app _ element) simplex).symm.trans target.symm))

/-- The summand of the degree-`m` restriction of the lower shriek image from degree `n` labelled by
a simplex map `φ : [n] ⟶ [m]`. -/
private noncomputable def lowerShriekSummand (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    integerSheaf (S.componentTopology m) ⟶
      ((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology).obj (componentIntegerSheaf S n) :=
  (transitionIntegerIso' S φ).hom ≫
    (Sigma.ι (fun ψ : n ⟶ m => transitionInverseImageAb S ψ) φ).app
      (integerSheaf (S.componentTopology n)) ≫
    (componentLowerShriekRestrictionIsoCoproduct S n m).inv.app
      (integerSheaf (S.componentTopology n))

/-- Substituting an identity between two factorizations of a middle stretch of a four-fold
composite: if `a ≫ b` is `ab` and `b ≫ c` is `e ≫ f`, then `ab ≫ c ≫ d` is `a ≫ e ≫ f ≫ d`. -/
private theorem comp_middle_eq {D : Type*} [Category D] {V W X Y Y' Z : D}
    {a : V ⟶ W} {b : W ⟶ X} {c : X ⟶ Y} {e : W ⟶ Y'} {f : Y' ⟶ Y} {d : Y ⟶ Z}
    {ab : V ⟶ X} (hab : a ≫ b = ab) (h : b ≫ c = e ≫ f) :
    ab ≫ c ≫ d = a ≫ e ≫ f ≫ d := by
  rw [← hab, Category.assoc, ← Category.assoc b c d, h, Category.assoc]

/-- Substituting an identity between two factorizations of the last stretch of a four-fold
composite. -/
private theorem comp_tail_eq {D : Type*} [Category D] {V W X Y Y' Z : D}
    {a : V ⟶ W} {b : W ⟶ X} {c : X ⟶ Y} {d : Y ⟶ Z} {e : X ⟶ Y'} {f : Y' ⟶ Z}
    (h : c ≫ d = e ≫ f) : a ≫ b ≫ c ≫ d = a ≫ b ≫ e ≫ f :=
  congrArg (fun arrow => a ≫ b ≫ arrow) h

/-- Collecting three successive images under a functor into the image of their composite, in
front of a fourth factor. -/
private theorem map_comp₃_comp {D E : Type*} [Category D] [Category E] {F : D ⥤ E}
    {W X Y Z : D} {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ Z} {T : E} {g : F.obj Z ⟶ T} :
    F.map a ≫ F.map b ≫ F.map c ≫ g = F.map (a ≫ b ≫ c) ≫ g := by
  simp only [Functor.map_comp, Category.assoc]

/-- Substituting an identity for the second factor inside the image of a composite. -/
private theorem map_comp_tail_eq {D E : Type*} [Category D] [Category E] {F : D ⥤ E}
    {W X Y : D} {a : W ⟶ X} {b b' : X ⟶ Y} {T : E} {g : F.obj Y ⟶ T} (h : b = b') :
    F.map (a ≫ b) ≫ g = F.map (a ≫ b') ≫ g :=
  congrArg (fun arrow => F.map (a ≫ arrow) ≫ g) h

/-- Cancelling an isomorphism prefixing both sides of an identity of composites, after
reassociating the left-hand side. -/
private theorem iso_cancel_assoc {D : Type*} [Category D] {T V W X : D} {i : T ≅ V}
    {g : V ⟶ W} {c : W ⟶ X} {h : V ⟶ X} (hyp : (i.hom ≫ g) ≫ c = i.hom ≫ h) :
    g ≫ c = h :=
  (i.cancel_iso_hom_left (g ≫ c) h).mp ((Category.assoc i.hom g c).symm.trans hyp)

/-- The degree comparison carries the summand labelled by `φ` to the restricted generator labelled
by `φ`. -/
private theorem lowerShriekSummand_degreeMap' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    lowerShriekSummand S φ ≫
      ((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology).map (resolutionDegreeMap' S n) =
    resolutionRestrictedGenerator' S φ := by
  have comparison := summandForgetCompatibility S φ
    (integerSheaf (S.componentTopology n))
  have generators :
      (S.transitionMorphism φ).inverseImage.map
          (constantIntegerGenerator (S.componentTopology n)) ≫
        transitionInverseImageForgetComparison S φ
          (integerSheaf (S.componentTopology n)) =
      (transitionTerminalIso S φ).hom ≫
        constantIntegerGenerator (S.componentTopology m) ≫
        (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
          (transitionIntegerIso' S φ).hom := by
    rcases S with ⟨C | C⟩
    · exact transitionIntegerGenerator_comparison_inl C φ
    · exact transitionIntegerGenerator_comparison_inr C φ
  have fiber :
      (S.transitionMorphism φ).inverseImage.map
          (constantIntegerGenerator (S.componentTopology n) ≫
            (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
              (resolutionRestrictedGenerator' S (𝟙 n))) ≫
        (fiberTransition S φ).app
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj
            ((resolutionSimplicial' S).obj (Opposite.op n))) =
      (transitionTerminalIso S φ).hom ≫
        constantIntegerGenerator (S.componentTopology m) ≫
        (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
          (resolutionRestrictedGenerator' S φ) := by
    rcases S with ⟨C | C⟩
    · exact resolutionFiberGenerator_inl C φ
    · exact resolutionFiberGenerator_inr C φ
  have unit_map :
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (componentFunctor S n) Ab.{u} (S.componentTopology n) S.totalTopology).unit.app
          (integerSheaf (S.componentTopology n)) ≫
        ((componentFunctor S n).sheafPushforwardContinuous Ab.{u}
          (S.componentTopology n) S.totalTopology).map (resolutionDegreeMap' S n) =
      resolutionRestrictedGenerator' S (𝟙 n) :=
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentFunctor S n) Ab.{u} (S.componentTopology n) S.totalTopology).homEquiv
        _ _).apply_symm_apply _
  have unit_underlying :
      (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (componentFunctor S n) Ab.{u} (S.componentTopology n) S.totalTopology).unit.app
              (integerSheaf (S.componentTopology n))) ≫
        (S.restrict n).map
          ((sheafCompose S.totalTopology (forget Ab.{u})).map (resolutionDegreeMap' S n)) =
      (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        (resolutionRestrictedGenerator' S (𝟙 n)) := by
    rcases S with ⟨C | C⟩
    all_goals
      exact (Functor.map_comp _ _ _).symm.trans
        (congrArg ((sheafCompose _ (forget Ab.{u})).map) unit_map)
  have transport :
      (fiberTransition S φ).app
            ((sheafCompose S.totalTopology (forget Ab.{u})).obj
              ((Functor.sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
                (S.componentTopology n) S.totalTopology).obj
                (integerSheaf (S.componentTopology n)))) ≫
          (S.restrict m).map
            ((sheafCompose S.totalTopology (forget Ab.{u})).map (resolutionDegreeMap' S n)) =
        (S.transitionMorphism φ).inverseImage.map
            ((S.restrict n).map
              ((sheafCompose S.totalTopology (forget Ab.{u})).map (resolutionDegreeMap' S n))) ≫
          (fiberTransition S φ).app
            ((sheafCompose S.totalTopology (forget Ab.{u})).obj
              ((resolutionSimplicial' S).obj (Opposite.op n))) :=
    ((fiberTransition S φ).naturality
      ((sheafCompose S.totalTopology (forget Ab.{u})).map (resolutionDegreeMap' S n))).symm
  have equation :
      ((transitionTerminalIso S φ).hom ≫
          constantIntegerGenerator (S.componentTopology m) ≫
          (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
            (transitionIntegerIso' S φ).hom) ≫
        (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
          ((Sigma.ι (fun ψ : n ⟶ m => transitionInverseImageAb S ψ) φ).app
              (integerSheaf (S.componentTopology n)) ≫
            (componentLowerShriekRestrictionIsoCoproduct S n m).inv.app
              (integerSheaf (S.componentTopology n))) ≫
        (S.restrict m).map
          ((sheafCompose S.totalTopology (forget Ab.{u})).map (resolutionDegreeMap' S n)) =
      (transitionTerminalIso S φ).hom ≫
        constantIntegerGenerator (S.componentTopology m) ≫
        (sheafCompose (S.componentTopology m) (forget Ab.{u})).map
          (resolutionRestrictedGenerator' S φ) :=
    (comp_middle_eq generators comparison).trans
      ((comp_tail_eq transport).trans
        (map_comp₃_comp.trans ((map_comp_tail_eq unit_underlying).trans fiber)))
  apply integerGenerator_hom_ext (S.componentTopology m)
  intro object
  have point := congrArg (fun arrow => arrow.hom.app object PUnit.unit)
    (iso_cancel_assoc equation)
  change ((lowerShriekSummand S φ ≫
    ((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
      (S.componentTopology m) S.totalTopology).map (resolutionDegreeMap' S n)).hom.app object)
      ((constantIntegerGenerator (S.componentTopology m)).hom.app object PUnit.unit) =
    (resolutionRestrictedGenerator' S φ).hom.app object
      ((constantIntegerGenerator (S.componentTopology m)).hom.app object PUnit.unit) at point
  simpa only [constantIntegerGenerator_app] using point

/-- Restricted to degree `m`, the lower shriek image of the constant integer sheaf in degree `n` is
the coproduct of its summands over the simplex maps `[n] ⟶ [m]`. -/
private noncomputable def lowerShriekRestrictionCofanIsColimit
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) :
    IsColimit (Cofan.mk _ (fun φ : n ⟶ m => lowerShriekSummand S φ)) := by
  let G := integerSheaf (S.componentTopology n)
  let diagram := fun φ : n ⟶ m =>
    transitionInverseImageAb S φ
  let evaluated := Cofan.mk ((∐ diagram).obj G)
    (fun φ : n ⟶ m => (Sigma.ι diagram φ).app G)
  letI : PreservesColimitsOfShape (Discrete (n ⟶ m))
      ((evaluation (Sheaf (S.componentTopology n) Ab.{u})
        (Sheaf (S.componentTopology m) Ab.{u})).obj G) :=
    evaluation_preservesColimitsOfShape G
  have evaluated_colimit : IsColimit evaluated :=
    (Cofan.isColimitMapCoconeEquiv
      ((evaluation _ _).obj G) _ (Cofan.mk _ (Sigma.ι diagram)))
      (isColimitOfPreserves ((evaluation _ _).obj G) (coproductIsCoproduct diagram))
  let comparison :
      Discrete.functor (fun _ : n ⟶ m =>
        integerSheaf (S.componentTopology m)) ≅
      Discrete.functor (fun φ : n ⟶ m => (diagram φ).obj G) :=
    Discrete.natIso (fun φ => transitionIntegerIso' S φ.as)
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv comparison evaluated).symm evaluated_colimit) ?_
  refine Cocone.ext
    ((componentLowerShriekRestrictionIsoCoproduct
      S n m).symm.app G) ?_
  intro entry
  change (_ ≫ _) ≫ _ = _
  exact Category.assoc _ _ _

/-- The degree comparison becomes an isomorphism after restriction to any simplicial degree. -/
private theorem resolutionDegreeMap_restriction_isIso' (S : SimplicialSiteSituation.{u})
    (n m : SimplexCategory) :
    IsIso (((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
      (S.componentTopology m) S.totalTopology).map (resolutionDegreeMap' S n)) := by
  let source := Cofan.mk _ (fun φ : n ⟶ m => lowerShriekSummand S φ)
  let target := resolutionRestrictionCofan S n m
  let morphism : source ⟶ target :=
    { hom := ((componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology).map (resolutionDegreeMap' S n)
      w := fun entry => lowerShriekSummand_degreeMap' S entry.as }
  let : IsIso morphism := IsColimit.hom_isIso
    (lowerShriekRestrictionCofanIsColimit S n m)
    (resolutionRestrictionCofanIsColimit S n m) morphism
  exact inferInstanceAs (IsIso ((Cocone.forget _).map morphism))

/-- The degree comparison is an isomorphism. -/
theorem resolutionDegreeMap_isIso' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    IsIso (resolutionDegreeMap' S n) := by
  suffices IsIso ((sheafToPresheaf _ _).map (resolutionDegreeMap' S n)) from
    isIso_of_reflects_iso (resolutionDegreeMap' S n) (sheafToPresheaf _ _)
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun object => ?_
  rcases S with ⟨C | C⟩
  · let := resolutionDegreeMap_restriction_isIso' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
      n object.unop.base.unop
    exact inferInstanceAs (IsIso
      (((Functor.sheafPushforwardContinuous
        (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) object.unop.base.unop)
        Ab.{u}
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology
          object.unop.base.unop)
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology).map
          (resolutionDegreeMap' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)).hom.app
            (Opposite.op object.unop.fiber)))
  · let := resolutionDegreeMap_restriction_isIso' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
      n object.unop.base.unop
    exact inferInstanceAs (IsIso
      (((Functor.sheafPushforwardContinuous
        (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) object.unop.base.unop)
        Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology
          object.unop.base.unop)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).map
          (resolutionDegreeMap' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n)).hom.app
            (Opposite.op object.unop.fiber)))

/-- **The lower shriek image of the constant integer sheaf is a sheafified free presheaf.** The
identification of the degree-`n` term of the resolution — the sheafification of the free abelian
presheaf on the presheaf of `n`-simplices — with the lower shriek image of the constant integer
sheaf in degree `n`. -/
noncomputable def resolutionDegreeIso' (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (presheafToSheaf S.totalTopology Ab.{u}).obj (stdSimplexPresheafAb' S n) ≅
      componentIntegerSheaf S n :=
  letI := resolutionDegreeMap_isIso' S n
  (asIso (resolutionDegreeMap' S n)).symm

/-- Under adjunction and the coproduct formula of Stacks 09WG, the `i`th face map of the simplicial
abelian sheaf of simplices is the inclusion of the summand labelled by the coface `δ i`. -/
theorem resolutionSimplicial_face_adjacent (S : SimplicialSiteSituation.{u}) (n : ℕ)
    (i : Fin (n + 2)) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentFunctor S ⦋n + 1⦌) Ab.{u}
      (S.componentTopology ⦋n + 1⦌) S.totalTopology).homEquiv _ _
      ((resolutionDegreeIso' S ⦋n + 1⦌).inv ≫ (resolutionSimplicial' S).δ i ≫
        (resolutionDegreeIso' S ⦋n⦌).hom) =
    (transitionIntegerIso' S (SimplexCategory.δ i)).hom ≫
      (Sigma.ι (fun φ : ⦋n⦌ ⟶ ⦋n + 1⦌ =>
        transitionInverseImageAb S φ)
        (SimplexCategory.δ i)).app
          (integerSheaf (S.componentTopology ⦋n⦌)) ≫
      (componentLowerShriekRestrictionIsoCoproduct
        S ⦋n⦌ ⦋n + 1⦌).inv.app
          (integerSheaf (S.componentTopology ⦋n⦌)) := by
  let := resolutionDegreeMap_isIso' S ⦋n⦌
  let := resolutionDegreeMap_isIso' S ⦋n + 1⦌
  show (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentFunctor S ⦋n + 1⦌) Ab.{u}
    (S.componentTopology ⦋n + 1⦌) S.totalTopology).homEquiv _ _
      (resolutionDegreeMap' S ⦋n + 1⦌ ≫
        (resolutionSimplicial' S).map (SimplexCategory.δ i).op ≫
        inv (resolutionDegreeMap' S ⦋n⦌)) =
    lowerShriekSummand S (SimplexCategory.δ i)
  apply (cancel_mono
    (((componentFunctor S ⦋n + 1⦌).sheafPushforwardContinuous Ab.{u}
      (S.componentTopology ⦋n + 1⦌) S.totalTopology).map
        (resolutionDegreeMap' S ⦋n⦌))).mp
  rw [← Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Adjunction.homEquiv_naturality_right]
  rw [show (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentFunctor S ⦋n + 1⦌) Ab.{u}
    (S.componentTopology ⦋n + 1⦌) S.totalTopology).homEquiv _ _
      (resolutionDegreeMap' S ⦋n + 1⦌) =
    resolutionRestrictedGenerator' S (𝟙 ⦋n + 1⦌) from Equiv.apply_symm_apply _ _]
  rw [resolutionRestrictedGenerator_map', Category.comp_id,
    lowerShriekSummand_degreeMap' S]

/-- The augmentation of the simplicial abelian sheaf of simplices is adjoint to restriction of the
integer generator to degree zero. -/
theorem resolutionAugmentation_adjacent (S : SimplicialSiteSituation.{u}) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (componentFunctor S ⦋0⦌) Ab.{u}
      (S.componentTopology ⦋0⦌) S.totalTopology).homEquiv _ _
      ((resolutionDegreeIso' S ⦋0⦌).inv ≫ resolutionAugmentation' S) =
    constantIntegerRestriction (componentFunctor S ⦋0⦌)
      (S.componentTopology ⦋0⦌) S.totalTopology := by
  show (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentFunctor S ⦋0⦌) Ab.{u} (S.componentTopology ⦋0⦌) S.totalTopology).homEquiv
      _ _ (resolutionDegreeMap' S ⦋0⦌ ≫ resolutionTermAugmentation' S ⦋0⦌) = _
  exact resolutionDegreeMap_augmentation' S ⦋0⦌

/-- The simplicial abelian sheaf of simplices, together with its degreewise identifications,
canonical transitions and exact augmentation. -/
noncomputable def resolutionIntegerResolution' (S : SimplicialSiteSituation.{u}) :
    SimplicialIntegerResolution S where
  simplicial := resolutionSimplicial' S
  degreeIso := fun n => resolutionDegreeIso' S ⦋n⦌
  transitionConstantIso := transitionIntegerIso' S
  transitionConstantIso_canonical := by
    rcases S with ⟨C | C⟩ <;> intro n m φ
    · exact transitionIntegerIso_canonical' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ
    · exact transitionIntegerIso_canonical' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ
  face_adjacent := resolutionSimplicial_face_adjacent S
  augmentation := resolutionAugmentation' S
  augmentation_adjacent := resolutionAugmentation_adjacent S
  augmentation_comp := resolutionAugmentation_comp' S
  exact_positive := resolutionSimplicial_exact_positive' S
  exact_zero := resolutionSimplicial_exact_zero' S
  augmentation_epi := resolutionAugmentation_epi' S

/-- **Stacks 09WI.** The lower shriek images of the constant integer sheaves form an
alternating-face resolution of the constant integer sheaf on the total site. -/
@[stacks 09WI "the resolution", sga "4 VIII 8.2" "resolution of Z"]
noncomputable def simplicialIntegerResolution (S : SimplicialSiteSituation.{u}) :
    SimplicialIntegerResolution S :=
  resolutionIntegerResolution' S

/-- The simplicial abelian sheaf underlying the resolution of Stacks 09WI is the degreewise
sheafification of the simplicial abelian presheaf of simplices. -/
theorem simplicialIntegerResolution_simplicial (S : SimplicialSiteSituation.{u}) :
    (simplicialIntegerResolution S).simplicial = resolutionSimplicial' S := rfl

/-- The degreewise identification of the resolution of Stacks 09WI with the lower shriek
images is the one of `resolutionDegreeIso'`. -/
theorem simplicialIntegerResolution_degreeIso (S : SimplicialSiteSituation.{u}) (n : ℕ) :
    (simplicialIntegerResolution S).degreeIso n = resolutionDegreeIso' S ⦋n⦌ := rfl

/-- The alternating-face chain complex `… → g_{2!} Z → g_{1!} Z → g_{0!} Z` of the simplicial
resolution of Stacks 09WI. -/
@[stacks 09WI "the complex"]
noncomputable abbrev simplicialIntegerComplex (S : SimplicialSiteSituation.{u}) :
    ChainComplex (Sheaf S.totalTopology Ab.{u}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (simplicialIntegerResolution S).simplicial

end SimplicialSiteSituation

end CategoryTheory

end
