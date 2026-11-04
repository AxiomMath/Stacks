module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism

/-!
# The resolution of the inverse image of an abelian sheaf along an augmentation

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
For an abelian sheaf `𝒢` on `(D, K)`, Stacks 0D78 asserts that there is an exact complex

`… ⟶ g_{2!}(a_2⁻¹𝒢) ⟶ g_{1!}(a_1⁻¹𝒢) ⟶ g_{0!}(a_0⁻¹𝒢) ⟶ a⁻¹𝒢 ⟶ 0`

of abelian sheaves on the total site, where `g_{n!}` is extension by zero along the inclusion of
the component of simplicial degree `n` and `a_n` is the augmentation of that degree.

The complex is built here, with all of its exactness, for an arbitrary abelian sheaf `F` on the
total site in place of `a⁻¹𝒢`: it is the alternating-face complex of the *simplex-coefficient*
simplicial abelian sheaf, whose degree-`n` term is the sheafification of the presheaf sending an
object of the total category of simplicial degree `k` to the direct sum of the sections of `F`
over that object indexed by the simplex maps `⦋n⦌ ⟶ ⦋k⦌`. Over a single object this is the
copower of one abelian group by the standard `k`-simplex, so the extra degeneracy of the standard
simplex gives a contracting homotopy objectwise; sheafification is exact, so the complex of
sheaves is exact in every positive degree and at its augmentation onto `F`, and the augmentation
is split epimorphic already on presheaves.

Taking `F = a⁻¹𝒢` therefore produces an exact complex augmented onto `a⁻¹𝒢`. Its degree-`n`
term is identified with `g_{n!}(a_n⁻¹𝒢)` in
`StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms`, by the direct-sum
formula of Stacks 09WG read at `a⁻¹𝒢`, which applies because `a⁻¹𝒢` is a cartesian sheaf
(Stacks 0D7H); that module carries the resolution of Stacks 0D78 itself.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.simplexCoefficientDiagram` and
  `.simplexCoefficientAugmented`: the simplex-coefficient simplicial object of a functor into an
  abelian category with coproducts, and its augmentation.
* `CategoryTheory.SimplicialSiteSituation.barSimplicial`, `.barAugmented` and
  `.barAugmentation`: the sheafified simplex-coefficient resolution of an abelian sheaf on the
  total site, and its augmentation onto that sheaf.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentInverseImageAb` and
  `.totalInverseImageAb`: the inverse images `a_n⁻¹` and `a⁻¹` on abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionTerm`: the term
  `g_{n!}(a_n⁻¹𝒢)`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.Resolution`: the exact complex of
  Stacks 0D78 as a structure — a simplicial abelian sheaf on the total site whose degree-`n` term
  is `g_{n!}(a_n⁻¹𝒢)`, an augmentation of its alternating-face complex onto `a⁻¹𝒢`, exactness in
  every positive degree, exactness at the augmentation, and epimorphy of the augmentation.

## Main results

* `CategoryTheory.SimplicialSiteSituation.exactAt_of_extraDegeneracy` and
  `.extraDegeneracy_exact_zero`: an augmented simplicial object with an extra degeneracy has an
  exact alternating-face complex, in positive degrees and at the augmentation.
* `CategoryTheory.SimplicialSiteSituation.barSimplicial_exactAt`,
  `.barAugmentation_exact` and `.barAugmentation_epi`: the simplex-coefficient resolution of an
  abelian sheaf on the total site is exact in every positive degree and at its augmentation, and
  its augmentation is an epimorphism.

## Implementation notes

The summands are indexed by the morphisms of `SimplexCategory`, which live in `Type`, so only
`CategoryTheory.Limits.HasCoproducts.{0}` is needed and no universe lifting appears.

Exactness is proved at the level of presheaves, where it is objectwise, and transported along
sheafification. Objectwise, the restriction of the simplex-coefficient diagram to one object is
the copower of its sections by the standard simplex on its own simplicial degree, and this
identification is the identity on the nose, so the extra degeneracy is written down directly
rather than transported along an isomorphism.

Several of the equations below are between morphisms whose source and target are spelled
differently but definitionally equally — typically `(Opposite.op ⦋n⦌).unop` against `⦋n⦌`, or the
augmentation of a whiskered augmented simplicial object against its unitor. A rewrite elaborates
its motive at a reduced transparency and fails on those; they are therefore taken either by
`change` to re-spell the goal or by `exact` against an explicit chain of `Category.assoc`,
`Category.comp_id` and `CategoryTheory.Limits.Sigma.ι_desc`, where definitional equality is
available.

The isomorphism class of the sheafification counit at a sheaf is supplied as an explicit term
rather than by instance search, since the two `HasWeakSheafify` instances in play — the one
derived from the `HasSheafify` hypothesis and the one instance search constructs — are not the
same term.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v w

namespace CategoryTheory.SimplicialSiteSituation

/-! ### Copowers indexed by the simplices over an object -/

section Copowers

variable {C : Type v} [Category.{w} C] [HasCoproducts.{0} C]

/-- The map between two copowers induced by a reindexing of the summands and a map of the
summand object. -/
def copowerMap {I J : Type} (f : I → J) {X Y : C} (h : X ⟶ Y) :
    (∐ fun _ : I => X) ⟶ ∐ fun _ : J => Y :=
  Sigma.desc fun i => h ≫ Sigma.ι (fun _ : J => Y) (f i)

/-- The summand inclusions of a copower map. -/
@[local simp, reassoc] lemma ι_copowerMap {I J : Type} (f : I → J)
    {X Y : C} (h : X ⟶ Y) (i : I) :
    Sigma.ι (fun _ : I => X) i ≫ copowerMap f h =
      h ≫ Sigma.ι (fun _ : J => Y) (f i) := by simp [copowerMap]

/-- The copower map of an identity reindexing and an identity map is the identity. -/
@[local simp] lemma copowerMap_id (I : Type) (X : C) :
    copowerMap (id : I → I) (𝟙 X) = 𝟙 _ :=
  Sigma.hom_ext _ _ fun _ => by simp

/-- Copower maps compose. -/
@[local simp] lemma copowerMap_comp {I J L : Type} (f : I → J) (g : J → L)
    {X Y Z : C} (h : X ⟶ Y) (k : Y ⟶ Z) :
    copowerMap (g ∘ f) (h ≫ k) = copowerMap f h ≫ copowerMap g k :=
  Sigma.hom_ext _ _ fun _ => by simp [copowerMap]

/-- The simplicial object whose degree-`n` term sends an object `U` to the copower of `F.obj U`
indexed by the simplex maps `⦋n⦌ ⟶ p U`, with structure maps reindexing the summands by
precomposition. -/
def simplexCoefficientDiagram {B : Type u} [Category B]
    (p : B ⥤ SimplexCategory) (F : B ⥤ C) : SimplicialObject (B ⥤ C) where
  obj n :=
    { obj U := ∐ fun _ : n.unop ⟶ p.obj U => F.obj U
      map {U V} f := copowerMap (fun φ => φ ≫ p.map f) (F.map f)
      map_id U := by
        apply Sigma.hom_ext
        intro φ
        simp [copowerMap]
      map_comp f g := by
        simp only [Functor.map_comp, ← copowerMap_comp]
        rfl }
  map {n m} θ :=
    { app U := copowerMap (fun φ => θ.unop ≫ φ) (𝟙 (F.obj U))
      naturality U V f := by
        simp only [← copowerMap_comp, Category.id_comp, Category.comp_id]
        rfl }
  map_id n := by
    apply NatTrans.ext
    funext U
    apply Sigma.hom_ext
    intro φ
    simp [copowerMap]
  map_comp θ η := by
    apply NatTrans.ext
    funext U
    apply Sigma.hom_ext
    intro φ
    simp [copowerMap, Category.assoc]

/-- The functor carrying `F` to the simplicial object whose degree-`n` term sends an object `U`
to the copower of `F.obj U` indexed by the simplex maps `⦋n⦌ ⟶ p U`, with structure maps
reindexing the summands by precomposition; a morphism `F ⟶ G` acts on each summand separately. -/
def simplexCoefficientDiagram' {B : Type u} [Category B]
    (p : B ⥤ SimplexCategory) : (B ⥤ C) ⥤ SimplicialObject (B ⥤ C) where
  obj F :=
    { obj n :=
        { obj U := ∐ fun _ : n.unop ⟶ p.obj U => F.obj U
          map {U V} f := copowerMap (fun φ => φ ≫ p.map f) (F.map f)
          map_id U := by
            apply Sigma.hom_ext
            intro φ
            simp [copowerMap]
          map_comp f g := by
            simp only [Functor.map_comp, ← copowerMap_comp]
            rfl }
      map {n m} θ :=
        { app U := copowerMap (fun φ => θ.unop ≫ φ) (𝟙 (F.obj U))
          naturality U V f := by
            simp only [← copowerMap_comp, Category.id_comp, Category.comp_id]
            rfl }
      map_id n := by
        apply NatTrans.ext
        funext U
        apply Sigma.hom_ext
        intro φ
        simp [copowerMap]
      map_comp θ η := by
        apply NatTrans.ext
        funext U
        apply Sigma.hom_ext
        intro φ
        simp [copowerMap, Category.assoc] }
  map {F G} α :=
    { app n :=
        { app U := copowerMap id (α.app U)
          naturality U V f := by
            apply Sigma.hom_ext
            intro φ
            simp [ι_copowerMap_assoc] }
      naturality n m θ := by
        apply NatTrans.ext
        funext U
        apply Sigma.hom_ext
        intro φ
        simp [ι_copowerMap_assoc] }
  map_id F := by
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext U
    apply Sigma.hom_ext
    intro φ
    simp
  map_comp α β := by
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext U
    apply Sigma.hom_ext
    intro φ
    simp [ι_copowerMap_assoc]

/-- The augmentation of `simplexCoefficientDiagram` towards `F`: in each degree it sums the
summands by the identity of `F.obj U`. -/
def simplexCoefficientAugmentation {B : Type u} [Category B]
    (p : B ⥤ SimplexCategory) (F : B ⥤ C) :
    simplexCoefficientDiagram p F ⟶ (SimplicialObject.const _).obj F where
  app n :=
    { app U := Sigma.desc fun _ => 𝟙 _
      naturality U V f := by
        apply Sigma.hom_ext
        intro φ
        simp [simplexCoefficientDiagram, copowerMap] }
  naturality n m θ := by
    ext U
    apply Sigma.hom_ext
    intro φ
    simp [simplexCoefficientDiagram, copowerMap]

/-- The augmentation of `simplexCoefficientDiagram'` towards `F`: in each degree it sums the
summands by the identity of `F.obj U`. -/
def simplexCoefficientAugmentation' {B : Type u} [Category B]
    (p : B ⥤ SimplexCategory) (F : B ⥤ C) :
    (simplexCoefficientDiagram' p).obj F ⟶ (SimplicialObject.const _).obj F where
  app n :=
    { app U := Sigma.desc fun _ => 𝟙 _
      naturality U V f := by
        apply Sigma.hom_ext
        intro φ
        simp [simplexCoefficientDiagram', copowerMap] }
  naturality n m θ := by
    ext U
    apply Sigma.hom_ext
    intro φ
    simp [simplexCoefficientDiagram', copowerMap]

/-- `simplexCoefficientDiagram` as an augmented simplicial object, augmented by `F`. -/
def simplexCoefficientAugmented {B : Type u} [Category B]
    (p : B ⥤ SimplexCategory) (F : B ⥤ C) : SimplicialObject.Augmented (B ⥤ C) where
  left := simplexCoefficientDiagram p F
  right := F
  hom := simplexCoefficientAugmentation p F

/-- Evaluated at an object `U`, the augmented simplicial object `simplexCoefficientAugmented`
has an extra degeneracy: it is the copower of `F.obj U` by the standard simplex on `p U`, and
the extra degeneracy of the standard simplex shifts a simplex map. -/
def simplexCoefficientExtraDegeneracy {B : Type u} [Category B]
    (p : B ⥤ SimplexCategory) (F : B ⥤ C) (U : B) :
    (((SimplicialObject.Augmented.whiskering _ _).obj ((evaluation B C).obj U)).obj
      (simplexCoefficientAugmented p F)).ExtraDegeneracy where
  s' := Sigma.ι (fun _ : Opposite.unop (Opposite.op ⦋0⦌) ⟶ p.obj U => F.obj U)
    (SimplexCategory.Hom.mk (OrderHom.const _ 0))
  s _ := copowerMap SSet.Augmented.StandardSimplex.shift (𝟙 _)
  s'_comp_ε := by
    change Sigma.ι (fun _ : Opposite.unop (Opposite.op ⦋0⦌) ⟶ p.obj U => F.obj U)
          (SimplexCategory.Hom.mk (OrderHom.const _ 0)) ≫
        ((Sigma.desc fun _ : Opposite.unop (Opposite.op ⦋0⦌) ⟶ p.obj U => 𝟙 (F.obj U)) ≫
          𝟙 (F.obj U)) = 𝟙 (F.obj U)
    rw [Category.comp_id]
    exact Sigma.ι_desc _ _
  s₀_comp_δ₁ := by
    apply Sigma.hom_ext
    intro φ
    simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
      SimplicialObject.Augmented.drop_obj, Functor.whiskeringRight_obj_obj,
      SimplicialObject.Augmented.point_obj, Functor.id_obj, evaluation_obj_obj, evaluation_obj_map,
      simplexCoefficientAugmented, simplexCoefficientDiagram, copowerMap,
      simplexCoefficientAugmentation, Functor.const_obj_obj, Functor.comp_obj, Nat.reduceAdd,
      SSet.Augmented.StandardSimplex.shift, Category.id_comp, SimplicialObject.δ, Fin.isValue,
      Functor.comp_map, Quiver.Hom.unop_op, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
      Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.constComp_hom_app, Category.comp_id]
    congr 1
    ext j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    apply Sigma.hom_ext
    intro φ
    simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
      SimplicialObject.Augmented.drop_obj, Functor.whiskeringRight_obj_obj,
      SimplicialObject.Augmented.point_obj, Functor.id_obj, evaluation_obj_obj, evaluation_obj_map,
      simplexCoefficientAugmented, simplexCoefficientDiagram, copowerMap, Functor.comp_obj,
      SSet.Augmented.StandardSimplex.shift, Category.id_comp, SimplicialObject.δ, Functor.comp_map,
      Quiver.Hom.unop_op, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, colimit.ι_desc, Category.comp_id]
    congr 1
    ext j
    rfl
  s_comp_δ n i := by
    apply Sigma.hom_ext
    intro φ
    simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
      SimplicialObject.Augmented.drop_obj, Functor.whiskeringRight_obj_obj,
      SimplicialObject.Augmented.point_obj, Functor.id_obj, evaluation_obj_obj, evaluation_obj_map,
      simplexCoefficientAugmented, simplexCoefficientDiagram, copowerMap, Functor.comp_obj,
      SSet.Augmented.StandardSimplex.shift, Category.id_comp, SimplicialObject.δ, Functor.comp_map,
      Quiver.Hom.unop_op, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, colimit.ι_desc, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe]
    congr 1
    ext j
    cases j using Fin.cases <;>
      simp [SSet.Augmented.StandardSimplex.shiftFun, SimplexCategory.δ] <;> rfl
  s_comp_σ n i := by
    apply Sigma.hom_ext
    intro φ
    simp only [SimplicialObject.Augmented.whiskering, SimplicialObject.Augmented.whiskeringObj,
      SimplicialObject.Augmented.drop_obj, Functor.whiskeringRight_obj_obj,
      SimplicialObject.Augmented.point_obj, Functor.id_obj, evaluation_obj_obj, evaluation_obj_map,
      simplexCoefficientAugmented, simplexCoefficientDiagram, copowerMap, Functor.comp_obj,
      SSet.Augmented.StandardSimplex.shift, Category.id_comp, SimplicialObject.σ, Functor.comp_map,
      Quiver.Hom.unop_op, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, colimit.ι_desc, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe]
    congr 1
    ext j
    cases j using Fin.cases <;>
      simp [SSet.Augmented.StandardSimplex.shiftFun, SimplexCategory.σ] <;> rfl

end Copowers

/-! ### Exactness of an augmented simplicial object with an extra degeneracy -/

section Exactness

variable {C : Type v} [Category.{w} C] [Abelian C]

/-- A short complex is exact as soon as the identity of its middle term is a retraction of its
first map plus a section of its second. -/
lemma exact_of_contracting (T : ShortComplex C)
    (r : T.X₂ ⟶ T.X₁) (s : T.X₃ ⟶ T.X₂) (h : r ≫ T.f + T.g ≫ s = 𝟙 _) :
    T.Exact := by
  rw [T.exact_iff_epi_kernel_lift]
  apply Epi.mk
  intro Z a b hab
  have hr : kernel.ι T.g ≫ r ≫ T.f = kernel.ι T.g := by
    simpa [Preadditive.comp_add] using congrArg (kernel.ι T.g ≫ ·) h
  have he : (kernel.ι T.g ≫ r) ≫ kernel.lift T.g T.f T.zero = 𝟙 _ := by
    apply (cancel_mono (kernel.ι T.g)).mp
    simpa using hr
  calc
    a = (kernel.ι T.g ≫ r) ≫ kernel.lift T.g T.f T.zero ≫ a := by
      rw [← Category.assoc, he]; simp
    _ = (kernel.ι T.g ≫ r) ≫ kernel.lift T.g T.f T.zero ≫ b := by rw [hab]
    _ = b := by rw [← Category.assoc, he]; simp

/-- The first differential of the alternating-face complex composed with the augmentation of an
augmented simplicial object vanishes. -/
lemma augmented_d_comp (Y : SimplicialObject.Augmented C) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y.left).d 1 0 ≫
      Y.hom.app (Opposite.op ⦋0⦌) = 0 := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Preadditive.add_comp, Preadditive.neg_comp]
  have h : ∀ i : Fin 2, Y.left.δ i ≫ Y.hom.app (Opposite.op ⦋0⦌) =
      Y.hom.app (Opposite.op ⦋1⦌) := fun i => by
    simp [SimplicialObject.δ]
  rw [h 0, h 1]
  abel

/-- The short complex of the first differential of the alternating-face complex and the
augmentation. -/
def augmentedShortComplex (Y : SimplicialObject.Augmented C) : ShortComplex C :=
  ShortComplex.mk _ _ (augmented_d_comp Y)

/-- An extra degeneracy makes the augmented short complex exact. -/
lemma extraDegeneracy_exact_zero (Y : SimplicialObject.Augmented C)
    (ed : Y.ExtraDegeneracy) : (augmentedShortComplex Y).Exact := by
  apply exact_of_contracting _ (ed.s 0) ed.s'
  dsimp [augmentedShortComplex]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  rw [ed.s_comp_δ₀, ed.s₀_comp_δ₁]
  abel

/-- An extra degeneracy makes the alternating-face complex exact in every positive degree. -/
theorem exactAt_of_extraDegeneracy (Y : SimplicialObject.Augmented C)
    (ed : Y.ExtraDegeneracy) (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (SimplicialObject.Augmented.drop.obj Y)).ExactAt n := by
  show (AlgebraicTopology.AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj Y)).ExactAt n
  rw [exactAt_iff_of_quasiIsoAt ed.homotopyEquiv.hom n]
  exact HomologicalComplex.exactAt_single_obj _ 0 _ n (by omega)

/-- A short complex of functors is exact as soon as all of its evaluations are. -/
lemma exact_of_evaluation {B : Type u} [Category B]
    (T : ShortComplex (B ⥤ C))
    (h : ∀ U, (T.map ((evaluation B C).obj U)).Exact) : T.Exact := by
  rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext U
  exact (IsZero.of_iso ((T.map ((evaluation B C).obj U)).exact_iff_isZero_homology.mp (h U))
    (T.mapHomologyIso ((evaluation B C).obj U)).symm).eq_of_src _ _

/-- The alternating-face complex of the simplex-coefficient diagram is exact in every positive
degree. -/
@[sga "4 Vbis 2.3.9" "partial"]
lemma simplexCoefficient_exact_positive {B : Type u} [Category B]
    [HasCoproducts.{0} C] (p : B ⥤ SimplexCategory) (F : B ⥤ C)
    (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (simplexCoefficientDiagram p F)).ExactAt n :=
  exact_of_evaluation _ fun U =>
    (exactAt_of_extraDegeneracy
      (((SimplicialObject.Augmented.whiskering _ _).obj ((evaluation B C).obj U)).obj
        (simplexCoefficientAugmented p F))
      (simplexCoefficientExtraDegeneracy p F U) n hn).of_iso
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      ((evaluation B C).obj U)).app (simplexCoefficientDiagram p F)).symm

/-- The alternating-face complex of the simplex-coefficient diagram
`(simplexCoefficientDiagram' p).obj F` is exact in every positive degree. -/
@[sga "4 Vbis 2.3.9" "partial"]
lemma simplexCoefficient_exact_positive' {B : Type u} [Category B]
    [HasCoproducts.{0} C] (p : B ⥤ SimplexCategory) (F : B ⥤ C)
    (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      ((simplexCoefficientDiagram' p).obj F)).ExactAt n :=
  simplexCoefficient_exact_positive p F n hn

/-- An additive functor carries the augmented short complex of an augmented simplicial object to
the augmented short complex of its image. -/
def augmentedShortComplexMapIso {D : Type*} [Category D] [Abelian D]
    (Y : SimplicialObject.Augmented C) (F : C ⥤ D) [F.Additive] :
    (augmentedShortComplex Y).map F ≅
      augmentedShortComplex (((SimplicialObject.Augmented.whiskering _ _).obj F).obj Y) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp [augmentedShortComplex, SimplicialObject.Augmented.whiskering,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD])
    (by simp [augmentedShortComplex, SimplicialObject.Augmented.whiskering])

/-- The augmented short complex of the simplex-coefficient diagram is exact. -/
@[sga "4 Vbis 2.3.9" "partial"]
lemma simplexCoefficient_exact_zero {B : Type u} [Category B]
    [HasCoproducts.{0} C] (p : B ⥤ SimplexCategory) (F : B ⥤ C) :
    (augmentedShortComplex (simplexCoefficientAugmented p F)).Exact :=
  exact_of_evaluation _ fun U => ShortComplex.exact_of_iso
    (augmentedShortComplexMapIso (simplexCoefficientAugmented p F)
      ((evaluation B C).obj U)).symm
    (extraDegeneracy_exact_zero _ (simplexCoefficientExtraDegeneracy p F U))

end Exactness

/-! ### The sheafified simplex-coefficient resolution of an abelian sheaf -/

section SheafResolution

variable {B : Type u} [Category.{u} B] (J : GrothendieckTopology B) [HasSheafify J Ab.{u}]
  (p : Bᵒᵖ ⥤ SimplexCategory) (F : Sheaf J Ab.{u})

/-- The simplex-coefficient diagram of the underlying presheaf of `F`, sheafified degreewise and
augmented by the sheafification of `F`. -/
def sheafSimplexAugmented : SimplicialObject.Augmented (Sheaf J Ab.{u}) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (presheafToSheaf J Ab.{u})).obj
    (simplexCoefficientAugmented p F.obj)

/-- The sheafified simplex-coefficient complex is exact in every positive degree. -/
lemma sheafSimplex_exact_positive (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (sheafSimplexAugmented J p F).left).ExactAt n := by
  have h := (simplexCoefficient_exact_positive p F.obj n hn).map (presheafToSheaf J Ab.{u})
  have h' : (((presheafToSheaf J Ab.{u}).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (simplexCoefficientDiagram p F.obj))).ExactAt n := h
  exact HomologicalComplex.ExactAt.of_iso h'
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (presheafToSheaf J Ab.{u})).app (simplexCoefficientDiagram p F.obj))

/-- The sheafified simplex-coefficient complex is exact at the augmentation. -/
lemma sheafSimplex_exact_zero :
    (augmentedShortComplex (sheafSimplexAugmented J p F)).Exact :=
  ShortComplex.exact_of_iso
    (augmentedShortComplexMapIso (simplexCoefficientAugmented p F.obj)
      (presheafToSheaf J Ab.{u}))
    ((simplexCoefficient_exact_zero p F.obj).map (presheafToSheaf J Ab.{u}))

/-- The augmentation of the sheafified simplex-coefficient complex is an epimorphism. -/
lemma sheafSimplex_augmentation_epi :
    Epi ((sheafSimplexAugmented J p F).hom.app (Opposite.op ⦋0⦌)) := by
  have hsplit (U : Bᵒᵖ) :
      Epi (((simplexCoefficientAugmented p F.obj).hom.app (Opposite.op ⦋0⦌)).app U) := by
    refine (show SplitEpi (((simplexCoefficientAugmented p F.obj).hom.app
      (Opposite.op ⦋0⦌)).app U) from
        ⟨Sigma.ι (fun _ : Opposite.unop (Opposite.op ⦋0⦌) ⟶ p.obj U => F.obj.obj U)
          (SimplexCategory.Hom.mk (OrderHom.const _ 0)), ?_⟩).epi
    exact Sigma.ι_desc _ _
  have hepi : Epi ((simplexCoefficientAugmented p F.obj).hom.app (Opposite.op ⦋0⦌)) :=
    NatTrans.epi_of_epi_app _
  have h1 : Epi ((presheafToSheaf J Ab.{u}).map
      ((simplexCoefficientAugmented p F.obj).hom.app (Opposite.op ⦋0⦌))) :=
    Functor.map_epi _ _
  have h2 : IsIso ((Functor.constComp SimplexCategoryᵒᵖ
      (simplexCoefficientAugmented p F.obj).right (presheafToSheaf J Ab.{u})).hom.app
      (Opposite.op ⦋0⦌)) := inferInstance
  show Epi ((presheafToSheaf J Ab.{u}).map
      ((simplexCoefficientAugmented p F.obj).hom.app (Opposite.op ⦋0⦌)) ≫
    (Functor.constComp SimplexCategoryᵒᵖ
      (simplexCoefficientAugmented p F.obj).right (presheafToSheaf J Ab.{u})).hom.app
      (Opposite.op ⦋0⦌))
  exact epi_comp _ _

/-- The augmentation of the sheafified simplex-coefficient complex, normalized so that it lands
in `F` itself rather than in its sheafification. -/
def sheafSimplexAugmentation :
    (sheafSimplexAugmented J p F).left.obj (Opposite.op ⦋0⦌) ⟶ F :=
  (sheafSimplexAugmented J p F).hom.app (Opposite.op ⦋0⦌) ≫
    (sheafificationAdjunction J Ab.{u}).counit.app F

/-- The normalized augmentation annihilates the first differential. -/
lemma sheafSimplexAugmentation_comp :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (sheafSimplexAugmented J p F).left).d 1 0 ≫ sheafSimplexAugmentation J p F = 0 :=
  (Category.assoc _ _ _).symm.trans ((augmented_d_comp _ =≫ _).trans zero_comp)

/-- The normalized augmentation is exact in degree zero. -/
lemma sheafSimplexAugmentation_exact :
    (ShortComplex.mk _ _ (sheafSimplexAugmentation_comp J p F)).Exact := by
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := augmentedShortComplex (sheafSimplexAugmented J p F))
      (S₂ := ShortComplex.mk _ _ (sheafSimplexAugmentation_comp J p F))
      (Iso.refl _) (Iso.refl _)
      (@asIso _ _ _ _ _ (isIso_sheafificationAdjunction_counit (J := J) (D := Ab.{u}) F))
      ?_ ?_)
    (sheafSimplex_exact_zero J p F)
  · simp [augmentedShortComplex]
  · simp [augmentedShortComplex, sheafSimplexAugmentation]
    rfl

/-- The normalized augmentation is an epimorphism. -/
lemma sheafSimplexAugmentation_epi : Epi (sheafSimplexAugmentation J p F) := by
  have h1 := sheafSimplex_augmentation_epi J p F
  have h2 : Epi ((sheafificationAdjunction J Ab.{u}).counit.app F) :=
    @IsIso.epi_of_iso _ _ _ _ _
      (isIso_sheafificationAdjunction_counit (J := J) (D := Ab.{u}) F)
  show Epi ((sheafSimplexAugmented J p F).hom.app (Opposite.op ⦋0⦌) ≫
    (sheafificationAdjunction J Ab.{u}).counit.app F)
  exact @epi_comp _ _ _ _ _ _ h1 _ h2

end SheafResolution

/-! ### The resolution on the total site of a simplicial-site situation -/

section Total

variable (S : SimplicialSiteSituation.{u})

/-- The simplicial degree of an object of the total category, as a functor. -/
def degreeFunctor : S.totalCategory ⥤ SimplexCategoryᵒᵖ :=
  match S with
  | ⟨Sum.inl C⟩ => Pseudofunctor.CoGrothendieck.forget C.totalPseudofunctor
  | ⟨Sum.inr C⟩ => CategoryTheory.Grothendieck.forget C.underlying

/-- Lower shriek on abelian sheaves from the component of degree `n` to the total site. -/
abbrev componentLowerShriekAb (n : SimplexCategory) :
    Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf S.totalTopology Ab.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
    (S.componentTopology n) S.totalTopology

/-- The simplex-coefficient resolution of an abelian sheaf on the total site, augmented by that
sheaf: in degree `n` it is the sheafification of the presheaf whose sections over an object of
degree `k` are the copower of the sections indexed by the simplex maps `⦋n⦌ ⟶ ⦋k⦌`. -/
def barAugmented (F : Sheaf S.totalTopology Ab.{u}) :
    SimplicialObject.Augmented (Sheaf S.totalTopology Ab.{u}) :=
  sheafSimplexAugmented S.totalTopology (degreeFunctor S).leftOp F

/-- The simplicial abelian sheaf underlying `barAugmented`. -/
def barSimplicial (F : Sheaf S.totalTopology Ab.{u}) :
    SimplicialObject (Sheaf S.totalTopology Ab.{u}) :=
  (barAugmented S F).left

/-- The simplex-coefficient resolution as a functor of the abelian sheaf being resolved: the
simplex-coefficient diagram of the underlying presheaf, sheafified degreewise. At an object it is
the simplicial abelian sheaf underlying `barAugmented`. -/
def barSimplicial' :
    Sheaf S.totalTopology Ab.{u} ⥤ SimplicialObject (Sheaf S.totalTopology Ab.{u}) :=
  sheafToPresheaf S.totalTopology Ab.{u} ⋙
    simplexCoefficientDiagram' (totalSimplexDegree S).leftOp ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
        (presheafToSheaf S.totalTopology Ab.{u})

/-- At an abelian sheaf, the functor `barSimplicial'` is the simplicial abelian sheaf underlying
`barAugmented`. -/
theorem barSimplicial_obj (F : Sheaf S.totalTopology Ab.{u}) :
    (barSimplicial' S).obj F = (barAugmented S F).left :=
  rfl

/-- The degree-`n` term of the simplex-coefficient resolution, as a functor of the abelian sheaf
being resolved.

It is reducible, and its action is written out rather than taken as `barSimplicial' S` composed
with evaluation at `n`, so that the type of a morphism into it unfolds to the degree-`n` term of
a particular resolution without unfolding `CategoryTheory.Functor.comp`: a rewrite checks its
motive at a reduced transparency, which `Functor.comp` does not survive. -/
abbrev barTerm (n : SimplexCategory) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf S.totalTopology Ab.{u} where
  obj F := ((barSimplicial' S).obj F).obj (Opposite.op n)
  map α := ((barSimplicial' S).map α).app (Opposite.op n)
  map_id F := by
    rw [(barSimplicial' S).map_id, NatTrans.id_app]
  map_comp α β := by
    rw [(barSimplicial' S).map_comp, NatTrans.comp_app]

/-- The augmentation of the simplex-coefficient resolution onto the sheaf being resolved. -/
def barAugmentation (F : Sheaf S.totalTopology Ab.{u}) :
    (barSimplicial S F).obj (Opposite.op ⦋0⦌) ⟶ F :=
  sheafSimplexAugmentation S.totalTopology (degreeFunctor S).leftOp F

/-- The augmentation of the simplex-coefficient resolution onto the sheaf being resolved. -/
def barAugmentation' (F : Sheaf S.totalTopology Ab.{u}) :
    ((barSimplicial' S).obj F).obj (Opposite.op ⦋0⦌) ⟶ F :=
  sheafSimplexAugmentation S.totalTopology (totalSimplexDegree S).leftOp F

/-- The augmentation annihilates the first differential of the alternating-face complex. -/
theorem barAugmentation_comp (F : Sheaf S.totalTopology Ab.{u}) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj (barSimplicial S F)).d 1 0 ≫
      barAugmentation S F = 0 :=
  sheafSimplexAugmentation_comp S.totalTopology (degreeFunctor S).leftOp F

/-- The augmentation annihilates the first differential of the alternating-face complex. -/
theorem barAugmentation_comp' (F : Sheaf S.totalTopology Ab.{u}) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj ((barSimplicial' S).obj F)).d 1 0 ≫
      barAugmentation' S F = 0 :=
  sheafSimplexAugmentation_comp S.totalTopology (totalSimplexDegree S).leftOp F

/-- The simplex-coefficient complex is exact in every positive degree. -/
theorem barSimplicial_exactAt (F : Sheaf S.totalTopology Ab.{u}) (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj (barSimplicial S F)).ExactAt n :=
  sheafSimplex_exact_positive S.totalTopology (degreeFunctor S).leftOp F n hn

/-- The simplex-coefficient complex is exact in every positive degree. -/
theorem barSimplicial_exactAt' (F : Sheaf S.totalTopology Ab.{u}) (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj ((barSimplicial' S).obj F)).ExactAt n :=
  sheafSimplex_exact_positive S.totalTopology (totalSimplexDegree S).leftOp F n hn

/-- The simplex-coefficient complex is exact at the augmentation. -/
theorem barAugmentation_exact (F : Sheaf S.totalTopology Ab.{u}) :
    (ShortComplex.mk _ _ (barAugmentation_comp S F)).Exact :=
  sheafSimplexAugmentation_exact S.totalTopology (degreeFunctor S).leftOp F

/-- The augmentation is an epimorphism. -/
theorem barAugmentation_epi (F : Sheaf S.totalTopology Ab.{u}) :
    Epi (barAugmentation S F) :=
  sheafSimplexAugmentation_epi S.totalTopology (degreeFunctor S).leftOp F

end Total

/-! ### The resolution of the inverse image of an abelian sheaf along an augmentation -/

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (G : Sheaf K Ab.{u})

/-- The inverse image `a_n⁻¹` of abelian sheaves along the augmentation of the simplicial degree
`n`: the canonical abelian inverse image of the morphism of topoi of Stacks 0D70, so that
forgetting the group operations returns the inverse image of sheaves of sets. -/
def componentInverseImageAb (n : SimplexCategory) :
    Sheaf K Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  Sites.abelianInverseImage (componentAugmentation S D K a n)

/-- The inverse image `a⁻¹` of abelian sheaves along the total augmentation of Stacks 0D70. -/
def totalInverseImageAb : Sheaf K Ab.{u} ⥤ Sheaf S.totalTopology Ab.{u} :=
  Sites.abelianInverseImage (totalMorphismOfTopoi S D K a)

/-- The term `g_{n!}(a_n⁻¹𝒢)` of the resolution of Stacks 0D78. -/
abbrev resolutionTerm (n : ℕ) : Sheaf S.totalTopology Ab.{u} :=
  (componentLowerShriekAb S ⦋n⦌).obj ((componentInverseImageAb S D K a ⦋n⦌).obj G)

/-- An exact complex of abelian sheaves on the total site resolving `a⁻¹𝒢` by the lower shriek
images `g_{n!}(a_n⁻¹𝒢)`: a simplicial abelian sheaf whose degree-`n` term is `g_{n!}(a_n⁻¹𝒢)`,
whose alternating-face complex is augmented onto `a⁻¹𝒢`, and which is exact in every positive
degree and at the augmentation. -/
structure Resolution where
  /-- The simplicial abelian sheaf whose alternating-face complex is the resolution. -/
  simplicial : SimplicialObject (Sheaf S.totalTopology Ab.{u})
  /-- In degree `n` the simplicial abelian sheaf is `g_{n!}(a_n⁻¹𝒢)`. -/
  degreeIso (n : ℕ) : simplicial _⦋n⦌ ≅ resolutionTerm S D K a G n
  /-- The augmentation `g_{0!}(a_0⁻¹𝒢) ⟶ a⁻¹𝒢` of the complex. -/
  augmentation : ((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).X 0 ⟶
    (totalInverseImageAb S D K a).obj G
  /-- The augmentation annihilates the first differential, so the augmented complex is a
  complex. -/
  augmentation_comp :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).d 1 0 ≫ augmentation = 0
  /-- The complex is exact in every positive degree. -/
  exact_positive (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).ExactAt n
  /-- The complex is exact at the augmentation. -/
  exact_zero :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj simplicial).d 1 0)
      augmentation augmentation_comp).Exact
  /-- The augmentation is an epimorphism, so the complex ends in `a⁻¹𝒢 ⟶ 0`. -/
  augmentation_epi : Epi augmentation

end Augmentation

end CategoryTheory.SimplicialSiteSituation

end
