module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkLimit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# The augmented Čech complex of an augmentation of a simplicial site

Let `S` be a simplicial-site situation of Stacks 09WE and let `a` be an augmentation of `S`
towards a site `(D, K)` as in Stacks 0D6Z. For an abelian sheaf `F` on the total site, the direct
images along the augmentations `a_n` of the simplicial degrees of the restrictions `F_n` of `F` to
the components form a cosimplicial abelian sheaf on the augmentation site, and the direct image
`a_*F` along the total augmentation of Stacks 0D70 maps to its degree-zero term. Stacks 0D79
asserts that the resulting complex

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ a_{2,*}F_2 ⟶ …`

is exact in degrees `-1` and `0`, and exact everywhere when `F` is injective.

This file constructs that complex and proves its exactness in degrees `-1` and `0`. The argument
is that `a_*F` is the limit over the simplex category of the cosimplicial sheaf of the degreewise
direct images — which is how the direct image of the total augmentation is built in Stacks 0D70,
part (2) — and that the limit of a cosimplicial object is the equalizer of its two cofaces in
degrees `0 ⇉ 1`, which in an additive category means that the degree-zero leg of the limit cone is
a kernel of the first differential of the alternating-coface complex. A kernel is a monomorphism,
which is exactness in degree `-1`, and exhibits the degree-zero term as an extension, which is
exactness in degree `0`.

## Main definitions

* `CategoryTheory.CosimplicialObject.augmentedAlternatingCofaceComplex`: for a cosimplicial
  object in an additive category and a cone over it, the alternating-coface complex augmented by
  the degree-zero leg of the cone.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianComponentPushforward`: the direct
  image along the augmentation of the simplicial degree `n` of the restriction of an abelian
  sheaf on the total site to the component of that degree.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianCosimplicialPushforward`: those
  direct images, as a cosimplicial abelian sheaf on the augmentation site.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianTotalPushforward`: the direct image
  of abelian sheaves along the total augmentation of Stacks 0D70.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.augmentedCechComplex`: the complex of
  Stacks 0D79, with `a_*F` in Lean degree `0` and `a_{n,*}F_n` in Lean degree `n + 1`.

## Main results

* `CategoryTheory.CosimplicialObject.isLimitKernelFork`: the degree-zero leg of a limit cone over
  a cosimplicial object in an additive category is a kernel of the first differential of the
  alternating-coface complex.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianCechCone_isLimit`: the direct image
  along the total augmentation is the limit of the cosimplicial sheaf of the degreewise direct
  images, as abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.augmentedCechComplex_exactAt_zero` and
  `.augmentedCechComplex_exactAt_one`: **Stacks 0D79**, exactness in degrees `-1` and `0`, for
  every abelian sheaf.

## Implementation notes

The augmentation shifts the complex by one: the source's degree `-1` term `a_*F` is the Lean
degree-`0` term, and the source's degree-`n` term `a_{n,*}F_n` is the Lean degree-`n + 1` term.
Accordingly `augmentedCechComplex_exactAt_zero` is exactness in the source's degree `-1` and
`augmentedCechComplex_exactAt_one` is exactness in the source's degree `0`.

The passage from sheaves of sets to abelian sheaves is the one of Stacks 04DB: an abelian sheaf is
a commutative group object of the topos of sheaves of sets, a finite-product-preserving functor of
sheaves of sets acts on commutative group objects, and the result is read off on sections again.
The direct images of the components and of the total augmentation are built in Stacks 0D70 for
sheaves of sets, and all three — the cosimplicial structure, the cone, and the limit — are
transported through that passage at once, because taking commutative group objects is functorial
in the finite-product-preserving functor. In particular no comparison of direct images is redone
for abelian sheaves. That the transported cone is still a limit is seen on underlying sheaves of
sets, where it is the defining limit of Stacks 0D70, part (2): forgetting the group operations
preserves limits and reflects isomorphisms, hence reflects limits.

## References

* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Stacks.Topos.AbelianPushforward
open scoped Simplicial

universe v₁ u₁ v₂ u₂ u

namespace SimplexCategory

/-- The first of the two cofaces `⦋0⦌ ⟶ ⦋1⦌` is the vertex `1` of the one-simplex. -/
theorem δ_zero_eq_const_one : δ (0 : Fin 2) = const ⦋0⦌ ⦋1⦌ 1 := by
  ext i
  revert i
  decide

/-- The second of the two cofaces `⦋0⦌ ⟶ ⦋1⦌` is the vertex `0` of the one-simplex. -/
theorem δ_one_eq_const_zero : δ (1 : Fin 2) = const ⦋0⦌ ⦋1⦌ 0 := by
  ext i
  revert i
  decide

end SimplexCategory

namespace CategoryTheory.CosimplicialObject

section Preadditive

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] (X : CosimplicialObject A)

/-- Composing with a morphism is zero exactly when composing with any morphism equal to it is. -/
theorem comp_eq_zero_congr {Z Y P : A} {f g : Z ⟶ Y} (hfg : f = g) (ι : P ⟶ Z) :
    ι ≫ f = 0 ↔ ι ≫ g = 0 := by
  subst hfg
  exact Iff.rfl

/-- A kernel of a morphism is a kernel of any morphism equal to it. -/
def isLimitKernelForkCongr {Z Y P : A} {f g : Z ⟶ Y} (hfg : f = g) {ι : P ⟶ Z}
    (wf : ι ≫ f = 0) (wg : ι ≫ g = 0) (hc : IsLimit (KernelFork.ofι ι wf)) :
    IsLimit (KernelFork.ofι ι wg) := by
  subst hfg
  exact hc

/-- The first differential of the alternating-coface complex is the difference of the two
cofaces `⦋0⦌ ⟶ ⦋1⦌`, which are the two vertices of the one-simplex. -/
@[sga "4 Vbis 2.3.9" "2.3.9.1 for n=0"]
theorem objD_zero_eq :
    AlternatingCofaceMapComplex.objD X 0 =
      X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) - X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) := by
  rw [AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  simp only [CosimplicialObject.δ, SimplexCategory.δ_zero_eq_const_one,
    SimplexCategory.δ_one_eq_const_zero]
  simp [sub_eq_add_neg]

/-- The differential from degree `0` to degree `1` of the alternating-coface complex of a
cosimplicial object is the difference of the two vertices of the one-simplex. -/
@[sga "4 Vbis 2.3.9" "2.3.9.1 for n=0"]
theorem d_zero_one_eq :
    ((alternatingCofaceMapComplex A).obj X).d 0 1 =
      X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) - X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) :=
  (CochainComplex.of_d _ _ _).trans (objD_zero_eq X)

/-- The degree-zero leg of a cone over a cosimplicial object is annihilated by the difference of
the two vertices of the one-simplex, because they agree on it. -/
theorem coneLeg_comp_sub (c : Cone X) :
    c.π.app ⦋0⦌ ≫ (X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) -
        X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) = 0 := by
  rw [Preadditive.comp_sub, c.w (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1),
    c.w (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0), sub_self]

/-- The degree-zero leg of a cone over a cosimplicial object is annihilated by the first
differential of the alternating-coface complex. -/
theorem coneLeg_comp_d (c : Cone X) :
    c.π.app ⦋0⦌ ≫ ((alternatingCofaceMapComplex A).obj X).d 0 1 = 0 :=
  (comp_eq_zero_congr (d_zero_one_eq X) (c.π.app ⦋0⦌)).2 (coneLeg_comp_sub X c)

/-- A map annihilated by the difference of the two vertices of the one-simplex equalises
them. -/
theorem forkCondition_of_comp_sub {W : A} (g : W ⟶ X.obj ⦋0⦌)
    (hg : g ≫ (X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) -
      X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) = 0) :
    g ≫ X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) =
      g ≫ X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) := by
  rw [Preadditive.comp_sub, sub_eq_zero] at hg
  exact hg.symm

/-- A map into the degree-zero term which is annihilated by the first differential of the
alternating-coface complex equalises the two vertices of the one-simplex. -/
theorem forkCondition_of_comp_d {W : A} (g : W ⟶ X.obj ⦋0⦌)
    (hg : g ≫ ((alternatingCofaceMapComplex A).obj X).d 0 1 = 0) :
    g ≫ X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) =
      g ≫ X.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) :=
  forkCondition_of_comp_sub X g ((comp_eq_zero_congr (d_zero_one_eq X) g).1 hg)

/-- **The degree-zero leg of a limit cone over a cosimplicial object is a kernel of the first
differential of its alternating-coface complex.** -/
def isLimitKernelFork (c : Cone X) (hc : IsLimit c) :
    IsLimit (KernelFork.ofι (c.π.app ⦋0⦌) (coneLeg_comp_d X c)) :=
  KernelFork.IsLimit.ofι _ _
    (fun g hg => hc.lift (coneOfFork X (Fork.ofι g (forkCondition_of_comp_d X g hg))))
    (fun g hg => by
      refine Eq.trans (hc.fac (coneOfFork X (Fork.ofι g
        (forkCondition_of_comp_d X g hg))) ⦋0⦌) ?_
      change g ≫ X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) = g
      rw [SimplexCategory.const_eq_id, X.map_id, Category.comp_id])
    (fun g hg m hm => by
      refine hc.uniq (coneOfFork X (Fork.ofι g (forkCondition_of_comp_d X g hg))) m fun n => ?_
      change m ≫ c.π.app n = g ≫ X.map (SimplexCategory.const ⦋0⦌ n 0)
      rw [← hm, Category.assoc]
      exact congrArg (fun k => m ≫ k) (c.w (SimplexCategory.const ⦋0⦌ n 0)).symm)

/-- The alternating-coface complex of a cosimplicial object, augmented by the degree-zero leg of
a cone over it: the vertex of the cone sits in degree `0` and the degree-`n` term of the
cosimplicial object sits in degree `n + 1`. -/
def augmentedAlternatingCofaceComplex (c : Cone X) : CochainComplex A ℕ :=
  ((alternatingCofaceMapComplex A).obj X).augment (c.π.app ⦋0⦌) (coneLeg_comp_d X c)

end Preadditive

section Abelian

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] (X : CosimplicialObject A)

/-- The augmented alternating-coface complex of a limit cone is exact in degree `0`: the
augmentation is a kernel, hence a monomorphism. -/
theorem augmentedAlternatingCofaceComplex_exactAt_zero (c : Cone X) (hc : IsLimit c) :
    (augmentedAlternatingCofaceComplex X c).ExactAt 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
    (CochainComplex.next ℕ 0)]
  refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
  · exact (augmentedAlternatingCofaceComplex X c).shape 0 0 (by simp)
  · exact mono_of_isLimit_fork (isLimitKernelFork X c hc)

/-- The augmented alternating-coface complex of a limit cone is exact in degree `1`: the
augmentation is a kernel of the first differential. -/
theorem augmentedAlternatingCofaceComplex_exactAt_one (c : Cone X) (hc : IsLimit c) :
    (augmentedAlternatingCofaceComplex X c).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (CochainComplex.prev_nat_succ 0)
    (CochainComplex.next ℕ 1)]
  exact ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork X c hc)

end Abelian

end CategoryTheory.CosimplicialObject

namespace CategoryTheory

attribute [local instance] CategoryTheory.sheafTypeCartesian CategoryTheory.sheafTypeBraided

attribute [local instance] Functor.Braided.ofChosenFiniteProducts

section CommGrpFunctoriality

variable {A₁ : Type u₁} [Category.{v₁} A₁] [CartesianMonoidalCategory A₁] [BraidedCategory A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [CartesianMonoidalCategory A₂] [BraidedCategory A₂]

/-- Taking commutative group objects sends the identity transformation to the identity. -/
theorem mapCommGrpNatTrans_id (P : A₁ ⥤ A₂) [P.Braided] :
    Functor.mapCommGrpNatTrans (𝟙 P) = 𝟙 P.mapCommGrp := rfl

/-- Taking commutative group objects is compatible with composition of transformations. -/
theorem mapCommGrpNatTrans_comp {P Q R : A₁ ⥤ A₂} [P.Braided] [Q.Braided] [R.Braided]
    (α : P ⟶ Q) (β : Q ⟶ R) :
    Functor.mapCommGrpNatTrans (α ≫ β) =
      Functor.mapCommGrpNatTrans α ≫ Functor.mapCommGrpNatTrans β := rfl

end CommGrpFunctoriality

/-- Forgetting the abelian-group operations of abelian sheaves preserves limits, because it does
so on underlying presheaves and limits of sheaves are computed there. -/
noncomputable instance preservesLimitsOfShape_sheafCompose_forget {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) (T : Type) [SmallCategory T] :
    PreservesLimitsOfShape T (sheafCompose J (forget AddCommGrpCat.{u})) :=
  have : PreservesLimitsOfShape T (sheafCompose J (forget AddCommGrpCat.{u}) ⋙
      sheafToPresheaf J (Type u)) :=
    (inferInstance : PreservesLimitsOfShape T (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u})))
  preservesLimitsOfShape_of_reflects_of_preserves
    (sheafCompose J (forget AddCommGrpCat.{u})) (sheafToPresheaf J (Type u))

namespace SimplicialSiteSituation

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- Restriction to a simplicial component preserves limits, being a direct image along a
continuous functor. -/
noncomputable instance preservesLimits_restrict (n : SimplexCategory) :
    PreservesLimitsOfSize.{0, 0}
      (show Sheaf S.totalTopology (Type u) ⥤ _ from S.restrict n) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (S.inclusion n) (Type u)
    (S.componentTopology n) S.totalTopology).rightAdjoint_preservesLimits

/-- The direct image along the augmentation of a simplicial degree preserves limits, being a
right adjoint. -/
noncomputable instance preservesLimits_componentAugmentation (n : SimplexCategory) :
    PreservesLimitsOfSize.{0, 0} (componentAugmentation S D K a n).pushforward :=
  (componentAugmentation S D K a n).adj.rightAdjoint_preservesLimits

/-- The direct image along the total augmentation preserves limits, being a right adjoint. -/
noncomputable instance preservesLimits_pushforward :
    PreservesLimitsOfSize.{0, 0} (pushforward S D K a) :=
  (totalMorphismOfTopoi S D K a).adj.rightAdjoint_preservesLimits

/-- Reading a functor of sheaves of sets as a functor of abelian sheaves: internalize the group
operations, apply the functor to commutative group objects, and read the resulting operations off
on sections again. This is the passage of Stacks 04DB. -/
def abelianConjugation :
    (CommGrp (Sheaf S.totalTopology (Type u)) ⥤ CommGrp (Sheaf K (Type u))) ⥤
      (Sheaf S.totalTopology AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft _ _ _).obj (Sites.AbelianSheaf.internalSheaf S.totalTopology) ⋙
    (Functor.whiskeringRight _ _ _).obj (Sites.AbelianSheaf.externalSheaf K)

/-- The direct image along the augmentation of the simplicial degree `n` of the restriction of an
abelian sheaf on the total site to the component of that degree: the functor `F ↦ a_{n,*}F_n`. -/
def abelianComponentPushforward (n : SimplexCategory) :
    Sheaf S.totalTopology AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  (abelianConjugation S D K).obj ((componentPushforward S D K a n).mapCommGrp)

/-- The underlying sheaf of sets of `a_{n,*}F_n` is the direct image along `a_n` of the
restriction to the component of degree `n` of the underlying sheaf of sets of `F`. -/
theorem abelianComponentPushforward_forget (n : SimplexCategory)
    (F : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    (sheafCompose K (forget AddCommGrpCat.{u})).obj
        ((abelianComponentPushforward S D K a n).obj F) =
      (componentPushforward S D K a n).obj
        ((sheafCompose S.totalTopology (forget AddCommGrpCat.{u})).obj F) := rfl

/-- The direct image of abelian sheaves along the total augmentation of Stacks 0D70: the functor
`F ↦ a_*F`. -/
def abelianTotalPushforward :
    Sheaf S.totalTopology AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u} :=
  abelianPushforward S.totalTopology (totalMorphismOfTopoi S D K a)

/-- The direct image of abelian sheaves along the total augmentation is the abelian reading of the
direct image of sheaves of sets along it. -/
theorem abelianTotalPushforward_eq :
    abelianTotalPushforward S D K a =
      (abelianConjugation S D K).obj ((pushforward S D K a).mapCommGrp) := rfl

/-- The projection of the direct image along the total augmentation onto the direct image along
the augmentation of a simplicial degree, natural in the sheaf on the total site. -/
def pushforwardProjectionNatTrans (n : SimplexCategory) :
    pushforward S D K a ⟶ componentPushforward S D K a n where
  app F := pushforwardProjection S D K a F n
  naturality _ _ α := pushforward_map_comp_projection S D K a α n

/-- The projections are compatible with the cosimplicial structure of the degreewise direct
images. -/
theorem pushforwardProjectionNatTrans_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    pushforwardProjectionNatTrans S D K a m ≫ componentPushforwardTransition S D K a φ =
      pushforwardProjectionNatTrans S D K a n :=
  NatTrans.ext (funext fun F => pushforwardProjection_comp S D K a F φ)

/-- The cosimplicial transition of the degreewise direct images along the identity is the
identity. -/
theorem componentPushforwardTransition_id (n : SimplexCategory) :
    componentPushforwardTransition S D K a (𝟙 n) = 𝟙 _ :=
  (cosimplicialPushforward S D K a).map_id n

/-- The cosimplicial transitions of the degreewise direct images compose. -/
theorem componentPushforwardTransition_comp {l m n : SimplexCategory} (χ : l ⟶ m) (φ : m ⟶ n) :
    componentPushforwardTransition S D K a (χ ≫ φ) =
      componentPushforwardTransition S D K a χ ≫ componentPushforwardTransition S D K a φ :=
  (cosimplicialPushforward S D K a).map_comp χ φ

/-- **The cosimplicial abelian sheaf of the degreewise direct images.** In degree `n` it is the
direct image along the augmentation of that degree of the restriction to the component of that
degree; its transitions are the abelian readings of those of Stacks 0D70, compatibility (c). -/
def abelianCosimplicialPushforward : SimplexCategory ⥤
    (Sheaf S.totalTopology AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) where
  obj n := abelianComponentPushforward S D K a n
  map φ := (abelianConjugation S D K).map
    (Functor.mapCommGrpNatTrans (componentPushforwardTransition S D K a φ))
  map_id n := by
    rw [componentPushforwardTransition_id, mapCommGrpNatTrans_id,
      (abelianConjugation S D K).map_id]
    rfl
  map_comp χ φ := by
    rw [componentPushforwardTransition_comp, mapCommGrpNatTrans_comp,
      (abelianConjugation S D K).map_comp]
    rfl

/-- On underlying sheaves of sets the cosimplicial transition attached to a simplex map is the
direct-image transition of Stacks 0D70, compatibility (c). -/
theorem abelianCosimplicialPushforward_map_forget {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf S.totalTopology AddCommGrpCat.{u}) :
    (sheafCompose K (forget AddCommGrpCat.{u})).map
        (((abelianCosimplicialPushforward S D K a).map φ).app F) =
      (componentPushforwardTransition S D K a φ).app
        ((sheafCompose S.totalTopology (forget AddCommGrpCat.{u})).obj F) := rfl

/-- The projections out of the direct image along the total augmentation are compatible with the
cosimplicial transitions, after reading everything on abelian sheaves. -/
theorem abelianCechConeNatTrans_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianConjugation S D K).map
          (Functor.mapCommGrpNatTrans (pushforwardProjectionNatTrans S D K a m)) ≫
        (abelianCosimplicialPushforward S D K a).map φ =
      (abelianConjugation S D K).map
        (Functor.mapCommGrpNatTrans (pushforwardProjectionNatTrans S D K a n)) := by
  show (abelianConjugation S D K).map
      (Functor.mapCommGrpNatTrans (pushforwardProjectionNatTrans S D K a m)) ≫
    (abelianConjugation S D K).map (Functor.mapCommGrpNatTrans
      (componentPushforwardTransition S D K a φ)) = _
  rw [← (abelianConjugation S D K).map_comp, ← mapCommGrpNatTrans_comp,
    pushforwardProjectionNatTrans_comp]

/-- The cone over the cosimplicial abelian sheaf of degreewise direct images with vertex the
direct image along the total augmentation, in the category of functors of the abelian sheaf. -/
def abelianCechConeNatTrans :
    (Functor.const SimplexCategory).obj (abelianTotalPushforward S D K a) ⟶
      abelianCosimplicialPushforward S D K a where
  app n := (abelianConjugation S D K).map
    (Functor.mapCommGrpNatTrans (pushforwardProjectionNatTrans S D K a n))
  naturality _ _ φ :=
    (Category.id_comp _).trans (abelianCechConeNatTrans_comp S D K a φ).symm

variable (F : Sheaf S.totalTopology AddCommGrpCat.{u})

/-- **The cosimplicial abelian sheaf attached to an abelian sheaf on the total site.** In degree
`n` it is `a_{n,*}F_n`. -/
def abelianCechDiagram : CosimplicialObject (Sheaf K AddCommGrpCat.{u}) :=
  abelianCosimplicialPushforward S D K a ⋙ (evaluation _ _).obj F

/-- The cone over `a_{n,*}F_n` with vertex `a_*F`, whose legs are the projections out of the
direct image along the total augmentation. -/
def abelianCechCone : Cone (abelianCechDiagram S D K a F) :=
  ((evaluation _ _).obj F).mapCone (Cone.mk _ (abelianCechConeNatTrans S D K a))

/-- On underlying sheaves of sets the cone is the defining limit cone of the direct image along
the total augmentation of Stacks 0D70, part (2). -/
theorem abelianCechCone_forget :
    (sheafCompose K (forget AddCommGrpCat.{u})).mapCone (abelianCechCone S D K a F) =
      limit.cone (pushforwardDiagram S D K a
        ((sheafCompose S.totalTopology (forget AddCommGrpCat.{u})).obj F)) := rfl

/-- **The direct image along the total augmentation is the limit of the cosimplicial abelian sheaf
of the degreewise direct images.** -/
def abelianCechCone_isLimit : IsLimit (abelianCechCone S D K a F) := by
  letI : ReflectsLimitsOfShape SimplexCategory
      (sheafCompose K (forget AddCommGrpCat.{u})) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine isLimitOfReflects (sheafCompose K (forget AddCommGrpCat.{u})) ?_
  rw [abelianCechCone_forget]
  exact limit.isLimit _

/-- **The complex of Stacks 0D79.** The alternating-coface complex of the cosimplicial abelian
sheaf `n ↦ a_{n,*}F_n`, augmented by the direct image `a_*F` along the total augmentation. The
source's degree `-1` is Lean degree `0` and the source's degree `n` is Lean degree `n + 1`. -/
def augmentedCechComplex : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℕ :=
  CosimplicialObject.augmentedAlternatingCofaceComplex (abelianCechDiagram S D K a F)
    (abelianCechCone S D K a F)

/-- The degree-`0` term of the complex of Stacks 0D79 is the direct image `a_*F` along the total
augmentation; it is the source's degree `-1` term. -/
theorem augmentedCechComplex_X_zero :
    (augmentedCechComplex S D K a F).X 0 = (abelianTotalPushforward S D K a).obj F := rfl

/-- The degree-`n + 1` term of the complex of Stacks 0D79 is `a_{n,*}F_n`; it is the source's
degree-`n` term. -/
theorem augmentedCechComplex_X_succ (n : ℕ) :
    (augmentedCechComplex S D K a F).X (n + 1) =
      (abelianComponentPushforward S D K a ⦋n⦌).obj F := rfl

/-- The augmentation of the complex of Stacks 0D79 is the projection of `a_*F` onto
`a_{0,*}F_0`. -/
theorem augmentedCechComplex_d_zero_one :
    (augmentedCechComplex S D K a F).d 0 1 = (abelianCechCone S D K a F).π.app ⦋0⦌ := rfl

/-- On underlying sheaves of sets the augmentation of the complex of Stacks 0D79 is the
projection of the direct image along the total augmentation onto the direct image along the
augmentation of simplicial degree zero. -/
theorem augmentedCechComplex_d_zero_one_forget :
    (sheafCompose K (forget AddCommGrpCat.{u})).map ((augmentedCechComplex S D K a F).d 0 1) =
      pushforwardProjection S D K a
        ((sheafCompose S.totalTopology (forget AddCommGrpCat.{u})).obj F) ⦋0⦌ := rfl

/-- Above the augmentation the differentials of the complex of Stacks 0D79 are those of the
alternating-coface complex of the cosimplicial sheaf of the degreewise direct images. -/
theorem augmentedCechComplex_d_succ_succ (n m : ℕ) :
    (augmentedCechComplex S D K a F).d (n + 1) (m + 1) =
      ((alternatingCofaceMapComplex (Sheaf K AddCommGrpCat.{u})).obj
        (abelianCechDiagram S D K a F)).d n m := rfl

/-- Exactness in degree `-1`: the complex

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …`

is exact at `a_*F`, which is Lean degree `0` because the augmentation shifts the complex by
one. -/
@[stacks 0D79 "exactness in degree -1"]
theorem augmentedCechComplex_exactAt_zero : (augmentedCechComplex S D K a F).ExactAt 0 :=
  CosimplicialObject.augmentedAlternatingCofaceComplex_exactAt_zero _ _
    (abelianCechCone_isLimit S D K a F)

/-- Exactness in degree `0`: the complex

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ …`

is exact at `a_{0,*}F_0`, which is Lean degree `1` because the augmentation shifts the complex by
one. -/
@[stacks 0D79 "exactness in degree 0"]
theorem augmentedCechComplex_exactAt_one : (augmentedCechComplex S D K a F).ExactAt 1 :=
  CosimplicialObject.augmentedAlternatingCofaceComplex_exactAt_one _ _
    (abelianCechCone_isLimit S D K a F)

end Augmentation

end SimplicialSiteSituation

end CategoryTheory

end
