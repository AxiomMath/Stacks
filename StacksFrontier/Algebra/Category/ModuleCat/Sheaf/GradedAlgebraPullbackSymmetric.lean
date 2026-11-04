module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCommutative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnital
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnitalCounit

/-!
# The pullback of a symmetric algebra along a morphism of ringed topoi

Let `f : X ⟶ Y` be a morphism of ringed topoi, `M` a sheaf of `𝒪_Y`-modules and `Sym(M)` a
symmetric algebra of `M`. The pullback `f^*Sym(M)` of sheaves of graded algebras (Stacks 0FQX) is
a symmetric algebra of `f^*M`: the comparison `Sym(f^*M) ⟶ f^*Sym(M)` extending the pullback of
the generator is an isomorphism in every degree. Its inverse is the transpose, along the graded
adjunction `f^* ⊣ f_*`, of the homomorphism `Sym(M) ⟶ f_*Sym(f^*M)` extending the transposed
generator; the two composites are the identity by the universal properties, once the unit and the
counit of the graded adjunction are known to preserve the unit sections.

## Main results

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.unitApp_map_one`: the unit of the graded
  adjunction preserves the unit sections; for the counit this is `counitApp_map_one`.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebraHom_map_one` and
  `pushforwardGradedAlgebra_mul_one_one_comm`: the direct image preserves unital homomorphisms
  and commutativity in degrees `(1, 1)`.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.isIso_symmetricPullbackHom_app`: the comparison
  `Sym(f^*M) ⟶ f^*Sym(M)` is an isomorphism in every degree.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraPullback
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

variable {X Y : RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C]
  (f : AlgebraicGeometry.RingedToposHom X Y)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
  /-- Multiplication in a direct image graded algebra is pointwise multiplication in the source,
  read through the transposed description of its local sections. -/
  private theorem pushedSectionEquiv_mul_app_apply
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) (U : Y.Cᵒᵖ) (x : ((pushforwardGradedAlgebra f A).piece i).val.obj U)
    (y : ((pushforwardGradedAlgebra f A).piece j).val.obj U) (V : X.Cᵒᵖ)
    (e : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w)).obj (smallYoneda.{w} U.unop))).obj.obj V) :
    (pushedSectionEquiv f (A.piece (i + j)) U
      (((pushforwardGradedAlgebra f A).mul i j).app U x y)).hom.app V e =
      (A.mul i j).app V ((pushedSectionEquiv f (A.piece i) U x).hom.app V e)
        ((pushedSectionEquiv f (A.piece j) U y).hom.app V e) :=
  transposedMultiplicationAt_apply f A i j U x y V e

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The unit of a direct image graded algebra, read through the transposed description of its
local sections, is the constant unit of the source. -/
theorem pushedSectionEquiv_one
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : Y.Cᵒᵖ) :
    pushedSectionEquiv f (A.piece 0) U ((pushforwardGradedAlgebra f A).one.eval U) =
      terminal.from _ ≫ oneSheafHom A := by
  set c := (pushedSectionEquiv f (A.piece 0) U).symm (terminal.from _ ≫ oneSheafHom A)
  have h1 : ((pushforwardGradedAlgebra f A).mul 0 0).app U c
      ((pushforwardGradedAlgebra f A).one.eval U) = (pushforwardGradedAlgebra f A).one.eval U := by
    apply (pushedSectionEquiv f (A.piece (0 + 0)) U).injective
    ext V e
    refine (pushedSectionEquiv_mul_app_apply f A 0 0 U _ _ V e).trans ?_
    rw [Equiv.apply_symm_apply]
    exact eq_of_heq (A.one_mul 0 V _)
  have h2 : ((pushforwardGradedAlgebra f A).mul 0 0).app U c
      ((pushforwardGradedAlgebra f A).one.eval U) = c :=
    eq_of_heq ((pushforwardGradedAlgebra f A).mul_one 0 U c)
  rw [← h1, h2, Equiv.apply_symm_apply]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The value of the unit of a direct image graded algebra on its transposed sections. -/
theorem pushedSectionEquiv_one_app
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : Y.Cᵒᵖ) (V : X.Cᵒᵖ)
    (e : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w)).obj (smallYoneda.{w} U.unop))).obj.obj V) :
    (pushedSectionEquiv f (A.piece 0) U ((pushforwardGradedAlgebra f A).one.eval U)).hom.app V e =
      A.one.eval V := by
  rw [pushedSectionEquiv_one]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The direct image of a unital homomorphism of sheaves of graded algebras is unital.** -/
theorem pushforwardGradedAlgebraHom_map_one
    {A A' : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : A ⟶ A') (hg : ∀ V, (g.app 0).val.app V (A.one.eval V) = A'.one.eval V) (U : Y.Cᵒᵖ) :
    ((pushforwardGradedAlgebraHom f g).app 0).val.app U
        ((pushforwardGradedAlgebra f A).one.eval U) =
      (pushforwardGradedAlgebra f A').one.eval U := by
  apply (pushedSectionEquiv f (A'.piece 0) U).injective
  refine (pushedSectionEquiv_map f (g.app 0) U _).trans ?_
  ext V e
  refine (sheafHom_comp_app_apply X.J _ _ V e).trans ?_
  rw [pushedSectionEquiv_one_app]
  exact (hg V).trans (pushedSectionEquiv_one_app f A' U V e).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Commutativity in degrees `(1, 1)` passes to the direct image.** -/
theorem pushforwardGradedAlgebra_mul_one_one_comm
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hA : ∀ (V : X.Cᵒᵖ) (x y : (A.piece 1).val.obj V),
      (A.mul 1 1).app V x y = (A.mul 1 1).app V y x)
    (U : Y.Cᵒᵖ) (x y : ((pushforwardGradedAlgebra f A).piece 1).val.obj U) :
    ((pushforwardGradedAlgebra f A).mul 1 1).app U x y =
      ((pushforwardGradedAlgebra f A).mul 1 1).app U y x := by
  apply (pushedSectionEquiv f (A.piece (1 + 1)) U).injective
  ext V e
  refine (pushedSectionEquiv_mul_app_apply f A 1 1 U _ _ V e).trans ?_
  refine Eq.trans ?_ (pushedSectionEquiv_mul_app_apply f A 1 1 U _ _ V e).symm
  exact hA V _ _

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- The unit of the inverse image of a graded algebra, as the inverse image of its unit. -/
theorem inverseImageGradedAlgebra_one_eval
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (V : X.Cᵒᵖ) (t : (f.toToposHom.inverseImage.obj (⊤_ (Sheaf Y.J (Type w)))).obj.obj V) :
    (inverseImageGradedAlgebra f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).one.eval V =
      (f.toToposHom.inverseImage.map (oneSheafHom B)).hom.app V t := by
  let : PreservesFiniteLimits f.toToposHom.inverseImage := f.toToposHom.preservesFiniteLimits
  show (transportSections X.J f.toToposHom.inverseImage V).map (oneSheafHom B) default = _
  exact congrArg ((transportSections X.J f.toToposHom.inverseImage V).map (oneSheafHom B))
    (Subsingleton.elim _ _)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- The unit of a pullback graded algebra is the change-of-rings image of the unit of the inverse
image. -/
theorem toposPullbackGradedAlgebra_one_eval
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (V : X.Cᵒᵖ) :
    ((pullFunctor f).obj B).one.eval V =
      (pullbackScalarUnit f (B.piece 0)).hom.app V
        ((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).one.eval V) :=
  (pullbackScalarUnit_app f (B.piece 0) V _).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The unit of the pullback-pushforward adjunction of graded algebras preserves the unit.** -/
theorem unitApp_map_one
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (U : Y.Cᵒᵖ) :
    ((unitApp f B).app 0).val.app U (B.one.eval U) =
      ((pushFunctor f).obj ((pullFunctor f).obj B)).one.eval U := by
  apply (pushedSectionEquiv f (((pullFunctor f).obj B).piece 0) U).injective
  refine (pushedSectionEquiv_unit f (B.piece 0) U (B.one.eval U)).trans ?_
  refine Eq.trans ?_ (pushedSectionEquiv_one f ((pullFunctor f).obj B) U).symm
  have hσ : sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece 0)) (B.one.eval U) =
      sectionEquivSmall Y.J U (⊤_ (Sheaf Y.J (Type w)))
        (default : (Sheaf.sectionsFunctor Y.J U).obj (⊤_ (Sheaf Y.J (Type w)))) ≫ oneSheafHom B :=
    sectionEquivSmall_comp Y.J U (oneSheafHom B)
      (default : (Sheaf.sectionsFunctor Y.J U).obj (⊤_ (Sheaf Y.J (Type w))))
  rw [hσ, Functor.map_comp]
  ext V s
  refine (sheafHom_comp_app_apply X.J _ _ V s).trans ?_
  refine (congrArg ((pullbackScalarUnit f (B.piece 0)).hom.app V)
    (sheafHom_comp_app_apply X.J _ _ V s)).trans ?_
  refine (congrArg ((pullbackScalarUnit f (B.piece 0)).hom.app V)
    (inverseImageGradedAlgebra_one_eval f B V _).symm).trans ?_
  exact (toposPullbackGradedAlgebra_one_eval f B V).symm

/-! ### The pullback of a symmetric algebra -/

section Symmetric

open SheafOfModules.GradedAlgebra

variable {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  {A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  (ι : M ⟶ A.piece 1) (hA : IsSymmetricAlgebra A ι)
  (hAc : ∀ (V : Y.Cᵒᵖ) (x y : (A.piece 1).val.obj V),
    (A.mul 1 1).app V x y = (A.mul 1 1).app V y x)
  {S' : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (ι' : f.toRingedToposModulesHom.pullbackModules.obj M ⟶ S'.piece 1)
  (hS : IsSymmetricAlgebra S' ι')
  (hSc : ∀ (V : X.Cᵒᵖ) (x y : (S'.piece 1).val.obj V),
    (S'.mul 1 1).app V x y = (S'.mul 1 1).app V y x)

/-- The pullback of the generator of `A`, a degree-one generator of the pullback of `A`. -/
noncomputable abbrev pullbackGen :
    f.toRingedToposModulesHom.pullbackModules.obj M ⟶ ((gradedPull f).obj A).piece 1 :=
  f.toRingedToposModulesHom.pullbackModules.map ι

include hAc in
omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- The pulled-back generator has pairwise commuting image. -/
theorem pairwiseCommutes_pullbackGen : PairwiseCommutes (pullbackGen f ι) :=
  fun U _ _ => toposPullbackGradedAlgebra_mul_one_one_comm f.toRingedToposModulesHom A hAc U _ _

/-- **The comparison `Sym(f^*M) ⟶ f^*Sym(M)`**: the unital homomorphism out of the symmetric
algebra of the pulled-back module extending the pullback of the generator. -/
noncomputable def symmetricPullbackHom : UnitalHom S' ((gradedPull f).obj A) :=
  hS.isUniversal.desc _ (pullbackGen f ι) (pairwiseCommutes_pullbackGen f ι hAc)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- The comparison carries the generator of `Sym(f^*M)` to the pullback of the generator. -/
theorem gen_comp_symmetricPullbackHom_app_one :
    ι' ≫ (symmetricPullbackHom f ι hAc ι' hS).app 1 = pullbackGen f (ι := ι) :=
  hS.isUniversal.desc_extends _ _ _

/-- The transpose of the generator of `S'`, a degree-one generator of its direct image. -/
noncomputable abbrev pushforwardGen :
    M ⟶ ((gradedPush f).obj S').piece 1 :=
  f.pullbackAdjPushforwardModulesViaComparison.unit.app M ≫ f.pushforwardModules.map ι'

/-- The homomorphism `Sym(M) ⟶ f_*Sym(f^*M)` extending the transposed generator of `Sym(f^*M)`. -/
noncomputable def symmetricPushforwardHom : UnitalHom A ((gradedPush f).obj S') :=
  hA.isUniversal.desc _ (pushforwardGen f ι')
    (fun U _ _ => pushforwardGradedAlgebra_mul_one_one_comm f S' hSc U _ _)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The homomorphism `Sym(M) ⟶ f_*Sym(f^*M)` carries the generator to the transposed one. -/
theorem gen_comp_symmetricPushforwardHom_app_one :
    ι ≫ (symmetricPushforwardHom f ι hA ι' hSc).app 1 = pushforwardGen f (ι' := ι') :=
  hA.isUniversal.desc_extends _ _ _

/-- The inverse comparison `f^*Sym(M) ⟶ Sym(f^*M)`, the transpose of
`symmetricPushforwardHom`. -/
noncomputable def symmetricPullbackInv : (gradedPull f).obj A ⟶ S' :=
  ((gradedAdj f).homEquiv A S').symm (symmetricPushforwardHom f ι hA ι' hSc).toHom

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse comparison is the pullback of its transpose followed by the counit. -/
theorem symmetricPullbackInv_eq :
    symmetricPullbackInv f ι hA ι' hSc =
      (gradedPull f).map (symmetricPushforwardHom f ι hA ι' hSc).toHom ≫
        (gradedAdj f).counit.app S' :=
  (gradedAdj f).homEquiv_counit (g := (symmetricPushforwardHom f ι hA ι' hSc).toHom)

/-- The inverse comparison preserves the unit. -/
theorem symmetricPullbackInv_map_one (U : X.Cᵒᵖ) :
    ((symmetricPullbackInv f ι hA ι' hSc).app 0).val.app U (((gradedPull f).obj A).one.eval U) =
      S'.one.eval U := by
  have h1 := gradedPull_map_one f (symmetricPushforwardHom f ι hA ι' hSc).toHom
    (symmetricPushforwardHom f ι hA ι' hSc).map_one U
  rw [symmetricPullbackInv_eq]
  exact (congrArg (fun x => (((gradedAdj f).counit.app S').app 0).val.app U x) h1).trans
    (counitApp_map_one f S' U)

/-- The inverse comparison, as a unital homomorphism. -/
noncomputable def symmetricPullbackInvUnital : UnitalHom ((gradedPull f).obj A) S' where
  app n := (symmetricPullbackInv f ι hA ι' hSc).app n
  map_mul := (symmetricPullbackInv f ι hA ι' hSc).map_mul
  map_one := symmetricPullbackInv_map_one f ι hA ι' hSc

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse comparison is degreewise the transpose along the module adjunction. -/
theorem symmetricPullbackInv_app (n : ℤ) :
    (symmetricPullbackInv f ι hA ι' hSc).app n =
      (f.pullbackAdjPushforwardModulesViaComparison.homEquiv _ _).symm
        ((symmetricPushforwardHom f ι hA ι' hSc).app n) := by
  rw [symmetricPullbackInv_eq]
  exact (f.pullbackAdjPushforwardModulesViaComparison.homEquiv_counit
    (g := (symmetricPushforwardHom f ι hA ι' hSc).app n)).symm

/-- The comparison followed by its inverse is the identity of `Sym(f^*M)`. -/
theorem symmetricPullbackHom_comp_inv :
    (symmetricPullbackHom f ι hAc ι' hS).comp (symmetricPullbackInvUnital f ι hA ι' hSc) =
      UnitalHom.id S' := by
  refine hS.isUniversal.eq_id ?_
  rw [UnitalHom.comp_app, ← Category.assoc, gen_comp_symmetricPullbackHom_app_one]
  show f.toRingedToposModulesHom.pullbackModules.map ι ≫
    (symmetricPullbackInv f ι hA ι' hSc).app 1 = ι'
  rw [symmetricPullbackInv_app]
  refine ((f.pullbackAdjPushforwardModulesViaComparison.homEquiv_naturality_left_symm ι
    ((symmetricPushforwardHom f ι hA ι' hSc).app 1)).symm).trans ?_
  refine (congrArg (f.pullbackAdjPushforwardModulesViaComparison.homEquiv _ _).symm
    (gen_comp_symmetricPushforwardHom_app_one f ι hA ι' hSc)).trans ?_
  exact (congrArg (f.pullbackAdjPushforwardModulesViaComparison.homEquiv _ _).symm
    (f.pullbackAdjPushforwardModulesViaComparison.homEquiv_unit (f := ι')).symm).trans
    (Equiv.symm_apply_apply _ _)

/-- The direct image of the comparison, as a unital homomorphism. -/
noncomputable def pushforwardSymmetricPullbackHom :
    UnitalHom ((gradedPush f).obj S') ((gradedPush f).obj ((gradedPull f).obj A)) where
  app n := ((gradedPush f).map (symmetricPullbackHom f ι hAc ι' hS).toHom).app n
  map_mul := ((gradedPush f).map (symmetricPullbackHom f ι hAc ι' hS).toHom).map_mul
  map_one := pushforwardGradedAlgebraHom_map_one f _ (symmetricPullbackHom f ι hAc ι' hS).map_one

/-- The unit of the graded adjunction at `A`, as a unital homomorphism. -/
noncomputable def gradedAdjUnitUnital :
    UnitalHom A ((gradedPush f).obj ((gradedPull f).obj A)) where
  app n := ((gradedAdj f).unit.app A).app n
  map_mul := ((gradedAdj f).unit.app A).map_mul
  map_one := unitApp_map_one f A

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transpose of the inverse comparison followed by the direct image of the comparison is
the unit of the graded adjunction. -/
theorem symmetricPushforwardHom_comp :
    (symmetricPushforwardHom f ι hA ι' hSc).comp (pushforwardSymmetricPullbackHom f ι hAc ι' hS) =
      gradedAdjUnitUnital f (A := A) := by
  refine hA.isUniversal.hom_ext (κ := ι ≫ ((gradedAdj f).unit.app A).app 1)
    (fun U s u => pushforwardGradedAlgebra_mul_one_one_comm f ((gradedPull f).obj A)
      (fun V x y => toposPullbackGradedAlgebra_mul_one_one_comm f.toRingedToposModulesHom A hAc
        V x y) U _ _) ?_ rfl
  rw [UnitalHom.comp_app, ← Category.assoc, gen_comp_symmetricPushforwardHom_app_one]
  show (f.pullbackAdjPushforwardModulesViaComparison.unit.app M ≫ f.pushforwardModules.map ι') ≫
      f.pushforwardModules.map ((symmetricPullbackHom f ι hAc ι' hS).app 1) =
    ι ≫ f.pullbackAdjPushforwardModulesViaComparison.unit.app (A.piece 1)
  rw [Category.assoc, ← Functor.map_comp, gen_comp_symmetricPullbackHom_app_one]
  exact (f.pullbackAdjPushforwardModulesViaComparison.unit.naturality ι).symm

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse comparison followed by the comparison is the identity of `f^*Sym(M)`. -/
theorem symmetricPullbackInv_comp_hom :
    symmetricPullbackInv f ι hA ι' hSc ≫ (symmetricPullbackHom f ι hAc ι' hS).toHom = 𝟙 _ := by
  apply ((gradedAdj f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, symmetricPullbackInv, Equiv.apply_symm_apply,
    Adjunction.homEquiv_id]
  exact congrArg UnitalHom.toHom (symmetricPushforwardHom_comp f ι hA hAc ι' hS hSc)

include hA hSc in
/-- **The comparison `Sym(f^*M) ⟶ f^*Sym(M)` is an isomorphism in every degree.** -/
theorem isIso_symmetricPullbackHom_app (n : ℤ) :
    IsIso ((symmetricPullbackHom f ι hAc ι' hS).app n) :=
  ⟨(symmetricPullbackInv f ι hA ι' hSc).app n,
    congrArg (fun g => UnitalHom.app g n) (symmetricPullbackHom_comp_inv f ι hA hAc ι' hS hSc),
    congrArg (fun g => Hom.app g n) (symmetricPullbackInv_comp_hom f ι hA hAc ι' hS hSc)⟩

end Symmetric

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
