module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexIsAResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of the integral Čech complex: tensoring with a presheaf of rings

Let `E` be a family of morphisms `U i ⟶ X` in a category `C` and let
`O : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings. The integral Čech
complex `integralCechComplex E` is a chain complex of abelian presheaves whose
degree `n` term is a direct sum of free abelian presheaves, and it is exact in
every positive degree. This file shows that exactness survives tensoring over
the constant presheaf `ℤ` with `O`: the resulting chain complex of presheaves of
`O`-modules has vanishing homology in every positive degree.

The argument is objectwise. Over an object `V` of the site, the evaluated
integral Čech complex is a complex of free abelian groups — indeed the chain
complex of a simplicial set with coefficients in a free abelian group — so all
of its terms, and its degree-zero homology, are projective. A complex of
projectives which is exact in positive degrees is a projective resolution of its
degree-zero opcycles, and two projective resolutions of the same object are
homotopy equivalent; hence applying any additive functor preserves exactness in
positive degrees. Applying this to extension of scalars along `ℤ → O(V)` gives
objectwise exactness, and a morphism of presheaves of modules vanishes as soon
as all of its components do.

## Main definitions

* `Stacks.CechSite.integralCechComplexTensorAt`: the objectwise extension of
  scalars of the integral Čech complex along `ℤ → O(V)`.
* `Stacks.CechSite.integralCechIntegralAt` and
  `Stacks.CechSite.integralCechIntegralMap`: the terms of the integral Čech
  complex and their restriction maps, regarded as integer modules in the
  universe used by extension of scalars.
* `Stacks.CechSite.IntegralCechComplexTensorSpec`: the data of a chain complex of
  presheaves of `O`-modules together with objectwise identifications with
  `integralCechComplexTensorAt` compatible with restriction on pure tensors.
* `Stacks.CechSite.integralCechComplexTensor`: the tensor product of the integral
  Čech complex with `O`, presented as such a specification.
* `Stacks.CechSite.extendScalarsGrp`: extension of scalars from abelian groups to
  modules over a ring, not assumed commutative, `A ↦ S ⊗[ℤ] A`.
* `Stacks.CechSite.integralCechTensorFunctorRing` and
  `Stacks.CechSite.integralCechComplexTensorRing`: the same tensor product for a presheaf
  `R : Cᵒᵖ ⥤ RingCat` of rings not assumed commutative.

## Main results

* `Stacks.CechSite.integralCechComplexTensor_homology_isZero`: the tensored
  complex has vanishing homology in every positive degree.
* `Stacks.CechSite.integralCechComplexTensorRing_homology_isZero`: the same for a presheaf
  of rings not assumed commutative. Nothing in the argument needs commutativity: `ℤ` is central
  in every ring, and the exactness only uses that extension of scalars is additive.

## Implementation notes

Extension of scalars from abelian presheaves to presheaves of `R`-modules is
built here as `extendScalarsPresheaf` and `extendScalarsPresheafMap`, together with
the adjunction `extendScalarsPresheafHomAddEquiv` that corepresents the underlying
abelian presheaf (used downstream, for Tag 03FC). The variant
`ModuleSheafCohomology.tensorPresheaf` in
`StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison` is
`no_expose` and forces the ring and module universes to agree, whereas here the
coefficient universe of the integral Čech complex and the universe of the ring
presheaf are independent and the tensor product lands in their maximum.

The compatibility of the objectwise identifications with restriction is packaged
as a field of `IntegralCechComplexTensorSpec` rather than proved separately,
because the tensor products in question are determined by their values on pure
tensors; stating the comparison on pure tensors is therefore the whole content.

## References

* [The Stacks Project, Tag 03F5](https://stacks.math.columbia.edu/tag/03F5)
-/

@[expose] public section

open AlgebraicTopology
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace Stacks.CechSite

section ExtendScalarsGrp

universe r z

open TensorProduct

variable (S : RingCat.{r})

/-- Extension of scalars from abelian groups to `S`-modules, `A ↦ S ⊗[ℤ] A`, with `S` acting
through the left-hand factor. This is the objectwise form of `extendScalarsPresheaf`. No
commutativity of `S` is involved: the base ring is `ℤ`, which is central in `S`. -/
public noncomputable def extendScalarsGrp :
    AddCommGrpCat.{max r z} ⥤ ModuleCat.{max r z} S where
  obj A := ModuleCat.of S (S ⊗[ℤ] A)
  map f := ModuleCat.ofHom
    (AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) f.hom.toIntLinearMap)
  map_id A := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    rfl

/-- On a pure tensor, `extendScalarsGrp S` sends `s ⊗ₜ a` along `f` to `s ⊗ₜ f a`. -/
public lemma extendScalarsGrp_map_tmul {A B : AddCommGrpCat.{max r z}} (f : A ⟶ B)
    (s : S) (a : A) :
    (extendScalarsGrp.{r, z} S).map f (s ⊗ₜ[ℤ] a) = s ⊗ₜ[ℤ] f a := rfl

/-- Extension of scalars `extendScalarsGrp S` from abelian groups to `S`-modules is an additive
functor. -/
public instance extendScalarsGrp_additive : (extendScalarsGrp.{r, z} S).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext <|
    TensorProduct.AlgebraTensorModule.ext fun s a => TensorProduct.tmul_add s (f a) (g a)

end ExtendScalarsGrp

section ExtendScalarsPresheaf

universe w v z r

open TensorProduct

variable {D : Type w} [Category.{v} D] (R : Dᵒᵖ ⥤ RingCat.{r})

/-- The restriction map of the objectwise tensor product `R ⊗[ℤ] F`, as a
semilinear map along the restriction map of `R`. -/
public def extendScalarsPresheafRestrict (F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    (R.obj X ⊗[ℤ] F.obj X) →ₛₗ[(R.map f).hom] (R.obj Y ⊗[ℤ] F.obj Y) where
  toFun := TensorProduct.map (R.map f).hom.toAddMonoidHom.toIntLinearMap
    (F.map f).hom.toIntLinearMap
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a x => simp [TensorProduct.smul_tmul', smul_eq_mul]

/-- The restriction map `extendScalarsPresheafRestrict R F f` sends a pure tensor `r ⊗ₜ x` to
`R.map f r ⊗ₜ F.map f x`. -/
public lemma extendScalarsPresheafRestrict_tmul (F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : F.obj X) :
    extendScalarsPresheafRestrict R F f (r ⊗ₜ[ℤ] x) = R.map f r ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Extension of scalars from abelian presheaves to presheaves of `R`-modules, on
objects. -/
public noncomputable def extendScalarsPresheaf (F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}) :
    PresheafOfModules.{max r z} R where
  obj X := ModuleCat.of (R.obj X) (R.obj X ⊗[ℤ] F.obj X)
  map f := (ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _)
    (extendScalarsPresheafRestrict R F f)
  map_id X := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change extendScalarsPresheafRestrict R F (𝟙 X) (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] x
    simp [extendScalarsPresheafRestrict_tmul]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change extendScalarsPresheafRestrict R F (f ≫ g) (a ⊗ₜ[ℤ] x) =
      extendScalarsPresheafRestrict R F g (extendScalarsPresheafRestrict R F f (a ⊗ₜ[ℤ] x))
    simp [extendScalarsPresheafRestrict_tmul]

/-- The restriction map of `extendScalarsPresheaf R F` along `f` sends a pure tensor `r ⊗ₜ x` to
`R.map f r ⊗ₜ F.map f x`. -/
public lemma extendScalarsPresheaf_map_tmul (F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z})
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (x : F.obj X) :
    (extendScalarsPresheaf R F).map f (r ⊗ₜ[ℤ] x) = R.map f r ⊗ₜ[ℤ] F.map f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Extension of scalars on a morphism of abelian presheaves. -/
public noncomputable def extendScalarsPresheafMap
    {F G : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}} (f : F ⟶ G) :
    extendScalarsPresheaf R F ⟶ extendScalarsPresheaf R G where
  app X := ModuleCat.ofHom (AlgebraTensorModule.map (LinearMap.id : R.obj X →ₗ[R.obj X] R.obj X)
    (f.app X).hom.toIntLinearMap)
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change R.map g r ⊗ₜ[ℤ] f.app Y (F.map g x) =
      R.map g r ⊗ₜ[ℤ] G.map g (f.app X x)
    rw [NatTrans.naturality_apply]

/-- The component at `X` of `extendScalarsPresheafMap R f` sends a pure tensor `r ⊗ₜ x` to
`r ⊗ₜ f.app X x`. -/
public lemma extendScalarsPresheafMap_app_tmul
    {F G : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}} (f : F ⟶ G)
    (X : Dᵒᵖ) (r : R.obj X) (x : F.obj X) :
    (extendScalarsPresheafMap R f).app X (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] f.app X x := rfl

/-- Extension of scalars sends the zero morphism to zero. -/
private lemma extendScalarsPresheafMap_zero {F G : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}} :
    extendScalarsPresheafMap R (0 : F ⟶ G) = 0 := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro r m
  change (extendScalarsPresheafMap R (0 : F ⟶ G)).app V (r ⊗ₜ[ℤ] m) = 0
  rw [extendScalarsPresheafMap_app_tmul]
  simp only [zero_app, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply,
    TensorProduct.tmul_zero]
  rfl

-- The sections of `extendScalarsPresheaf R F` are a tensor product only after
-- unfolding; making that unfolding visible lets the elaborator see the module
-- structure the lemmas below are about.
attribute [local implicit_reducible] extendScalarsPresheaf

/-- An additive morphism to the underlying abelian presheaf of a presheaf of
`R`-modules extends uniquely to an `R`-linear morphism out of the extension of
scalars. -/
public noncomputable def extendScalarsPresheafLift
    {F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}} {M : PresheafOfModules.{max r z} R}
    (f : F ⟶ M.presheaf) : extendScalarsPresheaf R F ⟶ M where
  app X := ModuleCat.ofHom
    (X := (extendScalarsPresheaf R F).obj X) (Y := M.obj X)
    (AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton (R.obj X) (F.obj X →ₗ[ℤ] M.obj X)
        (f.app X).hom.toIntLinearMap))
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    exact (congrArg (fun y => R.map g r • y) (NatTrans.naturality_apply f g x)).trans
      (M.map_smul g r (f.app X x)).symm

/-- The component at `X` of `extendScalarsPresheafLift R f` sends a pure tensor `r ⊗ₜ x` to
`r • f.app X x`. -/
public lemma extendScalarsPresheafLift_app_tmul {F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}}
    {M : PresheafOfModules.{max r z} R} (f : F ⟶ M.presheaf)
    (X : Dᵒᵖ) (r : R.obj X) (x : F.obj X) :
    (extendScalarsPresheafLift R f).app X (r ⊗ₜ[ℤ] x) = r • f.app X x := rfl

/-- The canonical additive morphism into the extension of scalars, given by tensoring
with `1`. -/
public noncomputable def extendScalarsPresheafUnit (F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}) :
    F ⟶ (extendScalarsPresheaf R F).presheaf where
  app X := AddCommGrpCat.ofHom ((TensorProduct.mk ℤ (R.obj X) (F.obj X) 1).toAddMonoidHom)
  naturality {X Y} f := by
    ext x
    change 1 ⊗ₜ[ℤ] F.map f x = (extendScalarsPresheaf R F).map f (1 ⊗ₜ[ℤ] x)
    rw [extendScalarsPresheaf_map_tmul, map_one]

/-- The linear extension `extendScalarsPresheafLift R f` restricts to `f` along the unit
`extendScalarsPresheafUnit R F`: precomposing its underlying additive morphism with the unit
recovers `f`. -/
public lemma extendScalarsPresheafUnit_comp_lift {F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}}
    {M : PresheafOfModules.{max r z} R} (f : F ⟶ M.presheaf) :
    extendScalarsPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map
      (extendScalarsPresheafLift R f) = f := by
  ext X x
  show (extendScalarsPresheafLift R f).app X (1 ⊗ₜ[ℤ] x) = f.app X x
  rw [extendScalarsPresheafLift_app_tmul, one_smul]

/-- Extension of scalars corepresents the underlying abelian presheaf: `R`-linear
morphisms out of `R ⊗[ℤ] F` are additive morphisms out of `F`. -/
public noncomputable def extendScalarsPresheafHomAddEquiv
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{max r z}) (M : PresheafOfModules.{max r z} R) :
    (extendScalarsPresheaf R F ⟶ M) ≃+ (F ⟶ M.presheaf) where
  toFun f := extendScalarsPresheafUnit R F ≫ (PresheafOfModules.toPresheaf R).map f
  invFun := extendScalarsPresheafLift R
  left_inv f := by
    ext1 X
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r • (f.app X).hom (1 ⊗ₜ[ℤ] x) = (f.app X).hom (r ⊗ₜ[ℤ] x)
    calc
      _ = (f.app X).hom (r • (1 ⊗ₜ[ℤ] x)) :=
        ((f.app X).hom.map_smul r (1 ⊗ₜ[ℤ] x)).symm
      _ = _ := by
        congr 1
        change (r * 1) ⊗ₜ[ℤ] x = r ⊗ₜ[ℤ] x
        rw [mul_one]
  right_inv := extendScalarsPresheafUnit_comp_lift R
  map_add' f g := by
    ext X x
    rfl

end ExtendScalarsPresheaf

universe w z v u

-- The carriers of `AddCommGrpCat.free`, `AddCommGrpCat.uliftFunctor` and
-- `ModuleCat.uliftFunctor` are `FreeAbelianGroup` and `ULift` only after unfolding;
-- making that unfolding visible keeps the rewrites below type-correct.
attribute [local implicit_reducible] AddCommGrpCat.free AddCommGrpCat.uliftFunctor
  ModuleCat.uliftFunctor ModuleCat.extendScalars

section


private noncomputable def freeLiftIso :
    AddCommGrpCat.free.{v} ⋙ AddCommGrpCat.uliftFunctor.{w} ≅
    CategoryTheory.uliftFunctor.{w} ⋙ AddCommGrpCat.free :=
  NatIso.ofComponents (fun A =>
    (show ULift.{w} (FreeAbelianGroup A) ≃+ FreeAbelianGroup (ULift.{w} A) from
      AddEquiv.ulift.trans (FreeAbelianGroup.equivOfEquiv Equiv.ulift.symm)).toAddCommGrpIso)
    (by
      intro A B f
      apply AddCommGrpCat.hom_ext
      ext x
      change FreeAbelianGroup.map ULift.up (FreeAbelianGroup.map f x.down) =
        FreeAbelianGroup.map (fun t => ULift.up (f t.down)) (FreeAbelianGroup.map ULift.up x.down)
      rw [← FreeAbelianGroup.map_comp_apply, ← FreeAbelianGroup.map_comp_apply]
      rfl)

private noncomputable def sigmaPUnitIso :
    sigmaConst.obj (PUnit : Type v) ≅ 𝟭 (Type v) :=
  NatIso.ofComponents
    (fun A => Types.coproductIso (fun _ : A => (PUnit : Type v)) ≪≫
      (Equiv.sigmaUnique A (fun _ => PUnit)).toIso)
    (by
      intro A B f
      apply Sigma.hom_ext
      intro a
      simp only [sigmaConst, Sigma.map', Iso.trans_hom, Category.assoc,
        Sigma.ι_desc_assoc, Category.id_comp]
      simp only [← Category.assoc, Types.coproductIso_ι_comp_hom]
      rfl)

private noncomputable def freeSigmaIso :
    AddCommGrpCat.free.{v} ≅ sigmaConst.obj (AddCommGrpCat.free.obj (PUnit : Type v)) :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight sigmaPUnitIso.symm _ ≪≫
    sigmaConstObjCompIso AddCommGrpCat.free (PUnit : Type v)

private noncomputable def formalCoproductEvalCompIso
    {D : Type*} [Category* D] {A : Type*} [Category* A]
    {B : Type*} [Category* B] [HasCoproducts.{w} A] [HasCoproducts.{w} B]
    (F : D ⥤ A) (G : A ⥤ B) [PreservesColimitsOfSize.{w, w} G] :
    (FormalCoproduct.eval.{w} D A).obj F ⋙ G ≅
      (FormalCoproduct.eval.{w} D B).obj (F ⋙ G) := by
  refine NatIso.ofComponents
    (fun T => (asIso (sigmaComparison G (fun i => F.obj (T.obj i)))).symm) ?_
  intro T T' f
  apply (cancel_epi (sigmaComparison G (fun i => F.obj (T.obj i)))).1
  change (sigmaComparison G (fun i => F.obj (T.obj i))) ≫
      G.map (Sigma.desc (fun i => F.map (f.φ i) ≫
        Sigma.ι (fun i => F.obj (T'.obj i)) (f.f i))) ≫
      inv (sigmaComparison G (fun i => F.obj (T'.obj i))) =
    (sigmaComparison G (fun i => F.obj (T.obj i))) ≫
      inv (sigmaComparison G (fun i => F.obj (T.obj i))) ≫
      Sigma.desc (fun i => G.map (F.map (f.φ i)) ≫
        Sigma.ι (fun i => G.obj (F.obj (T'.obj i))) (f.f i))
  rw [← Category.assoc, sigmaComparison_map_desc]
  apply Sigma.hom_ext
  intro i
  simp [Category.assoc]

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]

private noncomputable def cechSetRealization (V : Cᵒᵖ) :
    FormalCoproduct.{w} (Over X) ⥤ Type (max w v) :=
  (FormalCoproduct.eval _ _).obj
    (Over.forget X ⋙ uliftYoneda.{v} ⋙ (evaluation Cᵒᵖ (Type v)).obj V ⋙
      CategoryTheory.uliftFunctor.{w})

private noncomputable def cechRealizationIso (V : Cᵒᵖ) :
    integralCechRealization.{w, v, u, v} (X := X) ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V ⋙ AddCommGrpCat.uliftFunctor.{w} ≅
    cechSetRealization (X := X) V ⋙
      sigmaConst.obj (AddCommGrpCat.free.obj (PUnit : Type (max w v))) := by
  let H := Over.forget X ⋙ uliftYoneda.{v} ⋙ (evaluation Cᵒᵖ (Type v)).obj V
  refine formalCoproductEvalCompIso (Over.forget X ⋙ freeAbelianYoneda.{v, u, v})
    ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V ⋙ AddCommGrpCat.uliftFunctor.{w}) ≪≫ ?_
  change (FormalCoproduct.eval.{w} (Over X) AddCommGrpCat.{max w v}).obj
      (H ⋙ AddCommGrpCat.free ⋙ AddCommGrpCat.uliftFunctor.{w}) ≅ _
  refine (FormalCoproduct.eval _ _).mapIso (Functor.isoWhiskerLeft H freeLiftIso) ≪≫ ?_
  refine (formalCoproductEvalCompIso (H ⋙ CategoryTheory.uliftFunctor.{w})
    AddCommGrpCat.free).symm ≪≫ ?_
  exact Functor.isoWhiskerLeft _ freeSigmaIso

private noncomputable def cechSSet (V : Cᵒᵖ) : SSet.{max w v} :=
  cechSimplicialObject E ⋙ cechSetRealization (X := X) V

private noncomputable def evaluatedCechIso (V : Cᵒᵖ) :
    ((((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V ⋙
      AddCommGrpCat.uliftFunctor.{w}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (integralCechComplex.{w, v, u, v} E)) ≅
    (cechSSet E V).chainComplex (AddCommGrpCat.free.obj (PUnit : Type (max w v))) := by
  refine (alternatingFaceMapComplexCompMapHomologicalComplexIso _).app
    (integralCechSimplicialObject.{w, v, u, v} E) ≪≫ ?_
  exact (alternatingFaceMapComplex _).mapIso
    (Functor.isoWhiskerLeft (cechSimplicialObject E) (cechRealizationIso V))

private noncomputable def evaluatedCech (V : Cᵒᵖ) : ChainComplex AddCommGrpCat.{v} ℕ :=
  (((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V).mapHomologicalComplex _).obj
    (integralCechComplex.{w, v, u, v} E)

private lemma evaluatedCech_projective (V : Cᵒᵖ) (n : ℕ) :
    Projective ((evaluatedCech E V).X n) := by
  apply (AddCommGrpCat.uliftFunctor.{w, v}).projective_of_map_projective
  let P := AddCommGrpCat.free.obj (PUnit : Type (max w v))
  have : Projective P := AddCommGrpCat.adj.map_projective _ inferInstance
  exact Projective.of_iso ((HomologicalComplex.eval _ _ n).mapIso (evaluatedCechIso E V)).symm
    (inferInstanceAs (Projective (∐ fun _ : (cechSSet E V).obj _ => P)))

private lemma evaluatedCech_homology_zero_projective (V : Cᵒᵖ) :
    Projective ((evaluatedCech E V).homology 0) := by
  apply (AddCommGrpCat.uliftFunctor.{w, v}).projective_of_map_projective
  let P := AddCommGrpCat.free.obj (PUnit : Type (max w v))
  have : Projective P := AddCommGrpCat.adj.map_projective _ inferInstance
  let q := HomologicalComplex.homologyMapIso (evaluatedCechIso E V) 0 ≪≫
    (cechSSet E V).homology₀Iso P
  let t := ((evaluatedCech E V).sc 0).mapHomologyIso AddCommGrpCat.uliftFunctor.{w}
  exact Projective.of_iso (q.symm ≪≫ t)
    (inferInstanceAs (Projective (∐ fun _ : SSet.π₀ (cechSSet E V) => P)))

private lemma evaluatedCech_exactAt (V : Cᵒᵖ) (n : ℕ) (hn : 0 < n) :
    (evaluatedCech E V).ExactAt n :=
  (((integralCechComplex.{w, v, u, v} E).exactAt_iff_isZero_homology n).mpr
    (integralCechComplex_homology_isZero E n hn)).map ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V)

end

section

open HomologicalComplex

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

-- The degree-zero term of a single-object complex is the object itself only after
-- unfolding `HomologicalComplex.single`; making that unfolding visible keeps the
-- rewrites below type-correct.
attribute [local implicit_reducible] HomologicalComplex.single

private noncomputable def resolutionOfExact (K : ChainComplex A ℕ)
    [∀ i, Projective (K.X i)] (hK : ∀ n, 0 < n → K.ExactAt n) :
    ProjectiveResolution (K.opcycles 0) := by
  let π := (ChainComplex.toSingle₀Equiv K (K.opcycles 0)).symm
    ⟨K.pOpcycles 0, by simp⟩
  refine { complex := K, π := π, quasiIso := ?_ }
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have h : homologyMap π 0 = K.isoHomologyι₀.hom ≫
        (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (K.opcycles 0)).inv := by
      rw [← cancel_epi K.isoHomologyι₀.inv, ← cancel_epi (K.pOpcycles 0)]
      simp only [Iso.inv_hom_id_assoc]
      rw [ChainComplex.isoHomologyι₀_inv_naturality, p_opcyclesMap_assoc]
      dsimp only [π]
      rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
        ← cancel_mono (((ChainComplex.single₀ A).obj (K.opcycles 0)).homologyι 0),
        Category.assoc, Category.assoc, Category.assoc,
        HomologicalComplex.isoHomologyι_inv_hom_id, Category.comp_id,
        singleObjHomologySelfIso_inv_homologyι, singleObjOpcyclesSelfIso_hom,
        ChainComplex.single₀ObjXSelf, Iso.refl_inv]
      simp
    rw [h]
    infer_instance
  | succ n =>
    exact (quasiIsoAt_iff_exactAt π (n + 1) (hK _ (Nat.succ_pos _))).mpr
      (ChainComplex.exactAt_succ_single_obj _ _)

private lemma exactAt_map_of_projective (K : ChainComplex A ℕ)
    [∀ i, Projective (K.X i)] [Projective (K.homology 0)]
    (hK : ∀ n, 0 < n → K.ExactAt n) (F : A ⥤ B) [F.Additive]
    (n : ℕ) (hn : 0 < n) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).ExactAt n := by
  have : Projective (K.opcycles 0) := Projective.of_iso K.isoHomologyι₀ inferInstance
  let P := resolutionOfExact K hK
  let e := F.mapHomotopyEquiv (P.homotopyEquiv (ProjectiveResolution.self (K.opcycles 0)))
  apply (exactAt_iff_isZero_homology _ _).mpr
  apply IsZero.of_iso _ (e.toHomologyIso n)
  apply (exactAt_iff_isZero_homology _ _).mp
  apply HomologicalComplex.ExactAt.of_isZero
  show IsZero (F.obj (((ChainComplex.single₀ A).obj (K.opcycles 0)).X n))
  exact F.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.ne_of_gt hn))

end

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  (O : Cᵒᵖ ⥤ CommRingCat.{z})

/-- Any additive functor preserves the exactness of the evaluated integral Čech complex in
positive degrees. -/
private lemma evaluatedCech_map_exactAt
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (V : Cᵒᵖ) {B : Type*} [Category* B] [Abelian B] (F : AddCommGrpCat.{v} ⥤ B) [F.Additive]
    (n : ℕ) (hn : 0 < n) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (evaluatedCech E V)).ExactAt n := by
  have : ∀ i, Projective ((evaluatedCech E V).X i) := evaluatedCech_projective E V
  have : Projective ((evaluatedCech E V).homology 0) :=
    evaluatedCech_homology_zero_projective E V
  exact exactAt_map_of_projective _ (evaluatedCech_exactAt E V) F n hn

/-- Extension of scalars along `ℤ → O`, from abelian presheaves on the site to presheaves of
modules over `ringPresheaf O`, after lifting the coefficient universe of the abelian presheaf
into the universe of the tensor product. -/
public noncomputable def integralCechTensorFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤
      _root_.PresheafOfModules.{max v z} (ringPresheaf O) where
  obj F := extendScalarsPresheaf
    (ringPresheaf O) (F ⋙ AddCommGrpCat.uliftFunctor.{z, v})
  map {F G} f := extendScalarsPresheafMap
    (ringPresheaf O) (Functor.whiskerRight f AddCommGrpCat.uliftFunctor)
  map_id F := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    rfl

private lemma integralCechTensorFunctor_map_zero :
    ∀ {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}},
      (integralCechTensorFunctor O).map (0 : F ⟶ G) = 0 := by
  intro F G
  change extendScalarsPresheafMap _ (Functor.whiskerRight 0 _) = 0
  rw [Functor.whiskerRight_zero, extendScalarsPresheafMap_zero]

/-- The functor `integralCechTensorFunctor O` preserves zero morphisms. -/
public lemma integralCechTensorFunctor_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (integralCechTensorFunctor O) :=
  ⟨fun _ _ => integralCechTensorFunctor_map_zero O⟩

/-- The value at `V` of the integral Čech complex tensored over `ℤ` with
the ring presheaf `O`. -/
public noncomputable def integralCechComplexTensorAt (V : Cᵒᵖ)
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    ChainComplex (ModuleCat.{max v z} (O.obj V)) ℕ :=
  (((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V ⋙
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse ⋙
      ModuleCat.uliftFunctor.{z, v} ℤ ⋙
      ModuleCat.extendScalars (Int.castRingHom (O.obj V))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (integralCechComplex.{w, v, u, v} E)

/-- The integral Čech term at an object, regarded as an integer module in the
universe of the scalar-extension construction. -/
public noncomputable def integralCechIntegralAt (V : Cᵒᵖ) (n : ℕ)
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (k : ℕ) (i : Fin (k + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] : ModuleCat.{max v z} ℤ :=
  (ModuleCat.uliftFunctor.{z, v} ℤ).obj
    ((forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse.obj
      (((integralCechComplex.{w, v, u, v} E).X n).obj V))

/-- Restriction on an integral Čech term, viewed as an integer-linear map. -/
public noncomputable def integralCechIntegralMap {V W : Cᵒᵖ} (f : V ⟶ W) (n : ℕ)
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (k : ℕ) (i : Fin (k + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    integralCechIntegralAt.{w, z, v, u} E V n ⟶
      integralCechIntegralAt.{w, z, v, u} E W n :=
  (ModuleCat.uliftFunctor.{z, v} ℤ).map
    ((forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse.map
      (((integralCechComplex.{w, v, u, v} E).X n).map f))

/-- The inverse of the equivalence `forget₂ (ModuleCat ℤ) AddCommGrpCat` sends an abelian group
`A` to a `ℤ`-module isomorphic to `ModuleCat.of ℤ A`. -/
public noncomputable def zModuleIso (A : AddCommGrpCat.{v}) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.obj A ≅ ModuleCat.of ℤ A := by
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let eF := F.asEquivalence
  let e : F.obj (eF.inverse.obj A) ≅ F.obj (ModuleCat.of ℤ A) :=
    eF.counitIso.app A ≪≫ (Iso.refl A).symm
  exact (Equivalence.fullyFaithfulFunctor eF).preimageIso e

/-- The isomorphisms `zModuleIso` are natural in the abelian group. -/
public lemma zModuleIso_naturality (A B : AddCommGrpCat.{v}) (g : A ⟶ B) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.map g ≫ (zModuleIso B).hom =
      (zModuleIso A).hom ≫ ModuleCat.ofHom (g.hom.toIntLinearMap) := by
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let eF := F.asEquivalence
  let eIsoA : F.obj (eF.inverse.obj A) ≅ F.obj (ModuleCat.of ℤ A) :=
    eF.counitIso.app A ≪≫ (Iso.refl A).symm
  let eIsoB : F.obj (eF.inverse.obj B) ≅ F.obj (ModuleCat.of ℤ B) :=
    eF.counitIso.app B ≪≫ (Iso.refl B).symm
  apply (Equivalence.fullyFaithfulFunctor eF).map_injective
  have hA : F.map (zModuleIso A).hom = eIsoA.hom := eF.fullyFaithfulFunctor.map_preimage _
  have hB : F.map (zModuleIso B).hom = eIsoB.hom := eF.fullyFaithfulFunctor.map_preimage _
  show F.map (eF.inverse.map g) ≫ F.map (zModuleIso B).hom =
    F.map (zModuleIso A).hom ≫ F.map (ModuleCat.ofHom (g.hom.toIntLinearMap))
  rw [hB, hA]
  simp only [eIsoA, eIsoB]
  show (eF.inverse ⋙ F).map g ≫ eF.counitIso.hom.app B =
    eF.counitIso.hom.app A ≫ g
  exact eF.counitIso.hom.naturality g

/-- Lifting the universe of the `ℤ`-module `ModuleCat.of ℤ A` gives the `ℤ`-module of the
universe-lifted abelian group `ULift A`. -/
public noncomputable def uliftModuleIso (A : AddCommGrpCat.{v}) :
    (ModuleCat.uliftFunctor.{z, v} ℤ).obj (ModuleCat.of ℤ A) ≅
      ModuleCat.of ℤ (AddCommGrpCat.uliftFunctor.{z, v}.obj A) :=
  (forget₂ (ModuleCat.{max v z} ℤ) AddCommGrpCat.{max v z}).asEquivalence.fullyFaithfulFunctor
    |>.preimageIso (Iso.refl (AddCommGrpCat.of (ULift A)))

/-- The isomorphism `uliftModuleIso` is the identity on underlying elements of `ULift A`. -/
public lemma uliftModuleIso_hom_apply (A : AddCommGrpCat.{v}) (x : ULift.{z} A) :
    (uliftModuleIso.{z, v} A).hom.hom x = x := by
  let Fz := forget₂ (ModuleCat.{max v z} ℤ) (AddCommGrpCat.{max v z})
  have h : Fz.map (uliftModuleIso.{z, v} A).hom = 𝟙 (AddCommGrpCat.of (ULift A)) :=
    Fz.asEquivalence.fullyFaithfulFunctor.map_preimage _
  exact congrArg (fun k => k x) h

/-- The universe lift of the `ℤ`-module attached to an abelian group `A` by the inverse of the
equivalence `forget₂ (ModuleCat ℤ) AddCommGrpCat` is isomorphic to the `ℤ`-module of the
universe-lifted abelian group `ULift A`; this is `zModuleIso` followed by `uliftModuleIso`. -/
public noncomputable def zLiftIso (A : AddCommGrpCat.{v}) :
    (ModuleCat.uliftFunctor.{z, v} ℤ).obj
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.obj A) ≅
    ModuleCat.of ℤ (AddCommGrpCat.uliftFunctor.{z, v}.obj A) :=
  (ModuleCat.uliftFunctor.{z, v} ℤ).mapIso (zModuleIso A) ≪≫ uliftModuleIso A

private lemma zLiftIso_naturality (A B : AddCommGrpCat.{v}) (g : A ⟶ B) :
    (ModuleCat.uliftFunctor.{z, v} ℤ).map
        ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.map g) ≫
      (zLiftIso B).hom =
      (zLiftIso A).hom ≫ ModuleCat.ofHom
      ((AddCommGrpCat.uliftFunctor.map g).hom.toIntLinearMap) := by
  have h : (ModuleCat.uliftFunctor.{z, v} ℤ).map (ModuleCat.ofHom (g.hom.toIntLinearMap)) ≫
      (uliftModuleIso B).hom = (uliftModuleIso A).hom ≫ ModuleCat.ofHom
        ((AddCommGrpCat.uliftFunctor.map g).hom.toIntLinearMap) := by
    apply ModuleCat.hom_ext
    ext x
    show (uliftModuleIso B).hom.hom (ULift.up (g x.down)) =
      ULift.up (g ((uliftModuleIso A).hom.hom x).down)
    rw [uliftModuleIso_hom_apply, uliftModuleIso_hom_apply]
  simp only [zLiftIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, zModuleIso_naturality, Functor.map_comp,
    Category.assoc, h]

/-- For a commutative ring `S` and an abelian group `A`, the `S`-module `S ⊗[ℤ] ULift A` is
isomorphic to the extension of scalars of the `ℤ`-module `ULift A` along `ℤ → S`. -/
public noncomputable def zTensorIso (A : AddCommGrpCat.{v}) (S : Type z) [CommRing S] :
    ModuleCat.of S (TensorProduct ℤ S (AddCommGrpCat.uliftFunctor.{z, v}.obj A)) ≅
    (ModuleCat.extendScalars (Int.castRingHom S)).obj
      (ModuleCat.of ℤ (AddCommGrpCat.uliftFunctor.{z, v}.obj A)) := by
  let f : ℤ →+* S := Int.castRingHom S
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  let G := AddCommGrpCat.uliftFunctor.{z, v}.obj A
  let e₂ : G ≃ₗ[ℤ] G := LinearEquiv.refl ℤ G
  letI : Module S (M : Type _) := (ModuleCat.of S S).isModule
  letI : Module ℤ (M : Type _) := M.isModule
  letI : SMul ℤ (M : Type _) := M.isModule.toSMul
  letI : IsScalarTower ℤ S S := AddCommGroup.intIsScalarTower
  letI : IsScalarTower ℤ S (M : Type _) := ⟨fun n s x => by
    calc
      (n • s) • x = (f n • s) • x := by rw [show f n • s = n • s by simp [f]]
      _ = f n • (s • x) := smul_assoc _ _ _
      _ = n • (s • x) := (ModuleCat.restrictScalars.smul_def f n (s • x)).symm⟩
  let e₁ : S ≃ₗ[S] (M : Type _) := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact (TensorProduct.AlgebraTensorModule.congr (R := ℤ) (A := S)
    (M := S) (P := (M : Type _)) (N := G) (Q := G) e₁ e₂).toModuleIso

/-- For a commutative ring `S` and an abelian group `A`, the `S`-module `S ⊗[ℤ] ULift A` is
isomorphic to the extension of scalars along `ℤ → S` of the universe-lifted `ℤ`-module attached
to `A`; this is `zTensorIso` followed by the inverse of `zLiftIso` under extension of scalars. -/
public noncomputable def tensorTermIso (A : AddCommGrpCat.{v}) (S : Type z) [CommRing S] :
    ModuleCat.of S (TensorProduct ℤ S (AddCommGrpCat.uliftFunctor.{z, v}.obj A)) ≅
    (ModuleCat.extendScalars (Int.castRingHom S)).obj
      ((ModuleCat.uliftFunctor.{z, v} ℤ).obj
        ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.obj A)) :=
  zTensorIso A S ≪≫ ((ModuleCat.extendScalars (Int.castRingHom S)).mapIso (zLiftIso A)).symm

/-- The isomorphism `tensorTermIso A S` sends a pure tensor `s ⊗ₜ m` to
`s ⊗ₜ (zLiftIso A).inv m`. -/
public lemma tensorTermIso_hom_tmul (A : AddCommGrpCat.{v})
    (S : Type z) [CommRing S] (s : S) (m : AddCommGrpCat.uliftFunctor.{z, v}.obj A) :
    (tensorTermIso A S).hom (s ⊗ₜ[ℤ] m) =
      s ⊗ₜ[ℤ, Int.castRingHom S] ((zLiftIso A).inv m) := by
  show (ModuleCat.extendScalars (Int.castRingHom S)).map (zLiftIso A).inv
    ((zTensorIso A S).hom (s ⊗ₜ[ℤ] m)) = _
  show (ModuleCat.extendScalars (Int.castRingHom S)).map (zLiftIso A).inv
    (s ⊗ₜ[ℤ, Int.castRingHom S] m) = _
  exact ModuleCat.ExtendScalars.map_tmul _ _ _ _

/-- The inverse of `tensorTermIso A S` sends a pure tensor `s ⊗ₜ m` to
`s ⊗ₜ (zLiftIso A).hom m`. -/
public lemma tensorTermIso_inv_tmul (A : AddCommGrpCat.{v})
    (S : Type z) [CommRing S] (s : S)
    (m : (ModuleCat.uliftFunctor.{z, v} ℤ).obj
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.obj A)) :
    (tensorTermIso A S).inv (s ⊗ₜ[ℤ, Int.castRingHom S] m) =
      s ⊗ₜ[ℤ] ((zLiftIso A).hom m) := by
  show (zTensorIso A S).inv
    ((ModuleCat.extendScalars (Int.castRingHom S)).map (zLiftIso A).hom
      (s ⊗ₜ[ℤ, Int.castRingHom S] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

/-- A chain complex of presheaves of modules whose evaluations at all objects are exact in degree
`n` has vanishing homology in degree `n`. -/
private lemma isZero_homology_of_evaluation_exactAt (R : Cᵒᵖ ⥤ RingCat.{z})
    (K : ChainComplex (_root_.PresheafOfModules.{max v z} R) ℕ) (n : ℕ)
    (h : ∀ V : Cᵒᵖ, (((_root_.PresheafOfModules.evaluation R V).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).ExactAt n) :
    IsZero (K.homology n) := by
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro V
  exact ((h V).isZero_homology.of_iso
    ((K.sc n).mapHomologyIso (_root_.PresheafOfModules.evaluation R V)).symm).eq_of_src _ _

/-- The presheaf tensor construction, including the compatibility of its
objectwise tensor identifications with restriction. -/
public structure IntegralCechComplexTensorSpec
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] where
    /-- The chain complex of presheaves of modules over `ringPresheaf O`. -/
    K : ChainComplex (_root_.PresheafOfModules.{max v z}
      (ringPresheaf O)) ℕ
    /-- For each object `V`, an isomorphism between the complex `K` evaluated at `V` and
    `integralCechComplexTensorAt E O V`. -/
    ι : ∀ V : Cᵒᵖ,
        (((_root_.PresheafOfModules.evaluation
          (ringPresheaf O) V).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj K) ≅
          integralCechComplexTensorAt E O V
    naturality : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) (n : ℕ)
          (s : O.obj V) (m : integralCechIntegralAt.{w, z, v, u} E V n),
          (ι W).hom.f n
            ((K.X n).map f ((ι V).inv.f n
              (s ⊗ₜ[ℤ, Int.castRingHom (O.obj V)] m))) =
            (O.map f s) ⊗ₜ[ℤ, Int.castRingHom (O.obj W)]
              (integralCechIntegralMap.{w, z, v, u} E f n m)

/-- The integral Čech complex with `integralCechTensorFunctor O` applied termwise: a chain
complex of presheaves of modules over `ringPresheaf O`. -/
public noncomputable def integralCechTensorComplex
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    ChainComplex (_root_.PresheafOfModules.{max v z}
      (ringPresheaf O)) ℕ := by
  letI := integralCechTensorFunctor_preservesZeroMorphisms O
  exact ((integralCechTensorFunctor O).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (integralCechComplex.{w, v, u, v} E)

/-- The inverses of the isomorphisms `zLiftIso` are natural: for `g : A ⟶ B`, applying
`(zLiftIso B).inv` after the universe lift of `g` agrees with applying the image of `g` under the
universe-lifted inverse of `forget₂ (ModuleCat ℤ) AddCommGrpCat` after `(zLiftIso A).inv`. -/
public lemma zLiftIso_inv_naturality (A B : AddCommGrpCat.{v}) (g : A ⟶ B)
    (m : AddCommGrpCat.uliftFunctor.{z, v}.obj A) :
    (zLiftIso B).inv ((AddCommGrpCat.uliftFunctor.map g) m) =
      (ModuleCat.uliftFunctor.{z, v} ℤ).map
        ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.map g)
          ((zLiftIso A).inv m) := by
  apply (ConcreteCategory.bijective_of_isIso (zLiftIso B).hom).1
  have h := congrArg (fun k => k ((zLiftIso A).inv m)) (zLiftIso_naturality A B g)
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, ModuleCat.hom_ofHom,
    AddMonoidHom.coe_toIntLinearMap] using h.symm

/-- For each object `V`, the complex `integralCechTensorComplex E O` evaluated at `V` is
isomorphic to `integralCechComplexTensorAt E O V`, with components given by `tensorTermIso`. -/
public noncomputable def tensorComplexIso
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] (V : Cᵒᵖ) :
    (((PresheafOfModules.evaluation (ringPresheaf O) V).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (integralCechTensorComplex E O)) ≅
      integralCechComplexTensorAt E O V := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorTermIso (((integralCechComplex.{w, v, u, v} E).X n).obj V)
      (O.obj V)) ?_
  intro i j hij
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro r m
  symm
  change (tensorTermIso _ _).hom
    ((extendScalarsPresheafMap (ringPresheaf O)
      (Functor.whiskerRight ((integralCechComplex.{w, v, u, v} E).d i j)
        AddCommGrpCat.uliftFunctor)).app V (r ⊗ₜ[ℤ] m)) =
    (ModuleCat.extendScalars (Int.castRingHom (O.obj V))).map
      ((ModuleCat.uliftFunctor ℤ).map
        ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse.map
          (((integralCechComplex.{w, v, u, v} E).d i j).app V)))
      ((tensorTermIso _ _).hom (r ⊗ₜ[ℤ] m))
  rw [extendScalarsPresheafMap_app_tmul, tensorTermIso_hom_tmul, tensorTermIso_hom_tmul]
  congr 1
  exact zLiftIso_inv_naturality _ _ _ m

/-- The presheaf-of-`O`-modules complex obtained by tensoring the integral Čech
complex with `O` over the constant integer presheaf. -/
@[stacks 03F5 "the tensor product presheaf complex"]
public noncomputable def integralCechComplexTensor
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    IntegralCechComplexTensorSpec E O := by
  refine ⟨integralCechTensorComplex E O, tensorComplexIso E O, ?_⟩
  intro V W f n s m
  dsimp only [integralCechIntegralAt] at m
  change (tensorTermIso _ _).hom
    ((extendScalarsPresheaf (ringPresheaf O)
      ((integralCechComplex.{w, v, u, v} E).X n ⋙ AddCommGrpCat.uliftFunctor)).map f
      ((tensorTermIso _ _).inv (s ⊗ₜ[ℤ, Int.castRingHom (O.obj V)] m))) = _
  rw [tensorTermIso_inv_tmul, extendScalarsPresheaf_map_tmul,
    tensorTermIso_hom_tmul]
  dsimp only [Functor.comp_map]
  rw [zLiftIso_inv_naturality]
  simp only [Iso.hom_inv_id_apply]
  rfl

private lemma integralCechComplexTensorAt_exactAt
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (V : Cᵒᵖ) (n : ℕ) (hn : 0 < n) :
    (integralCechComplexTensorAt E O V).ExactAt n := by
  have : (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse.Additive := by
    have : (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.functor.Additive :=
      inferInstanceAs (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).Additive
    exact Equivalence.inverse_additive _
  have : (ModuleCat.extendScalars (Int.castRingHom (O.obj V)) :
      ModuleCat.{max v z} ℤ ⥤ _).Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (ModuleCat.extendScalars (Int.castRingHom (O.obj V)) : ModuleCat.{max v z} ℤ ⥤ _)
    exact Functor.additive_of_preservesBinaryBiproducts _
  exact evaluatedCech_map_exactAt E V
    ((forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse ⋙
      ModuleCat.uliftFunctor.{z, v} ℤ ⋙
      ModuleCat.extendScalars (Int.castRingHom (O.obj V))) n hn

/-- **Stacks Project, Tag 03F5.** Tensoring the integral Čech complex with a
presheaf of rings leaves it exact in every positive degree. -/
@[stacks 03F5 "positive-degree exactness"]
public theorem integralCechComplexTensor_homology_isZero
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (n : ℕ) (hn : 0 < n) :
    IsZero ((integralCechComplexTensor E O).K.homology n) := by
  exact isZero_homology_of_evaluation_exactAt _ _ n fun V =>
    (integralCechComplexTensorAt_exactAt E O V n hn).of_iso
      ((integralCechComplexTensor E O).ι V).symm

/-! ### Coefficients in a presheaf of rings, not assumed commutative

The same tensor product and the same exactness, for a presheaf `R : Cᵒᵖ ⥤ RingCat` of rings
which need not be commutative. Over an object of the site the tensored complex is
`extendScalarsGrp` applied to the evaluated integral Čech complex on the nose, so no
objectwise comparison isomorphism is needed. -/

section RingCoefficients

variable (R : Cᵒᵖ ⥤ RingCat.{z})

/-- Extension of scalars along `ℤ → R`, from abelian presheaves on the site to presheaves of
`R`-modules, lifting the coefficient universe of the abelian presheaf into the universe of the
tensor product. -/
public noncomputable def integralCechTensorFunctorRing :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ _root_.PresheafOfModules.{max v z} R where
  obj F := extendScalarsPresheaf R (F ⋙ AddCommGrpCat.uliftFunctor.{z, v})
  map {F G} f := extendScalarsPresheafMap R
    (Functor.whiskerRight f AddCommGrpCat.uliftFunctor)
  map_id F := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    rfl

private lemma integralCechTensorFunctorRing_map_zero :
    ∀ {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}},
      (integralCechTensorFunctorRing R).map (0 : F ⟶ G) = 0 := by
  intro F G
  change extendScalarsPresheafMap _ (Functor.whiskerRight 0 _) = 0
  rw [Functor.whiskerRight_zero, extendScalarsPresheafMap_zero]

/-- The functor `integralCechTensorFunctorRing R` preserves zero morphisms. -/
public instance integralCechTensorFunctorRing_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (integralCechTensorFunctorRing R) :=
  ⟨fun _ _ => integralCechTensorFunctorRing_map_zero R⟩

/-- The presheaf-of-`R`-modules complex obtained by tensoring the integral Čech
complex with `R` over the constant integer presheaf. -/
@[stacks 03F5 "the tensor product presheaf complex"]
public noncomputable def integralCechComplexTensorRing
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    ChainComplex (_root_.PresheafOfModules.{max v z} R) ℕ :=
  ((integralCechTensorFunctorRing R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (integralCechComplex.{w, v, u, v} E)

/-- Over an object of the site, the tensored integral Čech complex is the image of the
evaluated integral Čech complex under extension of scalars along `ℤ → R(V)`, which is an
additive functor; so it is exact in positive degrees because the evaluated integral Čech
complex is a complex of projectives, exact in positive degrees, with projective homology in
degree zero. -/
private lemma evaluation_integralCechComplexTensorRing_exactAt
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (V : Cᵒᵖ) (n : ℕ) (hn : 0 < n) :
    (((_root_.PresheafOfModules.evaluation R V).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (integralCechComplexTensorRing E R)).ExactAt n := by
  exact evaluatedCech_map_exactAt E V
    (AddCommGrpCat.uliftFunctor.{z, v} ⋙ extendScalarsGrp.{z, v} (R.obj V)) n hn

/-- **Stacks Project, Tag 03F5.** Tensoring the integral Čech complex with a
presheaf of rings leaves it exact in every positive degree. -/
@[stacks 03F5 "positive-degree exactness"]
public theorem integralCechComplexTensorRing_homology_isZero
    [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{v})]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (n : ℕ) (hn : 0 < n) :
    IsZero ((integralCechComplexTensorRing E R).homology n) := by
  exact isZero_homology_of_evaluation_exactAt _ _ n fun V =>
    evaluation_integralCechComplexTensorRing_exactAt E R V n hn

end RingCoefficients

end Stacks.CechSite
