module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# The sectionwise tensor product of a differential graded module with a complex

Part of `StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex` (see there for the
overview).
This file sets up the ambient categories of `O`-modules, the base ring and its `ScalarSections`
datum, the differential graded category `CompDG` and the endomorphism algebra `Rep`, the
structures `BalancedDegreeMap` and `TensorWithComplexData`, and builds, degree by degree and on
each object of the site, the balanced tensor product `M ⊗_E K(U)` with its pure tensors, its
restriction maps and its functoriality in `M`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open DifferentialGraded DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o r i

section Sheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification exists in any section universe containing the site. -/
public instance tensorHasSheafify [UnivLE.{u, r}] [UnivLE.{v, r}] :
    HasSheafify J AddCommGrpCat.{r} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{r, v, u} J

/-- In the ambient tensor universe, sheafification inverts precisely the
locally bijective morphisms. -/
public instance tensorWEqualsLocallyBijective
    [UnivLE.{u, r}] [UnivLE.{v, r}] [UnivLE.{max r v, r}] :
    J.WEqualsLocallyBijective AddCommGrpCat.{r} := by
  have : HasLimitsOfSize.{r, max r v} AddCommGrpCat.{r} :=
    hasLimitsOfSizeOfUnivLE.{r, r, r, max r v, r, r + 1} AddCommGrpCat.{r}
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, u, r + 1, r} J

end Sheafification

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

/-- The forgetful functor from sheaves of `O`-modules to presheaves of modules is additive. -/
local instance :
    (SheafOfModules.forget.{r} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive where
  map_add := by intros; rfl

-- `PresheafOfModules.map` lands in `ModuleCat.restrictScalars`, whose carrier is the underlying
-- module; unfolding it is what lets the sectionwise rewrite lemmas below match.
attribute [local implicit_reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

/-- The category of `O`-modules whose sections lie in the universe `t`. -/
public abbrev ModO := SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

set_option linter.checkUnivs false in
/-- The ambient category of `O`-modules in which tensor products are formed. Its section
universe contains the site, the structure ring, the sections of `K`, and an independent size
parameter `s` for the carriers of the differential graded modules. The universes `t` and `s`
enter only through the bound `max u v w t s`, so neither occurs on its own in the type. -/
public abbrev TensorModO := SheafOfModules.{max u v w t s}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Embed an arbitrary complex in the ambient universe used for tensor products.
This only lifts its section modules; the site and structure sheaf are unchanged. -/
public noncomputable abbrev liftComplex (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ :=
  ((Stacks.SheafOfModules.moduleULift.{max u v w s, t}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-! ### The base ring

Stacks 0CS6 fixes a ring `R` and a sheaf of commutative `R`-algebras on the site. What that datum
provides is exactly a linear structure over `R` on the sheaves of `O`-modules, through which the
endomorphism differential graded algebra of a complex is a differential graded `R`-algebra. The
universal choice is `R = Γ(C, O)`, whose instance is
`Stacks.Cohomology.SiteModules.linearSheafOfModules` and needs no further datum; every other base
ring is obtained from it along a ring map by `CategoryTheory.Linear.ofRingHom`, which is what
`Stacks.Cohomology.SiteModules.AlgebraSheaf.toGlobalSections` supplies. Taking `R = ℤ` recovers
the `ℤ`-linear reading verbatim: `CochainComplex.dgCategoryLinear B ℤ` is
`CochainComplex.dgCategory B` by `rfl`, so `CompDG` and `Rep` at `R = ℤ` are definitionally the
category of Stacks 09L9 and the algebra of Stacks 09LE.

A linear structure alone is enough for everything up to the tensor functor's additivity. Its
`R`-linearity needs the second half of the source's datum — that the scalars really are sections
of `O` — which is `AlgebraicGeometry.RingedSite.ScalarSections` below, assumed only from the
section where the tensor functor is built.
-/

variable (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]

/-- **The base-ring scalars are sections of `O`.** Stacks 0CS6 does not fix an arbitrary linear
structure on the sheaves of `O`-modules: it fixes a sheaf of commutative `R`-algebras on `O`,
so a scalar `r : R` acts on a morphism of sheaves of `O`-modules by multiplying its sections by
a section of `O`. That is what this class records, and it is what lets a base-ring scalar be
moved across the balancing relation of the tensor product, where only `O`-linearity is available.

Both of the cases the source needs satisfy it: `R = ℤ` by
`AlgebraicGeometry.RingedSite.scalarSectionsInt` below, since then the action is the `ℤ`-action of
the additive group, and `R = Γ(C, O)` by `Stacks.Cohomology.SiteModules.globalSmul`, from which
every sheaf of `R`-algebras is obtained along a ring map by `CategoryTheory.Linear.ofRingHom`. -/
public class ScalarSections where
  /-- The section of `O` over `U` by which the scalar `r` acts. -/
  scalarSection (r : R) (U : X.Cᵒᵖ) : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U
  /-- Multiplying a morphism of sheaves of `O`-modules by `r` multiplies its values on sections
  over `U` by `scalarSection r U`. -/
  smul_app (r : R) {P Q : TensorModO.{u, v, w, t, s} X} (f : P ⟶ Q) (U : X.Cᵒᵖ)
      (y : P.val.obj U) :
    ((r • f).val.app U) y = scalarSection r U • ((f.val.app U) y)

/-- The differential graded category `Comp^dg(O)` of complexes of ambient `O`-modules, read over
the base ring `R`. As for `TensorModO`, the universes `t` and `s` enter only through
`max u v w t s`. At `R = ℤ` this is `CochainComplex.dgCategory` of Stacks 09L9, definitionally. -/
public noncomputable abbrev CompDG :=
  CochainComplex.dgCategoryLinear (TensorModO.{u, v, w, t, s} X) R
/-- The endomorphism differential graded algebra of `K` in `CompDG X R`, with the
representable differential graded functor `Hom(K, -)`. -/
public noncomputable abbrev Rep (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :=
  DGCategory.homRepresentation (CompDG.{u, v, w, t, s, o} X R)
    (liftComplex.{u, v, w, t, s} X K)

/-- A homogeneous, sectionwise bilinear map balanced over the endomorphism DGA.
The target is a module over the ring of sections of the structure sheaf. -/
public structure BalancedDegreeMap (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) (U : X.Cᵒᵖ)
      (d :
        ℤ)
    (P : ModuleCat.{r} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) where
  /-- The bilinear component `M^p → K^q(U) → P` in each bidegree `(p, q)` with `p + q = d`. -/
  toFun (p q : ℤ) (h : p + q = d) :
    M.grading p →ₗ[ℤ] (((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) →ₗ[ℤ] P
  map_smul (p q : ℤ) (h : p + q = d) (x : M.grading p)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    toFun p q h x (r • y) = r • toFun p q h x y
  balance (p q n : ℤ) (h₁ : (p + n) + q = d)
      (h₂ : p + (q + n) = d) (x : M.grading p)
      (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    toFun (p + n) q h₁
      ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
        M.smul_mem p n x a x.property a.property⟩ y =
      toFun p (q + n) h₂ x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y)

/-- The DG tensor functor, with its sectionwise pure tensors and ordinary
tensor--Hom adjunction. The pure tensors are the local generators of the
sheafification of the balanced sectionwise tensor product. -/
public structure TensorWithComplexData (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) where
  /-- The DG functor `M ↦ M ⊗ K` from DG modules over the endomorphism DGA to `CompDG X R`. -/
  functor : DGCategory.DGFunctor
    (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra)
      (CompDG.{u, v, w, t, s, o} X R)
  /-- The sectionwise tensor complex before sheafification. -/
  sectionwise (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) :
    CochainComplex
      (PresheafOfModules.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ
  /-- Homogeneous pure tensors in the sectionwise presheaf complex. -/
  sectionwisePure (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
    K).algebra).Obj)
      (p q : ℤ) (U : X.Cᵒᵖ) :
    M.grading p →ₗ[ℤ] (((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) →ₗ[ℤ]
      (((sectionwise M).X (p + q)).obj U)
  /-- Balancing already holds before sheafification. -/
  sectionwisePure_balance (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
      K).algebra).Obj)
      (p q n : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
      (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq
      (sectionwisePure M (p + n) q U
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
          M.smul_mem p n x a x.property a.property⟩ y)
      (sectionwisePure M p (q + n) U x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y))
  /-- The pure-tensor map is linear over the structure-sheaf ring in its second factor. -/
  sectionwisePure_smul (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
      K).algebra).Obj)
      (p q : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    sectionwisePure M p q U x (r • y) =
      r • sectionwisePure M p q U x y
  /-- Pure tensors commute with restriction to smaller objects of the site. -/
  sectionwisePure_natural (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
      K).algebra).Obj)
      (p q : ℤ) {U V : X.Cᵒᵖ} (f : U ⟶ V)
      (x : M.grading p) (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    ((sectionwise M).X (p + q)).map f (sectionwisePure M p q U x y) =
      sectionwisePure M p q V x (((liftComplex.{u, v, w, t, s} X K).X q).val.map f y)
  /-- In each degree and on each object of the site, pure tensors have the
  universal property of the balanced tensor product. -/
  sectionwiseTensorUniversal
      (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
      (U : X.Cᵒᵖ) (d : ℤ)
      (P : ModuleCat.{max u v w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
      (b : BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d P) :
    ∃! f : ((sectionwise M).X d).obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P,
      ∀ (p q : ℤ) (h : p + q = d) (x : M.grading p)
        (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
        f (cast
          (congrArg (fun k : ℤ => (((sectionwise M).X k).obj U : Type _)) h)
          (sectionwisePure M p q U x y)) = b.toFun p q h x y
  /-- The differential on sectionwise pure tensors is the signed Leibniz differential. -/
  sectionwisePure_d (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
    K).algebra).Obj)
      (p q : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    (((sectionwise M).d (p + q) ((p + q) + 1)).app U)
        (sectionwisePure M p q U x y) =
      cast (congrArg (fun k : ℤ => (((sectionwise M).X k).obj U : Type _))
          (by omega : (p + 1) + q = (p + q) + 1))
        (sectionwisePure M (p + 1) q U
          ⟨M.d x, M.d_mem p x x.property⟩ y) +
      (p.negOnePow : ℤ) •
        cast (congrArg (fun k : ℤ => (((sectionwise M).X k).obj U : Type _))
            (by omega : p + (q + 1) = (p + q) + 1))
          (sectionwisePure M p (q + 1) U x
            ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y))
  /-- The canonical map from the sectionwise tensor complex to the underlying
  presheaf of its sheafification. -/
  sectionwiseToSheaf (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
    K).algebra).Obj)
      :
    sectionwise M ⟶
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (functor.obj M)
  /-- The resulting sheaf complex has the universal property of sheafification. -/
  sectionwiseUniversal (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
      K).algebra).Obj)
      (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
      (f : sectionwise M ⟶
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :
    ∃! g : HomologicalComplex.Hom (functor.obj M) P,
      sectionwiseToSheaf M ≫
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g = f
  /-- The images of homogeneous pure tensors over each object of the site. -/
  pure (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
      (p q : ℤ) (U : X.Cᵒᵖ) :
    M.grading p →ₗ[ℤ] (((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) →ₗ[ℤ]
      (((functor.obj M).X (p + q)).val.obj U)
  /-- The sheaf pure tensor is the image of the sectionwise pure tensor. -/
  pure_eq_sectionwise (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R
    K).algebra).Obj)
      (p q : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    pure M p q U x y =
      ((sectionwiseToSheaf M).f (p + q)).app U (sectionwisePure M p q U x y)
  /-- Pure tensors satisfy the sectionwise balancing relation over the endomorphism DGA. -/
  pure_balance (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
      (p q n : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
      (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq
      (pure M (p + n) q U
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
          M.smul_mem p n x a x.property a.property⟩ y)
      (pure M p (q + n) U x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y))
  /-- Homogeneous morphisms act on the first factor of a pure tensor. -/
  map_pure {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj} {n
    : ℤ}
      (f : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Hom L M n)
      (p q : ℤ) (U : X.Cᵒᵖ) (x : L.grading p)
      (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq
      (((((functor.map f).v (p + q) ((p + q) + n) (by omega)).val.app U)
        (pure L p q U x y)))
      (pure M (p + n) q U
        ⟨f.1 x, f.2.1 p x x.property⟩ y)
  /-- The tensor--Hom adjunction: `functor` is left adjoint to `Hom(K, -)` on complexes. -/
  adjunction : functor.onComp ⊣ (Rep.{u, v, w, t, s, o} X R K).functor.onComp

section

private def adjunctionOnComplexes {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (a : F ⊣ G) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      G.mapHomologicalComplex (ComplexShape.up ℤ) :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun P =>
            { f := fun i => a.unit.app (P.X i)
              comm' := fun i j _ => (a.unit.naturality (P.d i j)).symm }
          naturality := by
            intro P Q f
            ext i
            exact a.unit.naturality (f.f i) }
      counit :=
        { app := fun P =>
            { f := fun i => a.counit.app (P.X i)
              comm' := fun i j _ => (a.counit.naturality (P.d i j)).symm }
          naturality := by
            intro P Q f
            ext i
            exact a.counit.naturality (f.f i) }
      left_triangle := by
        ext P i
        dsimp
        simpa only [Category.id_comp] using a.left_triangle_components (P.X i)
      right_triangle := by
        ext P i
        dsimp
        simpa only [Category.id_comp] using a.right_triangle_components (P.X i) }

private noncomputable abbrev complexSheafification :
    CochainComplex
      (PresheafOfModules.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ ⥤
      CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ :=
  (PresheafOfModules.sheafification.{max u v w t s}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)

private noncomputable def complexSheafificationAdjunction :
    complexSheafification.{u, v, w, t, s} X ⊣
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  adjunctionOnComplexes (PresheafOfModules.sheafificationAdjunction.{max u v w t s} (𝟙
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))

private lemma complexSheafification_universal
    (P : CochainComplex
      (PresheafOfModules.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ)
    (Q : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (f : P ⟶ ((SheafOfModules.forget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q) :
    ∃! g : (complexSheafification.{u, v, w, t, s} X).obj P ⟶ Q,
      (complexSheafificationAdjunction.{u, v, w, t, s} X).unit.app P ≫
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g = f := by
  let a := complexSheafificationAdjunction.{u, v, w, t, s} X
  refine ⟨(a.homEquiv P Q).symm f, ?_, ?_⟩
  · change a.unit.app P ≫
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((a.homEquiv P Q).symm f) = f
    exact (a.homEquiv_unit P Q ((a.homEquiv P Q).symm f)).symm.trans
      ((a.homEquiv P Q).apply_symm_apply f)
  · intro g hg
    apply (a.homEquiv P Q).injective
    rw [a.homEquiv_unit, hg]
    exact ((a.homEquiv P Q).apply_symm_apply f).symm

private abbrev TensorDegreeIndex (d : ℤ) := {pq : ℤ × ℤ // pq.1 + pq.2 = d}

private abbrev UnbalancedTensorDegree {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ) (d : ℤ) :=
  DirectSum (TensorDegreeIndex d) (fun pq => TensorProduct ℤ (L pq.1.2) (M pq.1.1))

private noncomputable def unbalancedPure {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ)
    (d p q : ℤ) (h : p + q = d) :
    M p →ₗ[ℤ] L q →ₗ[ℤ] UnbalancedTensorDegree L M d := by
  classical
  exact (TensorProduct.mk ℤ (L q) (M p)).flip.compr₂
    (DirectSum.lof ℤ (TensorDegreeIndex d) (fun pq : TensorDegreeIndex d => TensorProduct ℤ (L
        pq.1.2) (M pq.1.1)) ⟨(p, q), h⟩)

private lemma unbalancedPure_smul {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ)
    (d p q : ℤ) (h : p + q = d) (x : M p) (a : S) (y : L q) :
    unbalancedPure L M d p q h x (a • y) =
      a • unbalancedPure L M d p q h x y := by
  classical
  change DirectSum.lof ℤ (TensorDegreeIndex d) (fun pq : TensorDegreeIndex d => TensorProduct ℤ (L
      pq.1.2) (M pq.1.1)) ⟨(p, q), h⟩
      ((a • y) ⊗ₜ[ℤ] x) = _
  rw [← TensorProduct.smul_tmul']
  exact (DirectSum.lof S (TensorDegreeIndex d) (fun pq : TensorDegreeIndex d => TensorProduct ℤ (L
      pq.1.2) (M pq.1.1)) ⟨(p, q), h⟩).map_smul a _

private noncomputable def unbalancedLiftInt {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ)
    (d : ℤ) {P : Type*} [AddCommGroup P]
    (b : ∀ p q : ℤ, p + q = d → M p →ₗ[ℤ] L q →ₗ[ℤ] P) :
    UnbalancedTensorDegree L M d →ₗ[ℤ] P := by
  classical
  exact DirectSum.toModule ℤ (TensorDegreeIndex d) P
    (fun pq => TensorProduct.lift (b pq.1.1 pq.1.2 pq.2).flip)

private lemma unbalancedLiftInt_pure {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ)
    (d : ℤ) {P : Type*} [AddCommGroup P]
    (b : ∀ p q : ℤ, p + q = d → M p →ₗ[ℤ] L q →ₗ[ℤ] P)
    (p q : ℤ) (h : p + q = d) (x : M p) (y : L q) :
    unbalancedLiftInt L M d b (unbalancedPure L M d p q h x y) = b p q h x y := by
  classical
  change DirectSum.toModule ℤ (TensorDegreeIndex d) P
      (fun pq => TensorProduct.lift (b pq.1.1 pq.1.2 pq.2).flip)
      (DirectSum.lof ℤ (TensorDegreeIndex d)
        (fun pq => TensorProduct ℤ (L pq.1.2) (M pq.1.1)) ⟨(p, q), h⟩ (y ⊗ₜ[ℤ] x)) = _
  exact (DirectSum.toModule_lof (R := ℤ) (φ := fun pq : TensorDegreeIndex d =>
    TensorProduct.lift (b pq.1.1 pq.1.2 pq.2).flip) ⟨(p, q), h⟩ (y ⊗ₜ[ℤ] x)).trans rfl

private lemma unbalancedTensorDegree_induction {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ) (d : ℤ)
    {motive : UnbalancedTensorDegree L M d → Prop} (z : UnbalancedTensorDegree L M d)
    (zero : motive 0) (add : ∀ z z', motive z → motive z' → motive (z + z'))
    (pure : ∀ p q h x y, motive (unbalancedPure L M d p q h x y)) : motive z := by
  classical
  induction z using DirectSum.induction_on with
  | zero => exact zero
  | add z z' hz hz' => exact add z z' hz hz'
  | of pq z =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [map_add]; exact add _ _ hz hz'
    | tmul y x => exact pure pq.1.1 pq.1.2 pq.2 x y

private noncomputable def unbalancedLift {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ)
    (d : ℤ) {P : Type*} [AddCommGroup P] [Module S P]
    (b : ∀ p q : ℤ, p + q = d → M p →ₗ[ℤ] L q →ₗ[ℤ] P)
    (hb : ∀ p q h x (a : S) y, b p q h x (a • y) = a • b p q h x y) :
    UnbalancedTensorDegree L M d →ₗ[S] P where
  __ := (unbalancedLiftInt L M d b).toAddHom
  map_smul' a z := by
    change unbalancedLiftInt L M d b (a • z) = a • unbalancedLiftInt L M d b z
    induction z using unbalancedTensorDegree_induction with
    | zero => simp
    | add z z' hz hz' => simp_all only [smul_add, map_add]
    | pure p q h x y =>
      rw [← unbalancedPure_smul, unbalancedLiftInt_pure, unbalancedLiftInt_pure]
      exact hb _ _ _ _ _ _

private lemma unbalancedTensorDegree_hom_ext {S : Type*} [Ring S]
    (L : ℤ → ModuleCat.{r} S) (M : ℤ → ModuleCat.{s} ℤ)
    (d : ℤ) {P : Type*} [AddCommGroup P] [Module S P]
    {f g : UnbalancedTensorDegree L M d →ₗ[S] P}
    (h : ∀ p q h x y, f (unbalancedPure L M d p q h x y) =
      g (unbalancedPure L M d p q h x y)) : f = g := by
  refine LinearMap.ext fun z => ?_
  induction z using unbalancedTensorDegree_induction with
  | zero => simp
  | add z z' hz hz' => simp_all only [map_add]
  | pure p q hpq x y => exact h p q hpq x y

private noncomputable abbrev tensorSections (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (U : X.Cᵒᵖ) (q : ℤ) :=
  ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U

private def tensorModuleDegrees {S : Type o} [CommRing S]
    {A : DifferentialGradedAlgebra.{o, r} S} (M : DifferentialGradedModule.{o, r, s} A)
    (p : ℤ) := ModuleCat.of ℤ (M.grading p)

private noncomputable def tensorDegreeRelations (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) :
    Submodule ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
      (UnbalancedTensorDegree (tensorSections.{u, v, w, t, s} X K U)
        (tensorModuleDegrees M) d) :=
  Submodule.span _ {z | ∃ (p q n : ℤ) (h₁ : (p + n) + q = d)
      (h₂ : p + (q + n) = d) (x : M.grading p)
      (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n)
      (y : tensorSections.{u, v, w, t, s} X K U q),
    z = unbalancedPure (tensorSections.{u, v, w, t, s} X K U) (tensorModuleDegrees M)
        d (p + n) q h₁
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
          M.smul_mem p n x a x.property a.property⟩ y -
      unbalancedPure (tensorSections.{u, v, w, t, s} X K U) (tensorModuleDegrees M)
        d p (q + n) h₂ x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y)}

private abbrev TensorDegree (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) :=
  UnbalancedTensorDegree (tensorSections.{u, v, w, t, s} X K U) (tensorModuleDegrees M) d ⧸
    tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d

private noncomputable def tensorDegreePure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p q : ℤ) (h : p + q = d) :
    M.grading p →ₗ[ℤ] tensorSections.{u, v, w, t, s} X K U q →ₗ[ℤ]
      TensorDegree.{u, v, w, t, s, o} X R K M U d :=
  (unbalancedPure (tensorSections.{u, v, w, t, s} X K U) (tensorModuleDegrees M) d p q h).compr₂
    ((tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ.restrictScalars ℤ)

private lemma tensorDegreePure_balance (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p q n : ℤ) (h₁ : (p + n) + q = d) (h₂ : p + (q + n) = d)
    (x : M.grading p) (a : (Rep.{u, v, w, t, s, o} X R K).algebra.grading n)
    (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreePure.{u, v, w, t, s, o} X R K M U d (p + n) q h₁
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
          M.smul_mem p n x a x.property a.property⟩ y =
      tensorDegreePure.{u, v, w, t, s, o} X R K M U d p (q + n) h₂ x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y) :=
          by
  apply (Submodule.Quotient.eq _).mpr
  exact Submodule.subset_span ⟨p, q, n, h₁, h₂, x, a, y, rfl⟩

private noncomputable def tensorDegreeBalanced
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d
      (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U d)) where
  toFun p q h := tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h
  map_smul p q h x a y := by
    change (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ
        (unbalancedPure _ _ _ _ _ h x (a • y)) = _
    exact congrArg (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ
      (unbalancedPure_smul (tensorSections.{u, v, w, t, s} X K U)
        (tensorModuleDegrees M) d p q h x a y) |>.trans
      ((tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ.map_smul a _)
  balance p q n h₁ h₂ x a y := tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U d p q n h₁ h₂ x
    a y

private noncomputable def tensorDegreeLift
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) (P : ModuleCat.{r} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    (b : BalancedDegreeMap.{u, v, w, t, s, o, r} X R K M U d P) :
    TensorDegree.{u, v, w, t, s, o} X R K M U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P :=
  by
  let b' : ∀ p q : ℤ, p + q = d → tensorModuleDegrees M p →ₗ[ℤ]
      tensorSections.{u, v, w, t, s} X K U q →ₗ[ℤ] P := b.toFun
  let f : UnbalancedTensorDegree (tensorSections.{u, v, w, t, s} X K U)
      (tensorModuleDegrees M) d →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P :=
    unbalancedLift (S := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
      (tensorSections.{u, v, w, t, s} X K U) (tensorModuleDegrees M) d b' b.map_smul
  refine (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).liftQ f ?_
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, n, h₁, h₂, x, a, y, rfl⟩
  change f _ = 0
  rw [map_sub]
  exact (congrArg₂ (fun z z' : P => z - z')
    (unbalancedLiftInt_pure _ _ _ b' (p + n) q h₁
      ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
        M.smul_mem p n x a x.property a.property⟩ y)
    (unbalancedLiftInt_pure _ _ _ b' p (q + n) h₂ x
      (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U)
        y))).trans
    (sub_eq_zero.mpr (b.balance p q n h₁ h₂ x a y))

private lemma tensorDegreeLift_pure
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) (P : ModuleCat.{r} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    (b : BalancedDegreeMap.{u, v, w, t, s, o, r} X R K M U d P)
    (p q : ℤ) (h : p + q = d) (x : M.grading p)
    (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreeLift.{u, v, w, t, s, o} X R K M U d P b (tensorDegreePure.{u, v, w, t, s, o} X R K M
      U d p q
        h x y) =
      b.toFun p q h x y := by
  exact unbalancedLiftInt_pure (tensorSections.{u, v, w, t, s} X K U)
    (tensorModuleDegrees M) d b.toFun p q h x y

private lemma tensorDegree_hom_ext
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) (P : ModuleCat.{r} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    {f g : TensorDegree.{u, v, w, t, s, o} X R K M U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P}
    (h : ∀ p q h x y, f (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
      g (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y)) : f = g := by
  have hh : f.comp (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ =
      g.comp (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ := by
    apply unbalancedTensorDegree_hom_ext
    exact h
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (tensorDegreeRelations.{u, v, w, t, s, o} X R K M U d).mkQ_surjective z
  exact LinearMap.congr_fun hh z

private lemma tensorDegreeUniversal
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) (P : ModuleCat.{r} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    (b : BalancedDegreeMap.{u, v, w, t, s, o, r} X R K M U d P) :
    ∃! f : TensorDegree.{u, v, w, t, s, o} X R K M U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P,
      ∀ p q h x y, f (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
        b.toFun p q h x y := by
  refine ⟨tensorDegreeLift.{u, v, w, t, s, o} X R K M U d P b, ?_, ?_⟩
  · exact tensorDegreeLift_pure.{u, v, w, t, s, o} X R K M U d P b
  · intro f hf
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d P
    intro p q h x y
    exact (hf p q h x y).trans
      (tensorDegreeLift_pure.{u, v, w, t, s, o} X R K M U d P b p q h x y).symm

private noncomputable def tensorRestrictionBalanced
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    {U V : X.Cᵒᵖ} (f : U ⟶ V) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d
      ((ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
        (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M V d))) where
  toFun p q h :=
    (tensorDegreePure.{u, v, w, t, s, o} X R K M V d p q h).compl₂
      (((((liftComplex.{u, v, w, t, s} X K).X q).val.map f)).hom.restrictScalars ℤ)
  map_smul p q h x a y := by
    change tensorDegreePure.{u, v, w, t, s, o} X R K M V d p q h x
        ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) (a • y)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom a •
        tensorDegreePure.{u, v, w, t, s, o} X R K M V d p q h x
          ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y)
    rw [PresheafOfModules.map_smul]
    exact (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M V d).map_smul _ _ _ _ _ _
  balance p q n h₁ h₂ x a y := by
    have hn := (((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by
      omega)).val.naturality f
    have he := congrArg (fun g => g y) hn
    change
      (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app V)
        ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y)) =
      (((liftComplex.{u, v, w, t, s} X K).X (q + n)).val.map f)
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U) y)
      at he
    change tensorDegreePure.{u, v, w, t, s, o} X R K M V d (p + n) q h₁
        ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : M.M),
          M.smul_mem p n x a x.property a.property⟩
        ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y) =
      tensorDegreePure.{u, v, w, t, s, o} X R K M V d p (q + n) h₂ x _
    exact (tensorDegreePure_balance.{u, v, w, t, s, o} X R K M V d p q n h₁ h₂ x a
      ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y)).trans
      (congrArg (tensorDegreePure.{u, v, w, t, s, o} X R K M V d p (q + n) h₂ x) he)

private noncomputable def tensorDegreeRestriction
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    {U V : X.Cᵒᵖ} (f : U ⟶ V) (d : ℤ) :
    TensorDegree.{u, v, w, t, s, o} X R K M U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      ((ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom).obj
        (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M V d))) :=
  tensorDegreeLift.{u, v, w, t, s, o} X R K M U d _
    (tensorRestrictionBalanced.{u, v, w, t, s, o} X R K M f d)

private lemma tensorDegreeRestriction_pure
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    {U V : X.Cᵒᵖ} (f : U ⟶ V) (d p q : ℤ) (h : p + q = d)
    (x : M.grading p) (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreeRestriction.{u, v, w, t, s, o} X R K M f d
      (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
    tensorDegreePure.{u, v, w, t, s, o} X R K M V d p q h x
      ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y) :=
  tensorDegreeLift_pure.{u, v, w, t, s, o} X R K M U d _
    (tensorRestrictionBalanced.{u, v, w, t, s, o} X R K M f d) p q h x y

private noncomputable def tensorDegreePresheaf
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (d : ℤ) : PresheafOfModules.{max u v w t s}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj where
  obj U := ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U d)
  map {U V} f := ConcreteCategory.ofHom
    (C := ModuleCat.{max u v w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    (tensorDegreeRestriction.{u, v, w, t, s, o} X R K M f d)
  map_id U := by
    apply ModuleCat.hom_ext
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d _
    intro p q h x y
    change tensorDegreeRestriction.{u, v, w, t, s, o} X R K M (𝟙 U) d
        (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
      tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y
    rw [tensorDegreeRestriction_pure]
    have hy : (((liftComplex.{u, v, w, t, s} X K).X q).val.map (𝟙 U)) y = y := by
      rw [PresheafOfModules.map_id]
      rfl
    exact congrArg (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x) hy
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d _
    intro p q h x y
    change tensorDegreeRestriction.{u, v, w, t, s, o} X R K M (f ≫ g) d
        (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y) =
      tensorDegreeRestriction.{u, v, w, t, s, o} X R K M g d
        (tensorDegreeRestriction.{u, v, w, t, s, o} X R K M f d
          (tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y))
    have h₀ := tensorDegreeRestriction_pure.{u, v, w, t, s, o} X R K M (f ≫ g) d p q h x y
    have h₁ := tensorDegreeRestriction_pure.{u, v, w, t, s, o} X R K M f d p q h x y
    have h₂ := tensorDegreeRestriction_pure.{u, v, w, t, s, o} X R K M g d p q h x
      ((((liftComplex.{u, v, w, t, s} X K).X q).val.map f) y)
    exact (h₀.trans (congrArg (tensorDegreePure.{u, v, w, t, s, o} X R K M W d p q h x)
      (PresheafOfModules.map_comp_apply _ f g y))).trans
      ((congrArg (tensorDegreeRestriction.{u, v, w, t, s, o} X R K M g d) h₁).trans h₂).symm


private lemma tensorDegreePure_congr
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d p p' q : ℤ) (hp : p = p')
    (h : p + q = d) (h' : p' + q = d)
    (x : M.grading p) (x' : M.grading p') (hx : (x : M.M) = x')
    (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreePure.{u, v, w, t, s, o} X R K M U d p q h x y =
      tensorDegreePure.{u, v, w, t, s, o} X R K M U d p' q h' x' y := by
  subst p'
  cases Subtype.ext hx
  rfl

private def homogeneousGradedMap {S : Type o} [CommRing S]
    {A : DifferentialGradedAlgebra.{o, r} S}
    {L M : DifferentialGradedModule.{o, r, s} A} {n : ℤ}
    (f : HomogeneousMap A L M n) (p : ℤ) :
    L.grading p →ₗ[ℤ] M.grading (p + n) where
  toFun x := ⟨f.1 x, f.2.1 p x x.property⟩
  map_add' x y := Subtype.ext (f.1.toAddMonoidHom.map_add x y)
  map_smul' a x := Subtype.ext (f.1.toAddMonoidHom.map_zsmul a x)

private noncomputable def tensorMapBalanced
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ)
    (d e : ℤ) (hde : d + n = e) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K L U d
      (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U e)) where
  toFun p q h :=
    (tensorDegreePure.{u, v, w, t, s, o} X R K M U e (p + n) q (by omega)).comp
      (homogeneousGradedMap f p)
  map_smul p q h x a y :=
    (tensorDegreeBalanced.{u, v, w, t, s, o} X R K M U e).map_smul _ _ _ _ _ _
  balance p q a h₁ h₂ x z y := by
    change tensorDegreePure.{u, v, w, t, s, o} X R K M U e ((p + a) + n) q _
        (homogeneousGradedMap f (p + a)
          ⟨MulOpposite.op (z : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : L.M),
            L.smul_mem p a x z x.property z.property⟩) y = _
    refine (tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U e
      ((p + a) + n) ((p + n) + a) q (by omega) (by omega) (by omega) _
      ⟨MulOpposite.op (z : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • f.1 x,
        M.smul_mem (p + n) a (f.1 x) z (f.2.1 p x x.property) z.property⟩
      (f.2.2 z x) y).trans ?_
    exact tensorDegreePure_balance.{u, v, w, t, s, o} X R K M U e
      (p + n) q a _ _ (homogeneousGradedMap f p x) z y

private noncomputable def tensorDegreeMap
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ)
    (d e : ℤ) (hde : d + n = e) :
    TensorDegree.{u, v, w, t, s, o} X R K L U d
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      TensorDegree.{u, v, w, t, s, o} X R K M U e :=
  tensorDegreeLift.{u, v, w, t, s, o} X R K L U d _
    (tensorMapBalanced.{u, v, w, t, s, o} X R K f U d e hde)

private lemma tensorDegreeMap_pure
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ)
    (d e : ℤ) (hde : d + n = e) (p q : ℤ) (h : p + q = d)
    (x : L.grading p) (y : tensorSections.{u, v, w, t, s} X K U q) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde
      (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y) =
    tensorDegreePure.{u, v, w, t, s, o} X R K M U e (p + n) q (by omega)
      (homogeneousGradedMap f p x) y :=
  tensorDegreeLift_pure.{u, v, w, t, s, o} X R K L U d _
    (tensorMapBalanced.{u, v, w, t, s, o} X R K f U d e hde) p q h x y

private noncomputable def tensorPresheafMap
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n)
    (d e : ℤ) (hde : d + n = e) :
    tensorDegreePresheaf.{u, v, w, t, s, o} X R K L d ⟶
      tensorDegreePresheaf.{u, v, w, t, s, o} X R K M e where
  app U := ModuleCat.ofHom (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde)
  naturality {U V} g := by
    apply ModuleCat.hom_ext
    apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K L U d _
    intro p q h x y
    change tensorDegreeMap.{u, v, w, t, s, o} X R K f V d e hde
        (tensorDegreeRestriction.{u, v, w, t, s, o} X R K L g d
          (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y)) =
      tensorDegreeRestriction.{u, v, w, t, s, o} X R K M g e
        (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde
          (tensorDegreePure.{u, v, w, t, s, o} X R K L U d p q h x y))
    rw [tensorDegreeRestriction_pure, tensorDegreeMap_pure,
      tensorDegreeMap_pure, tensorDegreeRestriction_pure]

private lemma tensorDegreeMap_add
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f g : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ)
    (d e : ℤ) (hde : d + n = e) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K (f + g) U d e hde =
      tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde +
        tensorDegreeMap.{u, v, w, t, s, o} X R K g U d e hde := by
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K L U d
    (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U e))
  intro p q h x y
  simp only [LinearMap.add_apply, tensorDegreeMap_pure.{u, v, w, t, s, o} X R K]
  have hx : homogeneousGradedMap (f + g) p x =
      homogeneousGradedMap f p x + homogeneousGradedMap g p x := by
    apply Subtype.ext
    rfl
  rw [hx, map_add, LinearMap.add_apply]

private lemma tensorDegreeMap_zsmul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (a : ℤ) (f : (dgCategory _).Hom L M n) (U : X.Cᵒᵖ)
    (d e : ℤ) (hde : d + n = e) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K (a • f) U d e hde =
      a • tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde := by
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K L U d
    (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U e))
  intro p q h x y
  simp only [LinearMap.smul_apply, tensorDegreeMap_pure.{u, v, w, t, s, o} X R K]
  have hx : homogeneousGradedMap (a • f) p x =
      a • homogeneousGradedMap f p x := by
    apply Subtype.ext
    rfl
  rw [hx, map_smul, LinearMap.smul_apply]

private lemma tensorPresheafMap_add
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f g : (dgCategory _).Hom L M n)
    (d e : ℤ) (hde : d + n = e) :
    tensorPresheafMap.{u, v, w, t, s, o} X R K (f + g) d e hde =
      tensorPresheafMap.{u, v, w, t, s, o} X R K f d e hde +
        tensorPresheafMap.{u, v, w, t, s, o} X R K g d e hde := by
  ext U x
  change (tensorDegreeMap.{u, v, w, t, s, o} X R K (f + g) U d e hde) x =
    ((tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde) +
      (tensorDegreeMap.{u, v, w, t, s, o} X R K g U d e hde)) x
  rw [tensorDegreeMap_add]

private lemma tensorPresheafMap_zsmul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (a : ℤ) (f : (dgCategory _).Hom L M n)
    (d e : ℤ) (hde : d + n = e) :
    tensorPresheafMap.{u, v, w, t, s, o} X R K (a • f) d e hde =
      a • tensorPresheafMap.{u, v, w, t, s, o} X R K f d e hde := by
  ext U x
  simp only [PresheafOfModules.zsmul_app, ModuleCat.hom_zsmul,
    LinearMap.smul_apply]
  change (tensorDegreeMap.{u, v, w, t, s, o} X R K (a • f) U d e hde) x =
    (a • tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde) x
  rw [tensorDegreeMap_zsmul]

private lemma tensorDegreeMap_id
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ) (h : d + 0 = d) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K
      ((dgCategory _).id M) U d d h = LinearMap.id := by
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K M U d
    (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K M U d))
  intro p q hpq x y
  rw [tensorDegreeMap_pure]
  have hx : homogeneousGradedMap ((dgCategory _).id M) p x =
      ⟨(x : M.M), by rw [add_zero]; exact x.property⟩ := by
    apply Subtype.ext
    change (((dgCategory _).id M).1 (x : M.M)) = x
    rw [dgCategory_id_val]
    rfl
  rw [hx]
  simpa only [LinearMap.id_apply] using
    (tensorDegreePure_congr.{u, v, w, t, s, o} X R K M U d (p + 0) p q
      (add_zero p) (by omega) hpq _ x (by rfl) y)

private lemma tensorDegreeMap_comp
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M N : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {m n k : ℤ} (hmn : m + n = k)
    (g : (dgCategory _).Hom M N m) (f : (dgCategory _).Hom L M n)
    (U : X.Cᵒᵖ) (d e j : ℤ) (hde : d + n = e) (hej : e + m = j) :
    tensorDegreeMap.{u, v, w, t, s, o} X R K ((dgCategory _).comp hmn g f) U d j (by omega) =
      (tensorDegreeMap.{u, v, w, t, s, o} X R K g U e j hej).comp
        (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e hde) := by
  apply tensorDegree_hom_ext.{u, v, w, t, s, o} X R K L U d
    (ModuleCat.of _ (TensorDegree.{u, v, w, t, s, o} X R K N U j))
  intro p q hpq x y
  simp only [LinearMap.comp_apply, tensorDegreeMap_pure.{u, v, w, t, s, o} X R K]
  apply tensorDegreePure_congr.{u, v, w, t, s, o} X R K N U j
    (p + k) ((p + n) + m) q (by omega) (by omega) (by omega)
  change (((dgCategory _).comp hmn g f).1 : L.M →ₗ[ℤ] N.M) x =
    (g.1 : M.M →ₗ[ℤ] N.M) (f.1 x)
  rw [dgCategory_comp_val]
  rfl

private lemma sheafModule_zsmul_val {F G : TensorModO.{u, v, w, t, s} X} (n : ℤ) (f : F ⟶ G) :
    (n • f).val = n • f.val := by
  change (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map (n • f) =
    n • (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map f
  rw [Functor.map_zsmul]

private lemma sheafModule_zero_val {F G : TensorModO.{u, v, w, t, s} X} :
    (0 : F ⟶ G).val = 0 := by
  change (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map (0 : F ⟶ G) = 0
  rw [Functor.map_zero]

/-- At `R = ℤ` the scalars are the integer sections: the `ℤ`-linear structure of a preadditive
category is the action of the additive group, and on sections that is multiplication by the image
of the integer in `O(U)`. -/
public noncomputable instance scalarSectionsInt : ScalarSections.{u, v, w, t, s, 0} X ℤ where
  scalarSection n U := (n : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
  smul_app := by
    intro n P Q f U y
    rw [sheafModule_zsmul_val]
    simp only [PresheafOfModules.zsmul_app, ModuleCat.hom_zsmul, LinearMap.smul_apply]
    exact (Int.cast_smul_eq_zsmul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) n
      ((f.val.app U) y)).symm

end

end AlgebraicGeometry.RingedSite
