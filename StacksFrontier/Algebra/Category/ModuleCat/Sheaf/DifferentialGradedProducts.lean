module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Products of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. The category of right differential graded `A`-modules has arbitrary products.

They are formed degreewise: in each degree the product of sheaves of modules is the sectionwise
product, which is already a sheaf, and both the differential and the action of `A` are
pointwise.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasProducts`: right differential graded modules over
  a sheaf of differential graded algebras admit arbitrary products.

## Implementation notes

The product is built by hand from the sectionwise product of sheaves of modules, rather than
obtained from general limits of right differential graded modules. The sheaf condition on the
degreewise product comes from `PresheafOfModules.isSheaf_of_isLimit` applied to the sectionwise
product fan.

The associativity and unit laws of the product action relate sections in propositionally — but
not definitionally — equal degrees, so they are stated with `HEq` on the component level and
assembled by the private `pi_heq`, which turns a pointwise family of `HEq`s between dependent
functions into a single one. Likewise `gradedCast_apply` evaluates a transport of a dependent
function at an index.

The index universe and the universe of the module sections are kept independent, with the
module sections living in their join; the product indexed by `I : Type w` of modules with
sections in `Type w` is the instance that `CategoryTheory.Limits.HasProducts.{w}` asks for.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m w v u

namespace SheafOfModules

namespace DifferentialGradedModule

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {I : Type w}

/-- The sectionwise product of a family of sheaves of modules, as a presheaf of modules. -/
private def productPresheaf (G : I → SheafOfModules.{max w m} R) :
    PresheafOfModules.{max w m} R.obj where
  obj U := ModuleCat.of _ (∀ i, (G i).val.obj U)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of _ (∀ i, (G i).val.obj V)))
    { toFun := fun x i => (G i).val.map f (x i)
      map_add' := by intros; funext i; exact map_add _ _ _
      map_smul' r x := funext fun i => (G i).val.map_smul f r (x i) }
  map_id U := by
    ext x
    funext i
    exact congrArg (fun f => f (x i)) ((G i).val.map_id U)
  map_comp f g := by
    ext x
    funext i
    exact (G i).val.map_comp_apply f g (x i)

/-- The projection of the sectionwise product of presheaves of modules. -/
private def productPresheafπ (G : I → SheafOfModules.{max w m} R) (i : I) :
    productPresheaf G ⟶ (G i).val where
  app _ := ModuleCat.ofHom (LinearMap.proj i)
  naturality _ := rfl

/-- The morphism into the sectionwise product of presheaves of modules determined by a family
of morphisms. -/
private def productPresheafLift (G : I → SheafOfModules.{max w m} R)
    {P : PresheafOfModules.{max w m} R.obj} (f : ∀ i, P ⟶ (G i).val) :
    P ⟶ productPresheaf G where
  app U := ModuleCat.ofHom (LinearMap.pi (fun i => (f i).app U |>.hom))
  naturality g := by
    ext x
    funext i
    exact PresheafOfModules.naturality_apply (f i) g x

/-- The sectionwise product of presheaves of modules is their product. -/
private def productPresheafIsLimit (G : I → SheafOfModules.{max w m} R) :
    IsLimit (Fan.mk (productPresheaf G) (productPresheafπ G)) :=
  Fan.IsLimit.mk _ (fun s => productPresheafLift G s.proj)
    (by intros; ext; rfl) (by
      intro s m hm
      ext U x
      funext i
      exact congrArg (fun f => f.app U x) (hm i))

/-- The sectionwise product of a family of sheaves of modules is a sheaf. -/
private noncomputable def productSheaf (G : I → SheafOfModules.{max w m} R) :
    SheafOfModules.{max w m} R where
  val := productPresheaf G
  isSheaf := PresheafOfModules.isSheaf_of_isLimit (productPresheafIsLimit G)
    (fun i => (G i.as).isSheaf)

/-- The projection of the sectionwise product of sheaves of modules. -/
private def productSheafπ (G : I → SheafOfModules.{max w m} R) (i : I) :
    productSheaf G ⟶ G i := ⟨productPresheafπ G i⟩

/-- A pointwise family of heterogeneous equalities between dependent functions over equal
degrees assembles into one. -/
private theorem pi_heq {P : I → ℤ → Type (max w m)} {n m' : ℤ} (h : n = m')
    {x : ∀ i, P i n} {y : ∀ i, P i m'} (hxy : ∀ i, HEq (x i) (y i)) : HEq x y := by
  subst m'
  exact heq_of_eq (funext (fun i => eq_of_heq (hxy i)))

/-- The morphism of sectionwise products induced by a family of morphisms. -/
private def productSheafMap
    {G H : I → SheafOfModules.{max w m} R} (f : ∀ i, G i ⟶ H i) :
    productSheaf G ⟶ productSheaf H :=
  ⟨productPresheafLift H (fun i => productPresheafπ G i ≫ (f i).val)⟩

/-- The degreewise product of the underlying complexes of a family of right differential graded
modules. -/
private def productComplex (F : I → DifferentialGradedModule.{t, a, max w m} A) :
    CochainComplex (SheafOfModules.{max w m} R) ℤ where
  X n := productSheaf (fun i => (F i).complex.X n)
  d n m' := productSheafMap (fun i => (F i).complex.d n m')
  shape n m' h := by
    apply SheafOfModules.hom_ext
    ext U x
    funext i
    exact congrArg (fun f => f.val.app U (x i)) ((F i).complex.shape n m' h)
  d_comp_d' n m' k _ _ := by
    apply SheafOfModules.hom_ext
    ext U x
    funext i
    exact congrArg (fun f => f.val.app U (x i)) ((F i).complex.d_comp_d n m' k)

/-- Transporting a dependent function along an equality of degrees acts componentwise. -/
private theorem gradedCast_apply {P : I → ℤ → Type (max w m)} {n m' : ℤ}
    (h : n = m') (x : ∀ i, P i n) (i : I) :
    gradedCast (fun n => ∀ i, P i n) h x i = gradedCast (P i) h (x i) := by
  subst m'
  rfl

/-- The product of a family of right differential graded modules, formed degreewise with
pointwise differential and pointwise action. -/
private def productModule (F : I → DifferentialGradedModule.{t, a, max w m} A) :
    DifferentialGradedModule.{t, a, max w m} A where
  complex := productComplex F
  mul n m' :=
    { app U :=
        { toFun := fun x =>
            { toFun := fun b i => ((F i).mul n m').app U (x i) b
              map_zero' := by funext i; exact map_zero _
              map_add' := by intros; funext i; exact map_add _ _ _ }
          map_zero' := by
            ext b
            funext i
            exact congrArg (fun f : _ →+ _ => f b) (((F i).mul n m').app U |>.map_zero)
          map_add' := by
            intros
            ext b
            funext i
            exact congrArg (fun f : _ →+ _ => f b)
              (((F i).mul n m').app U |>.map_add _ _) }
      map_smul_left U r x b := by
        funext i
        exact ((F i).mul n m').map_smul_left U r (x i) b
      map_smul_right U r x b := by
        funext i
        exact ((F i).mul n m').map_smul_right U r (x i) b
      naturality f x b := by
        funext i
        exact ((F i).mul n m').naturality f (x i) b }
  mul_assoc n m' k U x b c :=
    pi_heq (P := fun i n => ((F i).complex.X n).val.obj U) (add_assoc n m' k)
      (fun i => (F i).mul_assoc n m' k U (x i) b c)
  mul_one n U x :=
    pi_heq (P := fun i n => ((F i).complex.X n).val.obj U) (add_zero n)
      (fun i => (F i).mul_one n U (x i))
  leibniz n m' U x b := by
    change (fun i => ((F i).complex.d (n + m') (n + m' + 1)).val.app U
        (((F i).mul n m').app U (x i) b)) =
      gradedCast (fun q => ∀ i, ((F i).complex.X q).val.obj U)
          (add_right_comm n 1 m')
          (fun i => ((F i).mul (n + 1) m').app U
            (((F i).complex.d n (n + 1)).val.app U (x i)) b) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q => ∀ i, ((F i).complex.X q).val.obj U)
            (add_assoc n m' 1).symm
            (fun i => ((F i).mul n (m' + 1)).app U (x i)
              ((A.complex.d m' (m' + 1)).val.app U b))
    funext i
    simp only [Pi.add_apply, Pi.smul_apply,
      gradedCast_apply (P := fun i q => ((F i).complex.X q).val.obj U)]
    exact (F i).leibniz n m' U (x i) b

/-- The projection of the product of right differential graded modules. -/
private def productModuleπ (F : I → DifferentialGradedModule.{t, a, max w m} A) (i : I) :
    productModule F ⟶ F i where
  toHomologicalComplex :=
    { f n := productSheafπ (fun i => (F i).complex.X n) i
      comm' _ _ _ := by ext; rfl }
  map_mul _ _ _ _ _ := rfl

/-- The product fan of a family of right differential graded modules. -/
private def productFan (F : I → DifferentialGradedModule.{t, a, max w m} A) : Fan F :=
  Fan.mk (productModule F) (productModuleπ F)

/-- The degreewise product of right differential graded modules is their product. -/
private def productFanIsLimit (F : I → DifferentialGradedModule.{t, a, max w m} A) :
    IsLimit (productFan F) :=
  Fan.IsLimit.mk _ (fun s =>
    { toHomologicalComplex :=
        { f n := ⟨productPresheafLift (fun i => (F i).complex.X n)
            (fun i => ((s.proj i).toHomologicalComplex.f n).val)⟩
          comm' n m' _ := by
            ext U x
            funext i
            exact congrArg (fun f => f.val.app U x)
              ((s.proj i).toHomologicalComplex.comm n m') }
      map_mul n m' U x b := by
        funext i
        exact (s.proj i).map_mul n m' U x b })
    (fun _ _ => DifferentialGradedModule.Hom.ext fun _ => by ext; rfl) (by
      intro s m' hm
      refine DifferentialGradedModule.Hom.ext fun n => ?_
      ext U x
      funext i
      exact congrArg (fun f => (f.toHomologicalComplex.f n).val.app U x) (hm i))

/-- **Right differential graded modules have arbitrary products**, formed degreewise. This is the
product clause of Stacks 0FRJ, whose full statement is
`SheafOfModules.differentialGradedModule_abelian_ab5_hasLimits_hasColimits_forget`. -/
instance hasProducts (A : DifferentialGradedAlgebra.{t, a} R) :
    HasProducts.{w} (DifferentialGradedModule.{t, a, w} A) :=
  hasProducts_of_limit_fans productFan productFanIsLimit

end

end DifferentialGradedModule

end SheafOfModules
