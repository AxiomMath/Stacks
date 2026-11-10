module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushPullLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionComparisonPlain

/-!
# Restriction of differential graded modules along a functor of chaotic sites

Let `F : C' ⥤ C` be a functor of categories, both viewed as sites with the chaotic topology, let
`O` be a sheaf of commutative rings on `C` and let `(A, d)` be a sheaf of differential graded
`O`-algebras. Restricting along `F` gives a sheaf of commutative rings `O' = O ∘ F` on `C'` and a
sheaf of differential graded `O'`-algebras `A' = A ∘ F`, the *restriction* of `A`, whose sections
over `U'` are those of `A` over `F U'`, through the isomorphism of differential graded algebras
`restrictSectionHom`, and its inverse.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.directImage`: the direct image of a sheaf of
  differential graded algebras along a morphism of ringed sites, and `directImageHom` the identity
  homomorphism into it.
* `SheafOfModules.restrictRingSheaf`: the restriction of a sheaf of commutative rings along `F`.
* `SheafOfModules.DifferentialGradedAlgebra.restrict`: the restriction `A'` of `A` along `F`.
* `SheafOfModules.DifferentialGradedAlgebra.restrictSectionHom`: the identification of the
  sections of `A'` over `U'` with those of `A` over `F U'`, as a homomorphism of differential
  graded algebras, and `restrictSectionInv` its inverse.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u v' u'

namespace SheafOfModules

/-! ### The direct image of a sheaf of differential graded algebras -/

namespace DifferentialGradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  (F : C' ⥤ C) [F.IsContinuous J' J] (σ : R'.obj ⟶ F.op ⋙ R.obj)

/-- **The direct image of a sheaf of differential graded algebras** along a morphism of ringed
sites: its sections over `V` are the sections of `A` over `F V`, with the same multiplication,
unit and differential. -/
def directImage (A : DifferentialGradedAlgebra.{t, m} R) : DifferentialGradedAlgebra.{t, m} R' where
  complex := ((sitePushforward F σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj A.complex
  mul i j :=
    { app V := (A.mul i j).app (F.op.obj V)
      map_smul_left V r x y := (A.mul i j).map_smul_left (F.op.obj V) (σ.app V r) x y
      map_smul_right V r x y := (A.mul i j).map_smul_right (F.op.obj V) (σ.app V r) x y
      naturality f x y := (A.mul i j).naturality (F.op.map f) x y }
  one := ⟨fun V => A.one.eval (F.op.obj V), fun f => A.one.property (F.op.map f)⟩
  mul_assoc i j k V := A.mul_assoc i j k (F.op.obj V)
  one_mul i V := A.one_mul i (F.op.obj V)
  mul_one i V := A.mul_one i (F.op.obj V)
  leibniz i j V := A.leibniz i j (F.op.obj V)

/-- The identity homomorphism from the direct image, read as a semilinear homomorphism. -/
def directImageHom (A : DifferentialGradedAlgebra.{t, m} R) :
    SemilinearHom F σ (directImage F σ A) A where
  app _ _ := AddMonoidHom.id _
  map_smul _ _ _ _ := rfl
  naturality _ _ _ _ _ := rfl
  comm_d _ _ _ := rfl
  map_mul _ _ _ _ _ := rfl
  map_one _ := rfl

end DifferentialGradedAlgebra

/-! ### Restriction along a functor of chaotic sites -/

section Chaotic

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

/-- Every functor out of a site with the chaotic topology is continuous. -/
instance isContinuous_of_bot {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (K : GrothendieckTopology D) : F.IsContinuous (⊥ : GrothendieckTopology C) K where
  op_comp_isSheaf_of_types _ := Presieve.isSheaf_bot

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]

/-- The restriction of a sheaf of commutative rings on a chaotic site along a functor. -/
def restrictRingSheaf (Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}) :
    Sheaf (⊥ : GrothendieckTopology C') CommRingCat.{t} :=
  ⟨F.op ⋙ Osharp.obj, Presheaf.isSheaf_bot _⟩

variable {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}

namespace DifferentialGradedAlgebra

variable (A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- **The restriction of a sheaf of differential graded algebras along a functor of chaotic
sites**: its sections over `U'` are those of `A` over `F U'`. -/
abbrev restrict : DifferentialGradedAlgebra.{t, m}
    (Stacks.SheafOfModules.Tensor.ringSheaf (restrictRingSheaf F Osharp)) :=
  directImage (R' := Stacks.SheafOfModules.Tensor.ringSheaf (restrictRingSheaf F Osharp)) F
    (𝟙 (F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)) A

/-- The identity homomorphism from the restriction, as a semilinear homomorphism along `F`. -/
abbrev restrictHom :
    SemilinearHom F (𝟙 (F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj))
    (A.restrict F) A :=
  directImageHom (R' := Stacks.SheafOfModules.Tensor.ringSheaf (restrictRingSheaf F Osharp)) F
    (𝟙 (F.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)) A

/-- The sections of the restriction over `U'` are the sections of `A` over `F U'`, as rings. -/
def restrictSectionRing (U' : C'ᵒᵖ) :
    (A.restrict F).toGradedAlgebra.totalSections U' →+*
      A.toGradedAlgebra.totalSections (F.op.obj U') :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (A.toGradedAlgebra.sectionsPiece (F.op.obj U')) n).comp
      (AddMonoidHom.id _))
    (DirectSum.of_zero_one _)
    (fun {i j} p q ↦ (GradedAlgebra.of_mul_of_eq A.toGradedAlgebra (F.op.obj U') i j p q).symm)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `restrictSectionRing` sends the degree-`n` component `x` to `x` in degree `n`. -/
@[simp] theorem restrictSectionRing_of (U' : C'ᵒᵖ) (n : ℤ)
    (x : (A.restrict F).toGradedAlgebra.sectionsPiece U' n) :
    A.restrictSectionRing F U' (DirectSum.of _ n x) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece (F.op.obj U')) n x :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of (A.toGradedAlgebra.sectionsPiece (F.op.obj U')) n).comp
      (AddMonoidHom.id _)) n x

/-- The sections of `A` over `F U'` are the sections of the restriction over `U'`, as rings. -/
def restrictSectionRingInv (U' : C'ᵒᵖ) :
    A.toGradedAlgebra.totalSections (F.op.obj U') →+*
      (A.restrict F).toGradedAlgebra.totalSections U' :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of ((A.restrict F).toGradedAlgebra.sectionsPiece U') n).comp
      (AddMonoidHom.id _))
    (DirectSum.of_zero_one _)
    (fun {i j} p q ↦ (GradedAlgebra.of_mul_of_eq (A.restrict F).toGradedAlgebra U' i j p q).symm)

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `restrictSectionRingInv` sends the degree-`n` component `x` to `x` in degree `n`. -/
@[simp] theorem restrictSectionRingInv_of (U' : C'ᵒᵖ) (n : ℤ)
    (x : A.toGradedAlgebra.sectionsPiece (F.op.obj U') n) :
    A.restrictSectionRingInv F U' (DirectSum.of _ n x) =
      DirectSum.of ((A.restrict F).toGradedAlgebra.sectionsPiece U') n x :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of ((A.restrict F).toGradedAlgebra.sectionsPiece U') n).comp
      (AddMonoidHom.id _)) n x

/-- **The sections of the restriction over `U'` are the sections of `A` over `F U'`**, as
differential graded algebras. -/
def restrictSectionHom (U' : C'ᵒᵖ) :
    ((A.restrict F).sectionAlgebra U').Hom (A.sectionAlgebra (F.op.obj U')) where
  toAlgebraHom := Stacks.uliftIntAlgHom (A.restrictSectionRing F U')
  map_grading := by
    rintro n x ⟨p, rfl⟩
    exact ⟨_, (A.restrictSectionRing_of F U' n p).symm⟩
  map_d x := by
    have key : (A.restrictSectionRing F U').toAddMonoidHom.comp ((A.restrict F).sectionD U') =
        (A.sectionD (F.op.obj U')).comp (A.restrictSectionRing F U').toAddMonoidHom := by
      refine DirectSum.addHom_ext fun n p => ?_
      change A.restrictSectionRing F U' ((A.restrict F).sectionD U' (DirectSum.of _ n p)) =
        A.sectionD (F.op.obj U') (A.restrictSectionRing F U' (DirectSum.of _ n p))
      rw [sectionD_of, restrictSectionRing_of, restrictSectionRing_of]
      exact (A.sectionD_of (F.op.obj U') n p).symm
    exact DFunLike.congr_fun key x

/-- The inverse identification, as a homomorphism of differential graded algebras. -/
def restrictSectionInv (U' : C'ᵒᵖ) :
    (A.sectionAlgebra (F.op.obj U')).Hom ((A.restrict F).sectionAlgebra U') where
  toAlgebraHom := Stacks.uliftIntAlgHom (A.restrictSectionRingInv F U')
  map_grading := by
    rintro n x ⟨p, rfl⟩
    exact ⟨_, (A.restrictSectionRingInv_of F U' n p).symm⟩
  map_d x := by
    have key : (A.restrictSectionRingInv F U').toAddMonoidHom.comp (A.sectionD (F.op.obj U')) =
        ((A.restrict F).sectionD U').comp (A.restrictSectionRingInv F U').toAddMonoidHom := by
      refine DirectSum.addHom_ext fun n p => ?_
      change A.restrictSectionRingInv F U' (A.sectionD (F.op.obj U') (DirectSum.of _ n p)) =
        (A.restrict F).sectionD U' (A.restrictSectionRingInv F U' (DirectSum.of _ n p))
      rw [sectionD_of, restrictSectionRingInv_of, restrictSectionRingInv_of]
      exact ((A.restrict F).sectionD_of U' n p).symm
    exact DFunLike.congr_fun key x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `restrictSectionHom` is a left inverse of `restrictSectionInv`. -/
theorem restrictSectionHom_inv (U' : C'ᵒᵖ) (x : (A.sectionAlgebra (F.op.obj U')).A) :
    (A.restrictSectionHom F U').toAlgebraHom ((A.restrictSectionInv F U').toAlgebraHom x) = x := by
  have key : (A.restrictSectionRing F U').comp (A.restrictSectionRingInv F U') = RingHom.id _ := by
    refine DirectSum.ringHom_ext fun n p => ?_
    change A.restrictSectionRing F U' (A.restrictSectionRingInv F U' (DirectSum.of _ n p)) = _
    rw [restrictSectionRingInv_of]
    exact A.restrictSectionRing_of F U' n p
  exact DFunLike.congr_fun key x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- `restrictSectionInv` is a left inverse of `restrictSectionHom`. -/
theorem restrictSectionInv_hom (U' : C'ᵒᵖ) (x : ((A.restrict F).sectionAlgebra U').A) :
    (A.restrictSectionInv F U').toAlgebraHom ((A.restrictSectionHom F U').toAlgebraHom x) = x := by
  have key : (A.restrictSectionRingInv F U').comp (A.restrictSectionRing F U') = RingHom.id _ := by
    refine DirectSum.ringHom_ext fun n p => ?_
    change A.restrictSectionRingInv F U' (A.restrictSectionRing F U' (DirectSum.of _ n p)) = _
    rw [restrictSectionRing_of]
    exact A.restrictSectionRingInv_of F U' n p
  exact DFunLike.congr_fun key x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The identification of sections commutes with the restriction homomorphisms. -/
theorem restrictSectionHom_sectionRestriction {U' V' : C'ᵒᵖ} (a : V' ⟶ U')
    (x : ((A.restrict F).sectionAlgebra V').A) :
    (A.restrictSectionHom F U').toAlgebraHom
        (((A.restrict F).sectionRestriction a).toAlgebraHom x) =
      (A.sectionRestriction (F.op.map a)).toAlgebraHom
        ((A.restrictSectionHom F V').toAlgebraHom x) := by
  have key : (A.restrictSectionRing F U').comp ((A.restrict F).sectionRestrictRing a) =
      (A.sectionRestrictRing (F.op.map a)).comp (A.restrictSectionRing F V') := by
    refine DirectSum.ringHom_ext fun n p => ?_
    change A.restrictSectionRing F U'
        ((A.restrict F).sectionRestrictRing a (DirectSum.of _ n p)) =
      A.sectionRestrictRing (F.op.map a) (A.restrictSectionRing F V' (DirectSum.of _ n p))
    rw [sectionRestrictRing_of, restrictSectionRing_of, restrictSectionRing_of]
    exact (A.sectionRestrictRing_of (F.op.map a) n p).symm
  exact DFunLike.congr_fun key x

omit [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [(⊥ : GrothendieckTopology C').HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The inverse identification of sections commutes with the restriction homomorphisms. -/
theorem restrictSectionInv_sectionRestriction {U' V' : C'ᵒᵖ} (a : V' ⟶ U')
    (x : (A.sectionAlgebra (F.op.obj V')).A) :
    (A.restrictSectionInv F U').toAlgebraHom ((A.sectionRestriction (F.op.map a)).toAlgebraHom x) =
      ((A.restrict F).sectionRestriction a).toAlgebraHom
        ((A.restrictSectionInv F V').toAlgebraHom x) := by
  have hinj : Function.Injective (A.restrictSectionHom F U').toAlgebraHom := fun y z hyz => by
    rw [← A.restrictSectionInv_hom F U' y, hyz, A.restrictSectionInv_hom]
  apply hinj
  rw [restrictSectionHom_inv, restrictSectionHom_sectionRestriction, restrictSectionHom_inv]

end DifferentialGradedAlgebra

end Chaotic

end SheafOfModules
