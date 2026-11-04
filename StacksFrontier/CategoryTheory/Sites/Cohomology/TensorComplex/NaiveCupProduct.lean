module

public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism

/-! # The naive cup product

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose underlying functor of
sites is a morphism of sites, and let `K`, `M` be unbounded cochain complexes of `O_C`-modules.
The *naive cup product* is the map of complexes of `O_D`-modules

`Tot(f_*K ⊗_{O_D} f_*M) ⟶ f_*Tot(K ⊗_{O_C} M)`

adjoint, under `f^* ⊣ f_*` of **Stacks 03D7**, to the comparison
`f^*Tot(f_*K ⊗_{O_D} f_*M) ≅ Tot(f^*f_*K ⊗_{O_C} f^*f_*M)` of **Stacks 03EL** followed by the
ordinary counit `f^*f_* ⟶ id` in each of the two tensor factors.

## Main definitions

* `Stacks.Cohomology.NaiveCupProduct.pushforwardComplex` — degreewise pushforward of complexes.
* `Stacks.Cohomology.NaiveCupProduct.complexAdjunction` — `f^* ⊣ f_*` on cochain complexes.
* `Stacks.Cohomology.NaiveCupProduct.naiveCupProductTranspose` — the map of which the naive cup
  product is the adjoint transpose.
* `Stacks.Cohomology.NaiveCupProduct.naiveCupProduct` — **the naive cup product**.

## Main results

* `Stacks.Cohomology.NaiveCupProduct.pullbackComplex_naiveCupProduct_counit` — the square which
  identifies the naive cup product against the ordinary counits, and which the Stacks project
  says may be viewed as its definition.
* `Stacks.Cohomology.NaiveCupProduct.naiveCupProduct_eq_unit_comp` — the map written through the
  unit of `f^* ⊣ f_*`.

## Implementation notes

*Why the adjoint transpose is taken as the definition.*  Degreewise the naive cup product is the
two-sided comparison `f_*F ⊗_{O_D} f_*G ⟶ f_*(F ⊗_{O_C} G)` on each summand of each total
degree.  Assembling those into a map of complexes would ask for the total complex of the tensor
double complex pushed forward termwise, which is not available: `f_*` does not preserve the
coproducts of a total degree.  The adjoint transpose needs none of that, and nothing is lost,
because `pullbackComplex_naiveCupProduct_counit` — the square the source itself offers as the
definition — determines the map uniquely, being the statement that it is that transpose.

No boundedness hypothesis is imposed on `K` or `M`; the source imposes none and no step here
needs one.

The hypothesis `hmos`, that the underlying functor of sites is a morphism of sites, is what the
passage from Stacks 03EL for a four-field morphism of ringed topoi to the site-presented
pullback consumes; see
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism`.

## References

* [Stacks Project, Tag 0FPJ](https://stacks.math.columbia.edu/tag/0FPJ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.DerivedPullback Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Cohomology.NaiveCupProduct

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-! ## Pushforward of complexes and the adjunction on complexes -/

/-- The degreewise pushforward of cochain complexes of sheaves of modules along a morphism of
ringed topoi. -/
abbrev pushforwardComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ :=
  f.pushforwardTopos.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The adjunction `f^* ⊣ f_*` on cochain complexes of modules, induced degreewise by the
adjunction of Stacks 03D7.  Its unit and counit are those of Stacks 03D7 in each degree. -/
def complexAdjunction : pullbackComplex f ⊣ pushforwardComplex f :=
  Adjunction.mapHomologicalComplexAdjunction f.pullbackPushforwardAdjunctionTopos
    (ComplexShape.up ℤ)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The counit of `f^* ⊣ f_*` on complexes is the counit of Stacks 03D7 in each degree. -/
lemma complexAdjunction_counit_app_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    ((complexAdjunction f).counit.app K).f n =
      f.pullbackPushforwardAdjunctionTopos.counit.app (K.X n) := rfl

/-! ## The naive cup product -/

section Total

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The map `f^*Tot(f_*K ⊗_{O_D} f_*M) ⟶ Tot(K ⊗_{O_C} M)` of which the naive cup product is
the adjoint transpose: the comparison of Stacks 03EL on total tensor complexes followed by the
ordinary counit `f^*f_* ⟶ id` in each tensor factor. -/
def naiveCupProductTranspose :
    (pullbackComplex f).obj (HomologicalComplex.mapBifunctor ((pushforwardComplex f).obj K)
        ((pushforwardComplex f).obj M) (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (ComplexShape.up ℤ)) ⟶
      HomologicalComplex.mapBifunctor K M (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ) :=
  (pullbackToposTensorTotalIso f hmos ((pushforwardComplex f).obj K)
        ((pushforwardComplex f).obj M)).hom ≫
    HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
      ((complexAdjunction f).counit.app M) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)

/-- **The naive cup product** `Tot(f_*K ⊗_{O_D} f_*M) ⟶ f_*Tot(K ⊗_{O_C} M)`, for unbounded
cochain complexes `K`, `M` of `O_C`-modules: the map adjoint, under `f^* ⊣ f_*` of
Stacks 03D7, to the comparison `f^*Tot(f_*K ⊗ f_*M) ≅ Tot(f^*f_*K ⊗ f^*f_*M)` of Stacks 03EL
followed by the ordinary counit `f^*f_* ⟶ id` in each of the two tensor factors. -/
def naiveCupProduct :
    HomologicalComplex.mapBifunctor ((pushforwardComplex f).obj K)
        ((pushforwardComplex f).obj M) (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
        (ComplexShape.up ℤ) ⟶
      (pushforwardComplex f).obj (HomologicalComplex.mapBifunctor K M
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (complexAdjunction f).homEquiv _ _ (naiveCupProductTranspose f hmos K M)

/-- The naive cup product written through the unit of `f^* ⊣ f_*`. -/
lemma naiveCupProduct_eq_unit_comp :
    naiveCupProduct f hmos K M =
      (complexAdjunction f).unit.app (HomologicalComplex.mapBifunctor
          ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        (pushforwardComplex f).map (naiveCupProductTranspose f hmos K M) :=
  Adjunction.homEquiv_unit _ _ _ _

/-- **The square which identifies the naive cup product against the ordinary counits**, and
which the Stacks project says may be viewed as its definition: `f^*` of the naive cup product
followed by the counit `f^*f_*Tot(K ⊗ M) ⟶ Tot(K ⊗ M)` is the comparison of Stacks 03EL on
total tensor complexes followed by the counit in each tensor factor. -/
theorem pullbackComplex_naiveCupProduct_counit :
    (pullbackComplex f).map (naiveCupProduct f hmos K M) ≫
        (complexAdjunction f).counit.app (HomologicalComplex.mapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) =
      (pullbackToposTensorTotalIso f hmos ((pushforwardComplex f).obj K)
            ((pushforwardComplex f).obj M)).hom ≫
        HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
          ((complexAdjunction f).counit.app M) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) :=
  Equiv.symm_apply_apply ((complexAdjunction f).homEquiv _ _)
    (naiveCupProductTranspose f hmos K M)

end Total

end Stacks.Cohomology.NaiveCupProduct

end
