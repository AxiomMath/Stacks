module

public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingOfToposHom

/-! # The naive cup product, for a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of Stacks 01D3,
part (2) — a morphism of the underlying topoi together with the structure map, with no functor
between the underlying sites — and let `K`, `M` be unbounded cochain complexes of
`O_C`-modules.  The *naive cup product* of Stacks 0FPJ is the map of complexes of
`O_D`-modules

`Tot(f_*K ⊗_{O_D} f_*M) ⟶ f_*Tot(K ⊗_{O_C} M)`

adjoint, under `f^* ⊣ f_*` of **Stacks 03D7**, to the comparison
`f^*Tot(f_*K ⊗_{O_D} f_*M) ≅ Tot(f^*f_*K ⊗_{O_C} f^*f_*M)` of **Stacks 03EL** followed by the
ordinary counit `f^*f_* ⟶ id` in each of the two tensor factors.

## Main definitions

All in the namespace `Stacks.Cohomology.NaiveCupProductOfToposHom`.

* `pushforwardComplex` — degreewise direct image of complexes.
* `complexAdjunction` — `f^* ⊣ f_*` on cochain complexes, degreewise that of Stacks 03D7.
* `naiveCupProductTranspose` — the map of which the naive cup product is the adjoint transpose.
* `naiveCupProduct` — **the naive cup product**.

## Main results

* `pullbackComplex_naiveCupProduct_counit` — the square identifying the naive cup product
  against the ordinary counits, which the source offers as its definition.
* `naiveCupProduct_eq_unit_comp` — the map written through the unit of `f^* ⊣ f_*`.

## Implementation notes

The construction is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TensorComplex/NaiveCupProduct.lean` for a
site-presented morphism.  Here the pullback is that of Stacks 03D6 part (2),
`AlgebraicGeometry.RingedToposHom.pullbackModules`, and the comparison of Stacks 03EL on total
tensor complexes is stated for it directly
(`Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorComplexIso`), so no hypothesis on the
underlying sites enters.

Degreewise the naive cup product is the comparison `f_*F ⊗ f_*G ⟶ f_*(F ⊗ G)` on each summand of
each total degree; the adjoint transpose is taken as the definition because `f_*` does not
preserve the coproducts of a total degree, and `pullbackComplex_naiveCupProduct_counit`
characterizes the map uniquely.

## References

* [Stacks Project, Tag 0FPJ](https://stacks.math.columbia.edu/tag/0FPJ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Cohomology.NaiveCupProductOfToposHom

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-! ## Direct image of complexes and the adjunction on complexes -/

/-- The degreewise direct image of cochain complexes of sheaves of modules along a morphism of
ringed topoi. -/
abbrev pushforwardComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ :=
  (RingedToposHom.pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The adjunction `f^* ⊣ f_*` on cochain complexes of modules, induced degreewise by the
adjunction of Stacks 03D7.  Its unit and counit are those of Stacks 03D7 in each degree. -/
def complexAdjunction : pullbackComplex f ⊣ pushforwardComplex f :=
  Adjunction.mapHomologicalComplexAdjunction (RingedToposHom.pullbackAdjPushforwardModules f)
    (ComplexShape.up ℤ)

omit [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The counit of `f^* ⊣ f_*` on complexes is the counit of Stacks 03D7 in each degree. -/
lemma complexAdjunction_counit_app_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    ((complexAdjunction f).counit.app K).f n =
      (RingedToposHom.pullbackAdjPushforwardModules f).counit.app (K.X n) := rfl

/-! ## The naive cup product -/

section Total

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The map `f^*Tot(f_*K ⊗_{O_D} f_*M) ⟶ Tot(K ⊗_{O_C} M)` of which the naive cup product is
the adjoint transpose: the comparison of Stacks 03EL on total tensor complexes followed by the
ordinary counit `f^*f_* ⟶ id` in each tensor factor. -/
def naiveCupProductTranspose :
    (pullbackComplex f).obj (HomologicalComplex.mapBifunctor ((pushforwardComplex f).obj K)
        ((pushforwardComplex f).obj M)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ⟶
      HomologicalComplex.mapBifunctor K M
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  (Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorComplexIso f
        ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)).hom ≫
    HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
      ((complexAdjunction f).counit.app M)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)

/-- **The naive cup product** `Tot(f_*K ⊗_{O_D} f_*M) ⟶ f_*Tot(K ⊗_{O_C} M)` of Stacks 0FPJ,
for a morphism of ringed topoi and unbounded cochain complexes `K`, `M` of `O_C`-modules: the
map adjoint, under `f^* ⊣ f_*` of Stacks 03D7, to the comparison
`f^*Tot(f_*K ⊗ f_*M) ≅ Tot(f^*f_*K ⊗ f^*f_*M)` of Stacks 03EL followed by the ordinary counit
`f^*f_* ⟶ id` in each of the two tensor factors. -/
def naiveCupProduct :
    HomologicalComplex.mapBifunctor ((pushforwardComplex f).obj K)
        ((pushforwardComplex f).obj M)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ) ⟶
      (pushforwardComplex f).obj (HomologicalComplex.mapBifunctor K M
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
  (complexAdjunction f).homEquiv _ _ (naiveCupProductTranspose f K M)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The naive cup product written through the unit of `f^* ⊣ f_*`. -/
lemma naiveCupProduct_eq_unit_comp :
    naiveCupProduct f K M =
      (complexAdjunction f).unit.app (HomologicalComplex.mapBifunctor
          ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≫
        (pushforwardComplex f).map (naiveCupProductTranspose f K M) :=
  Adjunction.homEquiv_unit _ _ _ _

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The square which identifies the naive cup product against the ordinary counits**, and
which the Stacks project says may be viewed as its definition: `f^*` of the naive cup product
followed by the counit `f^*f_*Tot(K ⊗ M) ⟶ Tot(K ⊗ M)` is the comparison of Stacks 03EL on
total tensor complexes followed by the counit in each tensor factor. -/
theorem pullbackComplex_naiveCupProduct_counit :
    (pullbackComplex f).map (naiveCupProduct f K M) ≫
        (complexAdjunction f).counit.app (HomologicalComplex.mapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) =
      (Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorComplexIso f
            ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)).hom ≫
        HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
          ((complexAdjunction f).counit.app M)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  Equiv.symm_apply_apply ((complexAdjunction f).homEquiv _ _) (naiveCupProductTranspose f K M)

end Total

end Stacks.Cohomology.NaiveCupProductOfToposHom

end
