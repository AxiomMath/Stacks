module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCompEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp

/-!
# The unconditional composition comparison for graded pullbacks, at unrelated universes

This is `Stacks.Sheaves.GradedAlgebraPushforwardComp` with the objects, the morphisms and the
sections of the structure sheaf of the ringed topos in unrelated universes, so that it applies to
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, a `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`.
The hypotheses are the original ones together with `CategoryTheory.EssentiallySmall.{w}` on the
sites the direct images are taken to.

## Main definitions

* `pushforwardGradedAlgebraFunctorCompIso` and `gradedPushCompIso`: the comparison of the
  composite of two direct images of sheaves of graded algebras with the direct image along the
  composite.
* `gradedPullbackCompIsoOfComp`: the unconditional multiplicative composition comparison for
  pullbacks of sheaves of graded algebras.

## Main results

* `map_mul_gradedPullbackCompIsoOfComp`: the degreewise components of that comparison preserve
  products of homogeneous local sections.

## Implementation notes

The one universe-bound step of the original is the identification of local sections of a sheaf
of sets with morphisms out of a sheafified representable; it is replaced throughout by
`Stacks.Sites.SheafSection.sectionEquivSmall`, whose representable is the sectionwise small
model `Stacks.Sites.SheafSection.smallYoneda`. Everything else is the original argument.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v v' u₁ u₁' w w'

/-! ### The multiplication of a direct image, through the binary product comparison -/

section ProductComparison

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u₁', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w'} Y.C]
  (f : AlgebraicGeometry.RingedToposHom X Y)
  (A : SheafOfModules.GradedAlgebra.{w, w} (SheafOfModules.Tensor.ringSheaf X.O))

/-- Morphisms of sheaves of types that agree on every local section are equal. -/
private theorem hom_ext_of_apply_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {M N : Sheaf J (Type w)} {a b : M ⟶ N} (h : ∀ U z, a.hom.app U z = b.hom.app U z) :
    a = b := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  exact h U

/-- **The multiplication of a direct image of a graded algebra factors through the binary
product comparison of the direct image.** There is an isomorphism comparing the direct image of
a binary product of the underlying sheaves of sets with the binary product of the direct images,
compatible with both projections, through whose inverse the multiplication of
`pushforwardGradedAlgebra f A` is the direct image of the multiplication of `A`.

This is the direct-image specification
`Stacks.Sheaves.GradedAlgebraPushforward.isPushforwardGradedAlgebra_pushforwardGradedAlgebra`
with the degreewise identifications discharged: the comparison of a homogeneous piece of the
direct image with the direct image of the homogeneous piece is the identity. -/
public theorem exists_productComparison_multiplicationSheafMap (i j : ℤ) :
    ∃ R : f.toToposHom.pushforward.obj (underlyingPiece A i ⨯ underlyingPiece A j) ≅
        f.toToposHom.pushforward.obj (underlyingPiece A i) ⨯
          f.toToposHom.pushforward.obj (underlyingPiece A j),
      R.hom ≫ prod.fst = f.toToposHom.pushforward.map prod.fst ∧
      R.hom ≫ prod.snd = f.toToposHom.pushforward.map prod.snd ∧
      multiplicationSheafMap (pushforwardGradedAlgebra f A) i j =
        R.inv ≫ f.toToposHom.pushforward.map (multiplicationSheafMap A i j) := by
  obtain ⟨hpiece, hmul, -⟩ := isPushforwardGradedAlgebra_pushforwardGradedAlgebra f A
  obtain ⟨sourceMul, targetMul, R, hsource, htarget, hfst, hsnd, hfactor⟩ := hmul i j
  refine ⟨R, hfst, hsnd, ?_⟩
  have hsrc : sourceMul = multiplicationSheafMap A i j := hom_ext_of_apply_eq hsource
  have htgt : targetMul = multiplicationSheafMap (pushforwardGradedAlgebra f A) i j :=
    hom_ext_of_apply_eq htarget
  have hid : prod.lift
        (prod.fst ≫ (pieceComparison f A (pushforwardGradedAlgebra f A) hpiece i).hom)
        (prod.snd ≫ (pieceComparison f A (pushforwardGradedAlgebra f A) hpiece j).hom) =
      𝟙 (f.toToposHom.pushforward.obj (underlyingPiece A i) ⨯
        f.toToposHom.pushforward.obj (underlyingPiece A j)) := by
    have step : prod.lift
          (prod.fst ≫ 𝟙 (f.toToposHom.pushforward.obj (underlyingPiece A i)))
          (prod.snd ≫ 𝟙 (f.toToposHom.pushforward.obj (underlyingPiece A j))) =
        𝟙 (f.toToposHom.pushforward.obj (underlyingPiece A i) ⨯
          f.toToposHom.pushforward.obj (underlyingPiece A j)) := by
      simp
    exact step
  exact htgt ▸ ((Category.comp_id targetMul).symm.trans (hfactor.trans
    ((congrArg (fun t => t ≫ (R.inv ≫ f.toToposHom.pushforward.map sourceMul)) hid).trans
      (Category.id_comp _)))).trans (congrArg
        (fun m => R.inv ≫ f.toToposHom.pushforward.map m) hsrc)

end ProductComparison

/-! ### Transposition and binary products -/

section Transpose

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u₁', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w'} Y.C]
  (f : AlgebraicGeometry.RingedToposHom X Y)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w'} Y.C] in
/-- **Transposing across the adjunction of a morphism of topoi turns the binary product
comparison of the direct image into a binary product.** -/
public theorem homEquiv_symm_prodLift {M N : Sheaf X.J (Type w)}
    (R : f.toToposHom.pushforward.obj (M ⨯ N) ≅
      f.toToposHom.pushforward.obj M ⨯ f.toToposHom.pushforward.obj N)
    (hfst : R.hom ≫ prod.fst = f.toToposHom.pushforward.map prod.fst)
    (hsnd : R.hom ≫ prod.snd = f.toToposHom.pushforward.map prod.snd)
    (W : Sheaf Y.J (Type w')) (P : W ⟶ f.toToposHom.pushforward.obj M)
    (Q : W ⟶ f.toToposHom.pushforward.obj N) :
    (f.toToposHom.adj.homEquiv W (M ⨯ N)).symm (prod.lift P Q ≫ R.inv) =
      prod.lift ((f.toToposHom.adj.homEquiv W M).symm P)
        ((f.toToposHom.adj.homEquiv W N).symm Q) := by
  have hleft : (prod.lift P Q ≫ R.inv) ≫ f.toToposHom.pushforward.map prod.fst = P :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => prod.lift P Q ≫ k)
        ((congrArg (fun k => R.inv ≫ k) hfst.symm).trans (R.inv_hom_id_assoc _))).trans
          (prod.lift_fst P Q))
  have hright : (prod.lift P Q ≫ R.inv) ≫ f.toToposHom.pushforward.map prod.snd = Q :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => prod.lift P Q ≫ k)
        ((congrArg (fun k => R.inv ≫ k) hsnd.symm).trans (R.inv_hom_id_assoc _))).trans
          (prod.lift_snd P Q))
  refine prod.hom_ext ?_ ?_
  · exact ((f.toToposHom.adj.homEquiv_naturality_right_symm
        (prod.lift P Q ≫ R.inv) prod.fst).symm.trans
      (congrArg (fun k => (f.toToposHom.adj.homEquiv W M).symm k) hleft)).trans
        (prod.lift_fst _ _).symm
  · exact ((f.toToposHom.adj.homEquiv_naturality_right_symm
        (prod.lift P Q ≫ R.inv) prod.snd).symm.trans
      (congrArg (fun k => (f.toToposHom.adj.homEquiv W N).symm k) hright)).trans
        (prod.lift_snd _ _).symm

variable (A : SheafOfModules.GradedAlgebra.{w, w} (SheafOfModules.Tensor.ringSheaf X.O))

/-- **The transpose of a product in a direct image of a graded algebra is the product of the
transposes.** Two local sections of direct-image pieces, multiplied in the direct-image graded
algebra and transposed across the adjunction of `f`, give the product of their transposes in the
source algebra. -/
public theorem homEquiv_symm_prodLift_multiplicationSheafMap (i j : ℤ)
    (W : Sheaf Y.J (Type w'))
    (P : W ⟶ f.toToposHom.pushforward.obj (underlyingPiece A i))
    (Q : W ⟶ f.toToposHom.pushforward.obj (underlyingPiece A j)) :
    (f.toToposHom.adj.homEquiv W (underlyingPiece A (i + j))).symm
        (prod.lift P Q ≫ multiplicationSheafMap (pushforwardGradedAlgebra f A) i j) =
      prod.lift ((f.toToposHom.adj.homEquiv W (underlyingPiece A i)).symm P)
          ((f.toToposHom.adj.homEquiv W (underlyingPiece A j)).symm Q) ≫
        multiplicationSheafMap A i j := by
  obtain ⟨R, hfst, hsnd, hmul⟩ := exists_productComparison_multiplicationSheafMap f A i j
  refine Eq.trans (congrArg (fun k =>
    (f.toToposHom.adj.homEquiv W (underlyingPiece A (i + j))).symm (prod.lift P Q ≫ k)) hmul) ?_
  refine Eq.trans (congrArg (fun k =>
    (f.toToposHom.adj.homEquiv W (underlyingPiece A (i + j))).symm k)
      (Category.assoc (prod.lift P Q) R.inv
        (f.toToposHom.pushforward.map (multiplicationSheafMap A i j))).symm) ?_
  refine Eq.trans (f.toToposHom.adj.homEquiv_naturality_right_symm
    (prod.lift P Q ≫ R.inv) (multiplicationSheafMap A i j)) ?_
  exact congrArg (fun k => k ≫ multiplicationSheafMap A i j)
    (homEquiv_symm_prodLift f R hfst hsnd W P Q)

end Transpose

/-! ### Transposition for a composite -/

section TransposeComp

variable {X Y Z : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] [EssentiallySmall.{w} Z.C]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- **Transposition composes.** The transposed description of a local section of a direct image
along a composite is the transposed description for the second morphism, transposed again across
the adjunction of the first. -/
public theorem transposedSectionEquiv_comp_eq (U : Z.Cᵒᵖ) (N : Sheaf X.J (Type w))
    (s : (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj N)).obj.obj U) :
    transposedSectionEquiv (g.comp f) U N s =
      (f.toToposHom.adj.homEquiv _ N).symm
        (transposedSectionEquiv g U (f.toToposHom.pushforward.obj N) s) := by
  have hsection : transposedSectionEquiv (g.comp f) U N s =
      f.toToposHom.inverseImage.map (g.toToposHom.inverseImage.map
          (sectionEquivSmall Z.J U
            (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj N)) s)) ≫
        (g.comp f).toToposHom.adj.counit.app N :=
    Adjunction.homEquiv_counit (g.comp f).toToposHom.adj
      ((presheafToSheaf Z.J (Type w)).obj (smallYoneda.{w} U.unop)) N
      (sectionEquivSmall Z.J U
        (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj N)) s)
  have hcounit : (g.comp f).toToposHom.adj.counit.app N =
      f.toToposHom.inverseImage.map
          (g.toToposHom.adj.counit.app (f.toToposHom.pushforward.obj N)) ≫
        f.toToposHom.adj.counit.app N :=
    Adjunction.comp_counit_app g.toToposHom.adj f.toToposHom.adj N
  have houter : (f.toToposHom.adj.homEquiv
        (g.toToposHom.inverseImage.obj
          ((presheafToSheaf Z.J (Type w)).obj (smallYoneda.{w} U.unop))) N).symm
        (transposedSectionEquiv g U (f.toToposHom.pushforward.obj N) s) =
      f.toToposHom.inverseImage.map
          (transposedSectionEquiv g U (f.toToposHom.pushforward.obj N) s) ≫
        f.toToposHom.adj.counit.app N :=
    Adjunction.homEquiv_counit f.toToposHom.adj _ N _
  have hinner : transposedSectionEquiv g U (f.toToposHom.pushforward.obj N) s =
      g.toToposHom.inverseImage.map
          (sectionEquivSmall Z.J U
            (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj N)) s) ≫
        g.toToposHom.adj.counit.app (f.toToposHom.pushforward.obj N) :=
    Adjunction.homEquiv_counit g.toToposHom.adj
      ((presheafToSheaf Z.J (Type w)).obj (smallYoneda.{w} U.unop))
      (f.toToposHom.pushforward.obj N)
      (sectionEquivSmall Z.J U
        (g.toToposHom.pushforward.obj (f.toToposHom.pushforward.obj N)) s)
  rw [hsection, hcounit, houter, hinner, Functor.map_comp, Category.assoc]

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] in
/-- `transposedSectionEquiv_comp_eq` for sheaves of modules: the transposed description of a
local section of a direct image of sheaves of modules along a composite. -/
public theorem pushedSectionEquiv_comp_eq
    (M : SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)) (U : Z.Cᵒᵖ)
    (s : (g.pushforwardModules.obj (f.pushforwardModules.obj M)).val.obj U) :
    pushedSectionEquiv (g.comp f) M U s =
      (f.toToposHom.adj.homEquiv _ (Stacks.underlyingModuleSheaf X.J M)).symm
        (pushedSectionEquiv g (f.pushforwardModules.obj M) U s) :=
  transposedSectionEquiv_comp_eq f g U (Stacks.underlyingModuleSheaf X.J M) s

end TransposeComp

/-! ### The comparison of the direct images of a sheaf of graded algebras -/

section CompIso

variable {X Y Z : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] [EssentiallySmall.{w} Z.C]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)
  (A : SheafOfModules.GradedAlgebra.{w, w} (SheafOfModules.Tensor.ringSheaf X.O))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The multiplications of `g_*(f_*A)` and of `(g ∘ f)_*A` agree on local sections.** This is
the whole content of the comparison: transposition composes, and the transpose of a product in a
direct image is the product of the transposes, so both multiplications transpose to the same
product in `A`. -/
public theorem transposedMultiplicationAt_comp (i j : ℤ) (U : Z.Cᵒᵖ)
    (x : (g.pushforwardModules.obj
      (f.pushforwardModules.obj (A.piece i))).val.obj U)
    (y : (g.pushforwardModules.obj
      (f.pushforwardModules.obj (A.piece j))).val.obj U) :
    transposedMultiplicationAt g (pushforwardGradedAlgebra f A) i j U x y =
      transposedMultiplicationAt (g.comp f) A i j U x y := by
  apply (pushedSectionEquiv (g.comp f) (A.piece (i + j)) U).injective
  have hright : pushedSectionEquiv (g.comp f) (A.piece (i + j)) U
        (transposedMultiplicationAt (g.comp f) A i j U x y) =
      prod.lift (pushedSectionEquiv (g.comp f) (A.piece i) U x)
          (pushedSectionEquiv (g.comp f) (A.piece j) U y) ≫
        multiplicationSheafMap A i j :=
    (pushedSectionEquiv (g.comp f) (A.piece (i + j)) U).apply_symm_apply _
  have hleft : pushedSectionEquiv g ((pushforwardGradedAlgebra f A).piece (i + j)) U
        (transposedMultiplicationAt g (pushforwardGradedAlgebra f A) i j U x y) =
      prod.lift (pushedSectionEquiv g ((pushforwardGradedAlgebra f A).piece i) U x)
          (pushedSectionEquiv g ((pushforwardGradedAlgebra f A).piece j) U y) ≫
        multiplicationSheafMap (pushforwardGradedAlgebra f A) i j :=
    (pushedSectionEquiv g ((pushforwardGradedAlgebra f A).piece (i + j)) U).apply_symm_apply _
  refine Eq.trans (pushedSectionEquiv_comp_eq f g (A.piece (i + j)) U _) ?_
  refine Eq.trans (congrArg (fun k =>
    (f.toToposHom.adj.homEquiv _ (underlyingPiece A (i + j))).symm k) hleft) ?_
  refine Eq.trans (homEquiv_symm_prodLift_multiplicationSheafMap f A i j _ _ _) ?_
  refine Eq.trans ?_ hright.symm
  exact congrArg₂ (fun a b => prod.lift a b ≫ multiplicationSheafMap A i j)
    (pushedSectionEquiv_comp_eq f g (A.piece i) U x).symm
    (pushedSectionEquiv_comp_eq f g (A.piece j) U y).symm

/-- The comparison `g_*(f_*A) ⟶ (g ∘ f)_*A` of sheaves of graded algebras. Its degreewise
components are those of `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`, which are
the identity on local sections, so multiplicativity is `transposedMultiplicationAt_comp`. -/
public noncomputable def pushforwardGradedAlgebraCompHom :
    pushforwardGradedAlgebra g (pushforwardGradedAlgebra f A) ⟶
      pushforwardGradedAlgebra (g.comp f) A where
  app n := (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).inv.app (A.piece n)
  map_mul i j U x y := transposedMultiplicationAt_comp f g A i j U x y

/-- The comparison `(g ∘ f)_*A ⟶ g_*(f_*A)` of sheaves of graded algebras, inverse to
`pushforwardGradedAlgebraCompHom`. -/
public noncomputable def pushforwardGradedAlgebraCompInv :
    pushforwardGradedAlgebra (g.comp f) A ⟶
      pushforwardGradedAlgebra g (pushforwardGradedAlgebra f A) where
  app n := (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).hom.app (A.piece n)
  map_mul i j U x y := (transposedMultiplicationAt_comp f g A i j U x y).symm

/-- **The comparison `g_*(f_*A) ≅ (g ∘ f)_*A` of sheaves of graded algebras.** -/
public noncomputable def pushforwardGradedAlgebraCompIsoApp :
    pushforwardGradedAlgebra g (pushforwardGradedAlgebra f A) ≅
      pushforwardGradedAlgebra (g.comp f) A where
  hom := pushforwardGradedAlgebraCompHom f g A
  inv := pushforwardGradedAlgebraCompInv f g A
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).inv_hom_id_app (A.piece n)
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).hom_inv_id_app (A.piece n)

variable {A}

/-- **The comparison of the direct-image functors of sheaves of graded algebras**, part (1) of
Stacks 0FQX for a composite: the direct image along `g ∘ f` is the direct image along `f`
followed by the direct image along `g`, naturally in the sheaf of graded algebras. -/
public noncomputable def pushforwardGradedAlgebraFunctorCompIso :
    pushforwardGradedAlgebraFunctor f ⋙ pushforwardGradedAlgebraFunctor g ≅
      pushforwardGradedAlgebraFunctor (g.comp f) :=
  NatIso.ofComponents (fun A => pushforwardGradedAlgebraCompIsoApp f g A)
    (fun φ => SheafOfModules.GradedAlgebra.Hom.ext fun n =>
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).inv.naturality (φ.app n))

/-- The degree `n` component of `pushforwardGradedAlgebraFunctorCompIso` at `A` is the inverse
of `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` at the piece `A.piece n`. -/
@[simp]
public theorem pushforwardGradedAlgebraFunctorCompIso_hom_app_app
    (A : SheafOfModules.GradedAlgebra.{w, w} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    ((pushforwardGradedAlgebraFunctorCompIso f g).hom.app A).app n =
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).inv.app (A.piece n) :=
  rfl

/-- The degree `n` component of the inverse of `pushforwardGradedAlgebraFunctorCompIso` at `A`
is `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` at the piece `A.piece n`. -/
@[simp]
public theorem pushforwardGradedAlgebraFunctorCompIso_inv_app_app
    (A : SheafOfModules.GradedAlgebra.{w, w} (SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    ((pushforwardGradedAlgebraFunctorCompIso f g).inv.app A).app n =
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso f g).hom.app (A.piece n) :=
  rfl

end CompIso

/-! ### The unconditional composition comparison for pullbacks -/

section Pullback

variable {X Y Z : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] [EssentiallySmall.{w} Z.C]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)

/-- **The comparison `g_* ∘ f_* ≅ (g ∘ f)_*` of the direct images of sheaves of graded algebras
produced by part (3) of Stacks 0FQX.** This is the hypothesis of
`Stacks.Sheaves.GradedAlgebraPullbackComp.gradedPullbackCompIso`, discharged. -/
public noncomputable def gradedPushCompIso :
    gradedPush f ⋙ gradedPush g ≅ gradedPush (g.comp f) :=
  pushforwardGradedAlgebraFunctorCompIso f g

/-- **The multiplicative composition comparison for pullbacks of sheaves of graded algebras,
unconditionally.** The pullback along `g ∘ f` of sheaves of graded algebras is the pullback along
`g` followed by the pullback along `f`, as functors of sheaves of **graded algebras** — so the
comparison is multiplicative in every degree, which is what
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` leaves open. -/
public noncomputable def gradedPullbackCompIsoOfComp :
    gradedPull (g.comp f) ≅ gradedPull g ⋙ gradedPull f :=
  gradedPullbackCompIso f g (g.comp f) (gradedPushCompIso f g)

/-- **The unconditional composition comparison preserves products of homogeneous local sections
in every degree.** -/
public theorem map_mul_gradedPullbackCompIsoOfComp
    (B : SheafOfModules.GradedAlgebra.{w, w} (SheafOfModules.Tensor.ringSheaf Z.O))
    (i j : ℤ) (U : X.Cᵒᵖ)
    (x : (((gradedPull (g.comp f)).obj B).piece i).val.obj U)
    (y : (((gradedPull (g.comp f)).obj B).piece j).val.obj U) :
    ((((gradedPullbackCompIsoOfComp f g).hom.app B).app (i + j)).val.app U)
        ((((gradedPull (g.comp f)).obj B).mul i j).app U x y) =
      ((((gradedPull g ⋙ gradedPull f).obj B).mul i j)).app U
        ((((gradedPullbackCompIsoOfComp f g).hom.app B).app i).val.app U x)
        ((((gradedPullbackCompIsoOfComp f g).hom.app B).app j).val.app U y) :=
  map_mul_gradedPullbackCompIso f g (g.comp f) (gradedPushCompIso f g) B i j U x y

end Pullback
end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
