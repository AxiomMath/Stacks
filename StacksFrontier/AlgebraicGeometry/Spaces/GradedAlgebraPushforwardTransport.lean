module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardCompEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The direct image of sheaves of graded algebras along a 2-isomorphism

`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso` transports the direct image of
sheaves of *modules* along a 2-isomorphism of morphisms of ringed topoi: two morphisms whose
direct images of sheaves of sets are isomorphic by a transformation carrying the one structure
map to the other have isomorphic direct images of sheaves of modules.  This file does the same
for sheaves of **graded** algebras.

The reason it is needed is that the morphism of ringed topoi of Stacks 03G8 attached to a
morphism of algebraic spaces is *not* functorial on the nose: for `f : X ⟶ Y` and `g : Y ⟶ Z`
the morphism of `f ≫ g` is only 2-isomorphic to the composite of the morphisms of `f` and of
`g`.  The unconditional multiplicative composition comparison for pullbacks of sheaves of graded
algebras, `Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIsoOfComp`, is stated
for the honest composite `g ∘ f` of morphisms of ringed topoi, so it says nothing about `f ≫ g`
until the direct image of graded algebras has been transported along that 2-isomorphism.  With
the transport in hand, `gradedPullbackCompIso` — which takes an arbitrary morphism in the role
of the composite together with a comparison of the direct images — applies directly.

## Main definitions

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardNatIsoConjugate`: the conjugate of
  the 2-isomorphism, a transformation of the inverse images in the opposite direction.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebraIsoAppOfNatIso` and
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebraFunctorIsoOfNatIso`:
  **the direct image of sheaves of graded algebras, transported along a 2-isomorphism**, at a
  single sheaf of graded algebras and as an isomorphism of functors.

## Main results

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.transposedSectionEquiv_natIso` and
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushedSectionEquiv_natIso`: **the transposed
  description of a local section is carried by the 2-isomorphism into precomposition with its
  conjugate.**  This is the whole content of the transport.
* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.transposedMultiplicationAt_natIso`: the
  multiplication of a direct image is carried to the multiplication of the other direct image.

## Implementation notes

**Why the conjugate transformation appears.**  A local section over `U` of a direct image
`F_*M` is, by `Stacks.Sheaves.GradedAlgebraEssentiallySmall.transposedSectionEquiv`, a morphism
`F^{-1}Ŷ_U ⟶ M` out of the inverse image of the sheafified small representable of `U`; and the
multiplication of a direct-image graded algebra is read on those morphisms.  The two morphisms
of ringed topoi have *different* inverse images, so the transport cannot be an equality of
transposed descriptions: the transposed description for `H` is the transposed description for
`F` precomposed with a morphism `H^{-1}Ŷ_U ⟶ F^{-1}Ŷ_U`.  That morphism is the conjugate of the
given transformation of direct images under the two adjunctions, `CategoryTheory.conjugateEquiv`
of Mathlib.  Precomposition with a fixed morphism commutes with pairing and with multiplying in
the source algebra, which is why multiplicativity follows with no further input.

**Why the statement is at a general morphism of ringed topoi.**  Nothing below uses anything
about algebraic spaces; the file is placed under `StacksFrontier/AlgebraicGeometry/Spaces/` only
because `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso`, whose degreewise
components it reuses, is placed there — for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

/-! ### Transposing against a conjugate pair of adjunctions -/

/-- **Transposition carries postcomposition with a transformation of right adjoints into
precomposition with its conjugate.**  For adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and a
transformation `α : R₁ ⟶ R₂`, transposing `w ≫ α` across the second adjunction is transposing
`w` across the first and precomposing with the conjugate of `α`.

Both sides are `L₂.map w` followed by a morphism out of `L₂(R₁M)`, and the two morphisms agree
by `CategoryTheory.conjugateEquiv_counit_symm`, which is the defining property of the
conjugate. -/
private theorem homEquiv_symm_comp_conjugate {C : Type*} [Category C] {D : Type*} [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : R₁ ⟶ R₂) {A : C}
    {M : D} (w : A ⟶ R₁.obj M) :
    (adj₂.homEquiv A M).symm (w ≫ α.app M) =
      ((conjugateEquiv adj₁ adj₂).symm α).app A ≫ (adj₁.homEquiv A M).symm w := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, conjugateEquiv_counit_symm adj₁ adj₂ α M, ← Category.assoc,
    ← Category.assoc, ((conjugateEquiv adj₁ adj₂).symm α).naturality w]

/-! ### The transport of the direct image of graded algebras -/

section Transport

variable {X Z : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Z.C]
  (F H : AlgebraicGeometry.RingedToposHom X Z)
  (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)

/-- **The conjugate of a 2-isomorphism of morphisms of ringed topoi**, a transformation of the
inverse images in the opposite direction.  It is the morphism through which the transposed
descriptions of local sections of the two direct images are compared. -/
noncomputable def pushforwardNatIsoConjugate :
    H.toToposHom.inverseImage ⟶ F.toToposHom.inverseImage :=
  (conjugateEquiv F.toToposHom.adj H.toToposHom.adj).symm e.hom

variable (he : F.fSharpRing ≫
  pullbackRingSheafMapOfNatTrans Z.J (SheafOfModules.Tensor.ringSheaf X.O) e.hom = H.fSharpRing)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The transposed description of a local section of a direct image, transported along a
2-isomorphism.**  The 2-isomorphism carries a local section of `F_*M` over `U` to one of
`H_*M`, and the transposed description of the image is the transposed description of the
original precomposed with the conjugate of the 2-isomorphism.

The transposed description is transposition across the adjunction of the morphism of ringed
topoi applied to the identification of local sections with morphisms out of a sheafified small
representable, which is natural in the sheaf; so this is
`Stacks.Sites.SheafSection.sectionEquivSmall_comp` followed by
`homEquiv_symm_comp_conjugate`. -/
theorem transposedSectionEquiv_natIso (U : Z.Cᵒᵖ) (M : Sheaf X.J (Type w))
    (z : (F.toToposHom.pushforward.obj M).obj.obj U) :
    transposedSectionEquiv H U M ((e.hom.app M).hom.app U z) =
      (pushforwardNatIsoConjugate F H e).app
          ((presheafToSheaf Z.J (Type w)).obj (smallYoneda.{w} U.unop)) ≫
        transposedSectionEquiv F U M z := by
  change (H.toToposHom.adj.homEquiv _ M).symm
      (sectionEquivSmall Z.J U (H.toToposHom.pushforward.obj M)
        ((e.hom.app M).hom.app U z)) = _
  rw [sectionEquivSmall_comp Z.J U (e.hom.app M) z]
  exact homEquiv_symm_comp_conjugate F.toToposHom.adj H.toToposHom.adj e.hom
    (sectionEquivSmall Z.J U (F.toToposHom.pushforward.obj M) z)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `transposedSectionEquiv_natIso` for sheaves of modules: the transposed description of the
image of a local section of `F_*M` under the transported morphism of sheaves of modules.

The transported morphism is the 2-isomorphism on underlying sheaves of sets, by
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesMapOfNatIso`, and the
transposed description of a local section of a direct image of sheaves of modules is the
transposed description of the underlying sheaf of sets. -/
theorem pushedSectionEquiv_natIso (M : SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))
    (U : Z.Cᵒᵖ) (z : (F.pushforwardModules.obj M).val.obj U) :
    pushedSectionEquiv H M U
        ((AlgebraicGeometry.RingedToposHom.pushforwardModulesMapOfNatIso F H e he M).val.app
          U z) =
      (pushforwardNatIsoConjugate F H e).app
          ((presheafToSheaf Z.J (Type w)).obj (smallYoneda.{w} U.unop)) ≫
        pushedSectionEquiv F M U z :=
  transposedSectionEquiv_natIso F H e U (Stacks.underlyingModuleSheaf X.J M) z

omit [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The multiplication of a direct image of a graded algebra is transported along a
2-isomorphism.**  The degreewise components of the transport carry the multiplication of
`F_*A` to the multiplication of `H_*A`.

On transposed descriptions both sides are precomposition with the conjugate of the
2-isomorphism applied to the pairing of the two transposed descriptions followed by the
multiplication of `A`, because precomposition with a fixed morphism commutes with pairing. -/
theorem transposedMultiplicationAt_natIso
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) (U : Z.Cᵒᵖ)
    (x : (F.pushforwardModules.obj (A.piece i)).val.obj U)
    (y : (F.pushforwardModules.obj (A.piece j)).val.obj U) :
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesMapOfNatIso F H e he
          (A.piece (i + j))).val.app U (transposedMultiplicationAt F A i j U x y) =
      transposedMultiplicationAt H A i j U
        ((AlgebraicGeometry.RingedToposHom.pushforwardModulesMapOfNatIso F H e he
          (A.piece i)).val.app U x)
        ((AlgebraicGeometry.RingedToposHom.pushforwardModulesMapOfNatIso F H e he
          (A.piece j)).val.app U y) := by
  apply (pushedSectionEquiv H (A.piece (i + j)) U).injective
  rw [pushedSectionEquiv_natIso F H e he (A.piece (i + j)) U
    (transposedMultiplicationAt F A i j U x y)]
  change _ ≫ (pushedSectionEquiv F (A.piece (i + j)) U)
      ((pushedSectionEquiv F (A.piece (i + j)) U).symm _) = _
  rw [Equiv.apply_symm_apply, transposedMultiplicationAt, Equiv.apply_symm_apply,
    pushedSectionEquiv_natIso F H e he (A.piece i) U x,
    pushedSectionEquiv_natIso F H e he (A.piece j) U y, ← Category.assoc, prod.comp_lift]

/-- **The direct image of a sheaf of graded algebras, transported along a 2-isomorphism.**  Its
degreewise components are those of
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso`, and multiplicativity is
`transposedMultiplicationAt_natIso`. -/
noncomputable def pushforwardGradedAlgebraHomOfNatIso
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    pushforwardGradedAlgebra F A ⟶ pushforwardGradedAlgebra H A where
  app n := AlgebraicGeometry.RingedToposHom.pushforwardModulesMapOfNatIso F H e he (A.piece n)
  map_mul i j U x y := transposedMultiplicationAt_natIso F H e he A i j U x y

/-- **The direct image of a sheaf of graded algebras is transported along a 2-isomorphism.**
Both directions are `pushforwardGradedAlgebraHomOfNatIso`, the second one for the inverse
2-isomorphism, which satisfies the same hypothesis by
`AlgebraicGeometry.RingedToposHom.fSharpRing_comp_pullbackRingSheafMapOfNatTrans_inv`. -/
noncomputable def pushforwardGradedAlgebraIsoAppOfNatIso
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    pushforwardGradedAlgebra F A ≅ pushforwardGradedAlgebra H A where
  hom := pushforwardGradedAlgebraHomOfNatIso F H e he A
  inv := pushforwardGradedAlgebraHomOfNatIso H F e.symm
    (AlgebraicGeometry.RingedToposHom.fSharpRing_comp_pullbackRingSheafMapOfNatTrans_inv
      F H e he) A
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoAppOfNatIso F H e he
      (A.piece n)).hom_inv_id
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoAppOfNatIso F H e he
      (A.piece n)).inv_hom_id

/-- **The direct-image functor of sheaves of graded algebras is transported along a
2-isomorphism of morphisms of ringed topoi.**  Naturality is naturality of
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso` in each degree, the degreewise
components of the direct image of a homomorphism of sheaves of graded algebras being the direct
images of its degreewise components. -/
noncomputable def pushforwardGradedAlgebraFunctorIsoOfNatIso :
    pushforwardGradedAlgebraFunctor F ≅ pushforwardGradedAlgebraFunctor H :=
  NatIso.ofComponents (fun A => pushforwardGradedAlgebraIsoAppOfNatIso F H e he A)
    (fun φ => SheafOfModules.GradedAlgebra.Hom.ext fun n =>
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso F H e he).hom.naturality
        (φ.app n))

/-- The degreewise components of the transport are those of the transport of the direct image of
sheaves of modules. -/
theorem pushforwardGradedAlgebraFunctorIsoOfNatIso_hom_app_app
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    ((pushforwardGradedAlgebraFunctorIsoOfNatIso F H e he).hom.app A).app n =
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso F H e he).hom.app
        (A.piece n) :=
  rfl

end Transport

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
