module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Commutativity of the degree-one multiplication is inherited by a pullback

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `B` be a sheaf
of graded `O_D`-algebras whose degree-`(1,1)` multiplication is commutative.  Then so is the
degree-`(1,1)` multiplication of the pullback `f^*B`.

This is what makes the universal property of the symmetric algebra available at a pullback: the
hypothesis `SheafOfModules.GradedAlgebra.PairwiseCommutes` of
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` is exactly commutativity of the degree-`(1,1)`
multiplication on the image of a degree-one generator, so a pullback whose degree-one piece is
taken as its own generator satisfies it.

The pullback is the inverse image followed by extension of scalars, and extension of scalars is
the sectionwise tensor product followed by sheafification, so commutativity has to be carried
through three constructions.  None of the three has computable sections, and each is handled in
the way its own construction allows.

* **Inverse image.**  Every operation of the inverse image of a sheaf of graded algebras is the
  image, under a finite-product-preserving functor to types, of a morphism of sheaves of sets on
  the target site.  Commutativity therefore follows from the single equation
  `Stacks.Sheaves.GradedAlgebraInverseImage.mulSheafHom_comm` between such morphisms, which is
  checked on sections over the target site, where the original multiplication is available.  No
  description of the sections of an inverse image is needed.
* **Sectionwise tensor product.**  Here the sections *are* a tensor product, so commutativity is
  two applications of `TensorProduct.induction_on`, reduced to pure tensors by
  `Stacks.Sheaves.BilinearChangeOfRings.baseChange₂_tmul`: the formula
  `(a ⊗ x)(c ⊗ y) = ac ⊗ xy` is symmetric because the ring of sections is commutative.
* **Sheafification.**  `Stacks.GradedAlgebra.pairwiseCommutes_sheafifyGen` already transfers
  commutativity on the image of a degree-one generator to the sheafification.  Taking the
  generator to be the identity of the degree-one piece turns it into the transfer of plain
  commutativity, because the sheafification of the identity is the identity.

## Main results

* `Stacks.Sheaves.BilinearChangeOfRings.baseChange₂_comm` and
  `Stacks.Sheaves.BilinearChangeOfRings.cofBil_app_comm`: base change of a symmetric bilinear
  map is symmetric.
* `Stacks.GradedAlgebra.sheafify_mul_one_one_comm`: the sheafification of a graded algebra of
  presheaves of modules with commutative degree-`(1,1)` multiplication has commutative
  degree-`(1,1)` multiplication.
* `Stacks.Sheaves.GradedAlgebraInverseImage.mulSheafHom_comm`,
  `transportGradedAlgebra_mul_one_one_comm` and `inverseImageGradedAlgebra_mul_one_one_comm`:
  the same for a transport along a finite-product-preserving functor of sheaves of sets, and in
  particular for the inverse image along a morphism of topoi.
* `Stacks.Sheaves.GradedAlgebraExtendScalars.extendScalarsGradedAlgebra_mul_one_one_comm` and
  `Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra_mul_one_one_comm`: the
  statements for extension of scalars and for the pullback itself.

## Implementation notes

Only degree `(1,1)` is treated, because that is the degree the symmetric-algebra universal
property constrains and because `Stacks.GradedAlgebra.pairwiseCommutes_sheafifyGen` is stated
there.  Nothing in the arguments below is special to degree one except that the two factors have
equal degrees, so that the two sides of the commutativity equation live in the *same*
homogeneous piece and the statement is an equality rather than a heterogeneous equality.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry TensorProduct PresheafOfModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.BilinearChangeOfRings
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.GradedAlgebraInverseImage

/-! ### Base change of a symmetric bilinear map -/

namespace Stacks.Sheaves.BilinearChangeOfRings

universe v u w

/-- **The base change of a symmetric bilinear map is symmetric.**  On pure tensors the base
change is `(a ⊗ m, c ⊗ n) ↦ ac ⊗ b m n`, which is symmetric because the base algebra is
commutative; the general case is two inductions on the tensor product. -/
public lemma baseChange₂_comm {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (b : M →ₗ[R] M →ₗ[R] P) (hb : ∀ m n : M, b m n = b n m) (x y : S ⊗[R] M) :
    baseChange₂ (S := S) b x y = baseChange₂ (S := S) b y x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | tmul c n => rw [baseChange₂_tmul, baseChange₂_tmul, mul_comm, hb]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (baseChange₂ (S := S) b) y₁ y₂, LinearMap.add_apply, ← h₁, ← h₂,
        map_add (baseChange₂ (S := S) b (a ⊗ₜ[R] m)) y₁ y₂]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (baseChange₂ (S := S) b) x₁ x₂, LinearMap.add_apply, h₁, h₂,
      map_add (baseChange₂ (S := S) b y) x₁ x₂]

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  {M P : PMod O₁}

/-- The base change of a symmetric bilinear map of presheaves of modules is symmetric, on
sections over an object of the site. -/
public lemma cofApp_comm (β : Stacks.BilinearMap M M P)
    (hβ : ∀ (X : Cᵒᵖ) (x y : M.obj X), β.app X x y = β.app X y x) (X : Cᵒᵖ)
    (x y : cofObj θ M X) : cofApp θ β X x y = cofApp θ β X y x := by
  let := (θ.app X).hom.toAlgebra
  exact baseChange₂_comm (S := O₂.obj X) (bilAt β X) (fun m n ↦ hβ X m n) x y

/-- The base change of a symmetric bilinear map of presheaves of modules is symmetric. -/
public lemma cofBil_app_comm (β : Stacks.BilinearMap M M P)
    (hβ : ∀ (X : Cᵒᵖ) (x y : M.obj X), β.app X x y = β.app X y x) (X : Cᵒᵖ)
    (x y : ((changeOfRings θ).obj M).obj X) :
    (cofBil θ β).app X x y = (cofBil θ β).app X y x :=
  cofApp_comm θ β hβ X x y

end Stacks.Sheaves.BilinearChangeOfRings

/-! ### Sheafification -/

namespace Stacks.GradedAlgebra

universe v u t a

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀} (A : GradedAlgebra P)

/-- **Commutativity of the degree-`(1,1)` multiplication passes to the sheafification.**  This is
`Stacks.GradedAlgebra.pairwiseCommutes_sheafifyGen` for the identity generator of the degree-one
piece, whose sheafification is the identity. -/
public theorem sheafify_mul_one_one_comm
    (hc : ∀ (X : Cᵒᵖ) (x y : (P 1).obj X),
      (A.mul 1 1).app X x y = (A.mul 1 1).app X y x)
    (U : Cᵒᵖ) (s u : ((A.sheafify α).piece 1).val.obj U) :
    ((A.sheafify α).mul 1 1).app U s u = ((A.sheafify α).mul 1 1).app U u s := by
  have hid : A.sheafifyGen α (𝟙 (P 1)) = 𝟙 ((A.sheafify α).piece 1) :=
    (sheafification α).map_id (P 1)
  have h := A.pairwiseCommutes_sheafifyGen α (gen := 𝟙 (P 1)) hc
  rw [hid] at h
  exact h U s u

end Stacks.GradedAlgebra

/-! ### Transport along a functor of sheaves of sets, and the inverse image -/

namespace Stacks.Sheaves.GradedAlgebraInverseImage

universe t w w' v u v' u'

section Operations

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{w'})] [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {O : Sheaf K RingCat.{w'}} (A : SheafOfModules.GradedAlgebra.{w', w'} O)

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- **A symmetric multiplication in two equal degrees is a symmetric morphism of sheaves of
sets.**  Precomposing `Stacks.Sheaves.GradedAlgebraInverseImage.mulSheafHom` with the braiding of
the binary product leaves it unchanged.  This is the form in which commutativity survives a
transport: both sides are morphisms of sheaves of sets on the target site. -/
public lemma mulSheafHom_comm (i : ℤ)
    (hc : ∀ (X : Dᵒᵖ) (x y : (A.piece i).val.obj X),
      (A.mul i i).app X x y = (A.mul i i).app X y x) :
    (prod.lift prod.snd prod.fst :
          pieceSheaf A i ⨯ pieceSheaf A i ⟶ pieceSheaf A i ⨯ pieceSheaf A i) ≫
        mulSheafHom A i i =
      mulSheafHom A i i := by
  refine hom_ext_sections fun V s ↦ ?_
  have hs : s = Functor.prodObjMk ((sectionsFunctor K V).map prod.fst s)
      ((sectionsFunctor K V).map prod.snd s) :=
    (Functor.prodObjMk_map_fst_map_snd s).symm
  rw [Functor.map_comp_apply, Functor.map_lift_apply, sections_mulSheafHom]
  conv_rhs => rw [hs]
  rw [sections_mulSheafHom]
  exact hc V _ _

end Operations

section Transport

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O : Sheaf K RingCat.{w'}} (A : SheafOfModules.GradedAlgebra.{w', w'} O)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **A transport inherits commutativity of the multiplication in two equal degrees.**  The
transported multiplication is the image of
`Stacks.Sheaves.GradedAlgebraInverseImage.mulSheafHom` under a finite-product-preserving functor
to types, so the symmetry of that morphism of sheaves of sets is carried along. -/
public theorem transportMulApp_comm (i : ℤ)
    (hc : ∀ (X : Dᵒᵖ) (x y : (A.piece i).val.obj X),
      (A.mul i i).app X x y = (A.mul i i).app X y x)
    (X : Cᵒᵖ) (x y : (transportSections J Φ X).obj (pieceSheaf A i)) :
    transportMulApp J Φ A i i X x y = transportMulApp J Φ A i i X y x := by
  have hm := mulSheafHom_comm A i hc
  change (transportSections J Φ X).map (mulSheafHom A i i) (Functor.prodObjMk x y) =
    (transportSections J Φ X).map (mulSheafHom A i i) (Functor.prodObjMk y x)
  conv_lhs => rw [← hm]
  rw [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_snd_prodObjMk,
    Functor.map_fst_prodObjMk]

/-- **A transported sheaf of graded algebras inherits commutativity of the degree-`(1,1)`
multiplication.** -/
public theorem transportGradedAlgebra_mul_one_one_comm
    (hc : ∀ (X : Dᵒᵖ) (x y : (A.piece 1).val.obj X),
      (A.mul 1 1).app X x y = (A.mul 1 1).app X y x)
    (X : Cᵒᵖ) (x y : ((transportGradedAlgebra J Φ A).piece 1).val.obj X) :
    ((transportGradedAlgebra J Φ A).mul 1 1).app X x y =
      ((transportGradedAlgebra J Φ A).mul 1 1).app X y x :=
  transportMulApp_comm J Φ A 1 hc X x y

end Transport

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'}) (A : SheafOfModules.GradedAlgebra.{w', w'} O)

/-- **The inverse image of a sheaf of graded algebras inherits commutativity of the degree-`(1,1)`
multiplication.** -/
public theorem inverseImageGradedAlgebra_mul_one_one_comm
    (hc : ∀ (X : Dᵒᵖ) (x y : (A.piece 1).val.obj X),
      (A.mul 1 1).app X x y = (A.mul 1 1).app X y x)
    (X : Cᵒᵖ) (x y : ((inverseImageGradedAlgebra f O A).piece 1).val.obj X) :
    ((inverseImageGradedAlgebra f O A).mul 1 1).app X x y =
      ((inverseImageGradedAlgebra f O A).mul 1 1).app X y x := by
  have : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  exact transportGradedAlgebra_mul_one_one_comm J f.inverseImage A hc X x y

end InverseImage

end Stacks.Sheaves.GradedAlgebraInverseImage

/-! ### Extension of scalars -/

namespace Stacks.Sheaves.GradedAlgebraExtendScalars

universe v u w

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (J : GrothendieckTopology C)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf O₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf O₂))
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Extension of scalars inherits commutativity of the degree-`(1,1)` multiplication.**  At the
presheaf level the multiplication is the base change `(a ⊗ x)(c ⊗ y) = ac ⊗ xy`, which is
symmetric; sheafification preserves that. -/
public theorem extendScalarsGradedAlgebra_mul_one_one_comm
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁))
    (hc : ∀ (X : Cᵒᵖ) (x y : (B.piece 1).val.obj X),
      (B.mul 1 1).app X x y = (B.mul 1 1).app X y x)
    (U : Cᵒᵖ) (s u : ((extendScalarsGradedAlgebra θ J h₁ h₂ B).piece 1).val.obj U) :
    ((extendScalarsGradedAlgebra θ J h₁ h₂ B).mul 1 1).app U s u =
      ((extendScalarsGradedAlgebra θ J h₁ h₂ B).mul 1 1).app U u s :=
  Stacks.GradedAlgebra.sheafify_mul_one_one_comm
    (𝟙 (commRingSheaf J O₂ h₂).obj)
    (changeOfRingsGradedAlgebra θ (forgetSheaf J h₁ B))
    (fun X x y ↦ cofBil_app_comm θ (B.mul 1 1) hc X x y) U s u

end Stacks.Sheaves.GradedAlgebraExtendScalars

/-! ### The pullback along a morphism of ringed topoi -/

namespace Stacks.Sheaves.GradedAlgebraPullback

universe w v u

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **The pullback of a sheaf of graded algebras inherits commutativity of the degree-`(1,1)`
multiplication.**  The pullback is the inverse image followed by extension of scalars, and both
steps preserve commutativity in two equal degrees.

This is the hypothesis that `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` asks of a
degree-one generator, so a pullback of a sheaf of graded algebras with commutative degree-one
multiplication receives a canonical homomorphism from the symmetric algebra on its degree-one
piece. -/
public theorem toposPullbackGradedAlgebra_mul_one_one_comm
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hc : ∀ (V : Y.Cᵒᵖ) (x y : (B.piece 1).val.obj V),
      (B.mul 1 1).app V x y = (B.mul 1 1).app V y x)
    (U : X.Cᵒᵖ) (s u : ((toposPullbackGradedAlgebra f B).piece 1).val.obj U) :
    ((toposPullbackGradedAlgebra f B).mul 1 1).app U s u =
      ((toposPullbackGradedAlgebra f B).mul 1 1).app U u s := by
  refine Stacks.Sheaves.GradedAlgebraExtendScalars.extendScalarsGradedAlgebra_mul_one_one_comm
    (fSharpCommRing f) X.J _ _
    (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) ?_ U s u
  exact fun V x y ↦
    inverseImageGradedAlgebra_mul_one_one_comm f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B hc V x y

end Stacks.Sheaves.GradedAlgebraPullback

end
