module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Cancelling an intermediate coefficient ring in a derived tensor product

Let `(C, J)` be a site and let `O ⟶ O' ⟶ O''` be maps of sheaves of commutative rings on it.
For `K` in `D(O)` and `G` in `D(O'')` the two ways of reading `K ⊗^L G` over the tower agree:

`(K ⊗^L_O O') ⊗^L_{O'} G ≅ K ⊗^L_O G`,

the tensor product over `O'` of an `O''`-module being again read through `O' ⟶ O''`. The
intermediate ring cancels. For a sheaf of ideals `I ⊆ O` and `m ≤ n` this gives

`(K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} G ≅ (K ⊗^L_O O/Iᵐ) ⊗^L_{O/Iᵐ} G`

for `G` in `D(O/Iᵐ)`, and in particular the case `m = 1` comparing the quotients by `Iⁿ` and
by `I`.

## Main definitions

* `Stacks.Cohomology.ChangeOfRingsCancellation.derivedCoefficientChangeCompIso`: the
  composition law `(- ⊗^L_O O') ⊗^L_{O'} O'' ≅ - ⊗^L_O O''` for derived change of
  coefficients.
* `Stacks.Cohomology.ChangeOfRingsCancellation.derivedTensorCancellationIso`,
  `derivedTensorCancellation` and `derivedTensorCancellationModule`: the cancellation of the
  intermediate ring, as a natural isomorphism of functors `D(O) ⥤ D(O'')`, at an object of
  `D(O)`, and for a sheaf of `O''`-modules in degree zero.
* `Stacks.Cohomology.ChangeOfRingsCancellation.adicDerivedTensorCancellationIso`,
  `adicDerivedTensorCancellation`, `adicDerivedTensorCancellationModule` and
  `adicDerivedTensorCancellationOne`: the instance of the cancellation at the tower of quotients
  by the powers of a sheaf of ideals.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.coefficientChange_comp`: a composite of two changes of
  coefficient rings on a fixed site is the change of coefficients along the composite, on the
  nose.
* `Stacks.Cohomology.ChangeOfRingsCancellation.derivedCoefficientChangeCompIso_hom`: the
  composition law is the canonical comparison of Stacks 0D6D, hence is pinned down by the
  Stacks 06YY comparisons of its three derived pullbacks.

## Implementation notes

The derived tensor product of `Stacks.SheafOfModules.DerivedTensorProduct` is a bifunctor on a
single `D(O'')` and carries no change-of-rings datum, so `K ⊗^L_O G` for `K` over `O` and `G`
over `O''` is read here as derived change of coefficients along `O ⟶ O''` followed by derived
tensoring over `O''`. The content of the cancellation is then exactly that derived change of
coefficients is functorial in the map of coefficient sheaves, and that is Stacks 0D6D for the
two morphisms of ringed topoi which the two maps present: the underlying morphism of sites is
the identity functor of `C` in both cases, which is a morphism of sites by
`CategoryTheory.Functor.isMorphismOfSites_id`, so the hypotheses of 0D6D are discharged
outright and the cancellation holds for arbitrary `K` and `G`, with no flatness or boundedness
assumption.

That the composite of the two presenting morphisms of ringed topoi is the one presenting
`α ≫ β` is `coefficientChange_comp`, and it holds by `rfl`: the underlying functors are the
identity of `C`, whose composite is again the identity, and the structure map of a composite is
the first structure map followed by the direct image of the second, both direct images being the
identity functor of the category of sheaves.

No `@[stacks]` attribute is placed. The composition formula is Stacks 0D6D, which is tagged
where it is proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi`, and the
statements below are its instance at a change of coefficients together with the specialisation
to the adic tower; neither is an assertion of the source. Stacks 0942 consumes the adic
specialisation but asserts something else, and the change-of-rings tags 03EX and 06YY concern
exactness and the comparison with degreewise pullback.

The universes collapse to one: that is inherited from the derived pullback of ringed topoi,
which is stated for `AlgebraicGeometry.RingedTopos` with its site, its hom types and the
sections of its structure sheaf in a single universe.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

universe u

namespace AlgebraicGeometry.RingedToposSiteHom

/-- **Changes of coefficient rings on a fixed site compose.** The morphism of ringed topoi
presenting `α ≫ β` is the composite of the ones presenting `α` and `β`: both underlying
functors are the identity of the site, and the direct image along the identity is the identity
functor of the category of sheaves, so no comparison intervenes. -/
theorem coefficientChange_comp {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {O O' O'' : Sheaf J CommRingCat.{u}} (α : O ⟶ O') (β : O' ⟶ O'') :
    (coefficientChange.{u, u, u} J α).comp (coefficientChange.{u, u, u} J β) =
      coefficientChange.{u, u, u} J (α ≫ β) :=
  rfl

end AlgebraicGeometry.RingedToposSiteHom

namespace Stacks.Cohomology.ChangeOfRingsCancellation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Composition

variable {O O' O'' : Sheaf J CommRingCat.{u}}

/-- **The derived pullback along a composite of coefficient changes exists.** By
`AlgebraicGeometry.RingedToposSiteHom.coefficientChange_comp` the composite is itself a
coefficient change, so this is the existence instance for one; it is restated at the composite
spelling because `AlgebraicGeometry.RingedToposSiteHom.comp` does not unfold at instance
transparency. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientChange_comp (α : O ⟶ O')
    (β : O' ⟶ O'') :
    (pullbackOnHomotopy ((RingedToposSiteHom.coefficientChange.{u, u, u} J α).comp
        (RingedToposSiteHom.coefficientChange.{u, u, u} J β))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientChange (α ≫ β)

/-- **Derived change of coefficients is functorial**: `(K ⊗^L_O O') ⊗^L_{O'} O''` is
`K ⊗^L_O O''`, naturally in `K`.

This is Stacks 0D6D for the two morphisms of ringed topoi presenting `α` and `β`, whose
underlying morphism of sites is in both cases the identity functor of the site. -/
def derivedCoefficientChangeCompIso (α : O ⟶ O') (β : O' ⟶ O'') :
    derivedCoefficientChange α ⋙ derivedCoefficientChange β ≅
      derivedCoefficientChange (α ≫ β) :=
  derivedPullbackCompIso (RingedToposSiteHom.coefficientChange.{u, u, u} J β)
    (RingedToposSiteHom.coefficientChange.{u, u, u} J α)
    (Functor.isMorphismOfSites_id J) (Functor.isMorphismOfSites_id J)

/-- The composition law is the canonical comparison of Stacks 0D6D: it is the unique map whose
composite with the Stacks 06YY comparison for `α ≫ β` is the Stacks 06YY comparison for `α`,
then the one for `β`, then the underived composition isomorphism. That characterisation is
`derivedPullbackCompComparison_comp_derivedPullbackComparison` of
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi`, and this identification is what makes it
available for the present isomorphism. -/
@[simp]
theorem derivedCoefficientChangeCompIso_hom (α : O ⟶ O') (β : O' ⟶ O'') :
    (derivedCoefficientChangeCompIso α β).hom =
      derivedPullbackCompComparison (RingedToposSiteHom.coefficientChange.{u, u, u} J β)
        (RingedToposSiteHom.coefficientChange.{u, u, u} J α) :=
  rfl

/-- The composition law for derived change of coefficients, stated against a given name `γ` for
the composite `α ≫ β`. This is the form a tower of coefficient rings consumes, the tower
providing the identification of the composite with one of its own maps. -/
def derivedCoefficientChangeCompIsoOfEq (α : O ⟶ O') (β : O' ⟶ O'') (γ : O ⟶ O'')
    (hγ : α ≫ β = γ) :
    derivedCoefficientChange α ⋙ derivedCoefficientChange β ≅ derivedCoefficientChange γ := by
  subst hγ
  exact derivedCoefficientChangeCompIso α β

/-- The composition law for derived change of coefficients at an object of `D(O)`. -/
def derivedCoefficientChangeCompObjIso (α : O ⟶ O') (β : O' ⟶ O'')
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))) :
    (derivedCoefficientChange β).obj ((derivedCoefficientChange α).obj K) ≅
      (derivedCoefficientChange (α ≫ β)).obj K :=
  (derivedCoefficientChangeCompIso α β).app K

end Composition

section Cancellation

open Stacks.SheafOfModules AlgebraicGeometry.RingedSite

variable {O O' O'' : Sheaf J CommRingCat.{u}}
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O'').Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O'').obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u, u} (ringedTopos J O'').toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor O'') (ComplexShape.up ℤ)]

/-- Derived tensoring over `O''` with a fixed second factor `G`, that is `E ↦ E ⊗^L_{O''} G`. -/
abbrev derivedTensorRight (T : DerivedTensorProduct (ringedTopos J O'').toRingedSite)
    (G : DerivedModules (ringedTopos J O'').toRingedSite) :
    DerivedModules (ringedTopos J O'').toRingedSite ⥤
      DerivedModules (ringedTopos J O'').toRingedSite :=
  T.tensor.flip.obj G

/-- **The change-of-rings cancellation.** For maps `α : O ⟶ O'` and `β : O' ⟶ O''` of sheaves of
commutative rings on a fixed site and `G` in `D(O'')`,

`(K ⊗^L_O O') ⊗^L_{O'} G ≅ K ⊗^L_O G`,

naturally in `K`, where tensoring over `O'` with the `O''`-module `G` means derived change of
coefficients along `β` followed by derived tensoring over `O''`. No flatness or boundedness
hypothesis enters.

The composite `α ≫ β` is named by the parameter `γ`, so that a tower of coefficient rings can
supply its own identification of the composite; `derivedTensorCancellationIso` below is the case
`γ = α ≫ β`. -/
def derivedTensorCancellationIsoOfEq (α : O ⟶ O') (β : O' ⟶ O'') (γ : O ⟶ O'')
    (hγ : α ≫ β = γ) (T : DerivedTensorProduct (ringedTopos J O'').toRingedSite)
    (G : DerivedModules (ringedTopos J O'').toRingedSite) :
    derivedCoefficientChange α ⋙ derivedCoefficientChange β ⋙ derivedTensorRight T G ≅
      derivedCoefficientChange γ ⋙ derivedTensorRight T G :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedCoefficientChangeCompIsoOfEq α β γ hγ)
      (derivedTensorRight T G)

/-- **The change-of-rings cancellation**, with the intermediate ring cancelled against the
composite `α ≫ β`: `(K ⊗^L_O O') ⊗^L_{O'} G ≅ K ⊗^L_O G`, naturally in `K`. -/
def derivedTensorCancellationIso (α : O ⟶ O') (β : O' ⟶ O'')
    (T : DerivedTensorProduct (ringedTopos J O'').toRingedSite)
    (G : DerivedModules (ringedTopos J O'').toRingedSite) :
    derivedCoefficientChange α ⋙ derivedCoefficientChange β ⋙ derivedTensorRight T G ≅
      derivedCoefficientChange (α ≫ β) ⋙ derivedTensorRight T G :=
  derivedTensorCancellationIsoOfEq α β (α ≫ β) rfl T G

/-- The change-of-rings cancellation at an object `K` of `D(O)`:
`(K ⊗^L_O O') ⊗^L_{O'} G ≅ K ⊗^L_O G`. -/
def derivedTensorCancellation (α : O ⟶ O') (β : O' ⟶ O'')
    (T : DerivedTensorProduct (ringedTopos J O'').toRingedSite)
    (G : DerivedModules (ringedTopos J O'').toRingedSite)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))) :
    (T.tensor.obj
          ((derivedCoefficientChange β).obj ((derivedCoefficientChange α).obj K))).obj G ≅
      (T.tensor.obj ((derivedCoefficientChange (α ≫ β)).obj K)).obj G :=
  (derivedTensorCancellationIso α β T G).app K

/-- The change-of-rings cancellation for a sheaf of `O''`-modules `G`, read in degree zero:
`(K ⊗^L_O O') ⊗^L_{O'} G ≅ K ⊗^L_O G`. -/
def derivedTensorCancellationModule (α : O ⟶ O') (β : O' ⟶ O'')
    (T : DerivedTensorProduct (ringedTopos J O'').toRingedSite)
    (G : Modules.{u, u, u} (ringedTopos J O'').toRingedSite)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))) :
    (T.tensor.obj
          ((derivedCoefficientChange β).obj ((derivedCoefficientChange α).obj K))).obj
        ((DerivedCategory.singleFunctor
          (Modules.{u, u, u} (ringedTopos J O'').toRingedSite) 0).obj G) ≅
      (T.tensor.obj ((derivedCoefficientChange (α ≫ β)).obj K)).obj
        ((DerivedCategory.singleFunctor
          (Modules.{u, u, u} (ringedTopos J O'').toRingedSite) 0).obj G) :=
  derivedTensorCancellation α β T _ K

end Cancellation

section Adic

open Stacks.SheafOfModules Stacks.Sites AlgebraicGeometry.RingedSite

variable [HasWeakSheafify J CommRingCat.{u}] {O : Sheaf J CommRingCat.{u}}

/-- **The cancellation along the tower of quotients by the powers of a sheaf of ideals.** For
`m ≤ n` and `G` in `D(O/Iᵐ)`,

`(K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} G ≅ (K ⊗^L_O O/Iᵐ) ⊗^L_{O/Iᵐ} G`,

naturally in `K`: the two factorisations of `O ⟶ O/Iᵐ` through the tower give the same functor,
by `Stacks.Sites.toAdicQuotient_comp_adicQuotientMap`. -/
def adicDerivedTensorCancellationIso (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (adicQuotient I m)).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (adicQuotient I m)).obj M).Additive]
    [∀ (K L : CochainComplex
        (Modules.{u, u, u} (ringedTopos J (adicQuotient I m)).toRingedSite) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (adicQuotient I m)) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct (ringedTopos J (adicQuotient I m)).toRingedSite)
    (G : DerivedModules (ringedTopos J (adicQuotient I m)).toRingedSite) :
    derivedCoefficientChange (toAdicQuotient I n) ⋙
        derivedCoefficientChange (adicQuotientMap I h) ⋙ derivedTensorRight T G ≅
      derivedCoefficientChange (toAdicQuotient I m) ⋙ derivedTensorRight T G :=
  derivedTensorCancellationIsoOfEq (toAdicQuotient I n) (adicQuotientMap I h)
    (toAdicQuotient I m) (toAdicQuotient_comp_adicQuotientMap I h) T G

/-- The adic cancellation at an object `K` of `D(O)`. -/
def adicDerivedTensorCancellation (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (adicQuotient I m)).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (adicQuotient I m)).obj M).Additive]
    [∀ (K L : CochainComplex
        (Modules.{u, u, u} (ringedTopos J (adicQuotient I m)).toRingedSite) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (adicQuotient I m)) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct (ringedTopos J (adicQuotient I m)).toRingedSite)
    (G : DerivedModules (ringedTopos J (adicQuotient I m)).toRingedSite)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))) :
    (T.tensor.obj ((derivedCoefficientChange (adicQuotientMap I h)).obj
          ((derivedCoefficientChange (toAdicQuotient I n)).obj K))).obj G ≅
      (T.tensor.obj ((derivedCoefficientChange (toAdicQuotient I m)).obj K)).obj G :=
  (adicDerivedTensorCancellationIso I h T G).app K

/-- The adic cancellation for a sheaf of `O/Iᵐ`-modules `G`, read in degree zero:

`(K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} G ≅ (K ⊗^L_O O/Iᵐ) ⊗^L_{O/Iᵐ} G`.

At `m = 1` this is the identification used in the proof of Stacks 0942 part (2). -/
def adicDerivedTensorCancellationModule (I : IdealSubsheaf O) {m n : ℕ} (h : m ≤ n)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (adicQuotient I m)).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (adicQuotient I m)).obj M).Additive]
    [∀ (K L : CochainComplex
        (Modules.{u, u, u} (ringedTopos J (adicQuotient I m)).toRingedSite) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (adicQuotient I m)) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct (ringedTopos J (adicQuotient I m)).toRingedSite)
    (G : Modules.{u, u, u} (ringedTopos J (adicQuotient I m)).toRingedSite)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))) :
    (T.tensor.obj ((derivedCoefficientChange (adicQuotientMap I h)).obj
          ((derivedCoefficientChange (toAdicQuotient I n)).obj K))).obj
        ((DerivedCategory.singleFunctor
          (Modules.{u, u, u} (ringedTopos J (adicQuotient I m)).toRingedSite) 0).obj G) ≅
      (T.tensor.obj ((derivedCoefficientChange (toAdicQuotient I m)).obj K)).obj
        ((DerivedCategory.singleFunctor
          (Modules.{u, u, u} (ringedTopos J (adicQuotient I m)).toRingedSite) 0).obj G) :=
  adicDerivedTensorCancellation I h T _ K

/-- The case `m = 1` of the adic cancellation, comparing the quotient by `Iⁿ` with the quotient
by `I`: for `G` in `D(O/I)`,

`(K ⊗^L_O O/Iⁿ) ⊗^L_{O/Iⁿ} G ≅ (K ⊗^L_O O/I) ⊗^L_{O/I} G`. -/
def adicDerivedTensorCancellationOne (I : IdealSubsheaf O) {n : ℕ} (hn : 1 ≤ n)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (adicQuotient I 1)).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (adicQuotient I 1)).obj M).Additive]
    [∀ (K L : CochainComplex
        (Modules.{u, u, u} (ringedTopos J (adicQuotient I 1)).toRingedSite) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (adicQuotient I 1)) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct (ringedTopos J (adicQuotient I 1)).toRingedSite)
    (G : DerivedModules (ringedTopos J (adicQuotient I 1)).toRingedSite)
    (K : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos J O).O))) :
    (T.tensor.obj ((derivedCoefficientChange (adicQuotientMap I hn)).obj
          ((derivedCoefficientChange (toAdicQuotient I n)).obj K))).obj G ≅
      (T.tensor.obj ((derivedCoefficientChange (toAdicQuotient I 1)).obj K)).obj G :=
  adicDerivedTensorCancellation I hn T G K

end Adic

end Stacks.Cohomology.ChangeOfRingsCancellation

end
