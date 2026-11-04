module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring with the dual of a perfect object computes derived internal Hom

Let `(C, O)` be a ringed site and let `K` be a **perfect** object of `D(O)`, with dual
`K^∨ = RSheafHom(K, O)` (`AlgebraicGeometry.RingedSite.derivedDual`). This file proves two of
the four assertions of **Stacks 08JJ**: for every object `M` of `D(O)` there is an isomorphism

`M ⊗^L_O K^∨ ≅ RSheafHom_O(K, M)`,

functorial in `M` and contravariantly functorial in `K`, and it identifies degree-zero global
hypercohomology with derived-category morphisms,

`H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M)`.

## The route, and why it is not the source's

The source proves the isomorphism by showing that the canonical map
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` of Stacks 08JD is invertible: the
question is local on the site, so `K` may be taken strictly perfect, and then the two sides are
computed degreewise. That route is blocked in this library at a precise point, recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualRepresentatives`: the
chain-level composition morphism of Stacks 0A91, which is what that canonical map is on a K-flat
model, has not been identified with the module-level map
`Stacks.SheafOfModules.tensorDualToSheafHom`.

The isomorphism itself does not need that identification, because the library already has the
same local-to-global argument carried out for a *different* canonical morphism between the same
two objects. The diagonal of Stacks 0BYS,

`A ⊗^L_O RSheafHom(B, L) ⟶ RSheafHom(B, A ⊗^L_O L)`,

is an isomorphism as soon as `B` is perfect — that is Stacks 0ATN,
`AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect`, whose proof is
exactly the locality argument the source performs, with the strictly perfect base case supplied
by `isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand`. Taking `A = M`, `B = K` and
`L = O[0]` the source of the diagonal is `M ⊗^L_O K^∨` on the nose, since
`derivedDual X K = RSheafHom(K, O[0])`, and its target is `RSheafHom(K, M ⊗^L_O O[0])`, which
the right unit constraint of Stacks 0FPT,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`, identifies with
`RSheafHom(K, M)`. Both factors are isomorphisms and both are natural, so the composite is the
functorial isomorphism Stacks 08JJ asserts.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`: **Stacks 08JJ**, the isomorphism
  `M ⊗^L_O K^∨ ≅ RSheafHom_O(K, M)` for perfect `K`.
* `AlgebraicGeometry.RingedSite.derivedDualTensorGlobalSectionsEquiv`: **Stacks 08JJ**, the
  identification `H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M)` as an isomorphism of abelian groups.

## Main results

* `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso_naturality`: **Stacks 08JJ**, that
  isomorphism is natural in `M`, which is the functoriality the source asserts.
* `AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso_naturality_dual`: it is also
  contravariantly natural in `K`, between perfect objects.

## Implementation notes

The derived tensor product is the canonical one,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, whose bifunctor is
`Stacks.SheafOfModules.derivedTensorProductFunctor`; it is instantiated rather than carried as a
parameter because the diagonal of Stacks 0BYS is stated for it. The right unit constraint is
stated in the packaging of a derived tensor product indexed by the structure sheaf rather than
by the ringed site, so `canonicalRingedSiteDerivedTensorProduct` carries the canonical datum
across by `Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct`; every
field is copied, so the two bifunctors are the same functor and no comparison is needed. The
unit object of that packaging, `Stacks.DerivedTensor.RingedSite.unitObject`, is
`AlgebraicGeometry.RingedSite.derivedStructureSheaf`, by
`derivedStructureSheaf_eq_singleFunctor_obj`, which is `rfl`.

The derived internal Hom is the bifunctor `RSheafHom(-, -)` itself,
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, and not the datum
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom`, which is a `Classical.choice`; the
diagonal of Stacks 0BYS and the dual `derivedDual` are both stated for the bifunctor, so the
two meet without a transport.

Both naturality statements are assembled in term mode through `comp_square_row`. Written as a
`dsimp only` of the isomorphism followed by `rw`, the second square leaves a goal that is not
type-correct at the `implicit` transparency level: unfolding the isomorphism exposes the two
spellings `Stacks.DerivedTensor.RingedSite.Modules X.O` and
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)` of the
same category, which are definitionally equal but not syntactically so, and the `rw` motive is
then rejected. The right unit constraint is therefore restated by ascription at the spelling of
the diagonal before it is used.

The universes are the diagonal `RingedSite.{u, u, u}` with the standard derived category, which
is the pin of Stacks 0ATN. It is the same diagonal that
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`, where the first assertion of
Stacks 08JJ lives, is stated at, and for a different reason: that file joins the derived
internal Hom cluster to the strictly perfect *comparison* statements, whose module universe is
forced to be that of the sections of the structure sheaf, while nothing below mentions a
strictly perfect complex — perfectness enters only through
`AlgebraicGeometry.RingedSite.IsPerfect`, which is available at the diagonal pin.

## What this file does not contain

**That the canonical map of Stacks 08JD is this isomorphism.** `derivedTensorDualToSheafHom` is
derived composition of Stacks 0A98 at intermediate object the structure sheaf, while the
isomorphism below is the diagonal of Stacks 0BYS at target object the structure sheaf; the two
are morphisms of the same type and nothing below compares them. In particular the hypothesis of
`AlgebraicGeometry.RingedSite.derivedDualCoevaluation` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing`, which asks for
invertibility of that canonical map at `M = K`, is **not** discharged by what is here, and
neither is the invertibility of the induced map
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap` on global sections. Comparing
them is a chain-level identity between the composition morphism of Stacks 0A91 and the
interchange morphism of Stacks 0BYR, with their Koszul signs, and it is not done here.

**The second assertion of Stacks 08JJ, that `(K^∨)^∨ ≅ K`.** That assertion is not proved here,
but it is in the library: the canonical map `K ⟶ (K^∨)^∨` is
`AlgebraicGeometry.RingedSite.derivedBidual` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidual`, and
`AlgebraicGeometry.RingedSite.isIso_derivedBidual_of_isPerfect` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect` asserts that it is
invertible for a perfect `K`.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- Two commuting squares sharing their middle vertical edge, composed along it. The shape is
the one both naturality statements below have: a square between the two diagonals, followed by
a square between the two unit constraints, the second living entirely in the targets of the
first. -/
private lemma comp_square_row {D : Type*} [Category D] {A A' B B' Z Z' : D}
    {a : A ⟶ A'} {p : A ⟶ B} {p' : A' ⟶ B'} {b : B ⟶ B'} {q : B ⟶ Z} {q' : B' ⟶ Z'}
    {c : Z ⟶ Z'} (h₁ : a ≫ p' = p ≫ b) (h₂ : b ≫ q' = q ≫ c) :
    a ≫ p' ≫ q' = (p ≫ q) ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- The canonical derived tensor product of Stacks 06YU, in the packaging indexed by the
structure sheaf rather than by the ringed site: the packaging the unit constraint of
Stacks 0FPT is stated in. Every field is copied, so its bifunctor is
`Stacks.SheafOfModules.derivedTensorProductFunctor`. -/
abbrev canonicalRingedSiteDerivedTensorProduct :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O :=
  Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u} X)

/-- **Stacks 08JJ: tensoring with the dual of a perfect object is derived internal Hom.** Let
`(C, O)` be a ringed site, let `K` be a perfect object of `D(O)` with dual
`K^∨ = RSheafHom(K, O)`, and let `M` be an arbitrary object of `D(O)`. Then

`M ⊗^L_O K^∨ ≅ RSheafHom_O(K, M)`.

It is the diagonal morphism of Stacks 0BYS at tensor factor `M`, internal-Hom source `K` and
target the structure sheaf in degree zero — invertible by Stacks 0ATN because `K` is perfect,
its source being `M ⊗^L_O RSheafHom(K, O) = M ⊗^L_O K^∨` — followed by the internal Hom out of
`K` of the right unit constraint `M ⊗^L_O O ≅ M` of Stacks 0FPT. -/
@[stacks 08JJ "the isomorphism M ⊗^L_O K^∨ ≅ RSheafHom_O(K, M) for perfect K; not the \
  invertibility of the canonical map of Stacks 08JD, which is a different morphism of the \
  same type"]
def derivedDualTensorSheafHomIso
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj (derivedDual X K) ≅
      ((derivedSheafHomBifunctor X).obj (op K)).obj M :=
  @asIso _ _ _ _ (derivedTensorHomDiagonal X M (derivedStructureSheaf X) K)
      (isIso_derivedTensorHomDiagonal_of_isPerfect X M (derivedStructureSheaf X) K hK) ≪≫
    ((derivedSheafHomBifunctor X).obj (op K)).mapIso
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
        (canonicalRingedSiteDerivedTensorProduct X) M)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 08JJ: the isomorphism is functorial in `M`.** This is the functoriality the source
asserts: the diagonal of Stacks 0BYS is natural in its tensor factor and the right unit
constraint of Stacks 0FPT is natural, so the composite of the two is. -/
@[stacks 08JJ "that isomorphism is functorial in M"]
theorem derivedDualTensorSheafHomIso_naturality
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : M ⟶ M') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app (derivedDual X K) ≫
        (derivedDualTensorSheafHomIso X K M' hK).hom =
      (derivedDualTensorSheafHomIso X K M hK).hom ≫
        ((derivedSheafHomBifunctor X).obj (op K)).map f := by
  have hu : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
          (derivedStructureSheaf X) ≫
        (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
          (canonicalRingedSiteDerivedTensorProduct X) M').hom =
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
          (canonicalRingedSiteDerivedTensorProduct X) M).hom ≫ f :=
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality X
      (canonicalRingedSiteDerivedTensorProduct X) f
  have h₂ := ((((derivedSheafHomBifunctor X).obj (op K)).map_comp _ _).symm.trans
      (congrArg (fun z ↦ ((derivedSheafHomBifunctor X).obj (op K)).map z) hu)).trans
    (((derivedSheafHomBifunctor X).obj (op K)).map_comp _ _)
  exact comp_square_row
    (derivedTensorHomDiagonal_natural_left X (derivedStructureSheaf X) K f) h₂

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 08JJ: the isomorphism is contravariantly functorial in the dualized object.** For a
morphism `g : K' ⟶ K` of perfect objects, the square comparing the two isomorphisms commutes:
the diagonal of Stacks 0BYS is contravariant in the source of its internal Hom, and the right
unit constraint does not involve that variable, so the second square is the naturality of the
transformation induced by `g`. -/
theorem derivedDualTensorSheafHomIso_naturality_dual
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : X.IsPerfect K) (hK' : X.IsPerfect K')
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g : K' ⟶ K) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).map
          (((derivedSheafHomBifunctor X).map g.op).app (derivedStructureSheaf X)) ≫
        (derivedDualTensorSheafHomIso X K' M hK').hom =
      (derivedDualTensorSheafHomIso X K M hK).hom ≫
        ((derivedSheafHomBifunctor X).map g.op).app M := by
  have h₂ : ((derivedSheafHomBifunctor X).map g.op).app
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj
            (derivedStructureSheaf X)) ≫
        ((derivedSheafHomBifunctor X).obj (op K')).map
          (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
            (canonicalRingedSiteDerivedTensorProduct X) M).hom =
      ((derivedSheafHomBifunctor X).obj (op K)).map
          (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
            (canonicalRingedSiteDerivedTensorProduct X) M).hom ≫
        ((derivedSheafHomBifunctor X).map g.op).app M :=
    (((derivedSheafHomBifunctor X).map g.op).naturality
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso X
        (canonicalRingedSiteDerivedTensorProduct X) M).hom).symm
  exact comp_square_row
    (derivedTensorHomDiagonal_natural_hom X M (derivedStructureSheaf X) g) h₂

/-- **Stacks 08JJ: `H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M)` for perfect `K`.** The degree-zero
global hypercohomology of `M ⊗^L_O K^∨` is the group of morphisms `K ⟶ M` in `D(O)`.

It is the degree-zero global hypercohomology of `derivedDualTensorSheafHomIso`, which is an
isomorphism of abelian groups because derived global sections and the degree-zero cohomology
functor both preserve isomorphisms, followed by the identification
`H⁰(C, RSheafHom(K, M)) = Hom_{D(O)}(K, M)` of Stacks 08JA. -/
@[stacks 08JJ "the identification H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M) for perfect K, as an \
  isomorphism of abelian groups; not the bijectivity of the induced map of Stacks 08JD"]
def derivedDualTensorGlobalSectionsEquiv
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedModuleGlobalSections X).obj
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj M).obj
            (derivedDual X K))) : Type u) ≃+ (K ⟶ M) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections X).mapIso
        (derivedDualTensorSheafHomIso X K M hK))).addCommGroupIsoToAddEquiv).trans
    (derivedSheafHomGlobalSectionsEquiv X K M)

end AlgebraicGeometry.RingedSite

end
