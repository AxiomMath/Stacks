module

public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupWithCohomologyClass
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductAssociativity
import StacksCore.Tactic.StacksAttribute

/-!
# Cup product with a cohomology class and the global Künneth map

Let `a : X ⟶ S` and `b : Y ⟶ S` be two spaces over a base `S`, let `p : W ⟶ X`, `q : W ⟶ Y`
and `f : W ⟶ S` with `p ≫ a = f = q ≫ b`; the source takes `W = X ×_S Y`.  Set
`A = Γ(S, 𝒪_S)`.  For `ℱ, 𝒢 ∈ D(𝒪_X)`, `ℰ ∈ D(𝒪_Y)` and a class `ξ ∈ Hⁱ(X, 𝒢)` the square

```
RΓ(X, ℱ)[-i] ⊗^𝐋_A RΓ(Y, ℰ) --ξ ⊗ 1--> RΓ(X, 𝒢 ⊗^𝐋 ℱ) ⊗^𝐋_A RΓ(Y, ℰ)
           |                                            |
           v                                            v
RΓ(W, Lp^*ℱ ⊗^𝐋 Lq^*ℰ)[-i] --p^*ξ--> RΓ(W, Lp^*(𝒢 ⊗^𝐋 ℱ) ⊗^𝐋 Lq^*ℰ)
```

commutes in `D(A)`, the horizontal maps being cup product with a class as in Remark 0G6W and
the vertical maps the global Künneth map of Equation 36.23.0.2.  This is Remark 0G7W.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.SectionsOverBaseComparison` — **the parameter**: a
  left adjoint of `RΓ(V, -) : D(𝒪_V) ⥤ D(A)` for a space `V` over the base, together with a
  comparison of bifunctors.  For `V = S` this is
  `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison`, from which the global cup
  product of Section 0FKU is built; here the same datum is taken for a space over the base, so
  that the cup products are `A`-linear as they are in the source.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOverBase` — the `A`-linear global cup
  product `RΓ(V, K) ⊗^𝐋_A RΓ(V, M) ⟶ RΓ(V, K ⊗^𝐋_{𝒪_V} M)` of Section 0FKU.
* `Stacks.Cohomology.DerivedGlobalCupProduct.classOverBase` — the morphism `A[-i] ⟶ RΓ(V, K)`
  representing a class in `Hⁱ(V, K)`, read `A`-linearly.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClassOverBase` — the map `ξ ∪ -` of
  Remark 0G6W, `A`-linearly: the horizontal arrows of the square.
* `Stacks.Cohomology.DerivedGlobalCupProduct.kunnethOverBase` — the global Künneth map in the
  shape in which Equation 36.23.0.2 is defined in the source, namely pulling back on derived
  global sections followed by the cup product on `W`: the vertical arrows of the square.
* `Stacks.Cohomology.DerivedGlobalCupProduct.CupProductPullbackCompatible` — the compatibility
  of the cup products on `X` and on `W` with the pullback map on derived global sections.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_cupClass_square` — the
  abstract form, and where the mathematics is.  For an adjunction `L ⊣ R`, bifunctors `A` and
  `B`, a comparison `α`, associativity constraints for `A` and `B` and three morphisms
  `u : Z ⟶ R G₁`, `x : P ⟶ R G₂`, `y : Q ⟶ R G₃`, contracting `u` against `x` and then against
  `y` agrees with contracting `x` against `y` first and `u` last.  It is deduced from the
  associativity `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_assoc` of
  the cup product, Tag 0FP4, which is the source's own reason for Remark 0G7W.
* `Stacks.Cohomology.DerivedGlobalCupProduct.kunnethOverBase_cupWithClassOverBase` — **Remark
  0G7W**: the square commutes.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupWithClassOverBase_eq` and
  `Stacks.Cohomology.DerivedGlobalCupProduct.kunnethOverBase_eq` — the horizontal and vertical
  arrows are the composites the source describes.

## Implementation notes

*The two identifications the source suppresses.*  The source's bottom-right corner is
`RΓ(W, p^*(𝒢 ⊗ ℱ) ⊗ q^*ℰ)`, which is where the right vertical lands, whereas cup product with
`p^*ξ ∈ Hⁱ(W, p^*𝒢)` along the bottom lands in `RΓ(W, p^*𝒢 ⊗ (p^*ℱ ⊗ q^*ℰ))`.  The source
identifies the two silently, by `p^*(𝒢 ⊗ ℱ) = p^*𝒢 ⊗ p^*ℱ` and by dropping brackets.  Here both
are honest arrows out of the source's corner into the second object: the derived
pullback–tensor comparison of Tag 079U, which in this development is a *morphism* and not an
isomorphism, and the associativity constraint.  So the square below is the source's square with
the right-hand route continued by those two canonical maps; nothing is absorbed into a
transport.

*What is carried and what is proved.*  Three things are parameters, and each of them is a
parameter elsewhere in this development for the same reason:

* `SectionsOverBaseComparison` on `X` and on `W`, which produce the two cup products.  For the
  base itself this is `OnePointComparison`, the datum
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/GlobalCupProduct.lean` already
  carries because the identification of modules on the one-point space `(pt, A)` with
  `A`-modules is absent; for a space over the base the same is true of the composite to that
  point.
* the pullback map `π` on derived global sections together with its compatibility
  `CupProductPullbackCompatible` with the two cup products.  That compatibility is a *different*
  result, Cohomology, Lemma 0FP6 — the relative cup product for a composite is the one for the
  outer morphism followed by the pushforward of the one for the inner morphism, whose abstract
  form `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap_comp` this repository
  has — read for `W ⟶ X ⟶ S ⟶ pt`.  Transporting it onto the two cup products here needs the
  compatibility of the comparison of Tag 079U with composition, recorded as absent in the
  implementation notes of
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductComposition.lean`,
  so it is the hypothesis `hπ`.
* the associativity constraints `aA` on `⊗^𝐋_A` and `aB` on `⊗^𝐋_{𝒪_W}`, their naturality, and
  the compatibility `hα` of the comparison with them.  These are universally quantified, so the
  statement is stronger for it, and they are not vacuous: an associator for `⊗^𝐋_A` with exactly
  the stated naturality is Tag 0BYJ
  (`CochainComplex.DerivedTensor.derivedTensorProduct_associator`), one for `⊗^𝐋_{𝒪_W}` is
  `Stacks.Cohomology.DerivedRelativeCupProduct.derivedAssociator` of Tag 0FPB with naturality
  `derivedAssociator_naturality`, and `hα` is, for the comparison of the parameter, the exact
  analogue of
  `Stacks.Cohomology.DerivedRelativeCupProduct.PullbackTensorComparisonAssociative`, which Tag
  0FP4 proves in this repository
  (`Stacks.Cohomology.DerivedRelativeCupProduct.pullbackTensorComparisonAssociative`).

Everything else is proved: the reduction of the square to the associativity of the cup product,
which is the source's one-line argument, and the shift bookkeeping.

*The shift.*  The source's corners `RΓ(X, ℱ)[-i]` and `RΓ(W, p^*ℱ ⊗ q^*ℰ)[-i]` are the corners
of the square below, and the identification `A[-i] ⊗^𝐋_A N = N[-i]` through which cup product
with a class is defined is `Stacks.Cohomology.DerivedGlobalCupProduct.baseShiftTensorIso`, taken
at the base ring.  It occurs twice in the left vertical and once in each horizontal, exactly as
in the source.

*Spaces rather than schemes.*  As in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/GlobalKunnethMap.lean`, the
statement is for morphisms of ringed spaces with the two projections taken as data, of which a
cartesian square of schemes is an instance; the fibre product plays no role.  The
factorizations `p ≫ a = f = q ≫ b` enter only through the pullback maps `π` and `ρ` on derived
global sections, which are data here.

## References

* [Stacks Project, Tag 0G7W](https://stacks.math.columbia.edu/tag/0G7W)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0G6W](https://stacks.math.columbia.edu/tag/0G6W)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP6](https://stacks.math.columbia.edu/tag/0FP6)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedRelativeCupProduct

/-! ### The abstract square -/

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The abstract form of Remark 0G7W.**  Let `aA` and `aB` be associativity constraints for
the two bifunctors, both natural (`haA`, `haB`), and let the comparison `α` be compatible with
them (`hα`, the associativity law of a monoidal functor).  Given `u : Z ⟶ R G₁`,
`x : P ⟶ R G₂` and `y : Q ⟶ R G₃`, contracting `u` against `x` by the abstract relative cup
product of Tag 0B68 and then contracting the result against `y` agrees with contracting `x`
against `y` first and `u` last.  With `u` the morphism representing a cohomology class and `x`,
`y` pullback maps on derived global sections this is the commutativity of the square of Remark
0G7W; it is deduced from the associativity of the cup product, which is the source's own
reason. -/
theorem adjunctionBitensorMap_cupClass_square
    (aA : ∀ P Q Z : C, A.obj (A.obj (P, Q), Z) ⟶ A.obj (P, A.obj (Q, Z)))
    (aB : ∀ U V Z : D, B.obj (B.obj (U, V), Z) ⟶ B.obj (U, B.obj (V, Z)))
    (haA : ∀ {P P' Q Q' Z Z' : C} (u : P ⟶ P') (v : Q ⟶ Q') (w : Z ⟶ Z'),
      A.map (A.map (u ×ₘ v) ×ₘ w) ≫ aA P' Q' Z' = aA P Q Z ≫ A.map (u ×ₘ A.map (v ×ₘ w)))
    (haB : ∀ {U U' V V' Z Z' : D} (u : U ⟶ U') (v : V ⟶ V') (w : Z ⟶ Z'),
      B.map (B.map (u ×ₘ v) ×ₘ w) ≫ aB U' V' Z' = aB U V Z ≫ B.map (u ×ₘ B.map (v ×ₘ w)))
    (hα : ∀ P Q Z : C,
      α.app (A.obj (P, Q), Z) ≫ B.map (α.app (P, Q) ×ₘ 𝟙 (L.obj Z)) ≫
          aB (L.obj P) (L.obj Q) (L.obj Z) =
        L.map (aA P Q Z) ≫ α.app (P, A.obj (Q, Z)) ≫ B.map (𝟙 (L.obj P) ×ₘ α.app (Q, Z)))
    (G₁ G₂ G₃ : D) {Z P Q : C} (u : Z ⟶ R.obj G₁) (x : P ⟶ R.obj G₂) (y : Q ⟶ R.obj G₃) :
    A.map (A.map (u ×ₘ x) ×ₘ y) ≫
        A.map (adjunctionBitensorMap adj A B α G₁ G₂ ×ₘ 𝟙 (R.obj G₃)) ≫
          adjunctionBitensorMap adj A B α (B.obj (G₁, G₂)) G₃ ≫ R.map (aB G₁ G₂ G₃) =
      aA Z P Q ≫
        A.map (u ×ₘ (A.map (x ×ₘ y) ≫ adjunctionBitensorMap adj A B α G₂ G₃)) ≫
          adjunctionBitensorMap adj A B α G₁ (B.obj (G₂, G₃)) := by
  rw [adjunctionBitensorMap_assoc adj A B α aA aB haB hα G₁ G₂ G₃,
    reassoc_of% haA u x y,
    ← Category.assoc (A.map (u ×ₘ A.map (x ×ₘ y)))
      (A.map (𝟙 (R.obj G₁) ×ₘ adjunctionBitensorMap adj A B α G₂ G₃))
      (adjunctionBitensorMap adj A B α G₁ (B.obj (G₂, G₃))),
    ← A.map_comp, prod_comp, Category.comp_id]

end Abstract

end Stacks.Cohomology.DerivedRelativeCupProduct

namespace Stacks.Cohomology.DerivedGlobalCupProduct

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Identities for a bifunctor on a product category -/

section Bifunctor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] (B : C₁ × C₂ ⥤ C₃)

/-- A triple composition in the first factor of a bifunctor splits around the morphism in the
second factor. -/
private lemma mapProdSplit₃ {P₀ P₁ P₂ P₃ : C₁} {Q Q' : C₂} (g₁ : P₀ ⟶ P₁) (g₂ : P₁ ⟶ P₂)
    (g₃ : P₂ ⟶ P₃) (h : Q ⟶ Q') :
    B.map ((g₁ ≫ g₂ ≫ g₃) ×ₘ h) =
      B.map (g₁ ×ₘ 𝟙 Q) ≫ B.map (g₂ ×ₘ h) ≫ B.map (g₃ ×ₘ 𝟙 Q') := by
  rw [← B.map_comp, ← B.map_comp, prod_comp, prod_comp, Category.id_comp, Category.comp_id]

/-- `mapProdSplit₃` in a longer composition. -/
private lemma mapProdSplit₃_comp {P₀ P₁ P₂ P₃ : C₁} {Q Q' : C₂} (g₁ : P₀ ⟶ P₁) (g₂ : P₁ ⟶ P₂)
    (g₃ : P₂ ⟶ P₃) (h : Q ⟶ Q') {E : C₃} (k : B.obj (P₃, Q') ⟶ E) :
    B.map (g₁ ×ₘ 𝟙 Q) ≫ B.map (g₂ ×ₘ h) ≫ B.map (g₃ ×ₘ 𝟙 Q') ≫ k =
      B.map ((g₁ ≫ g₂ ≫ g₃) ×ₘ h) ≫ k := by
  rw [mapProdSplit₃ B g₁ g₂ g₃ h]
  simp only [Category.assoc]

/-- The two factors of a bifunctor can be contracted in either order, in a longer
composition. -/
private lemma mapProdSwap_comp {P P' : C₁} {Q Q' : C₂} (u : P ⟶ P') (w : Q ⟶ Q') {E : C₃}
    (k : B.obj (P', Q') ⟶ E) :
    B.map (𝟙 P ×ₘ w) ≫ B.map (u ×ₘ 𝟙 Q') ≫ k = B.map (u ×ₘ w) ≫ k := by
  rw [← Category.assoc, ← B.map_comp, prod_comp, Category.id_comp, Category.comp_id]

end Bifunctor

/-! ### The `A`-linear cup product on a space over the base -/

/-- **The one-point comparison for a space over the base**, the one input of the `A`-linear
global cup product that this repository does not construct.  For `c : V ⟶ S` it consists of a
functor `L : D(A) ⥤ D(𝒪_V)` for `A = Γ(S, 𝒪_S)`, an adjunction `L ⊣ RΓ(V, -)` and a comparison
of bifunctors `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_V} L y`.

This is what the source's identification `D(pt, A) = D(A)` supplies for the composite
`V ⟶ S ⟶ (pt, A)`.  For `c = 𝟙 S` it is `OnePointComparison S`. -/
structure SectionsOverBaseComparison {S V : RingedSpace.{u, u}} (c : V ⟶ S) where
  /-- The left adjoint of `RΓ(V, -) : D(𝒪_V) ⥤ D(A)`. -/
  pullback : DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing V))
  /-- The left adjoint is left adjoint to `RΓ(V, -) : D(𝒪_V) ⥤ D(A)`. -/
  adjunction : pullback ⊣ sectionsOverBase c
  /-- The comparison `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_V} L y`, as a morphism of bifunctors. -/
  tensorComparison :
    Functor.uncurry.obj (tensorBase S) ⋙ pullback ⟶
      pullback.prod pullback ⋙ Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf)

variable {S V : RingedSpace.{u, u}} {c : V ⟶ S}

/-- **The `A`-linear global cup product**

`RΓ(V, K) ⊗^𝐋_A RΓ(V, M) ⟶ RΓ(V, K ⊗^𝐋_{𝒪_V} M)`

in `D(A)` for `A = Γ(S, 𝒪_S)` and a space `c : V ⟶ S` over the base: the relative cup product
construction of Tag 0B68 for the adjunction whose right adjoint is `RΓ(V, -)`, which is the
source's definition of the cup product of Section 0FKU as the relative cup product for the
morphism to the one-point space with ring `A`. -/
def cupProductOverBase (κ : SectionsOverBaseComparison c)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    ((tensorBase S).obj ((sectionsOverBase c).obj K)).obj ((sectionsOverBase c).obj M) ⟶
      (sectionsOverBase c).obj (((derivedTensorProductFunctor V.sheaf).obj K).obj M) :=
  adjunctionBitensorMap κ.adjunction (Functor.uncurry.obj (tensorBase S))
    (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf)) κ.tensorComparison K M

/-- The `A`-linear global cup product is natural in both complexes jointly. -/
theorem cupProductOverBase_naturality (κ : SectionsOverBaseComparison c)
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))}
    (k : K ⟶ K') (m : M ⟶ M') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((sectionsOverBase c).map k ×ₘ (sectionsOverBase c).map m) ≫
        cupProductOverBase κ K' M' =
      cupProductOverBase κ K M ≫
        (sectionsOverBase c).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf)).map (k ×ₘ m)) :=
  adjunctionBitensorMap_natural κ.adjunction (Functor.uncurry.obj (tensorBase S))
    (Functor.uncurry.obj (derivedTensorProductFunctor V.sheaf)) κ.tensorComparison k m

/-! ### Cup product with a cohomology class, `A`-linearly -/

/-- `Hⁱ(V, K)` for a space `c : V ⟶ S` over the base, as a module over `A = Γ(S, 𝒪_S)`. -/
abbrev cohomologyModuleOverBase (c : V ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (i : ℤ) :
    ModuleCat.{u} (baseRing S) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).obj
    ((sectionsOverBase c).obj K)

/-- The morphism `A[-i] ⟶ RΓ(V, K)` in `D(A)` representing a class `ξ ∈ Hⁱ(V, K)`, for
`A = Γ(S, 𝒪_S)` and a space `c : V ⟶ S` over the base.  The free module `A` is projective, so
taking `Hⁱ` is an `A`-linear isomorphism `Hom_{D(A)}(A[-i], RΓ(V, K)) ≅ Hⁱ(V, K)` by Tag 06XS;
this is its inverse. -/
def classOverBase (c : V ⟶ S) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (i : ℤ) (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModuleOverBase c K i) :
    baseShift S i ⟶ (sectionsOverBase c).obj K :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
    ((sectionsOverBase c).obj K) i (baseRing S)).symm ξ

/-- **The map `"ξ ∪ -"` of Remark 0G6W, `A`-linearly.**  For a space `c : V ⟶ S` over the base
and a class `ξ ∈ Hⁱ(V, G)` represented by a morphism `A[-i] ⟶ RΓ(V, G)` it is the morphism

`ξ ∪ - : RΓ(V, M)[-i] ⟶ RΓ(V, G ⊗^𝐋_{𝒪_V} M)`

in `D(A)` for `A = Γ(S, 𝒪_S)`, namely the identification `RΓ(V, M)[-i] = A[-i] ⊗^𝐋_A RΓ(V, M)`
followed by `ξ ⊗ 1` and by the `A`-linear cup product of Section 0FKU. -/
def cupWithClassOverBase (κ : SectionsOverBaseComparison c)
    (G M : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (i : ℤ)
    (ξ : baseShift S i ⟶ (sectionsOverBase c).obj G) :
    ((sectionsOverBase c).obj M)⟦-i⟧ ⟶
      (sectionsOverBase c).obj (((derivedTensorProductFunctor V.sheaf).obj G).obj M) :=
  (baseShiftTensorIso S i ((sectionsOverBase c).obj M)).inv ≫
    ((tensorBase S).map ξ).app ((sectionsOverBase c).obj M) ≫ cupProductOverBase κ G M

/-- The composition defining `ξ ∪ -`: the identification `RΓ(V, M)[-i] = A[-i] ⊗^𝐋_A RΓ(V, M)`,
the tensor of `ξ` with the identity, and the `A`-linear cup product of Section 0FKU. -/
theorem cupWithClassOverBase_eq (κ : SectionsOverBaseComparison c)
    (G M : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (i : ℤ)
    (ξ : baseShift S i ⟶ (sectionsOverBase c).obj G) :
    cupWithClassOverBase κ G M i ξ =
      (baseShiftTensorIso S i ((sectionsOverBase c).obj M)).inv ≫
        (Functor.uncurry.obj (tensorBase S)).map (ξ ×ₘ 𝟙 ((sectionsOverBase c).obj M)) ≫
          cupProductOverBase κ G M := by
  unfold cupWithClassOverBase
  rw [uncurry_map_id_right]

/-! ### The global Künneth map as pullback followed by cup product -/

section Kunneth

variable {X Y W : RingedSpace.{u, u}} {a : X ⟶ S} {b : Y ⟶ S} {p : W ⟶ X} {q : W ⟶ Y}
  {f : W ⟶ S}

/-- The derived pullback–tensor comparison `Lp^*(U ⊗^𝐋 V) ⟶ Lp^*U ⊗^𝐋 Lp^*V` of Tag 079U at a
pair of derived modules. -/
abbrev pullbackTensorComparisonApp (p : W ⟶ X)
    (U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback p).obj (((derivedTensorProductFunctor X.sheaf).obj U).obj V) ⟶
      ((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj U)).obj
        ((derivedPullback p).obj V) :=
  (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison p).app (U, V)

/-- **The global Künneth map in the shape in which Equation 36.23.0.2 is defined in the
source**, "pulling back followed by cup product on `W`":

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K) ⊗^𝐋_A RΓ(W, Lq^*M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

in `D(A)` for `A = Γ(S, 𝒪_S)`, for pullback maps `π` and `ρ` on derived global sections and the
`A`-linear cup product on `W` of Section 0FKU. -/
def kunnethOverBase (κ : SectionsOverBaseComparison f)
    (π : ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
      (sectionsOverBase a).obj K ⟶ (sectionsOverBase f).obj ((derivedPullback p).obj K))
    (ρ : ∀ M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      (sectionsOverBase b).obj M ⟶ (sectionsOverBase f).obj ((derivedPullback q).obj M))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((tensorBase S).obj ((sectionsOverBase a).obj K)).obj ((sectionsOverBase b).obj M) ⟶
      (sectionsOverBase f).obj
        (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
          ((derivedPullback q).obj M)) :=
  (Functor.uncurry.obj (tensorBase S)).map (π K ×ₘ ρ M) ≫
    cupProductOverBase κ ((derivedPullback p).obj K) ((derivedPullback q).obj M)

/-- The global Künneth map is the two-step composite of the source: pull back in each tensor
factor, then take the cup product on `W`. -/
theorem kunnethOverBase_eq (κ : SectionsOverBaseComparison f)
    (π : ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
      (sectionsOverBase a).obj K ⟶ (sectionsOverBase f).obj ((derivedPullback p).obj K))
    (ρ : ∀ M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      (sectionsOverBase b).obj M ⟶ (sectionsOverBase f).obj ((derivedPullback q).obj M))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethOverBase κ π ρ K M =
      (Functor.uncurry.obj (tensorBase S)).map (π K ×ₘ ρ M) ≫
        cupProductOverBase κ ((derivedPullback p).obj K) ((derivedPullback q).obj M) :=
  rfl

/-- **The cup products on `X` and on `W` are compatible with pullback.**  For `U, V ∈ D(𝒪_X)`
the square whose horizontal edges are the pullback map `π` on derived global sections and whose
vertical edges are the `A`-linear cup products of Section 0FKU commutes, the right-hand route
being continued by the derived pullback–tensor comparison of Tag 079U.  This is Cohomology,
Lemma 0FP6 for `W ⟶ X ⟶ S ⟶ pt`; see the implementation notes. -/
def CupProductPullbackCompatible (κX : SectionsOverBaseComparison a)
    (κW : SectionsOverBaseComparison f)
    (π : ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
      (sectionsOverBase a).obj K ⟶ (sectionsOverBase f).obj ((derivedPullback p).obj K)) :
    Prop :=
  ∀ U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
    (Functor.uncurry.obj (tensorBase S)).map (π U ×ₘ π V) ≫
        cupProductOverBase κW ((derivedPullback p).obj U) ((derivedPullback p).obj V) =
      cupProductOverBase κX U V ≫
        π (((derivedTensorProductFunctor X.sheaf).obj U).obj V) ≫
          (sectionsOverBase f).map (pullbackTensorComparisonApp p U V)


/-! ### Remark 0G7W -/

variable (κX : SectionsOverBaseComparison a) (κW : SectionsOverBaseComparison f)
  (π : ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
    (sectionsOverBase a).obj K ⟶ (sectionsOverBase f).obj ((derivedPullback p).obj K))
  (ρ : ∀ M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
    (sectionsOverBase b).obj M ⟶ (sectionsOverBase f).obj ((derivedPullback q).obj M))
  (𝒢 ℱ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
  (ℰ : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i : ℤ)

/-- Tensoring `ξ` with the identity and then taking the cup product on `X`, pulling back and
comparing, is tensoring the pulled-back class with the pullback and taking the cup product
on `W`. -/
private theorem cupProduct_pullback_class (hπ : CupProductPullbackCompatible κX κW π)
    (ξ : baseShift S i ⟶ (sectionsOverBase a).obj 𝒢) :
    ((tensorBase S).map ξ).app ((sectionsOverBase a).obj ℱ) ≫
        cupProductOverBase κX 𝒢 ℱ ≫
          π (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ≫
            (sectionsOverBase f).map
              (pullbackTensorComparisonApp p 𝒢 ℱ) =
      (Functor.uncurry.obj (tensorBase S)).map ((ξ ≫ π 𝒢) ×ₘ π ℱ) ≫
        cupProductOverBase κW ((derivedPullback p).obj 𝒢) ((derivedPullback p).obj ℱ) := by
  rw [← hπ 𝒢 ℱ, bifunctor_map_comp_left (Functor.uncurry.obj (tensorBase S)) ξ (π 𝒢) (π ℱ),
    uncurry_map_id_right (tensorBase S) ξ ((sectionsOverBase a).obj ℱ)]
  simp only [Category.assoc]

/-- Cup product with `ξ`, followed by pulling back and by the comparison of Tag 079U, is the
tensor of the pulled-back class with the pullback followed by the cup product on `W`. -/
private theorem cupWithClass_pullback (hπ : CupProductPullbackCompatible κX κW π)
    (ξ : baseShift S i ⟶ (sectionsOverBase a).obj 𝒢) :
    cupWithClassOverBase κX 𝒢 ℱ i ξ ≫
        π (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ≫
          (sectionsOverBase f).map
            (pullbackTensorComparisonApp p 𝒢 ℱ) =
      (baseShiftTensorIso S i ((sectionsOverBase a).obj ℱ)).inv ≫
        (Functor.uncurry.obj (tensorBase S)).map ((ξ ≫ π 𝒢) ×ₘ π ℱ) ≫
          cupProductOverBase κW ((derivedPullback p).obj 𝒢) ((derivedPullback p).obj ℱ) := by
  unfold cupWithClassOverBase
  simp only [Category.assoc]
  rw [cupProduct_pullback_class κX κW π 𝒢 ℱ i hπ ξ]

/-- The right vertical of the square followed by the comparison of Tag 079U: the comparison
crosses the cup product on `W` by naturality. -/
private theorem kunneth_comp_comparison {E : DerivedCategory (ModuleCat.{u} (baseRing S))}
    (k : (sectionsOverBase f).obj
        (((derivedTensorProductFunctor W.sheaf).obj
            (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj 𝒢)).obj
              ((derivedPullback p).obj ℱ))).obj ((derivedPullback q).obj ℰ)) ⟶ E) :
    kunnethOverBase κW π ρ (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ℰ ≫
        (sectionsOverBase f).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
              (pullbackTensorComparisonApp p 𝒢 ℱ ×ₘ 𝟙 ((derivedPullback q).obj ℰ))) ≫
          k =
      (Functor.uncurry.obj (tensorBase S)).map
          (π (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ×ₘ ρ ℰ) ≫
        (Functor.uncurry.obj (tensorBase S)).map
            ((sectionsOverBase f).map
                (pullbackTensorComparisonApp p 𝒢 ℱ) ×ₘ
              𝟙 ((sectionsOverBase f).obj ((derivedPullback q).obj ℰ))) ≫
          cupProductOverBase κW
              (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj 𝒢)).obj
                ((derivedPullback p).obj ℱ))
              ((derivedPullback q).obj ℰ) ≫
            k := by
  have hnat := (congrArg
    (fun z => (Functor.uncurry.obj (tensorBase S)).map
      ((sectionsOverBase f).map (pullbackTensorComparisonApp p 𝒢 ℱ) ×ₘ z) ≫ _)
    (CategoryTheory.Functor.map_id (sectionsOverBase f) ((derivedPullback q).obj ℰ)).symm).trans
    (cupProductOverBase_naturality κW (pullbackTensorComparisonApp p 𝒢 ℱ)
      (𝟙 ((derivedPullback q).obj ℰ)))
  unfold kunnethOverBase
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ k) hnat).trans (Category.assoc _ _ _))).symm

/-- The top edge of the square followed by the right vertical and by the comparison of
Tag 079U, in the shape of the abstract square. -/
private theorem route_top_right (hπ : CupProductPullbackCompatible κX κW π)
    (ξ : baseShift S i ⟶ (sectionsOverBase a).obj 𝒢)
    {E : DerivedCategory (ModuleCat.{u} (baseRing S))}
    (k : (sectionsOverBase f).obj
        (((derivedTensorProductFunctor W.sheaf).obj
            (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj 𝒢)).obj
              ((derivedPullback p).obj ℱ))).obj ((derivedPullback q).obj ℰ)) ⟶ E) :
    (Functor.uncurry.obj (tensorBase S)).map
          (cupWithClassOverBase κX 𝒢 ℱ i ξ ×ₘ 𝟙 ((sectionsOverBase b).obj ℰ)) ≫
        kunnethOverBase κW π ρ (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ℰ ≫
          (sectionsOverBase f).map
              ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
                (pullbackTensorComparisonApp p 𝒢 ℱ ×ₘ 𝟙 ((derivedPullback q).obj ℰ))) ≫
            k =
      (Functor.uncurry.obj (tensorBase S)).map
          ((baseShiftTensorIso S i ((sectionsOverBase a).obj ℱ)).inv ×ₘ
            𝟙 ((sectionsOverBase b).obj ℰ)) ≫
        (Functor.uncurry.obj (tensorBase S)).map
            ((Functor.uncurry.obj (tensorBase S)).map
                ((ξ ≫ π 𝒢) ×ₘ π ℱ) ×ₘ ρ ℰ) ≫
          (Functor.uncurry.obj (tensorBase S)).map
              (cupProductOverBase κW ((derivedPullback p).obj 𝒢)
                  ((derivedPullback p).obj ℱ) ×ₘ
                𝟙 ((sectionsOverBase f).obj ((derivedPullback q).obj ℰ))) ≫
            cupProductOverBase κW
                (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj 𝒢)).obj
                  ((derivedPullback p).obj ℱ))
                ((derivedPullback q).obj ℰ) ≫
              k := by
  refine (congrArg (_ ≫ ·) (kunneth_comp_comparison κW π ρ 𝒢 ℱ ℰ k)).trans ?_
  refine (mapProdSplit₃_comp (Functor.uncurry.obj (tensorBase S)) (cupWithClassOverBase κX 𝒢 ℱ i ξ)
    (π _) ((sectionsOverBase f).map _) (ρ ℰ) _).trans ?_
  refine (congrArg (fun z => (Functor.uncurry.obj (tensorBase S)).map (z ×ₘ ρ ℰ) ≫ _)
    (cupWithClass_pullback κX κW π 𝒢 ℱ i hπ ξ)).trans ?_
  exact (mapProdSplit₃_comp (Functor.uncurry.obj (tensorBase S)) _ _ _ (ρ ℰ) _).symm

/-- The left vertical of the square followed by its bottom edge, in the shape of the abstract
square. -/
private theorem route_left_bottom (ξ : baseShift S i ⟶ (sectionsOverBase a).obj 𝒢) :
    ((tensorBase S).obj (baseShift S i)).map (kunnethOverBase κW π ρ ℱ ℰ) ≫
        (baseShiftTensorIso S i
          ((sectionsOverBase f).obj
            (((derivedTensorProductFunctor W.sheaf).obj
              ((derivedPullback p).obj ℱ)).obj ((derivedPullback q).obj ℰ)))).hom ≫
          cupWithClassOverBase κW ((derivedPullback p).obj 𝒢)
            (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj ℱ)).obj
              ((derivedPullback q).obj ℰ)) i (ξ ≫ π 𝒢) =
      (Functor.uncurry.obj (tensorBase S)).map
          ((ξ ≫ π 𝒢) ×ₘ
            ((Functor.uncurry.obj (tensorBase S)).map (π ℱ ×ₘ ρ ℰ) ≫
              cupProductOverBase κW ((derivedPullback p).obj ℱ)
                ((derivedPullback q).obj ℰ))) ≫
        cupProductOverBase κW ((derivedPullback p).obj 𝒢)
          (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj ℱ)).obj
            ((derivedPullback q).obj ℰ)) := by
  unfold cupWithClassOverBase
  refine (congrArg (_ ≫ ·) (Iso.hom_inv_id_assoc _ _)).trans ?_
  refine (congrArg (· ≫ _) (uncurry_map_id_left (tensorBase S) _ _).symm).trans ?_
  refine (congrArg (_ ≫ · ≫ _) (uncurry_map_id_right (tensorBase S) _ _).symm).trans ?_
  exact mapProdSwap_comp _ _ _ _

/-- **Remark 0G7W.**  Let `a : X ⟶ S` and `b : Y ⟶ S` be spaces over a base, let `p : W ⟶ X`,
`q : W ⟶ Y` and `f : W ⟶ S` with `p ≫ a = f = q ≫ b`, and set `A = Γ(S, 𝒪_S)`.  For
`𝒢, ℱ ∈ D(𝒪_X)`, `ℰ ∈ D(𝒪_Y)` and a class `ξ ∈ Hⁱ(X, 𝒢)` represented by a morphism
`A[-i] ⟶ RΓ(X, 𝒢)`, the square

```
RΓ(X, ℱ)[-i] ⊗^𝐋_A RΓ(Y, ℰ) --ξ ⊗ 1--> RΓ(X, 𝒢 ⊗^𝐋 ℱ) ⊗^𝐋_A RΓ(Y, ℰ)
           |                                            |
           v                                            v
RΓ(W, Lp^*ℱ ⊗^𝐋 Lq^*ℰ)[-i] --p^*ξ--> RΓ(W, Lp^*(𝒢 ⊗^𝐋 ℱ) ⊗^𝐋 Lq^*ℰ)
```

commutes in `D(A)`, the horizontals being cup product with a class as in Remark 0G6W and the
verticals the global Künneth map of Equation 36.23.0.2.  The right-hand route is continued by
the pullback–tensor comparison of Tag 079U and the associativity constraint, the two
identifications the source makes silently in its bottom-right corner. -/
@[stacks 0G7W "the commutativity of the square, for A-linear cup products built from a \
  one-point comparison on X and on W (the parameters `κX`, `κW`, as for Section 0FKU in this \
  development), for the pullback map `π` on derived global sections with its compatibility \
  `hπ` with the two cup products (Cohomology, Lemma 0FP6, which this development cannot \
  transport onto them), and for associativity constraints `aA`, `aB` with their naturality \
  `haA`, `haB` and the compatibility `hα` of the comparison with them, all universally \
  quantified; the source's suppressed identifications p^*(G ⊗ F) = p^*G ⊗ p^*F of Tag 079U and \
  the rebracketing are the last two arrows of the right-hand route"]
theorem kunnethOverBase_cupWithClassOverBase
    (aA : ∀ P Q Z : DerivedCategory (ModuleCat.{u} (baseRing S)),
      ((tensorBase S).obj (((tensorBase S).obj P).obj Q)).obj Z ⟶
        ((tensorBase S).obj P).obj (((tensorBase S).obj Q).obj Z))
    (aB : ∀ U V Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing W)),
      ((derivedTensorProductFunctor W.sheaf).obj
          (((derivedTensorProductFunctor W.sheaf).obj U).obj V)).obj Z ⟶
        ((derivedTensorProductFunctor W.sheaf).obj U).obj
          (((derivedTensorProductFunctor W.sheaf).obj V).obj Z))
    (haA : ∀ {P P' Q Q' Z Z' : DerivedCategory (ModuleCat.{u} (baseRing S))} (k : P ⟶ P')
        (l : Q ⟶ Q') (m : Z ⟶ Z'),
      (Functor.uncurry.obj (tensorBase S)).map
            ((Functor.uncurry.obj (tensorBase S)).map (k ×ₘ l) ×ₘ m) ≫ aA P' Q' Z' =
        aA P Q Z ≫
          (Functor.uncurry.obj (tensorBase S)).map
            (k ×ₘ (Functor.uncurry.obj (tensorBase S)).map (l ×ₘ m)))
    (haB : ∀ {U U' V V' Z Z' : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))}
        (k : U ⟶ U') (l : V ⟶ V') (m : Z ⟶ Z'),
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map (k ×ₘ l) ×ₘ m) ≫
          aB U' V' Z' =
        aB U V Z ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            (k ×ₘ (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map (l ×ₘ m)))
    (hα : ∀ P Q Z : DerivedCategory (ModuleCat.{u} (baseRing S)),
      κW.tensorComparison.app ((Functor.uncurry.obj (tensorBase S)).obj (P, Q), Z) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
              (κW.tensorComparison.app (P, Q) ×ₘ 𝟙 (κW.pullback.obj Z)) ≫
            aB (κW.pullback.obj P) (κW.pullback.obj Q) (κW.pullback.obj Z) =
        κW.pullback.map (aA P Q Z) ≫
          κW.tensorComparison.app (P, (Functor.uncurry.obj (tensorBase S)).obj (Q, Z)) ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
              (𝟙 (κW.pullback.obj P) ×ₘ κW.tensorComparison.app (Q, Z)))
    (hπ : CupProductPullbackCompatible κX κW π)
    (ξ : baseShift S i ⟶ (sectionsOverBase a).obj 𝒢) :
    ((tensorBase S).map (cupWithClassOverBase κX 𝒢 ℱ i ξ)).app
            ((sectionsOverBase b).obj ℰ) ≫
        kunnethOverBase κW π ρ (((derivedTensorProductFunctor X.sheaf).obj 𝒢).obj ℱ) ℰ ≫
          (sectionsOverBase f).map
              ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
                (pullbackTensorComparisonApp p 𝒢 ℱ ×ₘ 𝟙 ((derivedPullback q).obj ℰ))) ≫
            (sectionsOverBase f).map
              (aB ((derivedPullback p).obj 𝒢) ((derivedPullback p).obj ℱ)
                ((derivedPullback q).obj ℰ)) =
      (Functor.uncurry.obj (tensorBase S)).map
          ((baseShiftTensorIso S i ((sectionsOverBase a).obj ℱ)).inv ×ₘ
            𝟙 ((sectionsOverBase b).obj ℰ)) ≫
        aA (baseShift S i) ((sectionsOverBase a).obj ℱ) ((sectionsOverBase b).obj ℰ) ≫
          ((tensorBase S).obj (baseShift S i)).map (kunnethOverBase κW π ρ ℱ ℰ) ≫
            (baseShiftTensorIso S i
              ((sectionsOverBase f).obj
                (((derivedTensorProductFunctor W.sheaf).obj
                  ((derivedPullback p).obj ℱ)).obj ((derivedPullback q).obj ℰ)))).hom ≫
              cupWithClassOverBase κW ((derivedPullback p).obj 𝒢)
                (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj ℱ)).obj
                  ((derivedPullback q).obj ℰ)) i (ξ ≫ π 𝒢) := by
  refine ((congrArg (· ≫ _) (uncurry_map_id_right (tensorBase S) _ _).symm).trans
    (route_top_right κX κW π ρ 𝒢 ℱ ℰ i hπ ξ _)).trans ?_
  refine (congrArg (_ ≫ ·) (adjunctionBitensorMap_cupClass_square κW.adjunction _ _
    κW.tensorComparison aA aB (fun k l m => haA k l m) (fun k l m => haB k l m) hα _ _ _
    (ξ ≫ π 𝒢) (π ℱ) (ρ ℰ))).trans ?_
  exact congrArg (_ ≫ _ ≫ ·) (route_left_bottom κW π ρ 𝒢 ℱ ℰ i ξ).symm

end Kunneth

end Stacks.Cohomology.DerivedGlobalCupProduct

end
