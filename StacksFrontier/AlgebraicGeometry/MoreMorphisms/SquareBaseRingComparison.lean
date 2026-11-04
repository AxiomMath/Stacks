module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CartesianSquareStalkLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials

/-!
# The canonical base-ring comparison of a commutative square

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commutative square of schemes.  The base change map of the naive cotangent complex
(`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`) is built from a *comparison*
`bc : (g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}` of sheaves of commutative rings on `X'` together
with the compatibility equation identifying the two towers
`(g')^{-1}f^{-1}𝒪_Y ⟶ (g')^{-1}𝒪_X ⟶ 𝒪_{X'}` and
`(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`.  Existence of such a comparison is
`Stacks.NaiveCotangentFlatBaseChange.exists_baseRingComparison`, and that is all the consumer
needs in order to *have* a base change map; but an existence statement determines nothing about
the stalks of the comparison, and the compatibility equation does not pin the witness down — it
constrains only the two composites into `𝒪_{X'}`.  Anything to be said about the stalk of `bc`
must therefore be said about a *constructed* comparison.

This file supplies that construction and computes its stalks.  The comparison is the composite

`(g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}g^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}`

of the canonical comparison of the two double inverse images of `𝒪_Y` provided by the square
with the inverse image along `f'` of the structure map of `g`.  Only the first factor is new:
the second is `Stacks.SheafOfModules.inverseImageFirstRingMap`, whose stalk is already known
(`AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso_hom_comp_stalkMap`).

## Main definitions

* `Stacks.SheafifyStalk.pullbackCompTranspose`: the adjoint transpose of `F ⟶ q_*p_*N` across
  `p^{-1} ⊣ p_*` and then `q^{-1} ⊣ q_*`, a morphism `p^{-1}q^{-1}F ⟶ N`.
* `Stacks.SheafifyStalk.pullbackSquareUnit`: the unit `F ⟶ (r ≫ s)_*(r^{-1}s^{-1}F)` of the
  composite adjunction `r^{-1}s^{-1} ⊣ s_*r_*`.
* `Stacks.SheafifyStalk.pullbackSquareComparison`: for continuous maps with `p ≫ q = r ≫ s`,
  the canonical comparison `p^{-1}q^{-1}F ⟶ r^{-1}s^{-1}F`, namely `pullbackSquareUnit`
  transported along the equality of the two composites and transposed twice.
* `Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace` and
  `AlgebraicGeometry.BaseChangeStalk.baseRingComparison`: the canonical base-ring comparison of
  a commutative square of ringed spaces, respectively of schemes.

## Main results

* `Stacks.SheafifyStalk.pullbackSquareComparison_comp`: the canonical comparison identifies the
  two factorisations of a structural map; this is the general form of the compatibility
  equation.
* `Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace_comp` and
  `AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp`: hence the canonical comparison
  satisfies the equation `baseChangeMapOfComparison` asks of its comparison argument, so it can
  be fed to that construction in place of a chosen witness.
* `Stacks.SheafifyStalk.pullbackSquareComparison_stalk`: the stalk at `x'` of the canonical
  comparison, read through the identifications of the stalks of the two double inverse images
  with the stalk of `F` at the image point, is the transport along the equality of those two
  image points.
* `AlgebraicGeometry.BaseChangeStalk.stalkFunctor_map_baseRingComparison`: hence the stalk at
  `x'` of the canonical base-ring comparison, read through
  `AlgebraicGeometry.BaseChangeStalk.stalkInverseImageBaseRingIso` and
  `AlgebraicGeometry.BaseChangeStalk.stalkInverseImageSheafIso`, is the stalk map of `g` at
  `f'(x')`, preceded by the transport along the equality of the two images of `x'` in `Y`.

## Implementation notes

The comparison must be built as a double adjoint transpose: a morphism out of `p^{-1}q^{-1}F`
is the same as a morphism `F ⟶ q_*p_*N`, and the only canonical such morphism is the unit of
the composite adjunction for `r` and `s`, which lands in `s_*r_*N`.  So a transport along
`p ≫ q = r ≫ s` is unavoidable, and it is carried by an `eqToHom` between the two direct images
of `N` along the two composites.  These two direct images are definitionally equal — the direct
image of sheaves along a composite *is* the composite of the direct images, which
`Stacks.SheafifyStalk.pushforward_comp_obj` and `pushforward_comp_map` record — but they are not
syntactically equal, so the two spellings are interchanged by hand rather than by `rw`, and the
proofs are written as chains of `Eq.trans` and `congrArg` rather than as rewrite sequences:
a rewrite has to match the spelling an earlier step left behind, and here the two spellings
alternate.

The stalk computation is three steps.  `pullbackCompTranspose_stalk` turns the stalk of a double
transpose into the stalk of what it was transposed from, followed by
`TopCat.Presheaf.stalkPushforward` along the composite: it is
`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp` applied twice and glued by
`TopCat.Presheaf.stalkPushforward.comp`.  `stalk_eqToHom_comp_stalkPushforward` moves the
transport out of the way, replacing it by the transport of the stalk of `F` along the equality
of the two image points — the `eqToHom` the statement advertises.  Finally
`pullbackSquareUnit_stalk` identifies the remaining stalk of the unit with the inverse of the
two inverse-image stalk comparisons along `s` and along `r`, by naturality of
`TopCat.Presheaf.stalkPushforward` in the presheaf together with
`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq`.

The compatibility equation is proved in the same way, on the adjoint side: both composites are
transposed twice, the left one becomes `a ≫ q_*b` and the right one `(c ≫ s_*d)` transported,
and the hypothesis is exactly the equality of those.  For a square of ringed spaces `a`, `b`,
`c`, `d` are the four structure-sheaf components, both sides are the structure-sheaf component
of the diagonal, and the hypothesis is `structureSheafMap_congr` — the transport of that
component along the commutativity of the square.

The construction is carried out for a commutative square of ringed spaces and the statement for
schemes obtained by instantiating along `AlgebraicGeometry.Scheme.Hom.toLRSHom` and
`AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom`, matching
`Stacks.NaiveCotangentFlatBaseChange.exists_baseRingComparison`, whose interface the canonical
construction is meant to feed and which is left untouched.

## References

* [Stacks Project, Tag 0FJZ](https://stacks.math.columbia.edu/tag/0FJZ), flat base change for
  the naive cotangent complex, whose stalkwise reduction consumes this comparison.
* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU), the comparison map of
  differentials of a commutative square, whose base-ring input is the same factorisation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.SheafOfModules (ringedSpaceStructureMap inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf structureSheafMap)

universe v w u

namespace Stacks.SheafifyStalk

/-! ### Plumbing for the direct image along a composite -/

section Plumbing

variable (A : Type w) [Category.{v} A]

/-- The underlying morphism of presheaves of a composite of morphisms of sheaves. -/
theorem sheaf_comp_hom {Z : TopCat.{v}} {F G H : TopCat.Sheaf A Z} (a : F ⟶ G) (b : G ⟶ H) :
    (a ≫ b).hom = a.hom ≫ b.hom := rfl

/-- Direct image along a composite is the composite of the direct images, on objects. -/
theorem pushforward_comp_obj {X' X Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    (N : TopCat.Sheaf A X') :
    (TopCat.Sheaf.pushforward A q).obj ((TopCat.Sheaf.pushforward A p).obj N) =
      (TopCat.Sheaf.pushforward A (p ≫ q)).obj N := rfl

/-- Direct image along a composite is the composite of the direct images, on morphisms. -/
theorem pushforward_comp_map {X' X Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    {N N' : TopCat.Sheaf A X'} (θ : N ⟶ N') :
    (TopCat.Sheaf.pushforward A q).map ((TopCat.Sheaf.pushforward A p).map θ) =
      (TopCat.Sheaf.pushforward A (p ≫ q)).map θ := rfl

/-- Transport of a direct image along an equality of continuous maps commutes with the direct
image of a morphism of sheaves. -/
theorem eqToHom_comp_pushforward_map {X' Y : TopCat.{v}} {m m' : X' ⟶ Y} (e : m = m')
    {N N' : TopCat.Sheaf A X'} (θ : N ⟶ N') :
    eqToHom (congrArg (fun k : X' ⟶ Y => (TopCat.Sheaf.pushforward A k).obj N) e).symm ≫
        (TopCat.Sheaf.pushforward A m).map θ =
      (TopCat.Sheaf.pushforward A m').map θ ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (TopCat.Sheaf.pushforward A k).obj N') e).symm := by
  subst e
  simp

end Plumbing

section PlumbingStalk

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable (A : Type w) [Category.{v} A] [HasColimits A]

/-- Transport of a direct image along an equality of continuous maps, read on stalks: the stalk
of a transported morphism followed by `TopCat.Presheaf.stalkPushforward` is the stalk of the
morphism itself, after the transport of the stalk of the source along the equality of points. -/
theorem stalk_eqToHom_comp_stalkPushforward {X' Y : TopCat.{v}} {m m' : X' ⟶ Y} (e : m = m')
    (F : TopCat.Sheaf A Y) (N : TopCat.Sheaf A X')
    (β : F ⟶ (TopCat.Sheaf.pushforward A m').obj N) (x' : X') :
    (stalkFunctor A (m x')).map
          (β ≫ eqToHom (congrArg (fun k : X' ⟶ Y =>
            (TopCat.Sheaf.pushforward A k).obj N) e).symm).hom ≫
        TopCat.Presheaf.stalkPushforward A m N.presheaf x' =
      eqToHom (congrArg F.presheaf.stalk (congrArg (fun k : X' ⟶ Y => k x') e)) ≫
        ((stalkFunctor A (m' x')).map β.hom ≫
          TopCat.Presheaf.stalkPushforward A m' N.presheaf x') := by
  subst e
  simp

end PlumbingStalk

/-! ### The canonical comparison of the two inverse images of a commutative square -/

section Square

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable (A : Type w) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- The adjoint transpose, across `p⁻¹ ⊣ p_*` and then `q⁻¹ ⊣ q_*`, of a morphism
`F ⟶ q_*p_*N`. -/
noncomputable def pullbackCompTranspose {X' X Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    {F : TopCat.Sheaf A Y} {N : TopCat.Sheaf A X'}
    (γ : F ⟶ (TopCat.Sheaf.pushforward A q).obj ((TopCat.Sheaf.pushforward A p).obj N)) :
    (TopCat.Sheaf.pullback A p).obj ((TopCat.Sheaf.pullback A q).obj F) ⟶ N :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
      ((TopCat.Sheaf.pullback A q).obj F) N).symm
    (((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
      ((TopCat.Sheaf.pushforward A p).obj N)).symm γ)

/-- The double transpose of `pullbackCompTranspose` is what it was built from. -/
theorem homEquiv_pullbackCompTranspose {X' X Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    {F : TopCat.Sheaf A Y} {N : TopCat.Sheaf A X'}
    (γ : F ⟶ (TopCat.Sheaf.pushforward A q).obj ((TopCat.Sheaf.pushforward A p).obj N)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj N)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
        ((TopCat.Sheaf.pullback A q).obj F) N (pullbackCompTranspose A p q γ)) = γ :=
  ((Equiv.apply_symm_apply
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj N)) γ).symm.trans
    (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj N))
      (Equiv.apply_symm_apply _ _).symm)).symm

/-- **The stalk of a doubly transposed morphism.**  Inverting the two inverse-image stalk
comparisons turns the stalk of `pullbackCompTranspose A p q γ` into the stalk of `γ` followed
by `TopCat.Presheaf.stalkPushforward` along the composite `p ≫ q`.

Two applications of `Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_comp`, glued by
`TopCat.Presheaf.stalkPushforward.comp`. -/
theorem pullbackCompTranspose_stalk {X' X Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    {F : TopCat.Sheaf A Y} {N : TopCat.Sheaf A X'}
    (γ : F ⟶ (TopCat.Sheaf.pushforward A q).obj ((TopCat.Sheaf.pushforward A p).obj N))
    (x' : X') :
    (stalkSheafPullbackIso A q F (p x')).inv ≫
        ((stalkSheafPullbackIso A p ((TopCat.Sheaf.pullback A q).obj F) x').inv ≫
          (stalkFunctor A x').map (pullbackCompTranspose A p q γ).hom) =
      (stalkFunctor A ((p ≫ q) x')).map γ.hom ≫
        TopCat.Presheaf.stalkPushforward A (p ≫ q) N.presheaf x' := by
  have hp : (TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
        ((TopCat.Sheaf.pullback A q).obj F) N (pullbackCompTranspose A p q γ) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj N)).symm γ :=
    Equiv.apply_symm_apply _ _
  have h1 := stalkSheafPullbackIso_inv_comp A p (pullbackCompTranspose A p q γ) x'
  rw [hp] at h1
  have h2 := stalkSheafPullbackIso_inv_comp A q
    (((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
      ((TopCat.Sheaf.pushforward A p).obj N)).symm γ) (p x')
  rw [Equiv.apply_symm_apply] at h2
  refine (congrArg (fun z => (stalkSheafPullbackIso A q F (p x')).inv ≫ z) h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ TopCat.Presheaf.stalkPushforward A p N.presheaf x') h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => (stalkFunctor A ((p ≫ q) x')).map γ.hom ≫ z)
    (TopCat.Presheaf.stalkPushforward.comp A N.presheaf p q x').symm

/-- The unit datum of a commutative square: the unit of `s⁻¹ ⊣ s_*` at `F`, followed by the
direct image along `s` of the unit of `r⁻¹ ⊣ r_*` at `s⁻¹F`.  A morphism
`F ⟶ (r ≫ s)_*(r⁻¹s⁻¹F)`, the unit of the composite adjunction. -/
noncomputable def pullbackSquareUnit {X' Y' Y : TopCat.{v}} (r : X' ⟶ Y') (s : Y' ⟶ Y)
    (F : TopCat.Sheaf A Y) :
    F ⟶ (TopCat.Sheaf.pushforward A (r ≫ s)).obj
      ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction A s).unit.app F ≫
    (TopCat.Sheaf.pushforward A s).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).unit.app
        ((TopCat.Sheaf.pullback A s).obj F))

/-- **`pullbackSquareUnit` is the unit of the composite adjunction**: composing it with the
direct image of `θ : r⁻¹s⁻¹F ⟶ H` is the double adjoint transpose of `θ`. -/
theorem pullbackSquareUnit_comp {X' Y' Y : TopCat.{v}} (r : X' ⟶ Y') (s : Y' ⟶ Y)
    (F : TopCat.Sheaf A Y) {H : TopCat.Sheaf A X'}
    (θ : (TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F) ⟶ H) :
    pullbackSquareUnit A r s F ≫ (TopCat.Sheaf.pushforward A (r ≫ s)).map θ =
      (TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F
        ((TopCat.Sheaf.pushforward A r).obj H)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv
          ((TopCat.Sheaf.pullback A s).obj F) H θ) := by
  refine Eq.trans ?_ (Adjunction.homEquiv_unit
    (TopCat.Sheaf.pullbackPushforwardAdjunction A s) F
    ((TopCat.Sheaf.pushforward A r).obj H)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv
      ((TopCat.Sheaf.pullback A s).obj F) H θ)).symm
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun z =>
    (TopCat.Sheaf.pullbackPushforwardAdjunction A s).unit.app F ≫ z) ?_
  refine (CategoryTheory.Functor.map_comp (TopCat.Sheaf.pushforward A s)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).unit.app
      ((TopCat.Sheaf.pullback A s).obj F))
    ((TopCat.Sheaf.pushforward A r).map θ)).symm.trans ?_
  exact congrArg (fun z => (TopCat.Sheaf.pushforward A s).map z)
    (Adjunction.homEquiv_unit (TopCat.Sheaf.pullbackPushforwardAdjunction A r)
      ((TopCat.Sheaf.pullback A s).obj F) H θ).symm

/-- The double transpose of `p⁻¹(a^♭) ≫ b^♭` is `a ≫ q_*b`. -/
private theorem homEquiv_pullback_map_comp_transpose {X' X Y : TopCat.{v}} (p : X' ⟶ X)
    (q : X ⟶ Y) {F : TopCat.Sheaf A Y} {G : TopCat.Sheaf A X} {H : TopCat.Sheaf A X'}
    (a : F ⟶ (TopCat.Sheaf.pushforward A q).obj G)
    (b : G ⟶ (TopCat.Sheaf.pushforward A p).obj H) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj H)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
          ((TopCat.Sheaf.pullback A q).obj F) H
          ((TopCat.Sheaf.pullback A p).map
              (((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F G).symm a) ≫
            ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv G H).symm b)) =
      a ≫ (TopCat.Sheaf.pushforward A q).map b := by
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- **The transpose of `pullbackSquareUnit` composed with a morphism out of `r⁻¹s⁻¹F`.**  For
`c : F ⟶ s_*G'` and `d : G' ⟶ r_*H`, the unit of the composite adjunction followed by the
direct image of `r⁻¹(c^♭) ≫ d^♭` is `c ≫ s_*d`. -/
theorem pullbackSquareUnit_comp_pushforward_map {X' Y' Y : TopCat.{v}} (r : X' ⟶ Y') (s : Y' ⟶ Y)
    {F : TopCat.Sheaf A Y} {G' : TopCat.Sheaf A Y'} {H : TopCat.Sheaf A X'}
    (c : F ⟶ (TopCat.Sheaf.pushforward A s).obj G')
    (d : G' ⟶ (TopCat.Sheaf.pushforward A r).obj H) :
    pullbackSquareUnit A r s F ≫ (TopCat.Sheaf.pushforward A (r ≫ s)).map
        ((TopCat.Sheaf.pullback A r).map
            (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d) =
      c ≫ (TopCat.Sheaf.pushforward A s).map d := by
  exact (pullbackSquareUnit_comp A r s F _).trans
    (homEquiv_pullback_map_comp_transpose A r s c d)

/-- **The canonical comparison of the two double inverse images of a commutative square of
continuous maps.**  For `p ≫ q = r ≫ s` and a sheaf `F` on `Y`, the morphism
`p⁻¹q⁻¹F ⟶ r⁻¹s⁻¹F` adjoint to the unit of the composite adjunction `r⁻¹s⁻¹ ⊣ s_*r_*`, read
through the equality of the two composites. -/
noncomputable def pullbackSquareComparison {X' X Y' Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    (r : X' ⟶ Y') (s : Y' ⟶ Y) (w : p ≫ q = r ≫ s) (F : TopCat.Sheaf A Y) :
    (TopCat.Sheaf.pullback A p).obj ((TopCat.Sheaf.pullback A q).obj F) ⟶
      (TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F) :=
  pullbackCompTranspose A p q
    (pullbackSquareUnit A r s F ≫
      eqToHom (congrArg (fun k : X' ⟶ Y => (TopCat.Sheaf.pushforward A k).obj
        ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F))) w).symm)

/-- The double transpose of `pullbackSquareComparison` is the unit of the composite adjunction,
transported along the equality of the two composites. -/
theorem homEquiv_pullbackSquareComparison {X' X Y' Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    (r : X' ⟶ Y') (s : Y' ⟶ Y) (w : p ≫ q = r ≫ s) (F : TopCat.Sheaf A Y) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj
          ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
        ((TopCat.Sheaf.pullback A q).obj F)
        ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F))
        (pullbackSquareComparison A p q r s w F)) =
      pullbackSquareUnit A r s F ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (TopCat.Sheaf.pushforward A k).obj
          ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F))) w).symm :=
  homEquiv_pullbackCompTranspose A p q _

/-- **The canonical comparison identifies the two factorisations of a structural map.**  Let
`a : F ⟶ q_*G`, `b : G ⟶ p_*H`, `c : F ⟶ s_*G'`, `d : G' ⟶ r_*H` be such that `a ≫ q_*b` and
`c ≫ s_*d` agree, the two being compared through the equality `p ≫ q = r ≫ s`.  Then the
composite `p⁻¹q⁻¹F ⟶ p⁻¹G ⟶ H` of the inverse image of `a^♭` with `b^♭` factors as the
canonical comparison followed by the composite `r⁻¹s⁻¹F ⟶ r⁻¹G' ⟶ H`.

For the structural maps of a commutative square of ringed spaces the hypothesis is the equality
of the two readings of the structural map of the diagonal, so this is the compatibility
equation required of a base-ring comparison. -/
theorem pullbackSquareComparison_comp {X' X Y' Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    (r : X' ⟶ Y') (s : Y' ⟶ Y) (w : p ≫ q = r ≫ s) {F : TopCat.Sheaf A Y}
    {G : TopCat.Sheaf A X} {G' : TopCat.Sheaf A Y'} {H : TopCat.Sheaf A X'}
    (a : F ⟶ (TopCat.Sheaf.pushforward A q).obj G)
    (b : G ⟶ (TopCat.Sheaf.pushforward A p).obj H)
    (c : F ⟶ (TopCat.Sheaf.pushforward A s).obj G')
    (d : G' ⟶ (TopCat.Sheaf.pushforward A r).obj H)
    (hcomp : a ≫ (TopCat.Sheaf.pushforward A q).map b =
      (c ≫ (TopCat.Sheaf.pushforward A s).map d) ≫
        eqToHom (congrArg (fun k : X' ⟶ Y =>
          (TopCat.Sheaf.pushforward A k).obj H) w).symm) :
    (TopCat.Sheaf.pullback A p).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F G).symm a) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv G H).symm b =
      (pullbackSquareComparison A p q r s w F ≫ (TopCat.Sheaf.pullback A r).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c)) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
    ((TopCat.Sheaf.pullback A q).obj F) H).injective
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
    ((TopCat.Sheaf.pushforward A p).obj H)).injective
  have hR : (TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj H)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
          ((TopCat.Sheaf.pullback A q).obj F) H
          ((pullbackSquareComparison A p q r s w F ≫ (TopCat.Sheaf.pullback A r).map
              (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c)) ≫
            ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d)) =
      (c ≫ (TopCat.Sheaf.pushforward A s).map d) ≫
        eqToHom (congrArg (fun k : X' ⟶ Y =>
          (TopCat.Sheaf.pushforward A k).obj H) w).symm := by
    refine (congrArg (fun z => (TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj H)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
          ((TopCat.Sheaf.pullback A q).obj F) H z))
      (Category.assoc (pullbackSquareComparison A p q r s w F)
        ((TopCat.Sheaf.pullback A r).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d))).trans ?_
    refine (congrArg (fun z => (TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv F
        ((TopCat.Sheaf.pushforward A p).obj H) z)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv_naturality_right
        (pullbackSquareComparison A p q r s w F)
        ((TopCat.Sheaf.pullback A r).map
            (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d))).trans ?_
    refine ((TopCat.Sheaf.pullbackPushforwardAdjunction A q).homEquiv_naturality_right
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A p).homEquiv
        ((TopCat.Sheaf.pullback A q).obj F)
        ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F))
        (pullbackSquareComparison A p q r s w F))
      ((TopCat.Sheaf.pushforward A p).map
        ((TopCat.Sheaf.pullback A r).map
            (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d))).trans ?_
    refine (congrArg (fun z => z ≫ (TopCat.Sheaf.pushforward A q).map
        ((TopCat.Sheaf.pushforward A p).map
          ((TopCat.Sheaf.pullback A r).map
              (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c) ≫
            ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d)))
      (homEquiv_pullbackSquareComparison A p q r s w F)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => pullbackSquareUnit A r s F ≫ z)
      (eqToHom_comp_pushforward_map A w
        ((TopCat.Sheaf.pullback A r).map
            (((TopCat.Sheaf.pullbackPushforwardAdjunction A s).homEquiv F G').symm c) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).homEquiv G' H).symm d))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun z => z ≫ eqToHom (congrArg (fun k : X' ⟶ Y =>
        (TopCat.Sheaf.pushforward A k).obj H) w).symm)
      (pullbackSquareUnit_comp_pushforward_map A r s c d)
  exact (homEquiv_pullback_map_comp_transpose A p q a b).trans (hcomp.trans hR.symm)

/-- **The stalk of `pullbackSquareUnit`** is the inverse of the two inverse-image stalk
comparisons along `s` and along `r`. -/
theorem pullbackSquareUnit_stalk {X' Y' Y : TopCat.{v}} (r : X' ⟶ Y') (s : Y' ⟶ Y)
    (F : TopCat.Sheaf A Y) (x' : X') :
    (stalkFunctor A ((r ≫ s) x')).map (pullbackSquareUnit A r s F).hom ≫
        TopCat.Presheaf.stalkPushforward A (r ≫ s)
          ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)).presheaf x' =
      (stalkSheafPullbackIso A s F (r x')).inv ≫
        (stalkSheafPullbackIso A r ((TopCat.Sheaf.pullback A s).obj F) x').inv := by
  have hnat := stalkPushforward_naturality A s
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).unit.app
      ((TopCat.Sheaf.pullback A s).obj F)).hom (r x')
  refine (congrArg (fun z => z ≫ TopCat.Presheaf.stalkPushforward A (r ≫ s)
      ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)).presheaf x')
    (CategoryTheory.Functor.map_comp (stalkFunctor A ((r ≫ s) x'))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A s).unit.app F).hom
      ((TopCat.Sheaf.pushforward A s).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).unit.app
          ((TopCat.Sheaf.pullback A s).obj F))).hom)).trans ?_
  refine (congrArg (fun z => ((stalkFunctor A ((r ≫ s) x')).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction A s).unit.app F).hom ≫
      (stalkFunctor A ((r ≫ s) x')).map
        ((TopCat.Sheaf.pushforward A s).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).unit.app
            ((TopCat.Sheaf.pullback A s).obj F))).hom) ≫ z)
    (TopCat.Presheaf.stalkPushforward.comp A
      ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)).presheaf r s
      x')).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (stalkFunctor A ((r ≫ s) x')).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction A s).unit.app F).hom ≫ z)
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫
        TopCat.Presheaf.stalkPushforward A r
          ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)).presheaf x')
      hnat).trans (Category.assoc _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫
      ((stalkFunctor A (r x')).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction A r).unit.app
            ((TopCat.Sheaf.pullback A s).obj F)).hom ≫
        TopCat.Presheaf.stalkPushforward A r
          ((TopCat.Sheaf.pullback A r).obj ((TopCat.Sheaf.pullback A s).obj F)).presheaf x'))
    (stalkSheafPullbackIso_inv_eq A s F (r x')).symm).trans ?_
  exact congrArg (fun z => (stalkSheafPullbackIso A s F (r x')).inv ≫ z)
    (stalkSheafPullbackIso_inv_eq A r ((TopCat.Sheaf.pullback A s).obj F) x').symm

/-- **The stalk of the canonical comparison of a commutative square**, in the direction of the
inverses of the four inverse-image stalk comparisons. -/
theorem pullbackSquareComparison_stalk_inv {X' X Y' Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    (r : X' ⟶ Y') (s : Y' ⟶ Y) (w : p ≫ q = r ≫ s) (F : TopCat.Sheaf A Y) (x' : X') :
    (stalkSheafPullbackIso A q F (p x')).inv ≫
        ((stalkSheafPullbackIso A p ((TopCat.Sheaf.pullback A q).obj F) x').inv ≫
          (stalkFunctor A x').map (pullbackSquareComparison A p q r s w F).hom) =
      eqToHom (congrArg F.presheaf.stalk (congrArg (fun k : X' ⟶ Y => k x') w)) ≫
        ((stalkSheafPullbackIso A s F (r x')).inv ≫
          (stalkSheafPullbackIso A r ((TopCat.Sheaf.pullback A s).obj F) x').inv) := by
  refine (pullbackCompTranspose_stalk A p q _ x').trans ?_
  refine (stalk_eqToHom_comp_stalkPushforward A w F _ (pullbackSquareUnit A r s F) x').trans ?_
  exact congrArg (fun z => eqToHom (congrArg F.presheaf.stalk
      (congrArg (fun k : X' ⟶ Y => k x') w)) ≫ z)
    (pullbackSquareUnit_stalk A r s F x')

/-- **The stalk of the canonical comparison of a commutative square.**  The stalk at `x'` of
`p⁻¹q⁻¹F ⟶ r⁻¹s⁻¹F`, followed by the identification of the stalk of `r⁻¹s⁻¹F` with the stalk of
`F` at the image point, is the identification of the stalk of `p⁻¹q⁻¹F` with the stalk of `F` at
the image point, followed by the transport along the equality of the two image points. -/
theorem pullbackSquareComparison_stalk {X' X Y' Y : TopCat.{v}} (p : X' ⟶ X) (q : X ⟶ Y)
    (r : X' ⟶ Y') (s : Y' ⟶ Y) (w : p ≫ q = r ≫ s) (F : TopCat.Sheaf A Y) (x' : X') :
    (stalkFunctor A x').map (pullbackSquareComparison A p q r s w F).hom ≫
        ((stalkSheafPullbackIso A r ((TopCat.Sheaf.pullback A s).obj F) x').hom ≫
          (stalkSheafPullbackIso A s F (r x')).hom) =
      (stalkSheafPullbackIso A p ((TopCat.Sheaf.pullback A q).obj F) x').hom ≫
        ((stalkSheafPullbackIso A q F (p x')).hom ≫
          eqToHom (congrArg F.presheaf.stalk (congrArg (fun k : X' ⟶ Y => k x') w))) := by
  have h2 := (Iso.inv_comp_eq
      (stalkSheafPullbackIso A p ((TopCat.Sheaf.pullback A q).obj F) x')).mp
    ((Iso.inv_comp_eq (stalkSheafPullbackIso A q F (p x'))).mp
      (pullbackSquareComparison_stalk_inv A p q r s w F x'))
  refine (congrArg (fun z => z ≫
      ((stalkSheafPullbackIso A r ((TopCat.Sheaf.pullback A s).obj F) x').hom ≫
        (stalkSheafPullbackIso A s F (r x')).hom)) h2).trans ?_
  simp

end Square

end Stacks.SheafifyStalk

namespace Stacks.NaiveCotangentFlatBaseChange

section RingedSpace

variable {X' X S' S : RingedSpace.{u, u}}

/-- Transport of the structure-sheaf component of a morphism of ringed spaces along an equality
of morphisms. -/
theorem structureSheafMap_congr {m m' : X' ⟶ S} (e : m = m') :
    structureSheafMap m' ≫ eqToHom (congrArg
        (fun k => (TopCat.Sheaf.pushforward CommRingCat.{u} k).obj X'.sheaf)
      (congrArg (fun t : X' ⟶ S => t.hom.base) e)).symm = structureSheafMap m := by
  subst e
  simp

/-- **The canonical base-ring comparison of a commutative square of ringed spaces.**  For
`g' ≫ f = f' ≫ g` the morphism `(g')⁻¹f⁻¹𝒪_S ⟶ (f')⁻¹𝒪_{S'}` of sheaves of rings on `X'`
obtained by comparing the two double inverse images of `𝒪_S` and then applying `(f')⁻¹` to the
structure map `g⁻¹𝒪_S ⟶ 𝒪_{S'}` of `g`. -/
noncomputable def baseRingComparisonRingedSpace (g' : X' ⟶ X) (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) :
    inverseImageBaseRing g' f ⟶ inverseImageSheaf f' :=
  Stacks.SheafifyStalk.pullbackSquareComparison CommRingCat.{u} g'.hom.base f.hom.base
      f'.hom.base g.hom.base (congrArg (fun t : X' ⟶ S => t.hom.base) w) S.sheaf ≫
    inverseImageFirstRingMap f' g

/-- **The canonical base-ring comparison identifies the two towers**: it satisfies the
compatibility equation that `Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`
requires of its comparison argument. -/
theorem baseRingComparisonRingedSpace_comp (g' : X' ⟶ X) (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) :
    inverseImageFirstRingMap g' f ≫ ringedSpaceStructureMap g' =
      baseRingComparisonRingedSpace g' f f' g w ≫ ringedSpaceStructureMap f' :=
  Stacks.SheafifyStalk.pullbackSquareComparison_comp CommRingCat.{u} g'.hom.base f.hom.base
    f'.hom.base g.hom.base (congrArg (fun t : X' ⟶ S => t.hom.base) w) (structureSheafMap f)
    (structureSheafMap g') (structureSheafMap g) (structureSheafMap f')
    (structureSheafMap_congr w).symm

end RingedSpace

end Stacks.NaiveCotangentFlatBaseChange

namespace AlgebraicGeometry.BaseChangeStalk

section Scheme

variable {X Y X' Y' : Scheme.{u}}

/-- The two spellings of the stalk of `(f')⁻¹𝒪_{Y'}` agree. -/
theorem stalkInverseImageSheafIso_eq (f' : X' ⟶ Y') (x' : X'.carrier) :
    stalkInverseImageSheafIso f' x' = stalkInverseImageMiddleRingIso f' x' := rfl

/-- `stalkInverseImageBaseRingIso` written out as the composite of the two inverse-image stalk
comparisons. -/
theorem stalkInverseImageBaseRingIso_hom (f : X ⟶ Y) (g' : X' ⟶ X) (x' : X'.carrier) :
    (stalkInverseImageBaseRingIso f g' x').hom =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} g'.base
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) x').hom ≫
        (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f.base Y.sheaf
          (g'.base x')).hom := rfl

/-- **The canonical base-ring comparison of a commutative square of schemes.** -/
noncomputable def baseRingComparison (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
      inverseImageSheaf f'.toLRSHom.toShHom :=
  Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace g'.toLRSHom.toShHom
    f.toLRSHom.toShHom f'.toLRSHom.toShHom g.toLRSHom.toShHom
    (congrArg (fun t : X' ⟶ Y => t.toLRSHom.toShHom) w)

/-- `baseRingComparison` written out. -/
theorem baseRingComparison_eq (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    baseRingComparison f f' g' g w =
      Stacks.SheafifyStalk.pullbackSquareComparison CommRingCat.{u} g'.base f.base f'.base g.base
          (congrArg (fun t : X' ⟶ Y => t.base) w) Y.sheaf ≫
        inverseImageFirstRingMap f'.toLRSHom.toShHom g.toLRSHom.toShHom := rfl

/-- **The canonical base-ring comparison identifies the two towers.** -/
theorem baseRingComparison_comp (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom =
      baseRingComparison f f' g' g w ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom :=
  Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace_comp g'.toLRSHom.toShHom
    f.toLRSHom.toShHom f'.toLRSHom.toShHom g.toLRSHom.toShHom
    (congrArg (fun t : X' ⟶ Y => t.toLRSHom.toShHom) w)

/-- **The stalk of the canonical base-ring comparison is the stalk map of `g`.** -/
theorem stalkFunctor_map_baseRingComparison (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (g : Y' ⟶ Y) (w : g' ≫ f = f' ≫ g) (x' : X'.carrier) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map (baseRingComparison f f' g' g w).hom ≫
        (stalkInverseImageSheafIso f' x').hom =
      (stalkInverseImageBaseRingIso f g' x').hom ≫
        eqToHom (congrArg Y.presheaf.stalk (congrArg (fun k : X' ⟶ Y => k.base x') w)) ≫
          g.stalkMap (f'.base x') := by
  refine (congrArg (fun z => z ≫ (stalkInverseImageSheafIso f' x').hom)
    (CategoryTheory.Functor.map_comp (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x')
      (Stacks.SheafifyStalk.pullbackSquareComparison CommRingCat.{u} g'.base f.base f'.base
        g.base (congrArg (fun t : X' ⟶ Y => t.base) w) Y.sheaf).hom
      (inverseImageFirstRingMap f'.toLRSHom.toShHom g.toLRSHom.toShHom).hom)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x').map
      (Stacks.SheafifyStalk.pullbackSquareComparison CommRingCat.{u} g'.base f.base f'.base
        g.base (congrArg (fun t : X' ⟶ Y => t.base) w) Y.sheaf).hom ≫ z)
    (stalkInverseImageBaseRingIso_hom_comp_stalkMap g f' x')).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ g.stalkMap (f'.base x'))
    (Stacks.SheafifyStalk.pullbackSquareComparison_stalk CommRingCat.{u} g'.base f.base f'.base
      g.base (congrArg (fun t : X' ⟶ Y => t.base) w) Y.sheaf x')).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z =>
      (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} g'.base
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) x').hom ≫ z)
    (Category.assoc _ _ _)).trans ?_
  exact (Category.assoc _ _ _).symm

end Scheme

end AlgebraicGeometry.BaseChangeStalk

end
