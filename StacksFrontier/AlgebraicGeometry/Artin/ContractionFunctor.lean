module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Artin's contraction functor

In the situation of Stacks 0GH8, recorded by
`AlgebraicGeometry.Artin.ContractionSituation`, Artin's strategy is to build an algebraic
space as the functor `F` on locally Noetherian schemes over `S` whose value at `V` is the set
of triples `(Z, u', x̂)` where

1. `Z ⊆ V` is a closed subset,
2. `u' : V ∖ Z ⟶ U'` is a morphism over `S`,
3. `x̂ : V_{/Z} ⟶ W` is an adic morphism of formal algebraic spaces over `S` (Stacks 0AQ2),
   that is, by Definition 0AQ3, a morphism representable by algebraic spaces,
4. `u'` and `x̂` are *compatible*.

Compatibility is the condition of Stacks 0GHA's section: pulling back the formal
modification `g` along `x̂` and applying the main theorem on dilatations produces a proper
morphism `V' ⟶ V` which is an isomorphism over `V ∖ Z` and whose completion along `Z` is the
pullback of `g` along `x̂`; the condition is that there be a morphism `x' : V' ⟶ X'`
restricting to `u'` over `V ∖ Z` and to the pullback `x̂' : V'_{/Z} ⟶ X'_{/T'}` over
`V'_{/Z}`. The source names this data "`V' ⟶ V`, `x̂'` and `x'` witness the compatibility
between `u'` and `x̂`", and that is how it is recorded here, as
`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness`: the uniqueness part of
the theorem on dilatations says that any `V' ⟶ V` which is proper, an isomorphism over
`V ∖ Z`, and whose completion square is cartesian, is *the* one the theorem produces, so
asking for the existence of a witness is asking for the compatibility of the source.

**Stacks 0GHA** is then the assertion that these sets, together with the rule sending a
morphism `φ : V₂ ⟶ V₁` and a triple `(Z₁, u'₁, x̂₁)` to the triple `(Z₂, u'₂, x̂₂)` with

1. `Z₂` the inverse image of `Z₁` under `φ`,
2. `u'₂` the composition of `u'₁` with `φ|_{V₂ ∖ Z₂} : V₂ ∖ Z₂ ⟶ V₁ ∖ Z₁`,
3. `x̂₂` the composition of `x̂₁` with `φ_{/Z₂} : V_{2,/Z₂} ⟶ V_{1,/Z₁}`,

form a contravariant functor. That is `AlgebraicGeometry.Artin.contractionFunctor`.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness`: the witness of the
  compatibility condition.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple`: the triples, that is the value of
  `F` on a locally Noetherian scheme over `S`.
* `AlgebraicGeometry.Artin.ContractionSituation.mapTriple`: the value of `F` on a morphism.
* `AlgebraicGeometry.Artin.contractionFunctor`: **Stacks 0GHA**, the functor `F`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.mapTriple_id` and
  `AlgebraicGeometry.Artin.ContractionSituation.mapTriple_comp`: the two functor laws, which
  are what Stacks 0GHA asserts beyond the construction of `F`.
* `AlgebraicGeometry.Space.isPullback_completionSheafRestrict`: the completion of a cartesian
  square of presheaves along a set of points of the common target and its inverse images is
  cartesian, in the form the compatibility witness of a transported triple is built from.

## What is assumed

Nothing. Adicness of condition (3) is the defining condition of Stacks 0AQ3, that the
morphism be representable by algebraic spaces, in the form
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift` in which the library carries
it for presheaves of `Type (u + 1)`; the two facts about it that the construction of `F(φ)`
needs are proved in the library, namely Stacks 0APY (a composition of morphisms
representable by algebraic spaces is one) and Stacks 0APV
(`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`, that the
morphism of completions induced by a morphism of algebraic spaces is one, it being a base
change of that morphism).

Cartesianness of the completion of a cartesian square, which is what produces the
compatibility witness of the new triple, is
`AlgebraicGeometry.Space.isPullback_completionSheafRestrict` below, a repackaging of
`AlgebraicGeometry.Space.isPullback_completionSheafMap_of_isPullback` for the restriction
morphisms used here.

In particular the compatibility condition is not assumed to be preserved:
`AlgebraicGeometry.Artin.ContractionSituation.mapTriple` constructs the witness for the new
triple out of the witness for the old one, by the argument of Stacks 0GHA —
`V'₂ = V₂ ×_{V₁} V'₁`, with `x̂'₂` the composition of `x̂'₁` with
`V'_{2,/Z₂} ⟶ V'_{1,/Z₁}` and `x'₂` the composition of `x'₁` with `V'₂ ⟶ V'₁`.

## Implementation notes

The category of locally Noetherian schemes over `S` is
`AlgebraicGeometry.LocallyNoetherianOver`, the full subcategory of locally Noetherian
objects of the big fppf site over `S` (Stacks 0GE4), and `V` enters the construction as the
algebraic space `CategoryTheory.yoneda.obj V` it represents. The triples and their
transport are therefore defined for an arbitrary object of the big fppf site over `S`, and
local Noetherianness enters only as the domain of the functor, exactly as in the source,
where `F` is a rule on locally Noetherian schemes over `S`.

`V ∖ Z` is the open subspace `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by the
complement of `Z` under the correspondence of Stacks 03BZ, exactly as `U' ⊆ X'` is in
`AlgebraicGeometry.Artin.ContractionSituation.U'`, and `V_{/Z}` is
`AlgebraicGeometry.Space.completionSheaf`, the completion of Stacks 0AMC.

The morphism `V_{2,/Z₂} ⟶ V_{1,/Z₁}` of a triple's third component is
`AlgebraicGeometry.Space.completionSheafMap`, which is defined for the inverse image set on
the nose. Pasting the completions of two cartesian squares, however, produces completions
along sets that agree only propositionally, so this file also provides
`AlgebraicGeometry.Space.completionSheafRestrict`, the same morphism for any source set
contained in the inverse image; `AlgebraicGeometry.Space.openSubspaceOfPointsRestrict` is
its counterpart for open subspaces. Both have the subset, rather than an equality, as
hypothesis, which is what makes them compose without transporting along equalities of sets
of points.

That `V' ⟶ V` is an isomorphism over `V ∖ Z` is recorded as cartesianness of the square
whose other two sides are the identity of `V ∖ Z` and the inclusion `V ∖ Z ⟶ V`: that says
precisely that `V ∖ Z` *is* the fibre product `(V ∖ Z) ×_V V'`, with the given morphism
`j : V ∖ Z ⟶ V'` as the comparison.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0APY](https://stacks.math.columbia.edu/tag/0APY)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction morphisms of open subspaces and of completions -/

section Restrict

variable {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism of open subspaces induced by a morphism `f : F' ⟶ F` of presheaves on the
big fppf site of `S`, from the subspace cut out by a set `W'` of points of `F'` to the one
cut out by a set `W` of points of `F`, whenever `f` carries `W'` into `W`. -/
def openSubspaceOfPointsRestrict (f : F' ⟶ F) (W' : Set (points B S hS F'))
    (W : Set (points B S hS F)) (h : W' ⊆ pointsMap B S hS F' f ⁻¹' W) :
    (openSubspaceOfPoints B S hS F' W').toFunctor ⟶
      (openSubspaceOfPoints B S hS F W).toFunctor where
  app U := ↾fun x => ⟨f.app U x.1, by
    rintro y ⟨w, rfl⟩
    rw [← yonedaEquiv_symm_naturality_right, pointsMap_comp, Function.comp_apply]
    exact h (x.2 ⟨w, rfl⟩)⟩
  naturality U V i := by
    ext x
    apply Subtype.ext
    exact NatTrans.naturality_apply f i x.1

/-- The restriction morphism of open subspaces is compatible with the inclusions into the
ambient presheaves. -/
@[simp]
theorem openSubspaceOfPointsRestrict_comp_ι (f : F' ⟶ F) (W' : Set (points B S hS F'))
    (W : Set (points B S hS F)) (h : W' ⊆ pointsMap B S hS F' f ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS f W' W h ≫ (openSubspaceOfPoints B S hS F W).ι =
      (openSubspaceOfPoints B S hS F' W').ι ≫ f := rfl

/-- Restricting along an identity is the identity. -/
theorem openSubspaceOfPointsRestrict_id (W : Set (points B S hS F))
    (h : W ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS (𝟙 F) W W h = 𝟙 _ := rfl

/-- Restricting along a composition is the composition of the restrictions. -/
theorem openSubspaceOfPointsRestrict_comp {F'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F'' ⟶ F') (g : F' ⟶ F) (W'' : Set (points B S hS F''))
    (W' : Set (points B S hS F')) (W : Set (points B S hS F))
    (h₁ : W'' ⊆ pointsMap B S hS F'' f ⁻¹' W') (h₂ : W' ⊆ pointsMap B S hS F' g ⁻¹' W)
    (h : W'' ⊆ pointsMap B S hS F'' (f ≫ g) ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS (f ≫ g) W'' W h =
      openSubspaceOfPointsRestrict B S hS f W'' W' h₁ ≫
        openSubspaceOfPointsRestrict B S hS g W' W h₂ := rfl

/-- The morphism of completion subfunctors induced by an inclusion of sets of points. -/
def completionSubfunctorMono (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T₁ T₂ : Set (points B S hS X)) (h : T₁ ⊆ T₂) :
    (completionSubfunctor B S hS X T₁).toFunctor ⟶
      (completionSubfunctor B S hS X T₂).toFunctor where
  app _ := ↾fun x => ⟨x.1, fun p => h (x.2 p)⟩
  naturality _ _ _ := rfl

/-- The morphism of completion subfunctors induced by a morphism `f : F' ⟶ F` of presheaves
on the big fppf site of `S` whenever `f` carries `T'` into `T`. -/
def completionSubfunctorRestrict (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T) :
    (completionSubfunctor B S hS F' T').toFunctor ⟶
      (completionSubfunctor B S hS F T).toFunctor :=
  completionSubfunctorMono B S hS F' T' (pointsMap B S hS F' f ⁻¹' T) h ≫
    completionMap B S hS f T

/-- The fppf sheafification of presheaves of `Type (u + 1)` on the big fppf site of `S`, as
a functor: the functor whose values are the completions of Stacks 0AMC and the sheafified
universe lifts, and whose functoriality is what makes them compose. -/
noncomputable abbrev fppfSheafification :
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) ⥤
      Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))

/-- The morphism of completions of Stacks 0AMC is the sheafification of the corresponding
morphism of completion subfunctors. -/
theorem completionSheafMap_eq_map (f : F' ⟶ F) (T : Set (points B S hS F)) :
    completionSheafMap B S hS f T =
      (fppfSheafification B S hS).map (completionMap B S hS f T) := rfl

/-- The morphism from a completion into its ambient sheaf is the sheafification of the
inclusion of the completion subfunctor. -/
theorem completionSheafInclusion_eq_map (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) :
    completionSheafInclusion B S hS X T =
      (fppfSheafification B S hS).map (completionSubfunctor B S hS X T).ι := rfl

/-- The sheafified universe lift of a morphism is the sheafification of its universe
lift. -/
theorem sheafifiedULiftMap_eq_map (f : F' ⟶ F) :
    sheafifiedULiftMap B S hS f =
      (fppfSheafification B S hS).map (Functor.whiskerRight f uliftFunctor.{u + 1}) := rfl

/-- The morphism of completions `X'_{/T'} ⟶ X_{/T}` induced by a morphism `f : X' ⟶ X`
whenever `f` carries `T'` into `T`. For `T'` the inverse image of `T` this is
`AlgebraicGeometry.Space.completionSheafMap`; the general form is what composes without
transporting along equalities of sets of points. -/
noncomputable def completionSheafRestrict (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T) :
    completionSheaf B S hS F' T' ⟶ completionSheaf B S hS F T :=
  (fppfSheafification B S hS).map (completionSubfunctorRestrict B S hS f T' T h)

/-- For the inverse image set the restriction morphism of completion subfunctors is the
morphism of Stacks 0AMC. -/
theorem completionSubfunctorRestrict_self (f : F' ⟶ F) (T : Set (points B S hS F))
    (h : pointsMap B S hS F' f ⁻¹' T ⊆ pointsMap B S hS F' f ⁻¹' T) :
    completionSubfunctorRestrict B S hS f (pointsMap B S hS F' f ⁻¹' T) T h =
      completionMap B S hS f T := rfl

/-- For the inverse image set the restriction morphism of completions is the morphism of
Stacks 0AMC. -/
theorem completionSheafRestrict_self (f : F' ⟶ F) (T : Set (points B S hS F))
    (h : pointsMap B S hS F' f ⁻¹' T ⊆ pointsMap B S hS F' f ⁻¹' T) :
    completionSheafRestrict B S hS f (pointsMap B S hS F' f ⁻¹' T) T h =
      completionSheafMap B S hS f T :=
  congrArg (fppfSheafification B S hS).map (completionSubfunctorRestrict_self B S hS f T h)

/-- Restricting completion subfunctors along a composition is the composition of the
restrictions. -/
theorem completionSubfunctorRestrict_comp {F'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F'' ⟶ F') (g : F' ⟶ F) (T'' : Set (points B S hS F''))
    (T' : Set (points B S hS F')) (T : Set (points B S hS F))
    (h₁ : T'' ⊆ pointsMap B S hS F'' f ⁻¹' T') (h₂ : T' ⊆ pointsMap B S hS F' g ⁻¹' T)
    (h : T'' ⊆ pointsMap B S hS F'' (f ≫ g) ⁻¹' T) :
    completionSubfunctorRestrict B S hS (f ≫ g) T'' T h =
      completionSubfunctorRestrict B S hS f T'' T' h₁ ≫
        completionSubfunctorRestrict B S hS g T' T h₂ := rfl

/-- Restricting completions along a composition is the composition of the restrictions. -/
theorem completionSheafRestrict_comp {F'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F'' ⟶ F') (g : F' ⟶ F) (T'' : Set (points B S hS F''))
    (T' : Set (points B S hS F')) (T : Set (points B S hS F))
    (h₁ : T'' ⊆ pointsMap B S hS F'' f ⁻¹' T') (h₂ : T' ⊆ pointsMap B S hS F' g ⁻¹' T)
    (h : T'' ⊆ pointsMap B S hS F'' (f ≫ g) ⁻¹' T) :
    completionSheafRestrict B S hS (f ≫ g) T'' T h =
      completionSheafRestrict B S hS f T'' T' h₁ ≫
        completionSheafRestrict B S hS g T' T h₂ :=
  (congrArg (fppfSheafification B S hS).map
      (completionSubfunctorRestrict_comp B S hS f g T'' T' T h₁ h₂ h)).trans
    ((fppfSheafification B S hS).map_comp _ _)

/-- The restriction morphism of completions is compatible with the morphisms into the
ambient spaces: the cartesian square of Stacks 0APV commutes for the general restriction
too. -/
theorem completionSheafRestrict_comp_inclusion (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T) :
    completionSheafRestrict B S hS f T' T h ≫ completionSheafInclusion B S hS F T =
      completionSheafInclusion B S hS F' T' ≫ sheafifiedULiftMap B S hS f :=
  (((fppfSheafification B S hS).map_comp
        (completionSubfunctorRestrict B S hS f T' T h)
        (completionSubfunctor B S hS F T).ι).symm.trans
      (congrArg (fppfSheafification B S hS).map
        (show completionSubfunctorRestrict B S hS f T' T h ≫
            (completionSubfunctor B S hS F T).ι =
          (completionSubfunctor B S hS F' T').ι ≫
            Functor.whiskerRight f uliftFunctor.{u + 1} from rfl))).trans
    ((fppfSheafification B S hS).map_comp _ _)

/-- The restriction morphism of open subspaces depends only on the morphism, not on the
witness that it carries the one set of points into the other. -/
theorem openSubspaceOfPointsRestrict_congr {f g : F' ⟶ F} (hfg : f = g)
    (W' : Set (points B S hS F')) (W : Set (points B S hS F))
    (h : W' ⊆ pointsMap B S hS F' f ⁻¹' W) (h' : W' ⊆ pointsMap B S hS F' g ⁻¹' W) :
    openSubspaceOfPointsRestrict B S hS f W' W h =
      openSubspaceOfPointsRestrict B S hS g W' W h' := by
  subst hfg
  rfl

/-- Restricting completion subfunctors along an identity is the identity. -/
theorem completionSubfunctorRestrict_id (T : Set (points B S hS F))
    (h : T ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' T) :
    completionSubfunctorRestrict B S hS (𝟙 F) T T h = 𝟙 _ := rfl

/-- Restricting completions along an identity is the identity. -/
theorem completionSheafRestrict_id (T : Set (points B S hS F))
    (h : T ⊆ pointsMap B S hS F (𝟙 F) ⁻¹' T) :
    completionSheafRestrict B S hS (𝟙 F) T T h = 𝟙 _ :=
  (congrArg (fppfSheafification B S hS).map
      (completionSubfunctorRestrict_id B S hS T h)).trans
    ((fppfSheafification B S hS).map_id _)

/-- For a source set that *equals* the inverse image the restriction morphism of completions
is the morphism of Stacks 0AMC composed with the transport along that equality. -/
theorem completionSheafRestrict_eq_eqToHom_comp (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T)
    (hT' : T' = pointsMap B S hS F' f ⁻¹' T) :
    completionSheafRestrict B S hS f T' T h =
      eqToHom (congrArg (completionSheaf B S hS F') hT') ≫
        completionSheafMap B S hS f T := by
  subst hT'
  rw [completionSheafRestrict_self]
  simp

/-- The restriction morphism of completions depends only on the morphism, not on the witness
that it carries the one set of points into the other. -/
theorem completionSheafRestrict_congr {f g : F' ⟶ F} (hfg : f = g)
    (T' : Set (points B S hS F')) (T : Set (points B S hS F))
    (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T) (h' : T' ⊆ pointsMap B S hS F' g ⁻¹' T) :
    completionSheafRestrict B S hS f T' T h =
      completionSheafRestrict B S hS g T' T h' := by
  subst hfg
  rfl

/-- The completion of a cartesian square of presheaves on the big fppf site of `S` along a
set `T` of points of the common target and its inverse images is cartesian, in the form that
presents the three source sets by equalities and uses the restriction morphisms
`AlgebraicGeometry.Space.completionSheafRestrict`.

This is `AlgebraicGeometry.Space.isPullback_completionSheafMap_of_isPullback`, that is
Stacks 0APV pasted with left exactness of fppf sheafification, with the transport along the
two descriptions of the set of points of the vertex absorbed into the restriction
morphism. -/
theorem isPullback_completionSheafRestrict {P X Y Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Q) (g : Y ⟶ Q) (hsq : IsPullback a b f g)
    (T : Set (points B S hS Q)) (TP : Set (points B S hS P)) (TX : Set (points B S hS X))
    (TY : Set (points B S hS Y)) (hTX : TX = pointsMap B S hS X f ⁻¹' T)
    (hTY : TY = pointsMap B S hS Y g ⁻¹' T) (hTP : TP = pointsMap B S hS P a ⁻¹' TX)
    (ha : TP ⊆ pointsMap B S hS P a ⁻¹' TX) (hb : TP ⊆ pointsMap B S hS P b ⁻¹' TY)
    (hf : TX ⊆ pointsMap B S hS X f ⁻¹' T) (hg : TY ⊆ pointsMap B S hS Y g ⁻¹' T) :
    IsPullback (completionSheafRestrict B S hS a TP TX ha)
      (completionSheafRestrict B S hS b TP TY hb)
      (completionSheafRestrict B S hS f TX T hf)
      (completionSheafRestrict B S hS g TY T hg) := by
  subst hTX hTY hTP
  rw [completionSheafRestrict_eq_eqToHom_comp B S hS b _ _ hb
    (preimage_pointsMap_eq_of_comm B S hS hsq.w T)]
  simpa only [completionSheafRestrict_self] using
    isPullback_completionSheafMap_of_isPullback B S hS hsq T

end Restrict

end Space

namespace Artin

attribute [local instance] Space.pointTopology

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In the situation of Stacks 0GH8, a witness of the compatibility between a morphism
`u : V ∖ Z ⟶ U'` and a morphism `x̂ : V_{/Z} ⟶ W`, in the sense of the discussion preceding
Stacks 0GHA: a proper morphism `p : V' ⟶ V` of algebraic spaces over `S` which is an
isomorphism over `V ∖ Z` (recorded as `isPullback_j`) and whose completion along `Z` is the
pullback of the formal modification `g` along `x̂` (recorded as `isPullback_xhat'`),
together with a morphism `x' : V' ⟶ X'` restricting to `u` over `V ∖ Z` and to the pullback
`x̂' : V'_{/Z} ⟶ X'_{/T'}` over `V'_{/Z}`.

By the main theorem on dilatations the morphism `p` is unique up to unique isomorphism, so
the existence of a witness is exactly the compatibility condition of the source. -/
structure CompatibilityWitness (c : ContractionSituation B S hS) (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V)))
    (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W) where
  /-- The algebraic space `V'` over `S`. -/
  V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `V'` is an algebraic space over `S`. -/
  isAlgebraicSpace_V' : IsAlgebraicSpace B S hS V'
  /-- The morphism `p : V' ⟶ V`. -/
  p : V' ⟶ yoneda.obj V
  /-- `p` is proper. -/
  isProper_p : Space.IsProper B S hS p
  /-- The morphism `j : V ∖ Z ⟶ V'` identifying `V ∖ Z` with an open subspace of `V'`. -/
  j : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ V'
  /-- `p` is an isomorphism over `V ∖ Z`, with `j` as the identification: `V ∖ Z` is the
  fibre product of `V ∖ Z` and `V'` over `V`. -/
  isPullback_j : IsPullback (𝟙 _) j
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι p
  /-- The morphism `x̂' : V'_{/Z} ⟶ X'_{/T'}`. -/
  xhat' : Space.completionSheaf B S hS V' (Space.pointsMap B S hS V' p ⁻¹' Z) ⟶
    Space.completionSheaf B S hS c.X' c.T'
  /-- The completion of `p` along `Z` is the pullback of the formal modification `g` along
  `x̂`, with `x̂'` as the second projection. -/
  isPullback_xhat' : IsPullback
    (Space.completionSheafRestrict B S hS p (Space.pointsMap B S hS V' p ⁻¹' Z) Z
      fun _ hz => hz) xhat' xhat c.g
  /-- The morphism `x' : V' ⟶ X'`. -/
  x' : V' ⟶ c.X'
  /-- `x'` restricts to `u` over `V ∖ Z`. -/
  restrict_x' : j ≫ x' = u ≫ c.U'.ι
  /-- `x'` restricts to `x̂'` over `V'_{/Z}`. -/
  completion_x' :
    Space.completionSheafInclusion B S hS V' (Space.pointsMap B S hS V' p ⁻¹' Z) ≫
        Space.sheafifiedULiftMap B S hS x' =
      xhat' ≫ Space.completionSheafInclusion B S hS c.X' c.T'

/-- In the situation of Stacks 0GH8, a triple `(Z, u', x̂)` over an object `V` of the big
fppf site over `S` satisfying the compatibility condition. For `V` a locally Noetherian
scheme over `S` this is the value of Artin's functor `F` at `V`. -/
structure Triple (c : ContractionSituation B S hS) (V : BigFppfOver B S hS) where
  /-- Condition (1): a subset `Z` of `|V|`. -/
  Z : Set (Space.points B S hS (yoneda.obj V))
  /-- Condition (1): `Z` is closed. -/
  isClosed_Z : IsClosed Z
  /-- Condition (2): a morphism `u' : V ∖ Z ⟶ U'` over `S`. -/
  u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor
  /-- Condition (3): a morphism `x̂ : V_{/Z} ⟶ W`. -/
  xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W
  /-- Condition (3): `x̂` is adic, which by Stacks 0AQ3 is to say that it is representable
  by algebraic spaces. -/
  adic_xhat : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xhat.hom
  /-- Condition (4): `u'` and `x̂` are compatible. -/
  compatible : Nonempty (CompatibilityWitness c V Z u xhat)

/-- Two triples are equal as soon as their first components are equal and their second and
third components agree over that equality. -/
theorem Triple.mk_congr {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    {Z Z' : Set (Space.points B S hS (yoneda.obj V))}
    (hZ : Z = Z') {hc hc' u u' x x' a a' w w'} (hu : HEq u u') (hx : HEq x x') :
    (Triple.mk (c := c) (V := V) Z hc u x a w) =
      Triple.mk Z' hc' u' x' a' w' := by
  subst hZ
  cases hu
  cases hx
  rfl

variable (c : ContractionSituation B S hS)

/-! ### Transporting the second and third components -/

section Transport

variable {F₃ F₂ F₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Restricting along an identity, read over an equality of sets of points. -/
theorem heq_openSubspaceOfPointsRestrict_id {f : F₁ ⟶ F₁} (hf : f = 𝟙 F₁)
    {W : Set (Space.points B S hS F₁)} {A : Set (Space.points B S hS F₁)} (hA : A = W)
    (h : Aᶜ ⊆ Space.pointsMap B S hS F₁ f ⁻¹' Wᶜ)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (y : (Space.openSubspaceOfPoints B S hS F₁ Wᶜ).toFunctor ⟶ Y) :
    HEq (Space.openSubspaceOfPointsRestrict B S hS f Aᶜ Wᶜ h ≫ y) y := by
  subst hA
  subst hf
  refine heq_of_eq ?_
  rw [Space.openSubspaceOfPointsRestrict_id, Category.id_comp]

/-- Restricting along an identity, read over an equality of sets of points. -/
theorem heq_completionSheafRestrict_id {f : F₁ ⟶ F₁} (hf : f = 𝟙 F₁)
    {W : Set (Space.points B S hS F₁)} {A : Set (Space.points B S hS F₁)} (hA : A = W)
    (h : A ⊆ Space.pointsMap B S hS F₁ f ⁻¹' W)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (y : Space.completionSheaf B S hS F₁ W ⟶ Y) :
    HEq (Space.completionSheafRestrict B S hS f A W h ≫ y) y := by
  subst hA
  subst hf
  refine heq_of_eq ?_
  rw [Space.completionSheafRestrict_id, Category.id_comp]

/-- Restricting along a composition, read over an equality of sets of points. -/
theorem heq_openSubspaceOfPointsRestrict_comp (f : F₃ ⟶ F₂) (g : F₂ ⟶ F₁)
    {k : F₃ ⟶ F₁} (hk : k = f ≫ g) {W : Set (Space.points B S hS F₁)}
    {A : Set (Space.points B S hS F₃)}
    (hA : A = Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W))
    (h : Aᶜ ⊆ Space.pointsMap B S hS F₃ k ⁻¹' Wᶜ)
    (h₁ : (Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W))ᶜ ⊆
      Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W)ᶜ)
    (h₂ : (Space.pointsMap B S hS F₂ g ⁻¹' W)ᶜ ⊆ Space.pointsMap B S hS F₂ g ⁻¹' Wᶜ)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (y : (Space.openSubspaceOfPoints B S hS F₁ Wᶜ).toFunctor ⟶ Y) :
    HEq (Space.openSubspaceOfPointsRestrict B S hS k Aᶜ Wᶜ h ≫ y)
      (Space.openSubspaceOfPointsRestrict B S hS f
          (Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W))ᶜ
          (Space.pointsMap B S hS F₂ g ⁻¹' W)ᶜ h₁ ≫
        (Space.openSubspaceOfPointsRestrict B S hS g
          (Space.pointsMap B S hS F₂ g ⁻¹' W)ᶜ Wᶜ h₂ ≫ y)) := by
  subst hA
  subst hk
  refine heq_of_eq ?_
  rw [Space.openSubspaceOfPointsRestrict_comp B S hS f g _ _ _ h₁ h₂, Category.assoc]

/-- Restricting along a composition, read over an equality of sets of points. -/
theorem heq_completionSheafRestrict_comp (f : F₃ ⟶ F₂) (g : F₂ ⟶ F₁)
    {k : F₃ ⟶ F₁} (hk : k = f ≫ g) {W : Set (Space.points B S hS F₁)}
    {A : Set (Space.points B S hS F₃)}
    (hA : A = Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W))
    (h : A ⊆ Space.pointsMap B S hS F₃ k ⁻¹' W)
    (h₁ : Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W) ⊆
      Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W))
    (h₂ : Space.pointsMap B S hS F₂ g ⁻¹' W ⊆ Space.pointsMap B S hS F₂ g ⁻¹' W)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (y : Space.completionSheaf B S hS F₁ W ⟶ Y) :
    HEq (Space.completionSheafRestrict B S hS k A W h ≫ y)
      (Space.completionSheafRestrict B S hS f
          (Space.pointsMap B S hS F₃ f ⁻¹' (Space.pointsMap B S hS F₂ g ⁻¹' W))
          (Space.pointsMap B S hS F₂ g ⁻¹' W) h₁ ≫
        (Space.completionSheafRestrict B S hS g
          (Space.pointsMap B S hS F₂ g ⁻¹' W) W h₂ ≫ y)) := by
  subst hA
  subst hk
  refine heq_of_eq ?_
  rw [Space.completionSheafRestrict_comp B S hS f g _ _ _ h₁ h₂, Category.assoc]

end Transport

/-! ### The compatibility condition is preserved -/

/-- **Stacks 0GHA**, the content of the proof: the compatibility condition is preserved by
the rule of the statement. Given a witness `V'₁ ⟶ V₁`, `x̂'₁`, `x'₁` of the compatibility
between `u'₁` and `x̂₁`, the fibre product `V'₂ = V₂ ×_{V₁} V'₁` together with the
composition of `x̂'₁` with `V'_{2,/Z₂} ⟶ V'_{1,/Z₁}` and the composition of `x'₁` with
`V'₂ ⟶ V'₁` witnesses the compatibility between `u'₂` and `x̂₂`. -/
theorem nonempty_compatibilityWitness_map {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (t : Triple c V₁) (Z₂ : Set (Space.points B S hS (yoneda.obj V₂)))
    (hZ₂ : Z₂ = Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z)
    (h₁ : Z₂ᶜ ⊆ Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Zᶜ)
    (h₂ : Z₂ ⊆ Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z) :
    Nonempty (CompatibilityWitness c V₂ Z₂
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) Z₂ᶜ t.Zᶜ h₁ ≫ t.u)
      (Space.completionSheafRestrict B S hS (yoneda.map φ) Z₂ t.Z h₂ ≫ t.xhat)) := by
  obtain ⟨w⟩ := t.compatible
  have hpb : IsPullback (pullback.fst (yoneda.map φ) w.p) (pullback.snd (yoneda.map φ) w.p)
      (yoneda.map φ) w.p := IsPullback.of_hasPullback _ _
  have halg : IsAlgebraicSpace B S hS (pullback (yoneda.map φ) w.p) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS V₂)
      w.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS V₁)
  -- the second projection carries the inverse image of `Z₂` into that of `t.Z`
  have hb : Space.pointsMap B S hS (pullback (yoneda.map φ) w.p)
        (pullback.fst (yoneda.map φ) w.p) ⁻¹' Z₂ ⊆
      Space.pointsMap B S hS (pullback (yoneda.map φ) w.p)
        (pullback.snd (yoneda.map φ) w.p) ⁻¹'
          (Space.pointsMap B S hS w.V' w.p ⁻¹' t.Z) :=
    (Set.preimage_mono h₂).trans (Space.preimage_pointsMap_eq_of_comm B S hS hpb.w t.Z).subset
  have hproper : Space.IsProper B S hS (pullback.fst (yoneda.map φ) w.p) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (pullback.fst (yoneda.map φ) w.p) :
          (⟨pullback (yoneda.map φ) w.p, halg⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V₂, isAlgebraicSpace_yoneda B S hS V₂⟩)
        (ObjectProperty.homMk (pullback.snd (yoneda.map φ) w.p) :
          (⟨pullback (yoneda.map φ) w.p, halg⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨w.V', w.isAlgebraicSpace_V'⟩)
        (ObjectProperty.homMk (yoneda.map φ) :
          (⟨yoneda.obj V₂, isAlgebraicSpace_yoneda B S hS V₂⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V₁, isAlgebraicSpace_yoneda B S hS V₁⟩)
        (ObjectProperty.homMk w.p :
          (⟨w.V', w.isAlgebraicSpace_V'⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj V₁, isAlgebraicSpace_yoneda B S hS V₁⟩) :=
      IsPullback.of_map_of_faithful
        (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS F)) hpb
    exact (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq.flip
      w.isProper_p
  have hr : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) Z₂ᶜ t.Zᶜ h₁ ≫
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) t.Zᶜ).ι =
    (Space.openSubspaceOfPoints B S hS (yoneda.obj V₂) Z₂ᶜ).ι ≫ yoneda.map φ :=
    Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _
  have hj : (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) t.Zᶜ).ι = w.j ≫ w.p :=
    (Category.id_comp _).symm.trans w.isPullback_j.w
  have hlift : (Space.openSubspaceOfPoints B S hS (yoneda.obj V₂) Z₂ᶜ).ι ≫ yoneda.map φ =
      (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) Z₂ᶜ t.Zᶜ h₁ ≫ w.j) ≫ w.p := by
    rw [Category.assoc, ← hj, hr]
  refine ⟨{ V' := pullback (yoneda.map φ) w.p
            isAlgebraicSpace_V' := halg
            p := pullback.fst (yoneda.map φ) w.p
            isProper_p := hproper
            j := hpb.lift _ _ hlift
            isPullback_j := ?_
            xhat' := Space.completionSheafRestrict B S hS
              (pullback.snd (yoneda.map φ) w.p) _ _ hb ≫ w.xhat'
            isPullback_xhat' := ?_
            x' := pullback.snd (yoneda.map φ) w.p ≫ w.x'
            restrict_x' := ?_
            completion_x' := ?_ }⟩
  · refine (IsPullback.of_right ?_ ?_ hpb.flip).flip
    · have hid : IsPullback
          (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) Z₂ᶜ t.Zᶜ h₁) (𝟙 _) (𝟙 _)
          (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) Z₂ᶜ t.Zᶜ h₁) :=
        IsPullback.of_id_snd
      have hcomposite := hid.paste_horiz w.isPullback_j.flip
      rwa [hr, ← hpb.lift_snd _ _ hlift] at hcomposite
    · rw [hpb.lift_fst, Category.id_comp]
  · exact (Space.isPullback_completionSheafRestrict B S hS (pullback.fst (yoneda.map φ) w.p)
      (pullback.snd (yoneda.map φ) w.p) (yoneda.map φ) w.p hpb t.Z _ Z₂ _ hZ₂ rfl rfl
      (fun _ hz => hz) hb h₂ (fun _ hz => hz)).paste_vert w.isPullback_xhat'
  · rw [← Category.assoc, hpb.lift_snd, Category.assoc, w.restrict_x', Category.assoc]
  · rw [Space.sheafifiedULiftMap_comp, ← Category.assoc,
      ← Space.completionSheafRestrict_comp_inclusion B S hS
        (pullback.snd (yoneda.map φ) w.p) _ _ hb,
      Category.assoc, w.completion_x', ← Category.assoc]

/-! ### The functor -/

/-- **Stacks 0GHA**, the value of `F` on a morphism: the triple `(Z₂, u'₂, x̂₂)` with `Z₂`
the inverse image of `Z₁`, with `u'₂` the composition of `u'₁` and the restriction of `φ`,
and with `x̂₂` the composition of `x̂₁` and the induced morphism of completions. -/
noncomputable def mapTriple {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁) :
    Triple c V₂ where
  Z := Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z
  isClosed_Z := t.isClosed_Z.preimage (Space.continuous_pointsMap B S hS _)
  u := Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ) _ t.Zᶜ (fun _ hz => hz) ≫ t.u
  xhat := Space.completionSheafRestrict B S hS (yoneda.map φ) _ t.Z (fun _ hz => hz) ≫ t.xhat
  adic_xhat :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
        (isAlgebraicSpace_yoneda B S hS V₂) (isAlgebraicSpace_yoneda B S hS V₁)
        (yoneda.map φ) t.Z)
      t.adic_xhat
  compatible := nonempty_compatibilityWitness_map c φ t _ rfl _ _

/-- The first functor law of Stacks 0GHA. -/
theorem mapTriple_id {V : BigFppfOver B S hS} (t : Triple c V) :
    mapTriple c (𝟙 V) t = t := by
  obtain ⟨Z, hc, u, x, a, w⟩ := t
  have hmap : yoneda.map (𝟙 V) = 𝟙 (yoneda.obj V) := yoneda.map_id V
  have hZ : Space.pointsMap B S hS (yoneda.obj V) (yoneda.map (𝟙 V)) ⁻¹' Z = Z := by
    rw [hmap, Space.pointsMap_id, Set.preimage_id]
  exact Triple.mk_congr hZ (heq_openSubspaceOfPointsRestrict_id hmap hZ _ u)
    (heq_completionSheafRestrict_id hmap hZ _ x)

/-- The second functor law of Stacks 0GHA. -/
theorem mapTriple_comp {V₃ V₂ V₁ : BigFppfOver B S hS} (φ : V₃ ⟶ V₂) (ψ : V₂ ⟶ V₁)
    (t : Triple c V₁) :
    mapTriple c (φ ≫ ψ) t = mapTriple c φ (mapTriple c ψ t) := by
  obtain ⟨Z, hc, u, x, a, w⟩ := t
  have hmap : yoneda.map (φ ≫ ψ) = yoneda.map φ ≫ yoneda.map ψ := yoneda.map_comp φ ψ
  have hZ : Space.pointsMap B S hS (yoneda.obj V₃) (yoneda.map (φ ≫ ψ)) ⁻¹' Z =
      Space.pointsMap B S hS (yoneda.obj V₃) (yoneda.map φ) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map ψ) ⁻¹' Z) := by
    rw [hmap, Space.pointsMap_comp, Set.preimage_comp]
  exact Triple.mk_congr hZ
    (heq_openSubspaceOfPointsRestrict_comp (yoneda.map φ) (yoneda.map ψ) hmap hZ _
      (fun _ hz => hz) (fun _ hz => hz) u)
    (heq_completionSheafRestrict_comp (yoneda.map φ) (yoneda.map ψ) hmap hZ _
      (fun _ hz => hz) (fun _ hz => hz) x)

end ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open ContractionSituation in
/-- **Stacks 0GHA.** In the situation of Stacks 0GH8 the rule `F` that sends a locally
Noetherian scheme `V` over `S` to the set of triples `(Z, u', x̂)` satisfying the
compatibility condition, and that sends a morphism `φ : V₂ ⟶ V₁` of locally Noetherian
schemes over `S` to the map `F(φ) : F(V₁) ⟶ F(V₂)` sending `(Z₁, u'₁, x̂₁)` to
`(Z₂, u'₂, x̂₂)` with `Z₂` the inverse image of `Z₁` under `φ`, with `u'₂` the composition
of `u'₁` and `φ|_{V₂ ∖ Z₂}`, and with `x̂₂` the composition of `x̂₁` and `φ_{/Z₂}`, is a
contravariant functor. -/
@[stacks 0GHA "the functor F, its values on objects and morphisms and the two functor laws, \
unconditionally; adicness of the third component of a triple is the defining condition of \
Stacks 0AQ3, that the morphism be representable by algebraic spaces"]
noncomputable def contractionFunctor (c : ContractionSituation B S hS) :
    (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj V := Triple c V.unop.obj
  map φ := ↾fun t => mapTriple c φ.unop.hom t
  map_id V := by
    ext t
    exact mapTriple_id c t
  map_comp φ ψ := by
    ext t
    exact mapTriple_comp c ψ.unop.hom φ.unop.hom t

end Artin

end AlgebraicGeometry

end
