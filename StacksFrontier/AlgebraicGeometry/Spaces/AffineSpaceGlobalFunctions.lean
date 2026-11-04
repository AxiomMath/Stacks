module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# The global functions of an affine algebraic space

Let `T` be an object of the big fppf site of `S`. The algebraic space `h_T` it represents has
`Γ(T, 𝒪_T)` as its ring of global regular functions: a compatible family of regular functions
on the étale charts of `h_T` is determined by, and may be built from, its value on the
*identity* chart.

Both halves come from the identity being a chart, and neither needs a terminality hypothesis on
`S`, so this holds over an arbitrary base scheme.

The point of the statement is that `AlgebraicGeometry.Space.globalFunctions` is a ring of
compatible families indexed by the small étale site, a category one universe above the schemes,
whereas `Γ(T, 𝒪_T)` is a ring of the working universe. For an *affine* algebraic space the
identification therefore also exhibits the ring of global functions as the ring whose spectrum
the space is — the input the proof of Stacks 07SQ takes from the affineness of the limit, there
being no other way to read `Γ(X, 𝒪_X) = colim Γ(X_i, 𝒪_{X_i})` as a statement about the ring of
the affine scheme `X`.

## Main definitions

* `AlgebraicGeometry.Space.reprGlobalFunctionsEquiv`: the ring isomorphism
  `Γ(h_T, 𝒪) ≅ Γ(T, 𝒪_T)`, given by restriction to the identity chart.
* `AlgebraicGeometry.Space.globalFunctionsMapEquiv`: the global functions of isomorphic
  algebraic spaces are isomorphic rings, along `AlgebraicGeometry.Space.globalFunctionsMap`.

## Main results

* `AlgebraicGeometry.Space.reprGlobalFunctionsSection_val`: the chart formula for the
  global function attached to a regular function on `T` — its value at a chart `V` is the
  pullback along the morphism of schemes `V ⟶ T`.
* `AlgebraicGeometry.Space.globalFunctionsChartRestriction_eq_of_idChart`: the same formula for
  an *arbitrary* global function on `h_T`, which is what makes restriction to the identity chart
  injective, and is the only input the two round trips need.
* `AlgebraicGeometry.Space.nonempty_globalFunctionsEquiv_of_isAffineSpace`: an affine algebraic
  space has the regular functions of the affine scheme representing it as its ring of global
  functions.

## Implementation notes

*Why no injectivity argument is needed.* That restriction to a surjective chart is injective is
`AlgebraicGeometry.Space.injective_globalFunctionsChartRestriction_of_isSurjective`, and the
identity chart is surjective, so one of the two round trips could be had that way. It is cheaper
not to: the identity chart is the *terminal* object of the small étale site of a representable
presheaf, which is `AlgebraicGeometry.Space.isTerminal_idChart`, and
`AlgebraicGeometry.Space.globalFunctionsChartRestriction_naturality` at the unique morphism to
it already says that the value at any chart `V` is the pullback of the value at the identity
chart. Both round trips are instances of that one formula.

*Which reading of the algebraic space of `T`.* The statements below need its presheaf to be
*syntactically* `yoneda.obj T`, since `AlgebraicGeometry.Space.idChart` and
`AlgebraicGeometry.Space.isTerminal_idChart` are stated there, and a chart's underlying object of
the site must reduce to `T` for the rewriting in the round trips to be type-correct. So
`AlgebraicGeometry.Space.representedAlgebraicSpace` is used, which is reducible and documented
for exactly that property, and not `AlgebraicGeometry.Space.schemeSpace`, which is the same term
but semireducible.

*The inverse.* It is `AlgebraicGeometry.Space.pullbackToGlobalFunctions` at the identity
morphism of `h_T`, which is the construction of the forward map of Stacks 05Z1. Only that
construction is used, not the bijection, so the terminality hypothesis of Stacks 05Z1 — needed
solely to produce a morphism *to* an affine object out of a ring homomorphism — does not enter.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity of the algebraic space represented by an object of the site, written so that its
underlying morphism of presheaves is the identity on the nose. -/
abbrev reprSpaceId (T : BigFppfOver B S hS) :
    representedAlgebraicSpace B S hS T ⟶ representedAlgebraicSpace B S hS T :=
  ObjectProperty.homMk (𝟙 (yoneda.obj T))

/-! ### Restriction to the identity chart, and its inverse -/

/-- Restriction of a global regular function on `h_T` to the identity chart. -/
def reprGlobalFunctionsRestriction (T : BigFppfOver B S hS) :
    globalFunctions B S hS (yoneda.obj T) →+*
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  globalFunctionsChartRestriction B S hS (representedAlgebraicSpace B S hS T) (idChart B S hS T)

/-- A regular function on `T`, read as a global regular function on `h_T` by pulling it back to
every étale chart. -/
def reprGlobalFunctionsSection (T : BigFppfOver B S hS) :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+*
      globalFunctions B S hS (yoneda.obj T) :=
  pullbackToGlobalFunctions B S hS (representedAlgebraicSpace B S hS T) T (reprSpaceId B S hS T)

/-- **The chart formula.** The value at an étale chart `V` of the global function attached to a
regular function `s` on `T` is the pullback of `s` along the morphism of schemes `V ⟶ T`. -/
theorem reprGlobalFunctionsSection_val {T : BigFppfOver B S hS}
    (V : SmallEtale B S hS (yoneda.obj T))
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (reprGlobalFunctionsSection B S hS T s).val (op V) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage V.obj.hom))) s := by
  refine (pullbackToGlobalFunctions_apply_chart B S hS (representedAlgebraicSpace B S hS T) T
    (reprSpaceId B S hS T) V s).trans ?_
  have hcomp : V.obj.hom ≫ (reprSpaceId B S hS T).hom = V.obj.hom := Category.comp_id _
  rw [hcomp]

/-- **The chart formula for an arbitrary global regular function on `h_T`.** Its value at an
étale chart `V` is the pullback along `V ⟶ T` of its value at the identity chart.

This is `AlgebraicGeometry.Space.globalFunctionsChartRestriction_naturality` at the unique
morphism to the terminal object of the small étale site. -/
theorem globalFunctionsChartRestriction_eq_of_idChart {T : BigFppfOver B S hS}
    (V : SmallEtale B S hS (yoneda.obj T))
    (s : globalFunctions B S hS (yoneda.obj T)) :
    globalFunctionsChartRestriction B S hS (representedAlgebraicSpace B S hS T) V s =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj T)).map
          ((isTerminal_idChart B S hS T).from V))))
        (reprGlobalFunctionsRestriction B S hS T s) :=
  (congrFun (globalFunctionsChartRestriction_naturality B S hS (representedAlgebraicSpace B S hS T)
    ((isTerminal_idChart B S hS T).from V)) s).symm

/-- The object of the site underlying the unique morphism of charts to the identity chart is the
chart's structure morphism, read through the Yoneda embedding. -/
theorem toOver_map_from_idChart {T : BigFppfOver B S hS}
    (V : SmallEtale B S hS (yoneda.obj T)) :
    (SmallEtale.toOver B S hS (yoneda.obj T)).map ((isTerminal_idChart B S hS T).from V) =
      yoneda.preimage V.obj.hom := by
  refine yoneda.map_injective ?_
  refine Eq.trans ?_ (yoneda.map_preimage V.obj.hom).symm
  exact (Category.comp_id _).symm.trans (CostructuredArrow.w _)

/-- Restriction to the identity chart undoes the passage from a regular function on `T` to a
global regular function on `h_T`. -/
theorem reprGlobalFunctionsRestriction_section (T : BigFppfOver B S hS)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    reprGlobalFunctionsRestriction B S hS T
        (reprGlobalFunctionsSection B S hS T s) = s := by
  refine (reprGlobalFunctionsSection_val B S hS (idChart B S hS T) s).trans ?_
  show Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
    (yoneda.preimage (𝟙 (yoneda.obj T)) : T ⟶ T))) s = s
  rw [Functor.preimage_id, CategoryTheory.Functor.map_id]
  rfl

/-- The passage from a regular function on `T` to a global regular function on `h_T` undoes
restriction to the identity chart. -/
theorem reprGlobalFunctionsSection_restriction (T : BigFppfOver B S hS)
    (s : globalFunctions B S hS (yoneda.obj T)) :
    reprGlobalFunctionsSection B S hS T
        (reprGlobalFunctionsRestriction B S hS T s) = s := by
  refine Subtype.ext (funext fun V => ?_)
  refine (reprGlobalFunctionsSection_val B S hS V.unop
    (reprGlobalFunctionsRestriction B S hS T s)).trans ?_
  rw [← toOver_map_from_idChart B S hS V.unop]
  exact (globalFunctionsChartRestriction_eq_of_idChart B S hS V.unop s).symm

/-- **The global functions of the algebraic space of a scheme over `S` are the regular functions
on that scheme**, by restriction to the identity chart. -/
def reprGlobalFunctionsEquiv (T : BigFppfOver B S hS) :
    globalFunctions B S hS (yoneda.obj T) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) where
  toFun := reprGlobalFunctionsRestriction B S hS T
  invFun := reprGlobalFunctionsSection B S hS T
  left_inv := reprGlobalFunctionsSection_restriction B S hS T
  right_inv := reprGlobalFunctionsRestriction_section B S hS T
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism of `AlgebraicGeometry.Space.reprGlobalFunctionsEquiv` is restriction to the
identity chart, which is what makes it canonical. -/
theorem reprGlobalFunctionsEquiv_apply (T : BigFppfOver B S hS)
    (s : globalFunctions B S hS (yoneda.obj T)) :
    reprGlobalFunctionsEquiv B S hS T s =
      reprGlobalFunctionsRestriction B S hS T s := rfl

/-! ### Transport along an isomorphism of algebraic spaces -/

/-- **The global functions of isomorphic algebraic spaces are isomorphic rings**, along
`AlgebraicGeometry.Space.globalFunctionsMap`. -/
def globalFunctionsMapEquiv {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) :
    globalFunctions' B S hS Y.obj ≃+* globalFunctions' B S hS X.obj where
  toFun := globalFunctionsMap B S hS e.hom
  invFun := globalFunctionsMap B S hS e.inv
  left_inv s := by
    rw [← RingHom.comp_apply, ← globalFunctionsMap_comp, e.inv_hom_id,
      globalFunctionsMap_id, RingHom.id_apply]
  right_inv s := by
    rw [← RingHom.comp_apply, ← globalFunctionsMap_comp, e.hom_inv_id,
      globalFunctionsMap_id, RingHom.id_apply]
  map_mul' := map_mul _
  map_add' := map_add _

/-- **An affine algebraic space has the regular functions of a representing affine scheme as its
ring of global functions.** The space is isomorphic to the one represented by an object of the
site with affine underlying scheme, and the global functions of the latter are the regular
functions on that scheme. -/
theorem nonempty_globalFunctionsEquiv_of_isAffineSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAffineSpace B S hS F) :
    ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (globalFunctions B S hS F ≃+*
        Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) := by
  have hFalg : IsAlgebraicSpace B S hS F := hF.isAlgebraicSpace
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  refine ⟨T, hT, ⟨?_⟩⟩
  let eS : (⟨F, hFalg⟩ : AlgebraicSpaces B S hS) ≅ representedAlgebraicSpace B S hS T :=
    Functor.preimageIso (ObjectProperty.ι _) e
  exact (globalFunctionsMapEquiv B S hS eS).symm.trans
    (reprGlobalFunctionsEquiv B S hS T)

end AlgebraicGeometry.Space

end
