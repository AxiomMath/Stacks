module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExact

/-!
# Sections with support are étale-local in every degree

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Inverse image of
abelian sheaves along `f` is restriction along postcomposition of étale charts,
`AlgebraicGeometry.Space.etaleAbelianRestriction`, and
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportEtaleLocal.lean` identifies the
subsheaves of sections with support across it in degree zero.  This file extends that
identification to the right derived functors, in every degree, which is the sheaf-level
conclusion of **Stacks 0A4P**.

The source's argument is that an injective resolution of `F` pulls back to an injective
resolution of `f⁻¹F`, so the two inputs are that `f⁻¹` is exact and that it carries injective
abelian sheaves to injective abelian sheaves.  Both are proved here, the second one by
constructing the left adjoint `f_!` of `f⁻¹` and showing it exact.

## The left adjoint

`f_!` is Mathlib's `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` along
`AlgebraicGeometry.Space.smallEtalePostcomp`, that is, sheafification of the left Kan extension.
Its exactness is the same fibrewise argument that
`StacksFrontier/CategoryTheory/Sites/Topos/LocalizationShriekExact.lean` runs for the projection
from the site of elements of a presheaf of sets, carried out here directly on the small étale
sites:

* for a chart `W` of `Y`, the comma category `CostructuredArrow j.op W` computing the Kan
  extension at `W` decomposes into connected components indexed by the `Y`-morphisms
  `ψ : W ⟶ X`, the component of `ψ` having the chart `(W, ψ)` of `X` as its initial object.
  That `(W, ψ)` *is* an étale chart of `X` is the cancellation property of étaleness
  (Stacks 03FV): `ψ` composed with `f` is étale and `f` is étale;
* so the discrete category on that set of morphisms is final in the comma category, the Kan
  extension at `W` is the coproduct `⨁_ψ G(W, ψ)`, and coproducts of abelian groups are exact
  (Grothendieck's axiom AB4);
* sheafification is exact, so `f_!` is left exact, hence preserves monomorphisms, hence its
  right adjoint `f⁻¹` preserves injective objects (Stacks 015Z).

## Main results

* `AlgebraicGeometry.Space.isEtaleChart_of_comp_etale`: **Stacks 03FV** for charts — a chart of
  `X` whose composite with `f` is an étale chart of `Y` is an étale chart of `X`.
* `AlgebraicGeometry.Space.EtaleShriek.fibFunctor_final`: the discrete fibre is final in the
  comma category computing the left Kan extension along `j.op`.
* `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleAbelianRestriction`: **inverse image
  along an étale morphism preserves injective abelian sheaves.**
* `AlgebraicGeometry.Space.preservesFiniteColimits_etaleAbelianRestriction`: inverse image along
  an étale morphism is right exact. Instance search makes it left exact, since
  `AlgebraicGeometry.Space.etaleAbelianRestriction` is `Functor.sheafPushforwardContinuous`, a
  right adjoint; so it is exact.
* `AlgebraicGeometry.Space.higherSectionsWithSupportEtaleRestrictionIso` and
  `AlgebraicGeometry.Space.closedHigherSectionsWithSupportEtaleRestrictionIso`: **Stacks 0A4P**,
  the sheaf-level conclusion in every degree, on the ambient small étale site.

## Implementation notes

The comparison is assembled from three pieces of homological algebra that are already in the
tree: `CategoryTheory.Functor.rightDerivedCompIso` pulls the exact functor `f⁻¹` out of a right
derived functor; `CategoryTheory.Functor.rightDerivedIsoOfNatIso` transports along the
degree-zero comparison `AlgebraicGeometry.Space.sectionsWithSupportEtaleRestrictionIso`; and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` — Stacks 015Z — pushes `f⁻¹`
back in, which is where preservation of injectives is used.  The same three steps are
`StacksTag03LR.rightDerivedBaseChangeIso`.

What is proved here is the sheaf-level conclusion of Stacks 0A4P on the *ambient* small étale
site of `X`, in every degree, for an arbitrary set `T` of points of `Y` and, specialised,
for the inverse image of a subspace presented by a cartesian square.

The source states the sheaf identity on `Z = f⁻¹Z` rather than on the ambient site, and states
in addition the global identity `H^q_Z(Y, F) = H^q_{f⁻¹Z}(X, f⁻¹F)`.  Both need to move the
comparison across the closed immersions, that is the compatibility
`i_{f⁻¹Z}⁻¹ ∘ f⁻¹ ≅ k⁻¹ ∘ i_Z⁻¹` of inverse image along a closed immersion with restriction
along postcomposition, where `k : f⁻¹Z ⟶ Z` is the isomorphism the source assumes.  The
corresponding statement for sheaves of sets is
`AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso`, Stacks 03LR's footnote; at abelian
coefficients it needs Stacks 03LQ at abelian coefficients.

The sheaf identity on `Z` is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleAbelianInverseImageSquare.lean`, as
`AlgebraicGeometry.Space.closedHigherSectionsWithSupportOnSubspaceIso`: Stacks 03LQ at abelian
coefficients is `AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso`, which
identifies `AlgebraicGeometry.Space.etaleAbelianRestriction` — the functor this file's
comparisons are stated in — with the inverse image of abelian sheaves along the morphism of
small étale topoi, and the footnote at abelian coefficients is
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageSquareIso`, so whiskering this file's
ambient comparison by inverse image along `i_{f⁻¹Z}` gives
`k⁻¹(H^q_Z(F)|_Z) = H^q_{f⁻¹Z}(f⁻¹F)|_{f⁻¹Z}` on `f⁻¹Z` — the source's statement with the
source's hypothesis on `k` removed rather than used.  Putting that hypothesis back in and
cancelling `k` gives the identity on `Z` itself,
`AlgebraicGeometry.Space.closedHigherSectionsWithSupportOnZIso`, which is the reading the
source states; the cancellation is two applications of the composition isomorphism of
Stacks 03G2, part (3) at abelian coefficients, at `inv k ≫ k = 𝟙 Z` and at `𝟙 Z ≫ i_Z = i_Z`,
and so needs no unit law for `AlgebraicGeometry.Space.smallToposMorphism`.

The global identity is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/GlobalSectionsWithSupportEtaleExcision.lean`, as
`AlgebraicGeometry.Space.closedCohomologyWithSupportEtaleExcisionIso`.  It does not go through a
comparison `Γ(Y, i_*G) ≅ Γ(Z, G)` of global sections across a closed immersion, for which both
site-theoretic routes fail (see below).

What it needs is a covering of `Y` itself, and the small étale site has no object `Y` to cover —
its objects are étale scheme charts, so global sections there is a limit over the whole site and is
evaluation nowhere.  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleGlobalSectionsTerminal.lean`
supplies the missing move: `AlgebraicGeometry.Space.ΓTerminalNatIso` identifies global sections
over the small étale site of the restriction of a spaces-étale sheaf with its sections at the
terminal object `Y` of the spaces-étale site, naturally in the sheaf and at arbitrary
coefficients.  On the spaces-étale site of Stacks 03G0 both `X` and the open complement `Y ∖ Z`
*are* objects, and together they cover `Y`:
`AlgebraicGeometry.Space.isCovering_excisionCover` of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionCoveringOverSubspace.lean`, where `|f|` reaches
every point of `Z` precisely because the source's `k` is an isomorphism — `f` itself is not
surjective.

So the global clause is the sheaf condition for that two-element covering, which is the
source's own excision argument.  Sections of `ℋ_Z(F)` over an object lying outside `Z` vanish,
so the second member of the covering and every overlap involving it contribute nothing, and the
only compatibility left is that two morphisms `V ⟶ X` over `Y` restrict a section of `ℋ_Z(F)`
over `X` to the same section over `V`.  That is where the hypothesis on `k` enters a second
time: by `AlgebraicGeometry.Space.eq_of_comp_eq_of_factorsThrough_subspace` the two morphisms
agree over `Z`, hence agree on the base change of the étale diagonal of `f`
(`AlgebraicGeometry.Space.isEtale_selfFibreDiagonal`), an object of the site through which
everything of `V` lying over `Z` factors; and the section vanishes on the open complement of
that part.

The two counterexamples below rule out the other reading, suggested by the source's phrasing,
in which the global clause is obtained from the sheaf identity on `Z` by comparing global
sections across the closed immersion.

*The dense-subsite route fails.* Base change of étale scheme
charts along a closed immersion is cover dense and locally full — that is Stacks 04E5,
`AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isClosedImmersion` and
`AlgebraicGeometry.Space.smallBaseChange_isLocallyFull_of_isClosedImmersion` — but it is not
locally faithful.
Over a field, take `Y = 𝔸¹`, `Z = {0}`, and the two étale charts `U₁ = 𝔸¹ ⊔ (𝔸¹ ∖ {0})` and
`U₂ = 𝔸¹ ⊔ 𝔸¹` of `Y`, with `a` the first inclusion on both components of `U₁` and `b` the
first inclusion on the first component and the second on the second.  Then `a ≠ b`, their base
changes along `Z ⊂ Y` agree because `U₁ ×_Y Z = {0} ⊔ ∅` meets only the first component, and
the sieve on `U₁` of morphisms equalizing `a` and `b` is the sieve of morphisms through the
first component, which does not cover.  This is why
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite` is stated for a *thickening*
and not for a closed immersion: as its own note records, local faithfulness there comes from
surjectivity on points, which is exactly the thickening hypothesis, and a `Z` with `|Z| = |Y|`
makes Stacks 0A4P vacuous.  For the same reason `smallBaseChange` is not final: finality would
say every étale chart of `Z` maps into the base change of a *single* étale chart of `Y`, a
global lifting statement of which Stacks 04E5 gives only the local form.

*The constant-sheaf route fails too.*
`Γ(X, i_*-) ≅ Γ(Z, -)` is true, and is equivalent by uniqueness of right adjoints to `i⁻¹`
carrying the constant sheaf to the constant sheaf.  The available construction of that
compatibility is
`Stacks.ConstantSheaf.overPullbackConstantSheafIso`, which gets it from
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`: sheafification
commutes with restriction along a functor that is both continuous *and cocontinuous*.  Base
change of étale charts along a closed immersion is not cocontinuous.  Over a field with
`Y = 𝔸¹` and `Z = {0}`, the chart `U = 𝔸¹ ∖ {0}` of `Y` has `U ×_Y Z = ∅`; the empty sieve
covers `∅` in `Z_étale`, and its preimage under base change is the empty sieve on the nonempty
`U`, which does not cover.  That this must fail is visible in the conclusion the construction
would produce — `const_Y ≅ i_*(const_Z)`, which is false, the right-hand side being supported
on `Z`.

So what that route would need is the compatibility of `constantSheaf` with `sheafPullback` for a
functor that is continuous only, and *that* is a statement of a different kind from the one this
file proves: it asks the comma categories computing the left Kan extension to be locally connected,
whereas the fibre computation above says its own comma categories are *disconnected*, one
initial object per `Y`-morphism `W ⟶ X`, which is exactly why `f_!` is a coproduct over a
fibre and does not preserve constant sheaves.  The initial-object argument of this file
therefore does not transfer.
That gap is already there in degree zero; the global clause avoids it through the
terminal-object comparison above.

The hypothesis of the source that `f⁻¹Z → Z` is an isomorphism plays no part in what is proved
here, exactly as in the degree-zero file, and is therefore not assumed.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03FV for charts.** Let `f : X ⟶ Y` be an étale morphism of algebraic spaces and let
`ψ` be a chart of `X` whose composite with `f` is an étale chart of `Y`. Then `ψ` is an étale
chart of `X`: a morphism between two presheaves étale over a third is étale. -/
theorem isEtaleChart_of_comp_etale (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {L : BigFppfOver B S hS} (ψ : yoneda.obj L ⟶ X.1)
    (h : IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (ψ ≫ f.hom))) :
    IsEtaleChart B S hS X.1 (CostructuredArrow.mk ψ) := by
  have hcomp : IsEtale B S hS (ψ ≫ f.hom) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (ψ ≫ f.hom)).2 h
  exact (isEtale_iff_presheaf_of_yoneda B S hS ψ).1
    (isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS L) X.2 Y.2
      ψ (ψ ≫ f.hom) f.hom hcomp hf rfl)

/-! ### The fibre of postcomposition over a chart of `Y` -/

namespace EtaleShriek

variable (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- The fibre of postcomposition over a chart `W` of `Y`: the `Y`-morphisms from `W` to `X`.
These index the connected components of the comma category computing the left Kan extension
along `j.op` at `W`. -/
def Fib (W : (SmallEtale B S hS Y.1)ᵒᵖ) :=
  {ψ : yoneda.obj W.unop.obj.left ⟶ X.1 // ψ ≫ f.hom = W.unop.obj.hom}

/-- The étale chart of `X` attached to an element of the fibre: the same scheme, with the
`Y`-morphism to `X` as its structure map. It is an étale chart by Stacks 03FV. -/
def fibObj {W : (SmallEtale B S hS Y.1)ᵒᵖ} (ψ : Fib B S hS f W) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk ψ.1,
    isEtaleChart_of_comp_etale B S hS f hf ψ.1 (by
      show IsEtaleChart B S hS Y.1 (CostructuredArrow.mk (ψ.1 ≫ f.hom))
      rw [show ψ.1 ≫ f.hom = W.unop.obj.hom from ψ.2]
      exact W.unop.property)⟩

attribute [local implicit_reducible] Fib fibObj smallEtalePostcomp

/-- The structure morphism of the fibre object: the identity of the underlying scheme, seen as
a morphism from `W` to the postcomposite of the fibre object. -/
def fibStruct {W : (SmallEtale B S hS Y.1)ᵒᵖ} (ψ : Fib B S hS f W) :
    W.unop ⟶ (smallEtalePostcomp B S hS f hf).obj (fibObj B S hS f hf ψ) :=
  InducedCategory.homMk (CostructuredArrow.homMk (𝟙 W.unop.obj.left)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp]; exact ψ.2))

/-- The discrete category on the fibre, sitting in the comma category of costructured arrows
of `j.op` over `W`. -/
def fibFunctor (W : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Discrete (Fib B S hS f W) ⥤
      CostructuredArrow (smallEtalePostcomp B S hS f hf).op W :=
  Discrete.functor fun ψ =>
    CostructuredArrow.mk (Y := op (fibObj B S hS f hf ψ))
      (Quiver.Hom.op (fibStruct B S hS f hf ψ))

/-- The element of the fibre cut out by an object of the comma category. -/
def idx {W : (SmallEtale B S hS Y.1)ᵒᵖ}
    (d : CostructuredArrow (smallEtalePostcomp B S hS f hf).op W) : Fib B S hS f W :=
  ⟨yoneda.map d.hom.unop.hom.left ≫ d.left.unop.obj.hom, by
    rw [Category.assoc]
    exact CostructuredArrow.w d.hom.unop.hom⟩

/-- The underlying chart map of an object of the comma category over `d` is that of `d`. -/
theorem hom_left_eq {W : (SmallEtale B S hS Y.1)ᵒᵖ}
    {d : CostructuredArrow (smallEtalePostcomp B S hS f hf).op W}
    (Z : StructuredArrow d (fibFunctor B S hS f hf W)) :
    Z.hom.left.unop.hom.left = d.hom.unop.hom.left := by
  have h := congrArg (fun m : (smallEtalePostcomp B S hS f hf).op.obj d.left ⟶ W =>
    m.unop.hom.left) (CostructuredArrow.w Z.hom)
  simpa [fibFunctor, fibStruct, smallEtalePostcomp_map_left] using h

/-- Every object of the comma category over `d` lies at the index cut out by `d`. -/
theorem idx_eq {W : (SmallEtale B S hS Y.1)ᵒᵖ}
    {d : CostructuredArrow (smallEtalePostcomp B S hS f hf).op W}
    (Z : StructuredArrow d (fibFunctor B S hS f hf W)) :
    Z.right.as = idx B S hS f hf d := by
  refine Subtype.ext ?_
  have hw : yoneda.map Z.hom.left.unop.hom.left ≫ (unop d.left).obj.hom =
      (Z.right.as).1 :=
    CostructuredArrow.w Z.hom.left.unop.hom
  rw [← hw, hom_left_eq]
  rfl

attribute [local implicit_reducible] fibFunctor

/-- The object of the comma category of `d` sitting at the index cut out by `d`. -/
def initObj {W : (SmallEtale B S hS Y.1)ᵒᵖ}
    (d : CostructuredArrow (smallEtalePostcomp B S hS f hf).op W) :
    StructuredArrow d (fibFunctor B S hS f hf W) :=
  StructuredArrow.mk (Y := Discrete.mk (idx B S hS f hf d))
    (CostructuredArrow.homMk
      (Quiver.Hom.op (InducedCategory.homMk
        (CostructuredArrow.homMk d.hom.unop.hom.left rfl)))
      (Quiver.Hom.unop_inj (InducedCategory.hom_ext
        (CostructuredArrow.hom_ext _ _ (Category.id_comp _)))))

attribute [local implicit_reducible] initObj

/-- The unique morphism out of `initObj d`: an object of the comma category whose structure map
is an identity receives at most one morphism, determined by the structure map of its source. -/
def initHom {W : (SmallEtale B S hS Y.1)ᵒᵖ}
    (d : CostructuredArrow (smallEtalePostcomp B S hS f hf).op W)
    (Z : StructuredArrow d (fibFunctor B S hS f hf W)) :
    initObj B S hS f hf d ⟶ Z := by
  obtain ⟨⟨⟨⟩⟩, ⟨t⟩, g⟩ := Z
  have ht : t = idx B S hS f hf d := idx_eq B S hS f hf (StructuredArrow.mk g)
  subst ht
  refine StructuredArrow.homMk (𝟙 _) ?_
  have hEq : (initObj B S hS f hf d).hom = g :=
    CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (InducedCategory.hom_ext
      (CostructuredArrow.hom_ext _ _ (hom_left_eq B S hS f hf (StructuredArrow.mk g)).symm)))
  exact (Category.comp_id _).trans hEq

/-- `initObj d` is an initial object of the comma category of `d`. -/
def isInitialInitObj {W : (SmallEtale B S hS Y.1)ᵒᵖ}
    (d : CostructuredArrow (smallEtalePostcomp B S hS f hf).op W) :
    IsInitial (initObj B S hS f hf d) :=
  IsInitial.ofUniqueHom (initHom B S hS f hf d) fun _ _ => by
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim

/-- The discrete fibre is final in the comma category of costructured arrows of `j.op` over a
chart of `Y`: each comma category has an initial object, hence is connected. -/
theorem fibFunctor_final (W : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (fibFunctor B S hS f hf W).Final :=
  Functor.Final.mk fun d => isConnected_of_isInitial _ (isInitialInitObj B S hS f hf d)

/-- Colimits over that comma category exist in abelian groups: the diagrams are final over the
discrete fibre. -/
theorem hasColimitsOfShape_costructuredArrow (W : (SmallEtale B S hS Y.1)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (smallEtalePostcomp B S hS f hf).op W)
      AddCommGrpCat.{u + 1} :=
  have := fibFunctor_final B S hS f hf W
  Functor.Final.hasColimitsOfShape_of_final (fibFunctor B S hS f hf W)

/-- Colimits of that shape in abelian groups are exact: they are coproducts over the fibre, and
coproducts of abelian groups are exact (Grothendieck's axiom AB4). -/
theorem hasExactColimitsOfShape_costructuredArrow (W : (SmallEtale B S hS Y.1)ᵒᵖ) :
    HasExactColimitsOfShape (CostructuredArrow (smallEtalePostcomp B S hS f hf).op W)
      AddCommGrpCat.{u + 1} :=
  have := fibFunctor_final B S hS f hf W
  hasExactColimitsOfShape_of_final AddCommGrpCat.{u + 1} (fibFunctor B S hS f hf W)

end EtaleShriek

/-! ### Exactness and preservation of injectives -/

/-- Inverse image of abelian sheaves along an étale morphism of algebraic spaces is additive:
it is restriction along a functor, so it is computed on sections. -/
instance etaleAbelianRestriction_additive (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleAbelianRestriction.{u + 1} B S hS f hf).Additive where
  map_add := by
    refine Sheaf.hom_ext ?_
    ext U x
    rfl

/-- **Stacks 015Z for the étale inverse image.** Inverse image of abelian sheaves along an étale
morphism of algebraic spaces carries injective abelian sheaves to injective abelian sheaves.

Its left adjoint `f_!` is the sheafification of the left Kan extension along postcomposition;
that Kan extension is a coproduct over the fibre of postcomposition, by
`AlgebraicGeometry.Space.EtaleShriek.fibFunctor_final`, hence left exact, and sheafification is
left exact, so `f_!` preserves monomorphisms. -/
theorem preservesInjectiveObjects_etaleAbelianRestriction
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleAbelianRestriction.{u + 1} B S hS f hf).PreservesInjectiveObjects := by
  have hcol : ∀ W, HasColimitsOfShape
      (CostructuredArrow (smallEtalePostcomp B S hS f hf).op W) AddCommGrpCat.{u + 1} :=
    fun W => EtaleShriek.hasColimitsOfShape_costructuredArrow B S hS f hf W
  have hpk : ∀ P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePostcomp B S hS f hf).op.HasPointwiseLeftKanExtension P :=
    fun _ _ => inferInstance
  have : HasSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} := inferInstance
  have hlan : PreservesFiniteLimits ((smallEtalePostcomp B S hS f hf).op.lan :
      ((SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((SmallEtale B S hS Y.1)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})) := by
    apply preservesFiniteLimits_of_evaluation
    intro W
    have := EtaleShriek.hasExactColimitsOfShape_costructuredArrow B S hS f hf W
    have : PreservesFiniteLimits
        (colim (J := CostructuredArrow (smallEtalePostcomp B S hS f hf).op W)
          (C := AddCommGrpCat.{u + 1})) := HasExactColimitsOfShape.preservesFiniteLimits
    exact preservesFiniteLimits_of_natIso
      (Stacks.Sites.LocalizationShriek.lanCompEvaluationIsoColim (E := AddCommGrpCat.{u + 1})
        (smallEtalePostcomp B S hS f hf).op W).symm
  have hpull : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (smallEtalePostcomp B S hS f hf) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)) := by
    have : PreservesFiniteLimits
        ((smallEtalePostcomp B S hS f hf).op.lan ⋙
          presheafToSheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  have : (Functor.sheafPullbackConstruction.sheafPullback
      (smallEtalePostcomp B S hS f hf) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcomp B S hS f hf) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1))

/-- The inverse image of an injective abelian sheaf along an étale morphism of algebraic spaces
is an injective abelian sheaf. -/
theorem injective_etaleAbelianRestriction_obj (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (I : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((etaleAbelianRestriction.{u + 1} B S hS f hf).obj I) :=
  have := preservesInjectiveObjects_etaleAbelianRestriction B S hS f hf
  Functor.injective_obj _ _

/-- Inverse image of abelian sheaves along an étale morphism of algebraic spaces is right exact:
postcomposition is cocontinuous as well as continuous, so restriction along it commutes with
colimits. -/
theorem preservesFiniteColimits_etaleAbelianRestriction
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    PreservesFiniteColimits (etaleAbelianRestriction.{u + 1} B S hS f hf) :=
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (etaleAbelianRestriction.{u + 1} B S hS f hf) :=
    Stacks.SheafOfModules.sheafPushforward_preservesColimits.{u + 1, u, u + 1, u + 1, u}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (smallEtalePostcomp B S hS f hf)
  PreservesColimitsOfSize.preservesFiniteColimits _

/-! ### The comparison in every degree -/

/-- **Stacks 0A4P, the sheaf-level conclusion in every degree, on the ambient site.** For an
étale morphism `f : X ⟶ Y` of algebraic spaces over `S` and a set `T` of points of `Y`, inverse
image along `f` identifies the `q`-th higher sections with support in `T` of an abelian sheaf
on `Y_étale` with the `q`-th higher sections with support in `|f|⁻¹T` of its inverse image:
`f⁻¹ H^q_T(F) = H^q_{f⁻¹T}(f⁻¹F)` as abelian sheaves on `X_étale`, naturally in `F`.

The three steps are the ones of the source: `f⁻¹` is exact, so it comes out of a right derived
functor; the degree-zero comparison identifies the two functors being derived; and `f⁻¹`
preserves injectives, so it goes back in. -/
def higherSectionsWithSupportEtaleRestrictionIso
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (T : Set (points B S hS Y.1)) (q : ℕ) :
    (sectionsWithSupport.{u + 1} B S hS Y.1 T).rightDerived q ⋙
        etaleAbelianRestriction.{u + 1} B S hS f hf ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        (sectionsWithSupport.{u + 1} B S hS X.1
          (pointsMap B S hS X.1 f.hom ⁻¹' T)).rightDerived q :=
  haveI := preservesFiniteColimits_etaleAbelianRestriction B S hS f hf
  haveI := preservesInjectiveObjects_etaleAbelianRestriction B S hS f hf
  haveI : (etaleAbelianRestriction.{u + 1} B S hS f hf).PreservesHomology := inferInstance
  (Functor.rightDerivedCompIso (sectionsWithSupport.{u + 1} B S hS Y.1 T)
      (etaleAbelianRestriction.{u + 1} B S hS f hf) q).symm ≪≫
    Functor.rightDerivedIsoOfNatIso
      (sectionsWithSupportEtaleRestrictionIso.{u + 1} B S hS f hf T) q ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (etaleAbelianRestriction.{u + 1} B S hS f hf)
      (sectionsWithSupport.{u + 1} B S hS X.1 (pointsMap B S hS X.1 f.hom ⁻¹' T)) q

/-- **Stacks 0A4P, the sheaf-level conclusion in every degree, for a subspace.** Let
`f : X ⟶ Y` be an étale morphism of algebraic spaces over `S`, let `iY : Z ⟶ Y` be a subspace
and let `iX : W ⟶ X` be its inverse image, presented by the cartesian square `hk`. Then inverse
image along `f` identifies the higher sections with support in `Z` with the higher sections
with support in `f⁻¹Z`, in every degree `q`:
`f⁻¹ H^q_Z(F) = H^q_{f⁻¹Z}(f⁻¹F)` as abelian sheaves on `X_étale`.

As in degree zero, the point sets match by Stacks 03H4, and the source's further hypothesis
that `f⁻¹Z → Z` is an isomorphism — which is what lets the source read both sides as sheaves on
`Z` itself — plays no part in the identification of the ambient sheaves proved here. -/
@[stacks 0A4P "every degree q, on the ambient site: f⁻¹ H^q_Z(F) = H^q_{f⁻¹Z}(f⁻¹F)"]
def closedHigherSectionsWithSupportEtaleRestrictionIso {W Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y) (iX : W ⟶ X) (k : W ⟶ Z)
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) (q : ℕ) :
    (closedSectionsWithSupport.{u + 1} B S hS iY).rightDerived q ⋙
        etaleAbelianRestriction.{u + 1} B S hS f hf ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        (closedSectionsWithSupport.{u + 1} B S hS iX).rightDerived q :=
  haveI hrange : Set.range (pointsMap B S hS W.1 iX.hom) =
      pointsMap B S hS X.1 f.hom ⁻¹' Set.range (pointsMap B S hS Z.1 iY.hom) := by
    have h := preimage_image_pointsMap_of_isPullback B S hS hk Set.univ
    simpa [Set.image_univ] using h.symm
  (higherSectionsWithSupportEtaleRestrictionIso B S hS f hf
      (Set.range (pointsMap B S hS Z.1 iY.hom)) q).trans
    (Functor.isoWhiskerLeft (etaleAbelianRestriction.{u + 1} B S hS f hf)
      (eqToIso (congrArg (fun T => (sectionsWithSupport.{u + 1} B S hS X.1 T).rightDerived q)
        hrange.symm)))

end AlgebraicGeometry.Space

end
