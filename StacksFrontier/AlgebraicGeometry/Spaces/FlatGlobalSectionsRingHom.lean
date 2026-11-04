module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CommRing

/-!
# Flatness of the ring map on global functions of a flat morphism of affine algebraic spaces

**Stacks 073K, part (2)** compares `H^i(X, 𝓕) ⊗_A B` with `H^i(X', 𝓕')` for a cartesian square
of algebraic spaces over an affine base `Y = Spec A` and an affine `Y' = Spec B` with
`A ⟶ B` *flat*.  In this development the two rings are the rings of global regular functions
`Γ(Y, 𝒪_Y)` and `Γ(Y', 𝒪_{Y'})` — `RingCat.sectionsSubring` of the structure ring sheaf of the
small étale ringed site — and the ring map is
`AlgebraicGeometry.Space.globalSectionsRingHomSite`, the map of **Stacks 0732**.  This file
supplies the flatness hypothesis of part (2) from flatness of the morphism `g : Y' ⟶ Y` of
algebraic spaces, so that nothing downstream has to carry it.

The route is the one the source takes implicitly.  An affine algebraic space is isomorphic to
the presheaf represented by an object `T` of the site with affine underlying scheme, and that
isomorphism is itself an étale chart which is a *terminal* object of the small étale site: a
chart of `yoneda.obj T` is a morphism into it, and `yoneda` is fully faithful.  Over a terminal
chart the compatible families of regular functions are just the regular functions on the chart,
so `Γ(Y, 𝒪_Y) ≅ Γ(T, 𝒪_T)` through evaluation at that chart, and the chart-square formula
`AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartDiagram` identifies the ring map of
Stacks 0732 with `Γ` of the morphism of schemes `T' ⟶ T` representing `g`.  That morphism of
schemes is flat because `AlgebraicGeometry.Space.IsFlat` of **Stacks 03ML** is by definition
flatness of the morphism of schemes underlying *every* commuting square of étale charts, and the
square of terminal charts is one; since `T` and `T'` are affine, Mathlib's
`AlgebraicGeometry.IsFlat` being a `AlgebraicGeometry.HasRingHomProperty` for `RingHom.Flat`
turns that into flatness of the ring map on global sections.  Flatness then transports back
along the two evaluation isomorphisms.

## Main results

* `AlgebraicGeometry.Space.isTerminalEtaleChartOfIso`: **the chart of a representable presheaf
  given by an isomorphism with it is a terminal object of the small étale site.**  Its
  underlying étale chart is `AlgebraicGeometry.Space.etaleChartOfIso`.
* `AlgebraicGeometry.Space.bijective_globalSectionsChartEval_of_isTerminal`: **evaluation of
  global regular functions at a terminal étale chart is bijective** — the companion of
  `AlgebraicGeometry.Space.globalFunctionsChartRestriction_injective`, where the chart is only
  surjective and the map only injective.  The evaluation map itself is
  `AlgebraicGeometry.Space.globalSectionsChartEval`.
* `AlgebraicGeometry.Space.globalSectionsChartEval_globalSectionsRingHomSite`: the ring map of
  **Stacks 0732** read through evaluation at the two charts of a chart diagram is `Γ` of the
  vertical morphism of schemes.
* `RingHom.Flat.of_bijective_comm_square`: flatness of a ring map transports across a
  commutative square of ring maps whose two horizontal maps are bijective, the four rings being
  allowed to live in four different universes.  This is what carries flatness from the
  coordinate rings of the charts back to the rings of global regular functions.
* `AlgebraicGeometry.Space.flat_globalSectionsRingHomSite_of_isFlat_of_isAffineSpace`: **the
  ring map `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})` of Stacks 0732 is flat for a flat morphism of affine
  algebraic spaces** — the flatness hypothesis of Stacks 073K, part (2), and
  `AlgebraicGeometry.Space.moduleFlat_globalSectionsRingHomSite_of_isFlat_of_isAffineSpace` the
  same as flatness of the module structure that ring map induces.

## Implementation notes

*Evaluation at a chart is restated rather than reused.*
`AlgebraicGeometry.Space.globalFunctionsChartRestriction` is the same ring homomorphism, but its
source is spelled `AlgebraicGeometry.Space.globalFunctions`, the sections of the presheaf of
regular functions, whose `CommRing` instance is `Subring.toCommRing` of the subring of
compatible families.  The ring map of Stacks 0732 is spelled at the subring itself, whose `Ring`
instance is `Subring.toRing`, and — as the implementation notes of
`AlgebraicGeometry.RingedSite.globalSectionsCommRing` explain — the two routes to the ring
structure must not be asked to compete.  `AlgebraicGeometry.Space.globalSectionsChartEval` is
therefore the same composite of `Pi.evalRingHom` with `Subring.subtype`, stated at the spelling
the ring map of Stacks 0732 uses.

*Why the ring equivalence is not formed.*  Only bijectivity of evaluation is proved, not a
`RingEquiv`: flatness transports along `RingHom.Flat.of_bijective` and
`RingHom.Flat.comp_iff_of_bijective_left`, which are stated for bijective ring homomorphisms and
are fully universe polymorphic.  The ring of global functions lives in `Type (u + 1)` — it is a
subtype of a product over the objects of the small étale site — while `Γ(T, 𝒪_T)` lives in
`Type u`, so no `ULift` is needed either; `RingHom` and `Function.Bijective` already span two
universes.

*The commutativity of the two rings of global functions* is
`AlgebraicGeometry.RingedSite.globalSectionsCommRing`, activated as a local instance as in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeMap.lean`; `RingHom.Flat` is
defined only for a map of commutative rings.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe u

namespace RingHom.Flat

/-- **Flatness of a ring map transports across a commutative square whose horizontal maps are
bijective.**  If `a : A ≃ R` and `a' : A' ≃ R'` are bijective ring maps intertwining
`φ : A →+* A'` with `ψ : R →+* R'`, then `φ` is flat as soon as `ψ` is.

The four rings may lie in four different universes, which is what this is for: the ring of
global regular functions of an algebraic space is a subtype of a product over the objects of its
small étale site and so lies one universe up from the coordinate ring of a chart. -/
theorem of_bijective_comm_square {A A' R R' : Type*} [CommRing A] [CommRing A'] [CommRing R]
    [CommRing R'] {φ : A →+* A'} {ψ : R →+* R'} {a : A →+* R} {a' : A' →+* R'}
    (ha : Function.Bijective a) (ha' : Function.Bijective a') (hsq : a'.comp φ = ψ.comp a)
    (hψ : ψ.Flat) : φ.Flat :=
  (RingHom.Flat.comp_iff_of_bijective_left ha').mp
    (by rw [hsq]; exact RingHom.Flat.comp (RingHom.Flat.of_bijective ha) hψ)

end RingHom.Flat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The terminal chart of a representable presheaf -/

/-- The étale chart of a presheaf `F` on the big fppf site of `S` given by an isomorphism of `F`
with the presheaf represented by an object `T` of the site.

It is an étale chart because it is an isomorphism of presheaves, and the property defining the
étale charts contains the identities and respects isomorphisms. -/
def etaleChartOfIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    (e : F ≅ yoneda.obj T) : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk e.inv, by
    have hId : MorphismProperty.ContainsIdentities
        (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have hIso : MorphismProperty.RespectsIso
        (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hId' : MorphismProperty.ContainsIdentities
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
    have hIso' : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
    exact MorphismProperty.presheaf_of_isIso _ e.inv⟩

/-- **The chart of a presheaf given by an isomorphism with a representable presheaf is a
terminal object of the small étale site.**

A morphism of étale charts into `AlgebraicGeometry.Space.etaleChartOfIso e` is a morphism
`U ⟶ T` of the site whose image under `yoneda`, followed by `e.inv`, is the given chart of `U`;
equivalently, whose image under `yoneda` is that chart followed by `e.hom`.  Full faithfulness
of the Yoneda embedding provides exactly one such morphism.

This is `AlgebraicGeometry.Space.isTerminalIdEtaleChart` with the identity of `yoneda.obj T`
replaced by an arbitrary isomorphism onto it, which is what makes it available for an *affine*
algebraic space: `AlgebraicGeometry.Space.IsAffineSpace` provides an isomorphism with a
representable presheaf, not an equality. -/
def isTerminalEtaleChartOfIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    (e : F ≅ yoneda.obj T) : IsTerminal (etaleChartOfIso B S hS e) := by
  have hw : ∀ A : SmallEtale B S hS F,
      yoneda.map (yoneda.preimage (A.obj.hom ≫ e.hom)) ≫ e.inv = A.obj.hom := by
    intro A
    rw [Functor.map_preimage, Category.assoc, e.hom_inv_id, Category.comp_id]
  have huniq : ∀ (A : SmallEtale B S hS F) (k₁ k₂ : A.obj.left ⟶ T),
      yoneda.map k₁ ≫ e.inv = A.obj.hom → yoneda.map k₂ ≫ e.inv = A.obj.hom → k₁ = k₂ := by
    intro A k₁ k₂ h₁ h₂
    refine yoneda.map_injective ?_
    rw [← Category.comp_id (yoneda.map k₁), ← e.inv_hom_id, ← Category.assoc, h₁, ← h₂,
      Category.assoc, e.inv_hom_id, Category.comp_id]
  exact IsTerminal.ofUniqueHom
    (fun A => ObjectProperty.homMk (CostructuredArrow.homMk
      (yoneda.preimage (A.obj.hom ≫ e.hom)) (hw A)))
    (fun A m => ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      (huniq A m.hom.left (yoneda.preimage (A.obj.hom ≫ e.hom))
        (CostructuredArrow.w m.hom) (hw A))))

/-! ### Evaluation of global functions at a chart -/

/-- Evaluation of a global regular function of an algebraic space at one of its étale scheme
charts, as a homomorphism of rings.

This is `AlgebraicGeometry.Space.globalFunctionsChartRestriction` with its source spelled as the
subring of compatible families inside the product over the charts, which is the spelling
`AlgebraicGeometry.Space.globalSectionsRingHomSite` uses; see the implementation notes. -/
def globalSectionsChartEval (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1) :
    RingCat.sectionsSubring (structureRingSheaf B S hS X).obj →+*
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V), ⊤) :=
  (Pi.evalRingHom (fun j => ToType ((structureRingSheaf B S hS X).obj.obj j)) (op V)).comp
    (RingCat.sectionsSubring (structureRingSheaf B S hS X).obj).subtype

/-- **Evaluation of global regular functions at a terminal étale chart is bijective.**

Injectivity: the value of a compatible family at any chart `U` is the pullback of its value at
the terminal chart along the unique morphism `U ⟶ V`.  Surjectivity: those pullbacks assemble,
for an arbitrary regular function on the terminal chart, into a compatible family, the
compatibility being the uniqueness of morphisms into a terminal object; and its value at the
terminal chart is the given function, the unique endomorphism of a terminal object being the
identity.

The companion statement
`AlgebraicGeometry.Space.globalFunctionsChartRestriction_injective` assumes only that the chart
is surjective and concludes only injectivity; a terminal chart is in particular surjective, but
the proof here uses nothing of the étale topology. -/
theorem bijective_globalSectionsChartEval_of_isTerminal (X : AlgebraicSpaces B S hS)
    {V : SmallEtale B S hS X.1} (hV : IsTerminal V) :
    Function.Bijective (globalSectionsChartEval B S hS X V) := by
  let F := (structureRingSheaf B S hS X).obj ⋙ forget RingCat.{u}
  have key : ∀ (a : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj)
      (U : (SmallEtale B S hS X.1)ᵒᵖ),
      F.map (hV.from U.unop).op (a.1 (op V)) = a.1 U :=
    fun a U => (a.2 : Functor.sections F a.1) (hV.from U.unop).op
  have hext : ∀ {U : (SmallEtale B S hS X.1)ᵒᵖ} (f f' : op V ⟶ U), f = f' :=
    fun f f' => Quiver.Hom.unop_inj (hV.hom_ext _ _)
  have hsec : ∀ x : ToType ((structureRingSheaf B S hS X).obj.obj (op V)),
      Functor.sections F (fun U => F.map (hV.from U.unop).op x) := by
    intro x U U' f
    change F.map f (F.map (hV.from U.unop).op x) = _
    rw [← Functor.map_comp_apply, hext ((hV.from U.unop).op ≫ f) (hV.from U'.unop).op]
  refine ⟨fun a b hab => Subtype.ext <| funext fun U => ?_, fun x =>
    ⟨⟨fun U => F.map (hV.from U.unop).op x, hsec x⟩, ?_⟩⟩
  · rw [← key a U, ← key b U]
    exact congrArg _ hab
  · change F.map (hV.from V).op x = x
    rw [hext (hV.from V).op (𝟙 (op V))]
    exact F.map_id_apply _ x

/-! ### The ring map of Stacks 0732 through evaluation at charts -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The ring map on global regular functions of Stacks 0732, read through evaluation at the
two charts of a chart diagram, is `Γ` of the vertical morphism of schemes.**

This is `AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartDiagram` with both sides
expressed through `AlgebraicGeometry.Space.globalSectionsChartEval`, and with
`AlgebraicGeometry.Space.chartDiagramPullback` unfolded to the pullback of regular functions it
is. -/
theorem globalSectionsChartEval_globalSectionsRingHomSite (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj) :
    globalSectionsChartEval B S hS X d.U (globalSectionsRingHomSite B S hS f a) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom
        (globalSectionsChartEval B S hS Y d.V a) :=
  globalSectionsRingHomSite_val_chartDiagram B S hS f a d

/-! ### Flatness -/

/-- **The ring map `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})` on global regular functions of Stacks 0732 is
flat for a flat morphism of affine algebraic spaces.**

This is the flatness hypothesis of **Stacks 073K, part (2)**, deduced from flatness of the
morphism of algebraic spaces rather than assumed.

Each of the two affine algebraic spaces is isomorphic to the presheaf represented by an object
of the site with affine underlying scheme, and that isomorphism is a terminal étale chart by
`AlgebraicGeometry.Space.isTerminalEtaleChartOfIso`, so evaluation there identifies the ring of
global regular functions with the coordinate ring of the chart by
`AlgebraicGeometry.Space.bijective_globalSectionsChartEval_of_isTerminal`.  The morphism of
algebraic spaces is represented by a morphism `T' ⟶ T` of the site, so the two terminal charts
form a chart diagram, and
`AlgebraicGeometry.Space.globalSectionsChartEval_globalSectionsRingHomSite` identifies the ring
map with `Γ` of the underlying morphism of schemes.  That morphism of schemes is flat because
`AlgebraicGeometry.Space.IsFlat` of **Stacks 03ML** is flatness of the morphism of schemes
underlying every commuting square of étale charts, and both schemes are affine, so
`AlgebraicGeometry.HasRingHomProperty.appTop` makes it a flat ring map.  Flatness then
transports back along the two bijections. -/
theorem flat_globalSectionsRingHomSite_of_isFlat_of_isAffineSpace {Y Y' : AlgebraicSpaces B S hS}
    (g : Y' ⟶ Y) (hg : IsFlat B S hS g.hom) (hY : IsAffineSpace B S hS Y.1)
    (hY' : IsAffineSpace B S hS Y'.1) :
    (globalSectionsRingHomSite B S hS g).Flat := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  obtain ⟨T', hT', ⟨e'⟩⟩ := hY'
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := hT'
  -- the morphism of the site representing `g`
  let h : T' ⟶ T := yoneda.preimage (e'.inv ≫ g.hom ≫ e.hom)
  have hcomm : (etaleChartOfIso B S hS e').obj.hom ≫ g.hom =
      yoneda.map h ≫ (etaleChartOfIso B S hS e).obj.hom := by
    change e'.inv ≫ g.hom = yoneda.map h ≫ e.inv
    rw [Functor.map_preimage, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  -- flatness of the morphism of schemes `T' ⟶ T`
  have hflat : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map h) :=
    hg T' T e'.inv e.inv h (etaleChartOfIso B S hS e').property
      (etaleChartOfIso B S hS e).property hcomm.symm
  have hring : RingHom.Flat
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom := by
    rw [Scheme.Γ_map_op]
    exact HasRingHomProperty.appTop (P := @_root_.AlgebraicGeometry.Flat.{u}) _ hflat
  have hsq : (globalSectionsChartEval B S hS Y' (etaleChartOfIso B S hS e')).comp
        (globalSectionsRingHomSite B S hS g) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom.comp
        (globalSectionsChartEval B S hS Y (etaleChartOfIso B S hS e)) :=
    RingHom.ext fun a => globalSectionsChartEval_globalSectionsRingHomSite B S hS g
      ⟨etaleChartOfIso B S hS e', etaleChartOfIso B S hS e, h, hcomm⟩ a
  exact RingHom.Flat.of_bijective_comm_square
    (bijective_globalSectionsChartEval_of_isTerminal B S hS Y (isTerminalEtaleChartOfIso B S hS e))
    (bijective_globalSectionsChartEval_of_isTerminal B S hS Y'
      (isTerminalEtaleChartOfIso B S hS e')) hsq hring

/-- **The ring of global regular functions of an affine algebraic space is a flat module over
that of an affine algebraic space it maps to flatly**, for the module structure induced by the
ring map of **Stacks 0732**.

This is
`AlgebraicGeometry.Space.flat_globalSectionsRingHomSite_of_isFlat_of_isAffineSpace` with
`RingHom.Flat` unfolded to its definition, which is the form a consumer forming an extension of
scalars along that ring map needs. -/
theorem moduleFlat_globalSectionsRingHomSite_of_isFlat_of_isAffineSpace
    {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (hg : IsFlat B S hS g.hom)
    (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1) :
    letI _iA : CommRing (RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj) :=
      RingedSite.globalSectionsCommRing (smallEtaleRingedSite B S hS Y.1 Y.2)
    letI _iA' : CommRing (RingCat.sectionsSubring (structureRingSheaf B S hS Y').obj) :=
      RingedSite.globalSectionsCommRing (smallEtaleRingedSite B S hS Y'.1 Y'.2)
    letI : Algebra (RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj)
        (RingCat.sectionsSubring (structureRingSheaf B S hS Y').obj) :=
      (globalSectionsRingHomSite B S hS g).toAlgebra
    Module.Flat (RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj)
      (RingCat.sectionsSubring (structureRingSheaf B S hS Y').obj) :=
  flat_globalSectionsRingHomSite_of_isFlat_of_isAffineSpace B S hS g hg hY hY'

end AlgebraicGeometry.Space

end

end
