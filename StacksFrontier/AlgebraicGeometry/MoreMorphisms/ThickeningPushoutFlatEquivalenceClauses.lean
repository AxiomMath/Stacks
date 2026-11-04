module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RXFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatCounitAux
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatFinitePresentation

/-!
# Flat schemes over a pushout along a thickening

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  Gluing
`Stacks.Pushout.gluingFunctor` is left adjoint to base change `Stacks.Pushout.baseChangeFunctor`
by [Stacks Project, Tag 07RV], and the unit of that adjunction is an isomorphism
(`Stacks.Pushout.gluingAdjunction_unit_app_isIso`).  This file proves the final assertion of
[Stacks Project, Tag 07RX] for schemes: the *counit* is an isomorphism at a scheme flat over
`Y'`, and consequently gluing and base change restrict to an equivalence between the schemes
flat over `Y'` and the compatible triples both of whose components are flat.

## Main definitions

* `Stacks.Pushout.flatOver`: the property of a scheme over `S` that its structure morphism is
  flat.
* `Stacks.Pushout.FlatBaseChangeEquivalenceData`: an equivalence from the schemes flat over `Y'`
  to the compatible triples with both components flat — the direction in which the source states
  it — together with the two natural isomorphisms identifying it with base change and its inverse
  with gluing.  The property of a compatible triple that both of its components are flat over
  their respective bases is `Stacks.Pushout.flatGluingData` of
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RXFlat`, where the same
  equivalence is also stated with the two categories exchanged.

## Main results

* `Stacks.Pushout.gluingCounit_isIso_of_flat`: the counit of the gluing adjunction is an
  isomorphism at every scheme flat over the pushout.
* `Stacks.Pushout.isPushout_baseChange_of_flat`: the same assertion read as a pushout square —
  a scheme flat over `Y'` is the pushout of its own two base changes along their common
  restriction to `X`.
* `Stacks.Pushout.flatBaseChangeEquivalence`: base change and gluing are mutually quasi-inverse
  between the schemes flat over `Y'` and the compatible triples with both components flat.

## Implementation notes

Three points about the organisation of the proof of Tag 07RX.

*There is no circularity.*  The equivalence is proved from the counit clause and from the
flatness characterisation of a glued scheme, so the characterisation cannot itself be derived
from the equivalence.  Here the characterisation is
`Stacks.Pushout.gluingFunctor_obj_flat_iff`, proved directly from the affine-local description of
the glued scheme, and the single consequence of it that the counit clause needs is the private
lemma `gluingObject_flat` below: the glued scheme of the base change of a flat scheme is flat,
because both components of that base change are base changes of a flat morphism.

*Everything that the counit clause needs beyond that lemma lives in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatCounitAux`*, which needs
no transparency or heartbeat overrides.  What is left here is local
assembly: the counit is affine, every point of the source has an affine neighbourhood over an
affine open of `Y'` on which the map of sections is the map of flat algebras over
`Γ(Y', V) = Γ(Y, V) ×_{Γ(X, ·)} Γ(X', V)` whose two base changes are the two base changes of the
counit, and those are isomorphisms because the unit is.

*Nothing is assumed beyond the hypotheses of the source.*  [Stacks Project, Tag 06AD] — a
thickening of an affine scheme is affine — is taken from the library, where it is proved
unconditionally as `Stacks.Thickenings.forall_isAffine_of_isThickening`; the lemmas of Tag 07RT
reached from here take it as an explicit hypothesis, and every call below discharges it with that
theorem.  The existence of `Y' = Y ⨿_X X'` is not assumed either: it is the first assertion of
Tag 07RT, obtained from `hi` and the affineness of `f` by
`Stacks.Pushout.hasPushout_of_isThickening`, and the statements below — including the three
fields of `Stacks.Pushout.FlatBaseChangeEquivalenceData` — bind that instance inside their own
types with `letI`, so that `pushout i f` is writable while only `hi` and the affineness of `f` are
hypotheses.  The structure `Stacks.Pushout.FlatBaseChangeEquivalenceData` carries the two
identifying natural isomorphisms, so that `Stacks.Pushout.flatBaseChangeEquivalence` asserts that
*these two functors* are quasi-inverse, not merely that some equivalence exists.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-! ### The counit at a flat scheme -/

/-- The scheme glued from the base change of a flat scheme over the pushout is itself flat over
the pushout: both components of that base change are base changes of a flat morphism. -/
private lemma gluingObject_flat {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (W' : Over (pushout i f)) [Flat W'.hom] :
    Flat ((gluingFunctor i f hi).obj ((baseChangeFunctor i f hi).obj W')).hom :=
  (gluingFunctor_obj_flat_iff i f hi _).2
    (flatGluingData_baseChangeFunctor_obj i f hi ⟨W', ‹_›⟩)

/-- A map of flat algebras over the sections of the pushout on an affine open is an isomorphism
as soon as its base changes to the sections of the two pieces of the pushout are. -/
theorem isIso_of_isIso_pushout_appLE {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {V : (pushout i f).Opens} (hV : IsAffineOpen V)
    {C D : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(pushout i f, V))} (φ : C ⟶ D)
    (hB : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      ((pushout.inr i f).appLE V (pushout.inr i f ⁻¹ᵁ V) le_rfl)).map φ))
    (hA : IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
      ((pushout.inl i f).appLE V (pushout.inl i f ⁻¹ᵁ V) le_rfl)).map φ)) :
    IsIso φ := by
  let P := pushout i f
  let a := pushout.inl i f
  let b := pushout.inr i f
  let VX' := a ⁻¹ᵁ V
  let VY := b ⁻¹ᵁ V
  let e : i ⁻¹ᵁ VX' = f ⁻¹ᵁ VY :=
    congrArg (fun q : X ⟶ P ↦ q ⁻¹ᵁ V) (pushout.condition (f := i) (g := f))
  let surjection : ↑Γ(X', VX') →+* ↑Γ(X, f ⁻¹ᵁ VY) :=
    (i.app VX' ≫ eqToHom (congrArg (fun q : X.Opens ↦ Γ(X, q)) e)).hom
  let toB : ↑Γ(P, V) →+* ↑Γ(Y, VY) := (b.appLE V VY le_rfl).hom
  let toA' : ↑Γ(P, V) →+* ↑Γ(X', VX') := (a.appLE V VX' le_rfl).hom
  let toBase : ↑Γ(Y, VY) →+* ↑Γ(X, f ⁻¹ᵁ VY) := (f.appLE VY (f ⁻¹ᵁ VY) le_rfl).hom
  have hsq : IsPullback (CommRingCat.ofHom toB) (CommRingCat.ofHom toA')
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection) := by
    simpa only [toB, toA', toBase, surjection, e, P, a, b,
      Scheme.Hom.app_eq_appLE,
      CommRingCat.of_carrier, CommRingCat.ofHom_hom] using
      (pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi V)
  have hsurj : Function.Surjective surjection := by
    have : IsAffineHom a := pushout_inl_isAffineHom i f hi
    have hVX' : IsAffineOpen VX' := hV.preimage a
    let : IsClosedImmersion i := hi.1
    dsimp [surjection]
    exact (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (fun q : X.Opens ↦ Γ(X, q)) e))).2.comp (i.app_surjective VX' hVX')
  exact MilnorPatching.isIso_of_isIso_baseChange_of_isPullback toB toA' toBase
    surjection hsq hsurj φ hB hA

/-- At a scheme `W'` flat over the pushout, the counit of the gluing adjunction induces an
isomorphism on the sections over every affine open of `W'` lying over an affine open of the
pushout. -/
theorem gluingCounit_app_isIso_of_flat {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ (W' : Over (pushout i f)) [Flat W'.hom] {V : (pushout i f).Opens} {U : W'.left.Opens},
      IsAffineOpen V → IsAffineOpen U → U ≤ W'.hom ⁻¹ᵁ V →
        IsIso (((gluingAdjunction i f hi).counit.app W').left.app U) := by
  let := hasPushout_of_isThickening i f hi
  intro W' _ V U hV hU hUV
  let P := pushout i f
  let a := pushout.inl i f
  let b := pushout.inr i f
  let c := (gluingAdjunction i f hi).counit.app W'
  let g := ((gluingFunctor i f hi).obj ((baseChangeFunctor i f hi).obj W')).hom
  let w := W'.hom
  let S := c.left ⁻¹ᵁ U
  have hhc : c.left ≫ w = g := Over.w c
  have hAff : IsAffineHom c.left := gluingCounit_isAffine i f hi W'
  have hFlatG : Flat g := gluingObject_flat i f hi W'
  have hFlatW : Flat w := ‹Flat W'.hom›
  have haAffine : IsAffineHom a := pushout_inl_isAffineHom i f hi
  have hbThick : IsThickening b :=
    pushout_inr_isThickening forall_isAffine_of_isThickening i f hi
  let : IsAffineHom b := (isClosedImmersion_iff_isAffineHom.mp hbThick.1).1
  let Cobj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(P, V)) :=
    MorphismProperty.Under.mk ⊤ (w.appLE V U hUV) (by
      rw [CommRingCat.flat_iff]
      exact w.flat_appLE hV hU hUV)
  have hSU : S ≤ g ⁻¹ᵁ V := by
    rw [← hhc, Scheme.Hom.comp_preimage]
    exact c.left.preimage_mono hUV
  let Dobj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(P, V)) :=
    MorphismProperty.Under.mk ⊤ (g.appLE V S hSU) (by
      rw [CommRingCat.flat_iff]
      exact g.flat_appLE hV (by dsimp [S]; exact hAff.isAffine_preimage U hU) hSU)
  let fObj : Cobj ⟶ Dobj := MorphismProperty.Under.homMk
    (c.left.appLE U S (by rfl)) (by
      show w.appLE V U hUV ≫ c.left.appLE U S (by rfl) = g.appLE V S hSU
      have hcomp : S ≤ (c.left ≫ w) ⁻¹ᵁ V := by rwa [hhc]
      calc
        w.appLE V U hUV ≫ c.left.appLE U S (by rfl) =
            (c.left ≫ w).appLE V S hcomp :=
          Scheme.Hom.appLE_comp_appLE c.left w V U S hUV (by rfl)
        _ = g.appLE V S hSU := by simp only [hhc])
  have : IsIso fObj := isIso_of_isIso_pushout_appLE i f hi hV fObj
    (AlgebraicGeometry.isIso_sectionsPushoutMap_of_isIso_pullback g w c.left b hhc hV hU hUV
      (baseChange_counit_inr_scheme_isIso i f hi W'))
    (AlgebraicGeometry.isIso_sectionsPushoutMap_of_isIso_pullback g w c.left a hhc hV hU hUV
      (baseChange_counit_inl_scheme_isIso i f hi W'))
  have hAppLE : IsIso (c.left.appLE U S le_rfl) :=
    Functor.map_isIso (CategoryTheory.Under.forget (CommRingCat.of Γ(P, V)))
      ((MorphismProperty.Under.forget CommRingCat.flat ⊤ (CommRingCat.of Γ(P, V))).map fObj)
  simpa only [Scheme.Hom.app_eq_appLE] using hAppLE

/-- **[Stacks Project, Tag 07RX], the final assertion.**  A scheme flat over the pushout
`Y' = Y ⨿_X X'` of an affine morphism along a thickening is recovered by gluing its two base
changes: the counit `G(F(W')) ⟶ W'` of the gluing adjunction is an isomorphism at it. -/
theorem gluingCounit_isIso_of_flat {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ (W' : Over (pushout i f)) [Flat W'.hom],
      IsIso ((gluingAdjunction i f hi).counit.app W') := by
  let := hasPushout_of_isThickening i f hi
  intro W' _
  let c := (gluingAdjunction i f hi).counit.app W'
  have : IsAffineHom c.left := gluingCounit_isAffine i f hi W'
  have hLocal : ∀ x : W'.left, ∃ U : W'.left.Opens, x ∈ U ∧ IsIso (c.left ∣_ U) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, _⟩ :=
      (pushout i f).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (W'.hom x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      W'.left.isBasis_affineOpens.exists_subset_of_mem_open
        (a := x) (by change x ∈ W'.hom ⁻¹ᵁ V; exact hyV)
        (W'.hom ⁻¹ᵁ V).2
    exact ⟨U, hxU, (isIso_morphismRestrict_iff_isIso_app c.left hU).2
      (gluingCounit_app_isIso_of_flat i f hi W' hV hU hUV)⟩
  have : IsIso c.left := IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict hLocal
  exact (isIso_iff_of_reflects_iso c (Over.forget _)).1 ‹_›

/-- **[Stacks Project, Tag 07RX], the final assertion, read as a pushout square.**  A scheme
`W'` flat over the pushout `Y' = Y ⨿_X X'` *is* the pushout of its own two base changes: the
square whose span is `W' ×_{Y'} X ⟶ W' ×_{Y'} X'` and `W' ×_{Y'} X ⟶ W' ×_{Y'} Y`, and whose
cocone point is `W'` itself, is a pushout of schemes, with its two legs lying over `Y ⟶ Y'` and
`X' ⟶ Y'`.

This is `Stacks.Pushout.gluingCounit_isIso_of_flat` transported along the counit isomorphism
into the pushout description of the glued scheme,
`Stacks.Pushout.gluingFunctor_obj_isPushout`: the counit identifies `G(F(W'))`, which is that
pushout, with `W'`. -/
theorem isPushout_baseChange_of_flat {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ (W' : Over (pushout i f)) [Flat W'.hom],
      ∃ (v : ((baseChangeFunctor i f hi).obj W').obj.left.left ⟶ W'.left)
        (u' : ((baseChangeFunctor i f hi).obj W').obj.right.left ⟶ W'.left),
        IsPushout (gluingSourceMap i f ((baseChangeFunctor i f hi).obj W'))
            (pullback.fst ((baseChangeFunctor i f hi).obj W').obj.right.hom i) v u' ∧
          v ≫ W'.hom =
            ((baseChangeFunctor i f hi).obj W').obj.left.hom ≫ pushout.inr i f ∧
          u' ≫ W'.hom =
            ((baseChangeFunctor i f hi).obj W').obj.right.hom ≫ pushout.inl i f := by
  let := hasPushout_of_isThickening i f hi
  intro W' _
  obtain ⟨v₀, u₀, hpush, hv, hu⟩ :=
    gluingFunctor_obj_isPushout i f hi ((baseChangeFunctor i f hi).obj W')
  have : IsIso ((gluingAdjunction i f hi).counit.app W') :=
    gluingCounit_isIso_of_flat i f hi W'
  have hcl : IsIso ((Over.forget (pushout i f)).map
      ((gluingAdjunction i f hi).counit.app W')) := Functor.map_isIso _ _
  change IsIso ((gluingAdjunction i f hi).counit.app W').left at hcl
  have hw : ((gluingAdjunction i f hi).counit.app W').left ≫ W'.hom =
      ((gluingFunctor i f hi).obj ((baseChangeFunctor i f hi).obj W')).hom :=
    ((gluingAdjunction i f hi).counit.app W').w
  refine ⟨v₀ ≫ ((gluingAdjunction i f hi).counit.app W').left,
    u₀ ≫ ((gluingAdjunction i f hi).counit.app W').left, ?_, ?_, ?_⟩
  · refine IsPushout.of_iso hpush (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso ((gluingAdjunction i f hi).counit.app W').left) ?_ ?_ ?_ ?_ <;> simp
  · rw [Category.assoc, hw, hv]
  · rw [Category.assoc, hw, hu]

/-! ### The equivalence of flat categories -/

/-- The property of a scheme over `S` that its structure morphism is flat. -/
abbrev flatOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun Z ↦ Flat Z.hom

/-- An equivalence **out of** the schemes flat over the pushout `Y' = Y ⨿_X X'` and **into** the
compatible triples with both components flat, together with the two natural isomorphisms
identifying it with base change `Stacks.Pushout.baseChangeFunctor` and its inverse with gluing
`Stacks.Pushout.gluingFunctor`.  Those two isomorphisms are what makes the equivalence canonical:
without them the statement would only say that some equivalence between the two categories
exists.

The source states the equivalence in this direction, with the schemes flat over `Y'` on the left;
`Stacks.Pushout.FlatGluingEquivalenceData` is the same pair of functors read the other way round,
with gluing as the functor and base change as the inverse. -/
structure FlatBaseChangeEquivalenceData {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] where
  /-- The equivalence between the flat schemes over the pushout and the flat compatible
  triples. -/
  equivalence :
    letI := hasPushout_of_isThickening i f hi
    (flatOver (pushout i f)).FullSubcategory ≌ (flatGluingData i f).FullSubcategory
  /-- Its functor is base change. -/
  restriction :
    letI := hasPushout_of_isThickening i f hi
    equivalence.functor ⋙ (flatGluingData i f).ι ≅
      (flatOver (pushout i f)).ι ⋙ baseChangeFunctor i f hi
  /-- Its inverse is gluing. -/
  gluing :
    letI := hasPushout_of_isThickening i f hi
    equivalence.inverse ⋙ (flatOver (pushout i f)).ι ≅
      (flatGluingData i f).ι ⋙ gluingFunctor i f hi

/-- **[Stacks Project, Tag 07RX], the final assertion.**  Base change `F` and gluing `G` are
mutually quasi-inverse between the schemes flat over the pushout `Y' = Y ⨿_X X'` and the
compatible triples both of whose components are flat, stated in the direction the source states
it: out of the schemes flat over `Y'`, by base change.  `Stacks.Pushout.flatGluingEquivalence` is
the same assertion with the two categories exchanged. -/
noncomputable def flatBaseChangeEquivalence {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    FlatBaseChangeEquivalenceData i f hi := by
  letI := hasPushout_of_isThickening i f hi
  let P := flatOver (pushout i f)
  let Q := flatGluingData i f
  let hF : ∀ Z : P.FullSubcategory, Q ((P.ι ⋙ baseChangeFunctor i f hi).obj Z) :=
    flatGluingData_baseChangeFunctor_obj i f hi
  let hG : ∀ T : Q.FullSubcategory, P ((Q.ι ⋙ gluingFunctor i f hi).obj T) :=
    flatOver_gluingFunctor_obj i f hi
  let F : P.FullSubcategory ⥤ Q.FullSubcategory :=
    Q.lift (P.ι ⋙ baseChangeFunctor i f hi) hF
  let G : Q.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (Q.ι ⋙ gluingFunctor i f hi) hG
  let A := gluingAdjunction i f hi
  let comm1 : Q.ι ⋙ gluingFunctor i f hi ≅ G ⋙ P.ι :=
    (P.liftCompιIso _ hG).symm
  let comm2 : P.ι ⋙ baseChangeFunctor i f hi ≅ F ⋙ Q.ι :=
    (Q.liftCompιIso _ hF).symm
  let adj := A.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι comm1 comm2
  letI : ∀ T : Q.FullSubcategory, IsIso (adj.unit.app T) := by
    intro T
    apply (Q.isIso_hom_iff _).mp
    change IsIso (Q.ι.map ((A.restrictFullyFaithful Q.fullyFaithfulι
      P.fullyFaithfulι comm1 comm2).unit.app T))
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    exact IsIso.comp_isIso' (gluingAdjunction_unit_app_isIso i f hi T.obj) (IsIso.comp_isIso'
      (Functor.map_isIso (baseChangeFunctor i f hi) (comm1.hom.app T)) inferInstance)
  letI : ∀ Z : P.FullSubcategory, IsIso (adj.counit.app Z) := by
    intro Z
    apply (P.isIso_hom_iff _).mp
    change IsIso (P.ι.map ((A.restrictFullyFaithful Q.fullyFaithfulι
      P.fullyFaithfulι comm1 comm2).counit.app Z))
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    have : Flat Z.obj.hom := Z.property
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
      (Functor.map_isIso (gluingFunctor i f hi) (comm2.inv.app Z))
      (gluingCounit_isIso_of_flat i f hi Z.obj))
  exact ⟨adj.toEquivalence.symm, (Q.liftCompιIso _ hF).symm, P.liftCompιIso _ hG⟩

end Stacks.Pushout

end
