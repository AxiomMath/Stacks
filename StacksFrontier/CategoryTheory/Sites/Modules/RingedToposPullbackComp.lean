module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom

/-!
# Composition of module pullbacks along morphisms of ringed topoi

Let `X ⟶ Y ⟶ Z` be morphisms of ringed topoi, presented as in
`AlgebraicGeometry.RingedToposSiteHom` by continuous functors between the underlying sites. The
pullback of sheaves of modules of Stacks 03D6 part (2) is pseudo-functorial: pulling back
along `g` and then along `f` is pulling back along `g ∘ f`.

This is the ringed-topos form of a statement Mathlib already proves for the primitive it is
built from. `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos f` is by definition
`SheafOfModules.pullback f.fSharpRing`, and `SheafOfModules.pullbackComp` composes two such
pullbacks into the pullback along `φ ≫ F_*(ψ)`. So the only thing owed here is that the
structure map of a composite of morphisms of ringed topoi *is* that composite of structure
maps, which is `comp_fSharpRing` below.

## Main definitions

There are no new definitions beyond the isomorphism itself.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.comp_fSharpRing`: the structure map of a composite,
  read on sheaves of not necessarily commutative rings, is the plain composite
  `O_Z ⟶ g_* O_Y ⟶ g_* f_* O_X`.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposComp`: the composition isomorphism
  `g^* ⋙ f^* ≅ (g ∘ f)^*` for the pullback of sheaves of modules.

## Implementation notes

`RingedToposSiteHom.comp` stores its structure map with the canonical comparison
`Functor.sheafPushforwardContinuousComp` appended, identifying `g_*(f_* O_X)` with
`(g ∘ f)_* O_X`. That comparison is `Iso.refl`, both functors being precomposition with
`u.op`, which is what makes `comp_fSharpRing` hold by `rfl` once `fSharpRing`,
`fSharpPresheaf` and `comp` are unfolded definitionally.

Two routes to `comp_fSharpRing` were tried first and both fail for the same reason, which is
worth recording because the failure looks like a missing lemma and is not. Rewriting the
comparison to `𝟙` and then applying `Category.comp_id` does not work: after the first
rewrite the identity is spelled at the *composite-functor* object
`(f_* ⋙ g_*).obj O_X`, while the composite it must cancel against has target
`g_*.obj (f_*.obj O_X)`. The two are definitionally equal and syntactically different, so
`rw [Category.comp_id]` reports that it cannot find the pattern `?f ≫ 𝟙 ?m` in a goal that
visibly ends in one, and `simp` normalises without closing. Stating the intermediate
equality `(g.comp f).fSharp = g.fSharp ≫ g_*.map f.fSharp` has the same defect in its own
statement: its two sides are terms of two spellings of one type. Reducing to the underlying
presheaf map first and then closing at default transparency avoids naming the identity at
all.

Because the two structure maps are definitionally equal, `pullbackToposComp` is
`SheafOfModules.pullbackComp` itself, with no `eqToIso` and no transport. The one thing that
must be supplied by hand is continuity of `g.u ⋙ f.u`: `RingedToposSiteHom.isContinuous` is an
instance on the field, but instance search runs at `instances` transparency and will not
unfold `comp` to see that `(g.comp f).u` is `g.u ⋙ f.u`, so the composite's continuity has
to be seated as `isContinuous_comp_u`. It is seated at the *same term*
`Functor.isContinuous_comp g.u f.u Z.J Y.J X.J` that `comp` uses, so no second instance for
one notion is introduced.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y Z : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying continuous functor of a composite is continuous, seated at the spelling
`g.u ⋙ f.u` that instance search meets after unfolding `pullbackTopos`. -/
instance isContinuous_comp_u (g : RingedToposSiteHom Y Z) (f : RingedToposSiteHom X Y) :
    (g.u ⋙ f.u).IsContinuous Z.J X.J :=
  Functor.isContinuous_comp g.u f.u Z.J Y.J X.J

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The canonical comparison of successive direct images with the direct image of the
composite is the identity: both functors are precomposition with `u.op`. -/
theorem sheafPushforwardContinuousComp_hom_app_eq_id
    (g : RingedToposSiteHom Y Z) (f : RingedToposSiteHom X Y) :
    (g.u.sheafPushforwardContinuousComp f.u CommRingCat.{w} Z.J Y.J X.J).hom.app X.O
      = 𝟙 _ := rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The structure map of a composite of morphisms of ringed topoi, read on sheaves of not
necessarily commutative rings, is the plain composite `O_Z ⟶ g_* O_Y ⟶ g_* f_* O_X`. -/
theorem comp_fSharpRing (g : RingedToposSiteHom Y Z) (f : RingedToposSiteHom X Y) :
    (g.comp f).fSharpRing =
      g.fSharpRing ≫
        (g.u.sheafPushforwardContinuous RingCat.{w} Z.J Y.J).map f.fSharpRing := by
  apply (ObjectProperty.ι _).map_injective
  dsimp only [fSharpRing, fSharpPresheaf, comp]
  rfl

section Pullback

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D6, part (2), pseudo-functoriality.** Pulling back sheaves of modules along
`g : Y ⟶ Z` and then along `f : X ⟶ Y` is pulling back along the composite `g ∘ f`. -/
def pullbackToposComp (g : RingedToposSiteHom Y Z) (f : RingedToposSiteHom X Y) :
    g.pullbackTopos ⋙ f.pullbackTopos ≅ (g.comp f).pullbackTopos :=
  SheafOfModules.pullbackComp g.fSharpRing f.fSharpRing

end Pullback

end AlgebraicGeometry.RingedToposSiteHom

end
