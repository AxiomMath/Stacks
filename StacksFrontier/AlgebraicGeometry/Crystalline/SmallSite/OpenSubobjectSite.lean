module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseCoverPreserving
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseZariski
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubobject

/-!
# Change of divided power base as the site of elements of an open subobject

Let `X' ⊆ X` and `S' ⊆ S` be open subschemes with `X'` mapping into `S'`, and let
`j : Cris(X'/S') ⥤ Cris(X/S)` be change of divided power base
(`Crystalline.GlobalCrystallineSituation.smallChangeBase`).  Let `F` be the sheaf
`u_{X/S}^{-1}h_{X'}` on `Cris(X/S)` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubobject.lean`, presented there as the
restriction `(forgetToOpens S)ᵒᵖ ⋙ h_{g(X')}` of the sheaf represented by the open image of
`X' ⟶ X`.

`F` is a *subterminal* sheaf: its values are subsingletons, so it is a subobject of the final
sheaf, an "open subobject" in the sense of the remark of [Stacks, Tag 07ML].  For such an `F` the
slice topos `Sh(Cris(X/S))/F` is the topos of the full subcategory of `Cris(X/S)` on the objects
over which `F` has a section, and this file assembles what is needed to recognise `j` as that
subcategory: the objects carrying a section of `F` are exactly the objects in the essential image
of `j`, and `j` reflects as well as preserves covering sieves.

## Main results

* `Crystalline.GlobalCrystallineSituation.nonempty_forgetToOpensOpCompOpensRepr_iff_essImage`
  — an object of `Cris(X/S)` carries a section of `F` exactly when it comes from `Cris(X'/S')`.
* `Crystalline.GlobalCrystallineSituation.nonempty_forgetToOpensOpCompOpensRepr_smallChangeBase`
  — the half of that equivalence which needs no hypothesis on the divided powers: everything in
  the image of `j` carries a section of `F`.
* `Crystalline.GlobalCrystallineSituation.mem_smallTopology_iff_functorPushforward_mem` — a sieve
  of `Cris(X'/S')` covers exactly when the sieve it generates in `Cris(X/S)` covers.
* `Crystalline.GlobalCrystallineSituation.subsingleton_forgetToOpensOpCompOpensRepr_obj` — `F`
  is subterminal.

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}
  [IsOpenImmersion g]

/-- **The restriction of `h_W` along the forgetful functor is subterminal.**  A section of it
over `(U, T, δ)` is an inclusion of the open image of `U` in `X` into `W`, and the opens of `X`
form a partial order, so there is at most one. -/
instance subsingleton_forgetToOpensOpCompOpensRepr_obj (W : S.X.Opens)
    (A : (CrystallineThickening S)ᵒᵖ) :
    Subsingleton (((forgetToOpens S).op ⋙ opensRepr W).obj A) :=
  subsingleton_opensRepr_obj W ((forgetToOpens S).op.obj A)

/-- **Everything in the image of change of divided power base carries a section of
`u_{X/S}^{-1}h_{X'}`.**  The open image in `X` of an object of `Cris(X/S)` that came from
`Cris(X'/S')` is the image under `X' ⟶ X` of an open of `X'`, hence lies in the open `g(X')`.

The square of sites commutes on the nose
(`Crystalline.GlobalCrystallineSituation.smallChangeBase_comp_forgetToOpens`), which is what
turns the open image of the transported object into the transport of an open image.

Unlike the converse this needs no hypothesis on the morphism `f` of divided power bases: it does
not assert essential surjectivity onto anything. -/
theorem nonempty_forgetToOpensOpCompOpensRepr_smallChangeBase (A : CrystallineThickening S) :
    Nonempty (((forgetToOpens S').op ⋙ opensRepr g.opensRange).obj
      (op ((smallChangeBase S S' f g h).obj A))) := by
  have hg : IsOpenMap g.base := g.isOpenEmbedding.isOpenMap
  have key := Functor.congr_obj (smallChangeBase_comp_forgetToOpens (f := f) (h := h) hg) A
  show Nonempty ((opensRepr g.opensRange).obj
    (op ((forgetToOpens S').obj ((smallChangeBase S S' f g h).obj A))))
  rw [nonempty_opensRepr_obj_iff]
  refine le_trans (le_of_eq key.symm) ?_
  rintro x ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

/-- **The objects of `Cris(X/S)` carrying a section of `u_{X/S}^{-1}h_{X'}` are exactly those in
the essential image of change of divided power base.**  A section over `(U, T, δ)` is an
inclusion of the open image of `U` in `X` into the open `g(X')`, that is, a factorization of
`U ⟶ X` through `X' ⊆ X`, and that is the description of the essential image given by
`Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff`.

Together with fullness and faithfulness of change of base this says that `Cris(X'/S')` is the
full subcategory of `Cris(X/S)` cut out by the subterminal sheaf `u_{X/S}^{-1}h_{X'}`, i.e. its
site of elements.

The hypothesis `Crystalline.DividedPowerScheme.IsInducedOpen` is the one the essential image
statement carries: without it the factorization `T ⟶ S'` of an object lying over `X'` need not be
a morphism of divided power schemes.  Only the direction proved without it is
`Crystalline.GlobalCrystallineSituation.nonempty_forgetToOpensOpCompOpensRepr_smallChangeBase`. -/
theorem nonempty_forgetToOpensOpCompOpensRepr_iff_essImage
    (hf : DividedPowerScheme.IsInducedOpen f) (B : CrystallineThickening S') :
    Nonempty (((forgetToOpens S').op ⋙ opensRepr g.opensRange).obj (op B)) ↔
      (smallChangeBase S S' f g h).essImage B := by
  show Nonempty ((opensRepr g.opensRange).obj (op ((forgetToOpens S').obj B))) ↔ _
  rw [nonempty_opensRepr_obj_iff, smallChangeBase_essImage_iff (h := h) hf]
  exact ⟨fun hle _ hx ↦ hle hx, fun hle _ hx ↦ hle hx⟩

/-- **Change of divided power base both preserves and reflects covering sieves.**  A sieve of an
object `A` of `Cris(X'/S')` is a Zariski covering sieve exactly when the sieve it generates in
`Cris(X/S)` covers the image of `A`; in other words the topology of `Cris(X'/S')` is the one
induced from `Cris(X/S)` along change of base.

The forward implication is cover preservation,
`Crystalline.GlobalCrystallineSituation.smallChangeBase_coverPreserving`.  The converse is
cocontinuity, `Crystalline.GlobalCrystallineSituation.smallChangeBase_isCocontinuous`, which
pulls the covering sieve back, together with the fact that pulling a pushed-forward sieve back
along a fully faithful functor returns the sieve itself
(`Crystalline.GlobalCrystallineSituation.smallChangeBase_functorPullback_functorPushforward`);
the hypothesis `[IsOpenImmersion f.hom]` is what fullness of change of base needs. -/
theorem mem_smallTopology_iff_functorPushforward_mem [IsOpenImmersion f.hom]
    (A : CrystallineThickening S) (T : Sieve A) :
    T ∈ smallTopology S A ↔
      T.functorPushforward (smallChangeBase S S' f g h) ∈
        smallTopology S' ((smallChangeBase S S' f g h).obj A) := by
  refine ⟨fun hT ↦ smallChangeBase_coverPreserving.cover_preserve hT, fun hT ↦ ?_⟩
  simpa only [smallChangeBase_functorPullback_functorPushforward] using
    (smallChangeBase S S' f g h).cover_lift (smallTopology S) (smallTopology S') hT

end Crystalline.GlobalCrystallineSituation

end
