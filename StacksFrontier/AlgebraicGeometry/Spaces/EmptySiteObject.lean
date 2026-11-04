module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# The empty object of the big fppf site

An object of the big fppf site over `S` whose underlying scheme is empty is initial, both in
the site and — after Yoneda — among algebraic spaces over `S`: it has exactly one morphism to
every algebraic space, it has no points, and every morphism out of it is locally of finite
presentation.

## Main definitions

* `AlgebraicGeometry.Space.emptyObject`: the object of the site cut out by the empty open of
  the base.

## Main results

* `AlgebraicGeometry.Space.isInitial_of_isEmpty`: an object of the site with empty underlying
  scheme is initial in the site.
* `AlgebraicGeometry.Space.isEmpty_points_yoneda_of_isEmpty`: it has no points.
* `AlgebraicGeometry.Space.exists_hom_of_isEmpty` and
  `AlgebraicGeometry.Space.hom_ext_yoneda_of_isEmpty`: there is exactly one morphism from the
  presheaf it represents to any algebraic space over `S`.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isEmpty`: every morphism out of it
  is locally of finite presentation.

## Implementation notes

The point of the file is the last result, which is what makes the empty object useful as a
*test object against limits*: a morphism locally of finite presentation has its Hom-functor
commuting with cofiltered limits of quasi-compact quasi-separated algebraic spaces with affine
transition morphisms (Stacks 0CP4), so if a cofiltered system of such spaces has a limit whose
vertex is the empty object, then one of its stages already admits a morphism to the empty
object, and is therefore itself empty. That is a descent of emptiness along a limit which
needs no nonemptiness theorem for limits, in contrast with Stacks 086W.

It does, however, still need a cardinality hypothesis on the index, because the library's form
of Stacks 0CP4, `AlgebraicGeometry.Space.QcqsLimitSquare`, carries `#I < B.cutoff.ord.cof`
together with a bound on the hom types. Nothing in this file removes that; the route is
recorded here because it is a genuinely different one from Stacks 086W, not because it is
cheaper.

Initiality is proved one layer at a time: the underlying scheme is initial among schemes
because it is empty, so the object of `B.Schemes` is initial there because the inclusion of
the site's scheme category into schemes is fully faithful, and the object of the slice is
initial because its structure morphism is then forced.

*Why the morphism results are here although nothing in this library calls them yet.*
`exists_hom_of_isEmpty`, `hom_ext_yoneda_of_isEmpty` and
`isLocallyOfFinitePresentation_of_isEmpty` have no consumers. They are kept deliberately: they are
exactly the input the emptiness descent sketched above needs, and that descent becomes
available in cardinality-free form the moment Stacks 0CP4 is proved without the bound above.
Do not delete them as dead code.

To be accurate about why they are unused rather than leaving a reader to guess: the descent
above is *not* the route by which Stacks 07SR is being proved in this development, and it is
not on the critical path of anything. Stacks 07SR goes through the schematic locus
(`StacksFrontier/AlgebraicGeometry/Spaces/SchematicLocusPreimage.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/OpenSubspaceCoveringLimit.lean`), and the cardinality question around it
turns on Stacks 07SQ, not on Stacks 0CP4. These three declarations are banked against a
cardinality-free 0CP4 and nothing nearer.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The empty object -/

/-- The empty object of the big fppf site over `S`: the object cut out by the empty open of
the base. -/
noncomputable def emptyObject : BigFppfOver B S hS :=
  openSiteObject B S hS (Over.mk (𝟙 (B.obj hS))) ⊥

/-- The underlying scheme of `emptyObject B S hS` is empty. -/
instance isEmpty_emptyObject :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj (emptyObject B S hS)) :=
  ⟨fun x => x.property⟩

/-! ### Initiality -/

/-- An object of the big fppf site over `S` whose underlying scheme is empty is initial. -/
noncomputable def isInitial_of_isEmpty (T : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj T)] : IsInitial T := by
  letI : IsEmpty (B.inclusion.obj T.left) :=
    inferInstanceAs (IsEmpty ((BigFppfOver.toScheme B S hS).obj T))
  let hT : IsInitial (B.inclusion.obj T.left) := isInitialOfIsEmpty
  let h : IsInitial T.left := IsInitial.ofUniqueHom
    (fun V => B.inclusion.preimage (hT.to (B.inclusion.obj V)))
    (fun _ _ => B.inclusion.map_injective (hT.hom_ext _ _))
  exact IsInitial.ofUniqueHom
    (fun V => Over.homMk (h.to V.left) (h.hom_ext _ _))
    (fun _ _ => Over.OverMorphism.ext (h.hom_ext _ _))

/-- An object of the big fppf site over `S` whose underlying scheme is empty represents a
presheaf with no points. -/
theorem isEmpty_points_yoneda_of_isEmpty (T : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj T)] :
    IsEmpty (points B S hS (yoneda.obj T)) :=
  (schemePointsHomeomorph B S hS T).toEquiv.isEmpty

/-! ### Morphisms out of the empty object -/

variable {B S hS}

/-- The source of a morphism in the site into an object with empty underlying scheme is empty. -/
private theorem isEmpty_of_hom {X Y : BigFppfOver B S hS}
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj Y)] (g : X ⟶ Y) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj X) :=
  ⟨fun x => isEmptyElim (((BigFppfOver.toScheme B S hS).map g) x)⟩

/-- There is a morphism from the presheaf represented by an empty object of the site to every
algebraic space over `S`. -/
theorem exists_hom_of_isEmpty (T : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj T)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    Nonempty (yoneda.obj T ⟶ F) := by
  obtain ⟨V, a, _, _⟩ := hF.exists_atlas
  exact ⟨yoneda.map ((isInitial_of_isEmpty B S hS T).to V) ≫ a⟩

/-- Any two morphisms from the presheaf represented by an empty object of the site to an
algebraic space over `S` agree. -/
theorem hom_ext_yoneda_of_isEmpty (T : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj T)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (a b : yoneda.obj T ⟶ F) : a = b := by
  let hr := hF.diagonal_representable
  let f := prod.lift a b
  let j : hr.pullback f ⟶ T := hr.snd f
  have := isEmpty_of_hom j
  let hT := isInitial_of_isEmpty B S hS T
  have : IsIso j :=
    ⟨⟨hT.to (hr.pullback f), (isInitial_of_isEmpty B S hS _).hom_ext _ _, hT.hom_ext _ _⟩⟩
  apply (cancel_epi (yoneda.map j)).mp
  have h := (hr.isPullback f).w
  have h₁ : hr.fst f = yoneda.map j ≫ a := by
    simpa [f, j] using congrArg (fun k => k ≫ prod.fst) h
  have h₂ : hr.fst f = yoneda.map j ≫ b := by
    simpa [f, j] using congrArg (fun k => k ≫ prod.snd) h
  exact h₁.symm.trans h₂

/-- Every morphism out of the presheaf represented by an empty object of the site is locally
of finite presentation. -/
theorem isLocallyOfFinitePresentation_of_isEmpty (T : BigFppfOver B S hS)
    [IsEmpty ((BigFppfOver.toScheme B S hS).obj T)]
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj T ⟶ G) :
    IsLocallyOfFinitePresentation B S hS f := by
  intro U V a b h _ _ _
  have := isEmpty_of_hom (yoneda.preimage a : U ⟶ T)
  infer_instance

end AlgebraicGeometry.Space

end
