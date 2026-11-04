module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Pushing an ideal sheaf forward along a closed immersion and pulling it back again

Pushforward and pullback of quasi-coherent ideal sheaves form a Galois connection, so for any
morphism `f : X ⟶ Y` of schemes and any `I : X.IdealSheafData` one has
`(I.map f).comap f ≤ I` (`AlgebraicGeometry.Scheme.IdealSheafData.comap_map_le`). The inequality
can be strict: pushing forward replaces the closed subscheme cut out by `I` with its
scheme-theoretic image in `Y`, and pulling that back can enlarge the subscheme.

When `f` is a closed immersion no information is lost. The closed subscheme cut out by `I` is
already a closed subscheme of `Y`, so it *is* its own scheme-theoretic image, and the square
exhibiting it as the fibre product of `f` with that image is a pullback square because a closed
immersion is a monomorphism. Hence the two operations are mutually inverse on ideal sheaves of
the source.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isClosedImmersion`: for a closed
  immersion `f`, pushing an ideal sheaf of the source forward along `f` and pulling it back
  returns the original ideal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **Pushforward along a closed immersion is a section of pullback.** For a closed immersion
`f : X ⟶ Y` and a quasi-coherent ideal sheaf `I` on `X`, the inverse image along `f` of the
pushforward of `I` is again `I`.

The general inequality `(I.map f).comap f ≤ I` is
`AlgebraicGeometry.Scheme.IdealSheafData.comap_map_le`; what is proved here is the reverse one,
and it uses that `f` is a monomorphism: the closed subscheme of `I` sits in the fibre product of
`f` with `I.subschemeι ≫ f` as an isomorphism onto the first projection, whose defining ideal is
`(I.map f).comap f`. -/
theorem comap_map_of_isClosedImmersion {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Y)
    [IsClosedImmersion f] : (I.map f).comap f = I := by
  have hpb : IsPullback I.subschemeι (𝟙 I.subscheme) f (I.subschemeι ≫ f) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hker : (pullback.fst f (I.subschemeι ≫ f)).ker = I := by
    rw [← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom, hpb.isoPullback_hom_fst,
      I.ker_subschemeι]
  simpa only [ker_fst_of_isClosedImmersion, map] using hker

end AlgebraicGeometry.Scheme.IdealSheafData

end
