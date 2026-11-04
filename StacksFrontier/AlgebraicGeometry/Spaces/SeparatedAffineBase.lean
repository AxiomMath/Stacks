module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Absolute separatedness of an algebraic space separated over an affine scheme

Stacks 082H replaces its morphism `f : X ⟶ Y` by a base change along an étale chart of the
target and then says "whence `X` is a separated algebraic space". That step is the following
one: a morphism of algebraic spaces which is separated in the sense of Stacks 03HL and whose
target is represented by an object of the site with *affine* underlying scheme has absolutely
separated source, in the sense of Stacks 03BS part (1).

The predicate "`X` is a separated algebraic space" is **not** new: it is
`AlgebraicGeometry.Space.IsAbsolutelySeparated` of
`StacksFrontier/AlgebraicGeometry/Spaces/Separated.lean`, which is Stacks 03BS part (1),
separatedness of `X` over the terminal scheme. Nothing here introduces a definition.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_to_affine`: a presheaf
  carrying a separated morphism to a representable presheaf with affine underlying scheme is
  absolutely separated.
* `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_of_isAffineRepresentation`:
  the same with the target only *isomorphic* to such a representable presheaf, which is the
  form "we may and do assume `Y` is an affine scheme" leaves behind.

## Implementation notes

Separatedness of an algebraic space is a property of its *diagonal*, so it is not an
étale-local property of schemes in the sense of Stacks 03E6 and the route through
`AlgebraicGeometry.Space.HasEtaleLocalProperty` is not available: a non-separated algebraic
space has separated — indeed affine — étale charts, so no condition on the charts alone can
detect it. `AlgebraicGeometry.Space.IsAbsolutelySeparated` accordingly tests the closed
immersion property on the absolute diagonal, and that is what is used here.

The argument is the composition `X ⟶ h_T ⟶ h_{⊤}` read over the terminal scheme. Relocalizing
along `S ⟶ ⊤_ Scheme` keeps `f` separated
(`AlgebraicGeometry.Space.isSeparated_relocalize`); the comparison of Stacks 03I4 part (3)
identifies the relocalization of `h_T` with the presheaf represented by the image of `T`,
whose underlying scheme is again affine; the structure morphism of that object to the terminal
object of the site over the terminal scheme is separated because both underlying schemes are
affine (`AlgebraicGeometry.Space.isSeparated_yoneda_map_of_isAffine`); and separatedness is
stable under composition. Separatedness of a morphism to a terminal presheaf is separatedness
over the base, by
`AlgebraicGeometry.Space.isSeparatedOver_iff_isSeparated_of_isTerminal`.

No algebraicity hypothesis on `X` is needed, and none is imposed: the forward direction of
`AlgebraicGeometry.Space.isSeparated_pullbackSnd_iff_isAbsolutelySeparated`, which is
conditions (3) ⇒ (4) of Stacks 03KM at one affine test object, carries one only because its
converse does. That forward direction is the special case of
`AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_to_affine` in which the morphism
is a projection `X ×_Y h_T ⟶ h_T`.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An algebraic space separated over an affine scheme is a separated algebraic space.** If
`f : X ⟶ h_T` is a separated morphism of algebraic spaces over `S` and the scheme underlying
`T` is affine, then `X` is separated over the terminal scheme, that is, absolutely separated
in the sense of Stacks 03BS part (1).

This is the step "whence `X` is a separated algebraic space" of the proof of Stacks 082H,
taken after the target has been replaced by an affine scheme. -/
theorem isAbsolutelySeparated_of_isSeparated_to_affine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (f : X ⟶ yoneda.obj T)
    (hf : IsSeparated B S hS f) : IsAbsolutelySeparated B S hS hZ X := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ))) := Over.mkIdTerminal
  have haffT : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T)) := hT
  have haff0 : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      (Over.mk (𝟙 (B.obj hZ)))) := inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
  have hm : IsSeparated B (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T))) :=
    isSeparated_yoneda_map_of_isAffine B (⊤_ Scheme.{u}) hZ _ haffT haff0
  have hiso := (OverShriek.relocalizeYonedaIso
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).app T
  have hterm' :=
    IsTerminal.isTerminalObj (yoneda (C := BigFppfOver B (⊤_ Scheme.{u}) hZ)) _ hterm
  have h1 := isSeparated_relocalize B S hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) hf
  have h2 := isSeparated_comp B (⊤_ Scheme.{u}) hZ _ _ h1
    (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ hiso.hom)
  have h3 := isSeparated_comp B (⊤_ Scheme.{u}) hZ _ _ h2 hm
  exact (isSeparatedOver_iff_isSeparated_of_isTerminal B (⊤_ Scheme.{u}) hZ hterm' _).2 h3

/-- **An algebraic space separated over a presheaf represented by an affine scheme is a
separated algebraic space.** This is
`AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_to_affine` with the target only
required to be *isomorphic* to the presheaf represented by an object of the site with affine
underlying scheme, which is what the reduction "we may and do assume `Y` is an affine scheme"
of Stacks 082H produces. -/
theorem isAbsolutelySeparated_of_isSeparated_of_isAffineRepresentation
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (e : Y ≅ yoneda.obj T)
    (f : X ⟶ Y) (hf : IsSeparated B S hS f) : IsAbsolutelySeparated B S hS hZ X :=
  isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ T hT (f ≫ e.hom)
    (isSeparated_comp B S hS f e.hom hf (isSeparated_of_isIso B S hS e.hom))

end AlgebraicGeometry.Space

end
