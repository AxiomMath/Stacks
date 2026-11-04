module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# A quasi-compact diagonal is quasi-affine (Stacks 02X3)

Section 65.13 of the Algebraic Spaces chapter closes with an assertion carrying no numbered
tag of its own: once the diagonal `Δ : F ⟶ F × F` of an algebraic space `F` over `S` is known
to be quasi-compact — which happens as soon as `F` is separated over `S` or quasi-separated
over `S` — the diagonal is *quasi-finite and separated*, and therefore *quasi-affine*.

The diagonal is representable, so each of these properties of it means the corresponding
property of every represented base change, which is `CategoryTheory.MorphismProperty.presheaf`
of the inverse image along `AlgebraicGeometry.BigFppfOver.toScheme`, the shape in which
Stacks 02X4 and Stacks 02X5 are already stated in this library.

The three inputs are all proved. Stacks 02X4, part (3) gives separatedness; Stacks 02X4,
part (4) gives locally quasi-finite and locally of finite type; quasi-compactness is the
hypothesis. Together these four are the separated quasi-finite morphisms of schemes, which
Stacks 02LR shows to be quasi-affine.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isSeparatedOver`: a separated algebraic
  space is quasi-separated, that is, a closed-immersion diagonal is quasi-compact. This is
  the parenthetical of the source assertion for the separated case; for the quasi-separated
  case it is the definition.
* `AlgebraicGeometry.Space.presheaf_isSeparated_inf_quasiFinite_diag_of_isQuasiSeparatedOver`:
  a quasi-compact diagonal is separated and quasi-finite.
* `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_diag_of_isQuasiSeparatedOver`: a
  quasi-compact diagonal is quasi-affine.

## Implementation notes

"Quasi-finite" is Stacks 02NG, locally quasi-finite together with of finite type, hence the
three conjuncts `AlgebraicGeometry.LocallyQuasiFinite`, `AlgebraicGeometry.LocallyOfFiniteType`
and `AlgebraicGeometry.QuasiCompact`; the conjunction is assembled in exactly the order
`AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom` expects, so that the
containment of morphism properties applies to it after
`CategoryTheory.MorphismProperty.monotone_inverseImage` and
`CategoryTheory.MorphismProperty.relative_monotone`.

Assembling the conjunction needs no new transport lemma: `P.relative yoneda f` universally
quantifies over *every* represented base-change square of `f`, so the three hypotheses speak
about the same data and their conclusions can simply be paired. Representability of the
diagonal is taken from the quasi-compactness hypothesis rather than from the
algebraic-space structure, so that the two agree by construction.

Quasi-affineness is stated for the representable morphism `Δ` through Stacks 02X4's idiom,
not through `AlgebraicGeometry.Space.IsQuasiAffineHom` of Stacks 03WL: the source sentence is
about the properties of a representable morphism of Definition 65.5.1, and that is what the
`CategoryTheory.MorphismProperty.presheaf` form says.

## References

* [Stacks Project, Tag 02X3](https://stacks.math.columbia.edu/tag/02X3)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 02X3.** An algebraic space separated over `S` is quasi-separated over `S`: a
diagonal which is a closed immersion is in particular quasi-compact. Together with the
definition of quasi-separatedness this is the parenthetical remark of Section 65.13, that the
diagonal is quasi-compact as soon as `F` is separated or quasi-separated over `S`. -/
@[stacks 02X3 "separated gives a quasi-compact diagonal"]
theorem isQuasiSeparatedOver_of_isSeparatedOver (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsSeparatedOver B S hS F) : IsQuasiSeparatedOver B S hS F := by
  refine MorphismProperty.relative_monotone (F := yoneda)
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) ?_) _ hF
  intro X Y f hf
  have : AlgebraicGeometry.IsClosedImmersion f := hf
  infer_instance

/-- **Stacks 02X3.** Let `F` be an algebraic space over `S` whose diagonal is quasi-compact,
that is, which is quasi-separated over `S`. Then the diagonal is separated and quasi-finite:
every represented base change of it is a separated, locally quasi-finite, locally of finite
type and quasi-compact morphism of schemes.

Separatedness is Stacks 02X4, part (3); locally quasi-finite and locally of finite type are
Stacks 02X4, part (4); quasi-compactness is the hypothesis. -/
@[stacks 02X3 "a quasi-compact diagonal is quasi-finite and separated"]
theorem presheaf_isSeparated_inf_quasiFinite_diag_of_isQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hΔ : IsQuasiSeparatedOver B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @AlgebraicGeometry.LocallyQuasiFinite.{u} ⊓
          @AlgebraicGeometry.LocallyOfFiniteType.{u} ⊓ @AlgebraicGeometry.QuasiCompact.{u} :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) := by
  obtain ⟨hrep, hqc⟩ := hΔ
  obtain ⟨-, hsep⟩ := presheaf_isSeparated_diag B S hS F hF
  obtain ⟨-, hqf⟩ := presheaf_locallyQuasiFinite_diag B S hS F hF
  exact ⟨hrep, fun _ _ g fst snd hpb =>
    ⟨⟨⟨hsep g fst snd hpb, (hqf g fst snd hpb).2⟩, (hqf g fst snd hpb).1⟩,
      hqc g fst snd hpb⟩⟩

/-- **Stacks 02X3.** Let `F` be an algebraic space over `S` whose diagonal is quasi-compact,
that is, which is quasi-separated over `S`. Then the diagonal is quasi-affine: every
represented base change of it is a quasi-affine morphism of schemes.

The diagonal is separated and quasi-finite, and a separated quasi-finite morphism of schemes
is quasi-affine by Stacks 02LR. -/
@[stacks 02X3 "a quasi-compact diagonal is quasi-affine"]
theorem presheaf_isQuasiAffineHom_diag_of_isQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hΔ : IsQuasiSeparatedOver B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) :=
  MorphismProperty.relative_monotone (F := yoneda)
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
      AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom) _
    (presheaf_isSeparated_inf_quasiFinite_diag_of_isQuasiSeparatedOver B S hS F hF hΔ)

end AlgebraicGeometry.Space

end
