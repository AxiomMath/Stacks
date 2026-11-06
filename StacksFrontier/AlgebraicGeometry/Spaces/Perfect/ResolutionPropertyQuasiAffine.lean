module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# The resolution property along an affine or quasi-affine morphism of algebraic spaces

Stacks 0GUU asserts that the source of an affine or quasi-affine morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` has the resolution property as soon as `Y` is quasi-compact,
quasi-separated and has the resolution property.  Its proof is a reduction: by Stacks 0GUQ the
structure sheaf `𝒪_X` is `f`-ample for such an `f`, so the statement is the case `L = 𝒪_X` of
Stacks 0GUT.

## Main definitions

* `AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple` is the statement of
  Stacks 0GUT, as a proposition about the base: for every morphism of algebraic spaces over `S`
  carrying a relatively ample module onto a quasi-compact, quasi-separated target with the
  resolution property, the source has the resolution property.

## Main results

* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isAffineHom`: **a step of Stacks 0GUU**, that an
  affine morphism of algebraic spaces is quasi-affine, so that the two hypotheses of the source
  are one hypothesis.
* `AlgebraicGeometry.Space.isRelativelyAmple_unit_of_isQuasiAffineHom` and
  `AlgebraicGeometry.Space.isRelativelyAmple_unit_of_isAffineHom`: the structure sheaf of the
  source of a quasi-affine, respectively affine, morphism is relatively ample.
* `AlgebraicGeometry.Space.exists_affine_etale_cover_hasResolutionProperty_of_isQuasiAffineHom`:
  **a step of Stacks 0GUU**, that for a quasi-affine `f` over a quasi-compact `Y` there is an
  affine surjective étale chart `V` of `Y` over which the fibre product `V ×_Y X` is a scheme
  with the resolution property.
* `AlgebraicGeometry.Space.hasResolutionProperty_of_isQuasiAffineHom` and
  `AlgebraicGeometry.Space.hasResolutionProperty_of_isAffineHom`: the reduction of the
  quasi-affine and of the affine case of Stacks 0GUU to Stacks 0GUT.

## Implementation notes

**What the two `@[stacks 0GUU]` attributes of this file sit on.**  They sit on the two steps of
the source's proof which are theorems here: that an affine morphism is quasi-affine, so that the
two cases of the statement are one case, and the chart of the target over which the fibre product
is a scheme with the resolution property.  The conclusion of the source — the resolution property
of `X` — is the conclusion of Stacks 0GUT read through Stacks 0GUQ, and Stacks 0GUT is not a
theorem of this tree; the two declarations
`AlgebraicGeometry.Space.hasResolutionProperty_of_isQuasiAffineHom` and
`AlgebraicGeometry.Space.hasResolutionProperty_of_isAffineHom` perform that reduction and take
`AlgebraicGeometry.Space.HasResolutionPropertyOfRelativelyAmple` — the statement of Stacks 0GUT
— as the input `hGUT`, so **they carry no `stacks` attribute**.  What the reduction needs from
Stacks 0GUT is recorded in the report of this file's statement of it, below.

The step of the source's proof which *is* available, and which
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple` describes as out
of reach, is in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections`: of the
three inputs that file lists, quasi-coherence of the direct image is now
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs` (Stacks 03M9), the
enclosing of finitely many sections in a finite type quasi-coherent submodule is
`AlgebraicGeometry.Space.chartExtensionProperty_id` (Stacks 0829), and finite local freeness of
a pullback is `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback`.

**`hGUT` is Stacks 0GUT and not its specialization.**  `hGUT` quantifies over an
arbitrary relatively ample module `L`, as Stacks 0GUT does.  Specializing it to `L = 𝒪_X` would
make it, by Stacks 0GUQ, equivalent to the conclusion being proved, so the implication would be
empty; with the general `L` the content of each reduction below is Stacks 0GUQ, which is what the
source's proof uses.

**Quasi-separatedness.**  "`Y` is quasi-separated" is the absolute notion of Stacks 03BS,
part (3), `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`, which needs the terminal scheme
in the site; that containment is the explicit hypothesis `hZ`, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Separated`.  It is used nowhere in this file except to be
passed to `hGUT`, so it is also the form in which `hGUT` asks for it.

**Affine implies quasi-affine.**  `AlgebraicGeometry.Space.IsAffineHom` produces, over an affine
test object, a cartesian square whose upper-left corner is an affine object of the site, and
`AlgebraicGeometry.Space.IsQuasiAffineHom` asks for an object of the site whose scheme is
quasi-affine together with an isomorphism onto the fibre product; the square is turned into that
isomorphism by `CategoryTheory.IsPullback.isoPullback` and
`CategoryTheory.Limits.pullbackSymmetry`, and an affine scheme is quasi-affine.

**The universes.**  `AlgebraicGeometry.Space.HasResolutionProperty` keeps the universe of the
module sections free, while relative ampleness is stated at the universe of the schemes; the
free universe is carried through `hGUT` and the conclusions below unchanged.

## References

* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0GUQ](https://stacks.math.columbia.edu/tag/0GUQ)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_resolutionPropertyQuasiAffine
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Affine morphisms are quasi-affine -/

/-- **The reduction of the affine case of Stacks 0GUU to its quasi-affine case.**  An affine
morphism of algebraic spaces is quasi-affine: its base change to an affine test object is
represented by an affine, hence quasi-affine, scheme.

This is why Stacks 0GUU may assume `f` quasi-affine throughout: its two hypotheses, affine and
quasi-affine, are one hypothesis. -/
@[stacks 0GUU "the reduction of the hypothesis: the affine case of the statement is its
quasi-affine case, an affine morphism of algebraic spaces being quasi-affine"]
theorem isQuasiAffineHom_of_isAffineHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsAffineHom B S hS f) : IsQuasiAffineHom B S hS f := by
  intro Z g
  obtain ⟨W, p, q, hsq⟩ := hf Z g
  refine ⟨(BigAffineFppf.inclusion B S hS).obj W, ?_,
    ⟨hsq.isoPullback ≪≫ pullbackSymmetry f g⟩⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W)) :=
    W.property
  infer_instance

/-! ### Stacks 0GUQ for affine and quasi-affine morphisms -/

/-- **Stacks 0GUQ for a quasi-affine morphism.** The structure sheaf of the source of a
quasi-affine morphism of algebraic spaces is relatively ample. -/
theorem isRelativelyAmple_unit_of_isQuasiAffineHom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsQuasiAffineHom B S hS f.hom) :
    IsRelativelyAmple B S hS f
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :=
  (isQuasiAffineHom_iff_isRelativelyAmple_unit f).mp hf

/-- **Stacks 0GUQ for an affine morphism.** The structure sheaf of the source of an affine
morphism of algebraic spaces is relatively ample. -/
theorem isRelativelyAmple_unit_of_isAffineHom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) :
    IsRelativelyAmple B S hS f
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :=
  isRelativelyAmple_unit_of_isQuasiAffineHom f (isQuasiAffineHom_of_isAffineHom hf)

/-! ### The chart step of Stacks 0GUU -/

/-- **The chart step of the proof of Stacks 0GUU.** For `f : X ⟶ Y` a
quasi-affine morphism of algebraic spaces with `Y` quasi-compact there are an affine scheme `V`
over the base with a surjective étale morphism to `Y` and a cartesian square presenting the
fibre product `V ×_Y X` as a scheme `U` with the resolution property.

This is the source's sentence *"Choose an affine scheme `V` and a surjective étale morphism
`V → Y`.  Set `U = V ×_Y X`"*, with the properties of `U` that the rest of the proof reads off
it: `𝒪_U` is ample on `U` because `f` is quasi-affine and `V` is affine (Stacks 0GUQ and
Stacks 01VK), so `U` has the resolution property by Stacks 0F87. -/
@[stacks 0GUU "the chart step of the proof: an affine surjective étale chart of the target over
which the scheme fibre product has the resolution property"]
theorem exists_affine_etale_cover_hasResolutionProperty_of_isQuasiAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQuasiAffineHom B S hS f.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        IsEtale B S hS g ∧
        ∃ (U : BigFppfOver B S hS) (q : U ⟶ V) (p : yoneda.obj U ⟶ X.1),
          IsPullback p (yoneda.map q) f.hom g ∧
            _root_.AlgebraicGeometry.HasResolutionProperty
              ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨V, g, hVaff, hVsurj, hVet, U, q, p, hsq, -, hUres⟩ :=
    exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple
      (isRelativelyAmple_unit_of_isQuasiAffineHom f hf) hY
  exact ⟨V, g, hVaff, hVsurj, hVet, U, q, p, hsq, hUres⟩

/-! ### The reduction of Stacks 0GUU to Stacks 0GUT -/

/-- **The statement of Stacks 0GUT**, for algebraic spaces over the scheme `S`: a morphism of
algebraic spaces carrying a relatively ample module whose target is quasi-compact,
quasi-separated and has the resolution property has a source with the resolution property. -/
def HasResolutionPropertyOfRelativelyAmple.{v, w} (B : BigFppfSite.{v}) (S : Scheme.{v})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{v})) : Prop :=
  ∀ (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y) (L : Modules.{v, v} B S hS X.1 X.2),
    IsRelativelyAmple B S hS f L → IsQuasiCompactSpace B S hS Y.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
        HasResolutionProperty.{v, w} B S hS Y.1 Y.2 →
          HasResolutionProperty.{v, w} B S hS X.1 X.2

/-- **The reduction of the quasi-affine case of Stacks 0GUU to Stacks 0GUT.** For `f : X ⟶ Y` a
quasi-affine morphism of algebraic spaces over `S` with `Y` quasi-compact, quasi-separated and
carrying the resolution property, the statement of Stacks 0GUT implies the resolution property
of `X`.

By Stacks 0GUQ the structure sheaf of `X` is `f`-ample, which is the case `L = 𝒪_X` of
Stacks 0GUT.  **No `stacks` attribute is carried**: `hGUT` is the statement of Stacks 0GUT,
which this tree does not prove, so only the reduction is content here. -/
theorem hasResolutionProperty_of_isQuasiAffineHom (hZ : B.Contains (⊤_ Scheme.{u}))
    (hGUT : HasResolutionPropertyOfRelativelyAmple.{u, m} B S hS hZ)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsQuasiAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, m} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, m} B S hS X.1 X.2 :=
  hGUT X Y f _ (isRelativelyAmple_unit_of_isQuasiAffineHom f hf) hYqc hYqs hYres

/-- **The reduction of the affine case of Stacks 0GUU to Stacks 0GUT.** For `f : X ⟶ Y` an
affine morphism of algebraic spaces over `S` with `Y` quasi-compact, quasi-separated and
carrying the resolution property, the statement of Stacks 0GUT implies the resolution property
of `X`.

An affine morphism is quasi-affine, so this is the previous theorem.  **No `stacks` attribute is
carried**, for the same reason as there. -/
theorem hasResolutionProperty_of_isAffineHom (hZ : B.Contains (⊤_ Scheme.{u}))
    (hGUT : HasResolutionPropertyOfRelativelyAmple.{u, m} B S hS hZ)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hYres : HasResolutionProperty.{u, m} B S hS Y.1 Y.2) :
    HasResolutionProperty.{u, m} B S hS X.1 X.2 :=
  hasResolutionProperty_of_isQuasiAffineHom hZ hGUT f (isQuasiAffineHom_of_isAffineHom hf)
    hYqc hYqs hYres

end AlgebraicGeometry.Space

end
