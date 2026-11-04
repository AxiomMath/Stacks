module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.WeilRestriction
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Weil restriction of a closed subscheme of a product with an affine scheme over a field

Let `k` be a field, let `a : A ⟶ Spec k` be affine and of finite type and let `b : B ⟶ Spec k`
be arbitrary.  Then every closed subscheme `Z ⊆ A ×_k B` admits a Weil restriction along the
projection `p : A ×_k B ⟶ B`: a closed subscheme of `B` through which a scheme over `B` factors
exactly when the base change of `Z` to it is all of `A ×_k B`.

This is the case of Tag 07AI in which the morphism along which one restricts is a base change of
an affine morphism of finite type over a field, and the point of the file is that in this case
Tag 07AI's hypotheses hold outright.  Three of them — flat, of finite presentation, quasi-compact
and quasi-separated — are base changes of properties of `a`, where they hold because `k` is a
field and hence Noetherian and because `a` is affine.  The fourth, purity of the structure sheaf
relative to the base, is the one with content, and it is Tag 05MD: for an affine morphism the
direct image of the structure sheaf is locally projective, and a module with locally projective
direct image is pure.  Over the field itself `p_* 𝒪_A` has sections `Γ(A, ⊤)`, a `k`-vector space
and so a projective `k`-module; Tag 02KG carries local projectivity of the direct image across
the cartesian square, and Tag 060M across the pullback along `b`.

## Main results

* `AlgebraicGeometry.isLocallyProjective_pushforwardStructureSheaf_of_isAffine_over_field`: the
  direct image of the structure sheaf of an affine scheme along its structure morphism to the
  spectrum of a field is locally projective.
* `AlgebraicGeometry.isLocallyProjective_pushforwardStructureSheaf_of_isPullback`: the same after
  a base change, for the base-changed projection.
* `AlgebraicGeometry.isSchemePureRelative_of_isPullback_of_isAffine_over_field`: the base change
  of an affine morphism of finite type over a field is pure relative to its base.
* `Stacks.Flatness.exists_closedImmersion_weilRestriction_of_isAffine_over_field`: the Weil
  restriction of a closed subscheme along such a base change is represented by a closed
  immersion into the base.

## Implementation notes

The ascriptions `show X.Modules from SheafOfModules.unit X.ringCatSheaf` are load-bearing rather
than cosmetic: `AlgebraicGeometry.Scheme.Modules` is a `def`, so an instance stated for a module
ascribed to `X.Modules` is not found for the same term ascribed to `SheafOfModules X.ringCatSheaf`,
and the quasi-coherence of the direct image is such an instance.

The identification `g^* 𝒪_Y ≅ 𝒪_X` is taken from the ringed-space library, where it holds for
every morphism of ringed spaces; the morphism of sheaves of rings a morphism of schemes induces
and the one its underlying morphism of ringed spaces induces are the same, so the isomorphism
transfers by `exact`.

## References

* [Stacks Project, Tag 07AI](https://stacks.math.columbia.edu/tag/07AI)
* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 060M](https://stacks.math.columbia.edu/tag/060M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u v

namespace AlgebraicGeometry

/-- Every module over a commutative ring which is a field is projective, because it is free. -/
private lemma projective_of_isField {R : Type u} [CommRing R] (hR : IsField R)
    (M : Type v) [AddCommGroup M] [Module R M] : Module.Projective R M := by
  let : Field R := hR.toField
  exact Module.Projective.of_basis (Module.Basis.ofVectorSpace R M)

/-- The ring of functions on the spectrum of a field is a field. -/
private lemma isField_sections_spec (k : Type u) [Field k] :
    IsField (Γ(Spec (CommRingCat.of k), ⊤)) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

/-- The inverse image of the structure sheaf is the structure sheaf, at the ascription to
`AlgebraicGeometry.Scheme.Modules` in which the consumers below need it. -/
private def pullbackStructureSheafIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Scheme.Modules.pullback g).obj
        (show Y.Modules from SheafOfModules.unit.{u} Y.ringCatSheaf) ≅
      (show X.Modules from SheafOfModules.unit.{u} X.ringCatSheaf) :=
  RingedSpaceModuleAdjunction.modulePullbackUnitIso g.toLRSHom.toShHom

/-- The direct image of the structure sheaf of an affine scheme along an affine morphism is
quasi-coherent. -/
private lemma isQuasicoherent_pushforward_structureSheaf {A Y : Scheme.{u}} [IsAffine A]
    (a : A ⟶ Y) [IsAffineHom a] :
    ((Scheme.Modules.pushforward a).obj
      (show A.Modules from SheafOfModules.unit.{u} A.ringCatSheaf)).IsQuasicoherent :=
  haveI : (show A.Modules from SheafOfModules.unit.{u} A.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit A
  inferInstance

/-- The direct image of the structure sheaf of an affine scheme along its structure morphism to
the spectrum of a field is locally projective.

The spectrum of a field is covered by its single affine open `⊤`, over which the sections of the
direct image are `Γ(A, ⊤)`; the ring of functions on the base is a field, so that module is a
vector space and hence projective. -/
theorem isLocallyProjective_pushforwardStructureSheaf_of_isAffine_over_field
    {k : Type u} [Field k] {A : Scheme.{u}} [IsAffine A] (a : A ⟶ Spec (CommRingCat.of k)) :
    Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward a).obj
        (show A.Modules from SheafOfModules.unit.{u} A.ringCatSheaf)) := by
  have : IsAffineHom a := isAffineHom_of_isAffine a
  have := isQuasicoherent_pushforward_structureSheaf a
  refine (isLocallyProjective_iff_exists_affineOpen_cover
      ((Scheme.Modules.pushforward a).obj
        (show A.Modules from SheafOfModules.unit.{u} A.ringCatSheaf))).2
    ⟨PUnit, fun _ => ⊤, TopologicalSpace.IsOpenCover.mk (by simp),
      fun _ => isAffineOpen_top _, fun _ => ?_⟩
  exact projective_of_isField (isField_sections_spec k) _

/-- The direct image of the structure sheaf along the base change of an affine morphism of an
affine scheme over a field is locally projective.

Tag 060M makes the pullback along `b` of the direct image over the field locally projective, and
Tag 02KG identifies that pullback with the direct image along the base-changed morphism of the
inverse image of the structure sheaf, which is the structure sheaf. -/
theorem isLocallyProjective_pushforwardStructureSheaf_of_isPullback
    {k : Type u} [Field k] {A X B : Scheme.{u}} [IsAffine A]
    (a : A ⟶ Spec (CommRingCat.of k)) (b : B ⟶ Spec (CommRingCat.of k))
    (q : X ⟶ A) (p : X ⟶ B) (h : IsPullback q p a b) :
    Scheme.Modules.IsLocallyProjective
      ((Scheme.Modules.pushforward p).obj
        (show X.Modules from SheafOfModules.unit.{u} X.ringCatSheaf)) := by
  have haff : IsAffineHom a := isAffineHom_of_isAffine a
  have hqc : (show A.Modules from SheafOfModules.unit.{u} A.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit A
  have := isQuasicoherent_pushforward_structureSheaf a
  have h₁ := pullback_isLocallyProjective b _
    (isLocallyProjective_pushforwardStructureSheaf_of_isAffine_over_field a)
  have h₂ := Scheme.Modules.isLocallyProjective_of_iso
    (Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso q p a b h haff _ hqc) h₁
  exact Scheme.Modules.isLocallyProjective_of_iso
    ((Scheme.Modules.pushforward p).mapIso (pullbackStructureSheafIso q)) h₂

/-- **The base change of an affine morphism of finite type over a field is pure relative to its
base.**

This is the implication of Tag 05MD from local projectivity of the direct image to relative
purity, applied to the structure sheaf, whose direct image is locally projective by
`AlgebraicGeometry.isLocallyProjective_pushforwardStructureSheaf_of_isPullback`. -/
theorem isSchemePureRelative_of_isPullback_of_isAffine_over_field
    {k : Type u} [Field k] {A X B : Scheme.{u}} [IsAffine A]
    (a : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a]
    (b : B ⟶ Spec (CommRingCat.of k))
    (q : X ⟶ A) (p : X ⟶ B) (h : IsPullback q p a b) :
    letI : LocallyOfFiniteType p := MorphismProperty.of_isPullback h inferInstance
    letI : QuasiCompact p := MorphismProperty.of_isPullback h inferInstance
    IsSchemePureRelative p := by
  have : IsAffineHom p := MorphismProperty.of_isPullback h inferInstance
  have : LocallyOfFiniteType p := MorphismProperty.of_isPullback h inferInstance
  have : QuasiCompact p := MorphismProperty.of_isPullback h inferInstance
  have : (show X.Modules from SheafOfModules.unit.{u} X.ringCatSheaf).IsFiniteType :=
    structureSheaf_isFiniteType X
  have : (show X.Modules from SheafOfModules.unit.{u} X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  exact isPureRelative_of_isLocallyProjective_pushforward p _
    (isLocallyProjective_pushforwardStructureSheaf_of_isPullback a b q p h)

end AlgebraicGeometry

namespace Stacks.Flatness

/-- **The case of Stacks Project, Tag 07AI, in which the morphism restricted along is a base
change of an affine morphism of finite type over a field.** Every closed subscheme `Z` of `X`
then has a Weil restriction along `p`: a closed immersion `W ⟶ B` such that the morphisms over
`B` from a scheme `T` to `W` correspond to the single proof that the base change `Z_T ⟶ X_T` is
an isomorphism.

All four hypotheses of Tag 07AI hold.  Flatness, finite presentation, quasi-compactness and
quasi-separatedness of `p` are inherited from `a`, which has them because `k` is a field — so
`Spec k` is Noetherian and `a`, being of finite type, is of finite presentation, and every
scheme over a field is flat over it — and because `a` is affine.  Purity is
`AlgebraicGeometry.isSchemePureRelative_of_isPullback_of_isAffine_over_field`. -/
@[sga "3 VIB 6.2.3" "(i)", sga "3 VIB 6.5.2" "special case", sga "3 XI 6.4" "partial"]
theorem exists_closedImmersion_weilRestriction_of_isAffine_over_field
    {k : Type u} [Field k] {A X B : Scheme.{u}} [IsAffine A]
    (a : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a]
    (b : B ⟶ Spec (CommRingCat.of k))
    (q : X ⟶ A) (p : X ⟶ B) (h : IsPullback q p a b)
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ W : Over B, IsClosedImmersion W.hom ∧
      ∀ T : Over B, Nonempty ((T ⟶ W) ≃
        PLift (IsIso (WeilRestriction.closedSubschemeBaseChange i p T))) := by
  have : IsAffineHom p := MorphismProperty.of_isPullback h inferInstance
  have : LocallyOfFiniteType p := MorphismProperty.of_isPullback h inferInstance
  have : QuasiCompact p := MorphismProperty.of_isPullback h inferInstance
  have : QuasiSeparated p := inferInstance
  have : Flat p := MorphismProperty.of_isPullback h inferInstance
  have : LocallyOfFinitePresentation p := MorphismProperty.of_isPullback h inferInstance
  obtain ⟨W, hW, ⟨e⟩⟩ :=
    weilRestriction_representableBy_closedImmersion_of_affineTests i p
      (isSchemePureRelative_of_isPullback_of_isAffine_over_field a b q p h)
  exact ⟨W, hW, fun T => ⟨e.homEquiv⟩⟩

end Stacks.Flatness

end
