module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Quasi-projective and H-quasi-projective morphisms compared

An H-quasi-projective morphism `f : X ⟶ S` — one admitting a quasi-compact immersion
`i : X ⟶ ℙⁿ_S` over `S` — is quasi-projective: it is of finite type, and `i^* 𝒪(1)` is an
invertible `𝒪_X`-module ample relative to `f`. That is [Stacks, Tag 01VY], and it is the easy
half of [Stacks, Tag 01VZ], which compares the two notions *locally over the base*: `f` is
locally quasi-projective exactly when the base has an open covering over whose members `f` is
H-quasi-projective. Both halves of that equivalence are proved below, with no hypothesis.

Finite type is read off the factorisation, `i` being an immersion and `ℙⁿ_S ⟶ S` proper. The
relatively ample module is produced by [Stacks, Tag 01VN] in the form
`Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion`, whose input is an
immersion over the base onto a scheme carrying a module ample relative to *its* structure
morphism. The module is `𝒪(1)` on `ℙⁿ_S`, and the relative ampleness it needs is proved here for
an arbitrary base.

## Main results

* `Stacks.HProjective.isAmple_twistingSheafAtUniverse`: `𝒪(1)` is ample on the integral model
  `ℙⁿ_ℤ`.
* `Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf`: **`𝒪(1)` is ample relative
  to `ℙⁿ_S ⟶ S`, with no hypothesis on `S`.** [Stacks, Tag 01VK] gives this over an affine base;
  the general case is proved here by base change, see below.
* `Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective`: **Stacks Tag 01VY.**
* `Stacks.HProjective.isLocallyQuasiProjective_iff_exists_openCover_isHQuasiProjective`:
  **Stacks Tag 01VZ**, together with its two implications
  `Stacks.HProjective.isLocallyQuasiProjective_of_exists_openCover_isHQuasiProjective` and
  `Stacks.HProjective.exists_openCover_isHQuasiProjective_of_isLocallyQuasiProjective`, and the
  literal `S = ⋃ Vⱼ` reading of condition (2) in
  `Stacks.HProjective.exists_opens_isHQuasiProjective_of_isLocallyQuasiProjective`.

## The two spellings of quasi-projectivity

The repository carries two definitions of each of the notions of [Stacks, Tag 01VW]:
`Stacks.HProjective.IsQuasiProjective`, over `Stacks.RelativeAmple.IsRelativelyAmple` and
`Stacks.Ample.IsAmple`, and `AlgebraicGeometry.IsQuasiProjective`, over
`Stacks.RelativeAmple.IsRelativelyAmple` and
`AlgebraicGeometry.Scheme.Modules.IsAmple`. The invertibility binders and the module pullbacks of
the two relative-ampleness predicates agree definitionally, and their two notions of absolute
ampleness are the same condition by `Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple`; so
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple` and
`Stacks.HProjective.modulesIsQuasiProjective_iff_isQuasiProjective` identify them with no new
mathematics. Tag 01VZ is stated over the `AlgebraicGeometry` spellings, because
`AlgebraicGeometry.IsLocallyQuasiProjective` and `AlgebraicGeometry.IsHQuasiProjective` are the
declarations carrying the Tag 01VW attribute; the two spellings of H-quasi-projectivity are
already equal by `rfl`, via `Stacks.HProjective.over_projectiveSpaceOver`.

## Stacks Tag 01VZ

The implication (2) ⟹ (1) is Tag 01VY applied over each member of the covering, exactly as in the
source.

For (1) ⟹ (2) the source reduces to an affine base. Here that reduction is performed by passing
to `AlgebraicGeometry.Scheme.OpenCover.affineRefinement`: over an affine member of the base
covering, relative ampleness *is* absolute ampleness by [Stacks, Tag 01VK]
(`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`), which is the service the source
takes from Lemma 01VT, and then [Stacks, Tag 01VS]
(`Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`, through
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine`) produces the immersion
into projective space. Quasi-compactness and local finite type descend to the restriction because
both are Zariski-local at the target.

Tag 01VK is what [Stacks, Tag 01VT] supplies over an affine base: it is the equivalence
`Stacks.AmpleRelativeFiniteType.isAmple_iff_isRelativelyAmple` read off that tag's list, and it
is used here in the primitive form.



`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine` is stated with Tag 01VS
as a named hypothesis, `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform`. That
hypothesis is a theorem, `Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`, so nothing
below carries it.

## The base change over an affine open of the base

Relative ampleness, [Stacks, Tag 01VH], asks for ampleness of `𝒪(1)` restricted to `p⁻¹(V)` for
every affine open `V` of `S`, where `p : ℙⁿ_S ⟶ S`. Since `𝒪(1)` on `ℙⁿ_S` is by definition the
pullback of `𝒪(1)` on `ℙⁿ_ℤ` along `q : ℙⁿ_S ⟶ ℙⁿ_ℤ`, its restriction to `p⁻¹(V)` is the pullback
along the composite `p⁻¹(V) ⟶ ℙⁿ_S ⟶ ℙⁿ_ℤ`, and that composite is an **affine** morphism:
pasting the pullback square of `AlgebraicGeometry.morphismRestrict` onto the one defining `ℙⁿ_S`
exhibits it as the base change of `V ⟶ Spec ℤ` along `ℙⁿ_ℤ ⟶ Spec ℤ`, and `V` and the terminal
scheme are both affine. Ampleness then travels along it by [Stacks, Tag 0B3E] for an affine
morphism, which is unconditional.

## Implementation notes

**No identification of `p⁻¹(V)` with `ℙⁿ_V` is made.** The affineness of the composite to the
integral model is all the base change is used for, and it is read directly off the pasted square,
so no isomorphism of schemes and no transport of modules across one appears below.

**The two spellings of the module pullback are the same functor.** `𝒪(1)` on `ℙⁿ_S` is written
with `AlgebraicGeometry.Scheme.Modules.pullback` while relative ampleness is written with
`RingedSpaceModuleAdjunction.modulePullback`; the two agree by `rfl`, so the isomorphisms of
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean` apply with no bridge.

## References

* [Stacks Project, Tag 01VY](https://stacks.math.columbia.edu/tag/01VY)
* [Stacks Project, Tag 01VZ](https://stacks.math.columbia.edu/tag/01VZ)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [EGA II, Proposition 5.3.4 (i)]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.HProjective

/-! ### The hyperplane sheaf on the integral model -/

section Integral

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`𝒪(1)` is ample on the integral model `ℙⁿ_ℤ`.** Projective space over the integers is
`Proj` of the polynomial ring in `n + 1` variables graded by total degree, and the coordinates
cover it by affine standard opens in degree one. -/
theorem isAmple_twistingSheafAtUniverse (n : ℕ) :
    IsAmple (projectiveSpaceAtUniverse.{u} n) (twistingSheafAtUniverse.{u} n) :=
  Stacks.ProjectiveSpace.isAmple_twistingSheaf_one (ULift.{u} ℤ) n

end Integral

/-! ### Relative ampleness of the hyperplane sheaf over an arbitrary base -/

/-- **The preimage of an affine open of the base maps affinely to the integral model.** The
square of `AlgebraicGeometry.morphismRestrict` over `V` pasted onto the square defining `ℙⁿ_S`
exhibits `p⁻¹(V) ⟶ ℙⁿ_ℤ` as the base change of `V ⟶ Spec ℤ` along `ℙⁿ_ℤ ⟶ Spec ℤ`, and a morphism
between affine schemes is affine. -/
theorem isAffineHom_preimage_ι_comp_toIntegralAtUniverse (n : ℕ) {S : Scheme.{u}}
    (V : S.Opens) (hV : IsAffineOpen V) :
    IsAffineHom (((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι ≫
      projectiveSpaceOver.toIntegralAtUniverse n S) := by
  have : IsAffine V.toScheme := hV
  have hbase : IsPullback (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOver.toIntegralAtUniverse n S) (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) := IsPullback.of_hasPullback _ _
  have hterm : IsAffineHom (V.ι ≫ terminal.from S) := by
    rw [show V.ι ≫ terminal.from S = terminal.from V.toScheme from terminal.hom_ext _ _]
    infer_instance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    ((isPullback_morphismRestrict (projectiveSpaceOver n S ↘ S) V).paste_vert hbase) hterm

/-- **`𝒪(1)` restricted to the preimage of an affine open of the base is ample.** It is the
pullback of `𝒪(1)` on `ℙⁿ_ℤ` along the affine morphism of
`Stacks.HProjective.isAffineHom_preimage_ι_comp_toIntegralAtUniverse`, and ampleness pulls back
along an affine morphism. -/
theorem isAmple_preimage_projectiveSpaceTwistingSheaf (n : ℕ) {S : Scheme.{u}}
    (V : S.Opens) (hV : IsAffineOpen V) :
    IsAmple ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).toScheme
      ((modulePullback ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        (projectiveSpaceTwistingSheaf n S)) := by
  have := isAffineHom_preimage_ι_comp_toIntegralAtUniverse n V hV
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (hN := Stacks.InvertiblePullback.isInvertibleModule_pullback
      ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι (projectiveSpaceTwistingSheaf n S))
    (hN' := Stacks.InvertiblePullback.isInvertibleModule_pullback
      (((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι ≫
        projectiveSpaceOver.toIntegralAtUniverse n S) (twistingSheafAtUniverse.{u} n))
    (Stacks.RelativeVeryAmple.modulePullbackPairIso
      ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι
      (projectiveSpaceOver.toIntegralAtUniverse n S) (twistingSheafAtUniverse.{u} n))).mpr
    (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom _ _
      (isAmple_twistingSheafAtUniverse n))

/-- **`𝒪(1)` is ample relative to the structure morphism of `ℙⁿ_S`, for every base scheme `S`.**
The structure morphism is proper, hence quasi-compact, and
`Stacks.HProjective.isAmple_preimage_projectiveSpaceTwistingSheaf` is the condition of
[Stacks, Tag 01VH] at each affine open of the base. -/
@[sga "6 VIII 3.1" "special case"]
theorem isRelativelyAmple_projectiveSpaceTwistingSheaf (n : ℕ) (S : Scheme.{u}) :
    Stacks.RelativeAmple.IsRelativelyAmple (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceTwistingSheaf n S) := by
  have := isProper_projectiveSpaceOver n S
  exact ⟨inferInstance, isAmple_preimage_projectiveSpaceTwistingSheaf n⟩

/-! ### Stacks Tag 01VY -/

/-- **Stacks Tag 01VY: an H-quasi-projective morphism is quasi-projective.** Let
`i : X ⟶ ℙⁿ_S` be a quasi-compact immersion with `i ≫ (ℙⁿ_S ↘ S) = f`. Then `f` is of finite
type, because `i` is an immersion and `ℙⁿ_S ⟶ S` is proper, and `i^* 𝒪(1)` is an invertible
module ample relative to `f` by [Stacks, Tag 01VN], `𝒪(1)` being ample relative to
`ℙⁿ_S ⟶ S`. -/
@[stacks 01VY]
theorem isQuasiProjective_of_isHQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsHQuasiProjective f) : IsQuasiProjective f := by
  obtain ⟨n, i, hi, hqc, hif⟩ := hf
  have := isProper_projectiveSpaceOver n S
  have hft : LocallyOfFiniteType f := by rw [← hif]; infer_instance
  have hqcf : QuasiCompact f := by rw [← hif]; infer_instance
  exact ⟨⟨hft, hqcf⟩, (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S),
    inferInstance, Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion
      Stacks.SectionExtension.amplePullbackGap f _ hqcf
      ⟨projectiveSpaceOver n S, projectiveSpaceOver n S ↘ S, projectiveSpaceTwistingSheaf n S,
        inferInstance, i, hi, hif, isRelativelyAmple_projectiveSpaceTwistingSheaf n S,
        ⟨Iso.refl _⟩⟩⟩

/-! ### The repository's two spellings of quasi-projectivity -/

/-- **The two quasi-projectivity predicates of [Stacks, Tag 01VW] are the same condition.** Both
ask for finite type together with an invertible module ample relative to the morphism; the
invertibility binders agree definitionally and the relative ampleness by
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple`.

No attribute is attached: Tag 01VW is already carried by each of the two definitions. -/
theorem modulesIsQuasiProjective_iff_isQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) :
    AlgebraicGeometry.IsQuasiProjective f ↔ IsQuasiProjective f :=
  Iff.rfl

/-! ### H-quasi-projectivity depends only on the isomorphism class of a morphism -/

/-- **H-quasi-projectivity is carried across a commuting square whose vertical sides are
isomorphisms.** The quasi-compact immersion into `ℙⁿ` over one base becomes one over the other
after composing with the inverse isomorphism of the sources and with the identification
`AlgebraicGeometry.projectiveSpaceOverCongr` of the two projective spaces; an isomorphism is both
an immersion and quasi-compact, so neither property of the immersion is lost.

This is `AlgebraicGeometry.IsProjectiveMorphism.of_iso` with the closed immersion weakened to a
quasi-compact immersion. -/
theorem isHQuasiProjective_of_iso {Y Z Y' Z' : Scheme.{u}} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (e : Y ≅ Y') (b : Z ≅ Z') (w : e.hom ≫ g' = g ≫ b.hom) (hg : IsHQuasiProjective g) :
    IsHQuasiProjective g' := by
  obtain ⟨n, i, hi, hqc, hig⟩ := hg
  refine ⟨n, e.inv ≫ i ≫ (projectiveSpaceOverCongr n b).hom, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, projectiveSpaceOverCongr_hom_over, ← Category.assoc i,
    hig, ← w, Iso.inv_hom_id_assoc]

/-! ### Stacks Tag 01VZ -/

/-- H-quasi-projectivity is carried across an isomorphism of arrows. -/
private theorem isHQuasiProjective_of_arrow_iso {Y Z Y' Z' : Scheme.{u}} {g : Y ⟶ Z}
    {g' : Y' ⟶ Z'} (e : Arrow.mk g ≅ Arrow.mk g') (hg : IsHQuasiProjective g) :
    IsHQuasiProjective g' :=
  isHQuasiProjective_of_iso (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) (Arrow.w e.hom) hg

/-- **A quasi-projective morphism is H-quasi-projective over every affine open of the base.**
This is the reduction to an affine base that the proof of [Stacks, Tag 01VZ] performs.

Relative ampleness of `L` with respect to `g` asserts, at the affine open `W`, precisely that the
restriction of `L` to `g⁻¹(W)` is ample there; so over the affine base `W` that restriction is
ample relative to `g ∣_ W` by [Stacks, Tag 01VK] — the service the source takes from Lemma 01VT —
and `g ∣_ W` is quasi-projective. Local finite type and quasi-compactness pass to the restriction
because both are Zariski-local at the target.
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine` then concludes, its
[Stacks, Tag 01VS] hypothesis supplied by
`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`. -/
theorem isHQuasiProjective_morphismRestrict_of_isQuasiProjective {A B : Scheme.{u}} (g : A ⟶ B)
    (hg : IsQuasiProjective g) (W : B.Opens) (hW : IsAffineOpen W) :
    IsHQuasiProjective (g ∣_ W) := by
  have : IsAffine W.toScheme := hW
  obtain ⟨⟨hft, hqc⟩, L, hLinv, hLamp⟩ := hg
  have := hLinv
  have hamp : Stacks.Ample.IsAmple (g ⁻¹ᵁ W).toScheme
      ((modulePullback (g ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L) := hLamp.2 W hW
  have hloftLocal : IsZariskiLocalAtTarget @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType
  have hqcLocal : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  refine isHQuasiProjective_of_isQuasiProjective_of_isAffine
    Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform.{u} _ ?_
  exact ⟨⟨IsZariskiLocalAtTarget.restrict hft W, IsZariskiLocalAtTarget.restrict hqc W⟩,
    (modulePullback (g ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L, inferInstance,
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (g ∣_ W) _).mpr hamp⟩

/-- **A quasi-projective morphism is H-quasi-projective after base change along an open immersion
with affine source.** The image of the open immersion is an affine open of the base, and the base
change is isomorphic as an arrow to the restriction over that open by
`AlgebraicGeometry.morphismRestrictOpensRange`. -/
theorem isHQuasiProjective_pullbackSnd_of_isQuasiProjective {A B : Scheme.{u}} (g : A ⟶ B)
    (hg : IsQuasiProjective g) {B' : Scheme.{u}} (k : B' ⟶ B) [IsOpenImmersion k] [IsAffine B'] :
    IsHQuasiProjective (pullback.snd g k) := by
  have e := morphismRestrictOpensRange g k
  exact isHQuasiProjective_of_arrow_iso e
    (isHQuasiProjective_morphismRestrict_of_isQuasiProjective g hg k.opensRange
      (isAffineOpen_opensRange k))

/-- **Stacks Tag 01VZ, the implication (2) ⟹ (1).** If the base carries an open covering over
whose members `f` is H-quasi-projective, then `f` is locally quasi-projective.

This is [Stacks, Tag 01VY] applied over each member of the covering, which is the source's own
proof of this implication. -/
@[stacks 01VZ "(2) implies (1): H-quasi-projective over a cover of the base"]
theorem isLocallyQuasiProjective_of_exists_openCover_isHQuasiProjective {X S : Scheme.{u}}
    (f : X ⟶ S) (h : ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
      AlgebraicGeometry.IsHQuasiProjective (pullback.snd f (𝒰.f i))) :
    AlgebraicGeometry.IsLocallyQuasiProjective f := by
  obtain ⟨𝒰, h⟩ := h
  exact ⟨𝒰, fun i => (modulesIsQuasiProjective_iff_isQuasiProjective _).mpr
    (isQuasiProjective_of_isHQuasiProjective _ (h i))⟩

/-- **Stacks Tag 01VZ, the implication (1) ⟹ (2).** A locally quasi-projective morphism admits an
open covering of the base over whose members it is H-quasi-projective.

Local quasi-projectivity gives a covering `𝒰` of the base over whose members `f` becomes
quasi-projective. Refining `𝒰` to an affine covering —
`AlgebraicGeometry.Scheme.OpenCover.affineRefinement`, whose members are the affine covers of the
members of `𝒰` — reduces to an affine base, where
`Stacks.HProjective.isHQuasiProjective_pullbackSnd_of_isQuasiProjective` applies. The refinement's
base change is identified with the iterated one by
`AlgebraicGeometry.Scheme.OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom`, and
H-quasi-projectivity travels across that identification by
`Stacks.HProjective.isHQuasiProjective_of_iso`. -/
@[stacks 01VZ "(1) implies (2): a cover of the base over which f is H-quasi-projective"]
theorem exists_openCover_isHQuasiProjective_of_isLocallyQuasiProjective {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : AlgebraicGeometry.IsLocallyQuasiProjective f) :
    ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
      AlgebraicGeometry.IsHQuasiProjective (pullback.snd f (𝒰.f i)) := by
  obtain ⟨𝒰, h⟩ := hf
  refine ⟨𝒰.affineRefinement.openCover, fun j => ?_⟩
  refine isHQuasiProjective_of_iso (𝒰.pullbackCoverAffineRefinementObjIso f j).symm (Iso.refl _)
    ?_ (isHQuasiProjective_pullbackSnd_of_isQuasiProjective (𝒰.pullbackHom f j.1)
      ((modulesIsQuasiProjective_iff_isQuasiProjective _).mp (h j.1))
      ((𝒰.X j.1).affineCover.f j.2))
  show (𝒰.pullbackCoverAffineRefinementObjIso f j).inv ≫
      𝒰.affineRefinement.openCover.pullbackHom f j =
    (𝒰.X j.1).affineCover.pullbackHom (𝒰.pullbackHom f j.1) j.2 ≫ 𝟙 _
  rw [Category.comp_id]
  exact Scheme.OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom f 𝒰 j

/-- **Stacks Tag 01VZ.** A morphism of schemes is locally quasi-projective if and only if the base
has an open covering over whose members it is H-quasi-projective. -/
@[stacks 01VZ "(1) iff (2): the equivalence the tag states"]
theorem isLocallyQuasiProjective_iff_exists_openCover_isHQuasiProjective {X S : Scheme.{u}}
    (f : X ⟶ S) :
    AlgebraicGeometry.IsLocallyQuasiProjective f ↔
      ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i : 𝒰.I₀,
        AlgebraicGeometry.IsHQuasiProjective (pullback.snd f (𝒰.f i)) :=
  ⟨exists_openCover_isHQuasiProjective_of_isLocallyQuasiProjective f,
    isLocallyQuasiProjective_of_exists_openCover_isHQuasiProjective f⟩

/-- **Stacks Tag 01VZ, condition (2) in the source's own phrasing.** A locally quasi-projective
`f : X ⟶ S` admits a family of opens `Vⱼ` of `S` with `S = ⋃ Vⱼ` such that every
`f⁻¹(Vⱼ) ⟶ Vⱼ` is H-quasi-projective.

The opens are the images of the covering produced by
`Stacks.HProjective.exists_openCover_isHQuasiProjective_of_isLocallyQuasiProjective`; they cover
`S` by `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`, and over each of them the base
change and the restriction are isomorphic as arrows by
`AlgebraicGeometry.morphismRestrictOpensRange`. -/
@[stacks 01VZ "(1) implies (2), with the cover as opens Vⱼ of S and f⁻¹(Vⱼ) → Vⱼ"]
theorem exists_opens_isHQuasiProjective_of_isLocallyQuasiProjective
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : AlgebraicGeometry.IsLocallyQuasiProjective f) :
    ∃ (ι : Type u) (V : ι → S.Opens), (⨆ j, V j) = ⊤ ∧
      ∀ j, AlgebraicGeometry.IsHQuasiProjective (f ∣_ V j) := by
  obtain ⟨𝒰, h⟩ := exists_openCover_isHQuasiProjective_of_isLocallyQuasiProjective f hf
  refine ⟨𝒰.I₀, fun j => (𝒰.f j).opensRange, 𝒰.iSup_opensRange, fun j => ?_⟩
  have e := (morphismRestrictOpensRange f (𝒰.f j)).symm
  exact isHQuasiProjective_of_arrow_iso e (h j)

end Stacks.HProjective

end
