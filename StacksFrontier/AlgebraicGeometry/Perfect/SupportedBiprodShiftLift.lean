module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.BiprodShiftLift
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedPushforwardRestriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedPullbackAdditive
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.NestedOpenOfLE
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportDetectedOnOneOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism

/-!
# Lifting a supported perfect object off a quasi-compact open of an affine scheme

Let `X = Spec A`, let `T ⊆ X` be closed with `X ∖ T` quasi-compact, and let `U ⊆ X` be a
quasi-compact open. For a perfect object `F` of `D(𝒪_U)` whose cohomology is supported on
`T ∩ U`, the object `F ⊕ F[1]` is the restriction to `U` of a perfect object of `D(𝒪_X)`
supported on `T`.

The route runs over the open `W = U ∪ (X ∖ T)` rather than over `X`. On `W` the subset `T ∩ W`
is `T ∩ U`: it is closed in `W`, and it lies inside the copy of `U` inside `W`. So `F` extends
by zero from `U` to `W` — the derived pushforward along the inclusion is perfect by
[Stacks, Tag 08DP], keeps the support by part (2) of [Stacks, Tag 08DF], and restricts back to
`F` — and the extension `G` is then lifted from `W` to `X` by [Stacks, Tag 08EI], which gives a
perfect `P` on `X` with `P|_W ≅ G ⊕ G[1]`. Support on `T` costs nothing after that choice of `W`:
`X ∖ T ⊆ W`, so the support condition, being stalkwise and tested only off `T`, is already
visible on `W`.

## Main results

* `Stacks.Perfect.SupportedBiprodShift.restrictNestedIsoRestrict_hom_comp_ofRestrict`: the
  comparison `(X|_W)|_Z ≅ X|_U` of
  `Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict` is compatible with the two
  routes into `X`, namely `Z ⟶ W ⟶ X` and `U ⟶ X`.
* `Stacks.Perfect.SupportedBiprodShift.restrictNestedIsoRestrict_base_val`: that comparison is
  the identity on underlying points, read in `X`.
* `Stacks.Perfect.SupportedBiprodShift.exists_isPerfect_supported_restrictNested`: **extension
  by zero from `U` to `W`.** For `U ≤ W` opens of a ringed space and `T` closed with
  `T ∩ W ⊆ U`, a perfect object of `D(𝒪_U)` supported on the preimage of `T` is the restriction
  to the copy of `U` inside `W` of a perfect object of `D(𝒪_W)` supported on the preimage of `T`.
* `Stacks.Perfect.SupportedBiprodShift.derivedRestrictNestedObjIso`: restricting an object of
  `D(𝒪_X)` to `W` and then to the copy of `U` inside `W` is restricting it to `U`, transported
  along the comparison of the two presentations of `X|_U`.
* `Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso`: for additive,
  shift-commuting `H` and `K` into one category and an isomorphism `H G ≅ K F`, an isomorphism
  `H (G ⊕ G[1]) ≅ K (F ⊕ F[1])`.
* `Stacks.Perfect.SupportedBiprodShift.exists_isPerfect_supported_biprod_shift_iso_restrict`:
  the conclusion stated above, for `X = Spec A`. The registration of [Stacks, Tag 08EK] is on
  another declaration, so no tag attribute is placed here.

## The consumer, and what the refinement of [Stacks, Tag 09IM] asks for

[Stacks, Tag 08EK] is what the induction of [Stacks, Tag 09IM] consumes at each affine open of
its cover, and 09IM is in turn what [Stacks, Tag 09IN] refines. In 09IM's setting — `X`
quasi-compact and quasi-separated, `U ⊆ X` a quasi-compact open, `T` closed with `X ∖ T`
retro-compact, `E` an object of `D_QCoh(𝒪_X)` and `α : P → E|_U` with `P` perfect and supported
on `T ∩ U` — the remark asks that the cohomology sheaves of `R|_U` and of `P` agree *above any
given degree*. Two readings of that phrase have to be kept apart, and only one of them is the
source's.

The source fixes the degree first: for every `n` there is a lift `R`, **depending on `n`**, whose
restriction agrees with `P` in all degrees `> n`. The other reading asks for a single `R` serving
every `n` at once, and that one is false — a perfect `R` is bounded, so agreement in every degree
would make `P → R|_U` an isomorphism and extend `P` to a perfect object of `D(𝒪_X)`, which is
what the `F ⊕ F[1]` of [Stacks, Tag 08EI], and hence this module, exists to work around. That
argument needs one `R` whose bound can be undercut; with `R` chosen after `n` its bound varies
with `n`, the argument is unavailable, and no obstruction to the source's reading is known.

The mechanism is the one the positive shifts supply. The complement in `R|_U = P ⊕ C` is a sum of
shifts `P[j]` with `j ≥ 1`, and `H^i(P[j]) = H^{i+j}(P)`, so each shift carries cohomology
downwards: one application already gives the remark's first sentence, that the top cohomology
sheaf of `R|_U` is that of `P`, and repeating the construction on the complement raises the
shifts and lowers `C`'s cohomology a degree at a time.

The iteration is a tower, coned downwards, and not a repeated single cone. Applying the
construction to the complement at each stage gives `ψ_k : R_k → R_{k-1}` with
`R_k|_U ≅ C_{k-1} ⊕ C_k`, where `C_0 = P`, each `ψ_k|_U` is the inclusion on `C_{k-1}`, and `C_k`
is a sum of shifts of `P` by `≥ k`. Coning `ψ₂` gives `Z₂` with `Z₂|_U ≅ cone(c₂ : C₂ → P)`, by
the shear of
`CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp`, so `C₁` cancels and
the bound drops by one. The step that continues it is that the composite `R₃ → R₁ → Z₂` has
restriction vanishing on the `C₂` summand — there it is `c₂` followed by `P → cone(c₂)`, two
consecutive maps of a distinguished triangle — so `Z₃ = cone(R₃ → Z₂)` drops the bound again,
and `Z_k = cone(R_k → Z_{k-1})` once more at each stage.

What that mechanism produces is the degree clause for a map `P → R|_U`: the cone is neither split
over `P` nor a recipient of a map to `E`, the map out of `R₁` going the wrong way for the latter.
A statement that also carries the splitting and the map to `E` — both of which 09IM's own
conclusion has, and neither of which the source's reading excludes — therefore has to carry them
through the affine-cover induction rather than recover them from the cone.

## Implementation notes

Three spelling hazards shaped the proof, and all three are handled by moving the identification
to a defeq check at an application rather than by a transparency attribute.

The right-derived-functor datum of the pushforward is an instance at the
`StrictlyPerfect.structureSheafOfRings` spelling of the structure sheaf of the subspace and is
*not* found at the `ExtensionByZeroModules.resRing` spelling that
`Stacks.Perfect.SupportedPushforward` is stated over, the two being equal only at default
transparency. The two applications therefore pass it positionally, with `@` and
`inferInstanceAs`, as `Stacks.Cohomology.ClosedSupportPerfect` does in
`isIso_extensionByZeroToDerivedPushforward_app_of_supported'`.

`HasDerivedCategory.standard` is made a local instance at priority `10000`, as in
[Stacks, Tag 08EI]'s own module. Without the priority a different model is selected, and
`Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff` is then stated about a
different category: its `IsPerfect` and the one of a hypothesis elaborated here differ in the
derived-category universe, with no error that names the cause.

The last step — that restriction distributes over `G ⊕ G[1]` — is proved as
`Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso`, over three variable
categories, and applied once in term mode. Elaborated directly at the geometry it fails: the
derived pullback's declared codomain is spelled with `AlgebraicGeometry.structureSheafRing` while
the shift of the same object is taken at the `StrictlyPerfect.OXMod` spelling, so the two
arguments of `CategoryTheory.Limits.HasBinaryBiproduct` sit in two spellings of one category and
instance search keys on neither. With the codomain a variable the objects are typed by it and the
instance is found. For the same reason the additivity and the shift-commutation of the derived
pullback are explicit arguments of that lemma and not instance arguments.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EI](https://stacks.math.columbia.edu/tag/08EI)
* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedPushforwardUnit)
open Stacks.Cohomology.ClosedSupportPerfect
open Stacks.Perfect.SupportedPushforward (cohomologySupportedOn_derivedPushforward_of_supported
  derivedRestriction_derivedPushforward_isoOfSupported)

universe u

namespace Stacks.Perfect.SupportedBiprodShift

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} (U W : Opens X)

/-! ### The copy of `U` inside a larger open `W` -/

/-- Transporting the inclusion of an open subspace along an equality of opens. -/
theorem eqToHom_restrict_comp_ofRestrict {O₁ O₂ : Opens X} (h : O₁ = O₂) :
    eqToHom (congrArg (fun O : Opens X => X.restrict O.isOpenEmbedding) h) ≫
        X.ofRestrict O₂.isOpenEmbedding = X.ofRestrict O₁.isOpenEmbedding := by
  subst h; simp

/-- **The two routes from the copy of `U` inside `W` to `X` agree.** For `U ≤ W` opens of a
ringed space, `Stacks.Cohomology.ClosedSupportPerfect.restrictNestedIsoRestrict` identifies
`(X|_W)|_Z` with `X|_U`, where `Z` is `U` read as an open of `W`; composed with the inclusion of
`U` it is the inclusion of `Z` into `W` followed by the inclusion of `W`.

This is `Stacks.Cohomology.ClosedSupportPerfect.nestedOpenToAmbientIso_hom_fac` with the image of
`Z` in `X` identified with `U`. -/
theorem restrictNestedIsoRestrict_hom_comp_ofRestrict (hUW : U ≤ W) :
    (restrictNestedIsoRestrict U W hUW).hom ≫ X.ofRestrict U.isOpenEmbedding =
      (X.restrict W.isOpenEmbedding).ofRestrict (nestedOpenOfLE U W).isOpenEmbedding ≫
        X.ofRestrict W.isOpenEmbedding := by
  have hfac := nestedOpenToAmbientIso_hom_fac W (nestedOpenOfLE U W)
  have hO : (SheafedSpace.IsOpenImmersion.opensFunctor
      (nestedOpenInclusion W (nestedOpenOfLE U W))).obj ⊤ = U :=
    (opensFunctor_nestedOpenInclusion_obj_top W (nestedOpenOfLE U W)).trans
      (image_nestedOpenOfLE U W hUW)
  show ((nestedOpenToAmbientIso W (nestedOpenOfLE U W)).hom ≫
      eqToHom (congrArg (fun O : Opens X => X.restrict O.isOpenEmbedding) hO)) ≫
        X.ofRestrict U.isOpenEmbedding = _
  rw [Category.assoc, eqToHom_restrict_comp_ofRestrict hO]
  exact hfac

/-- **The comparison `(X|_W)|_Z ≅ X|_U` does not move points.** A point of the copy of `U` inside
`W` and its image in `U` have the same image in `X`. This is
`Stacks.Perfect.SupportedBiprodShift.restrictNestedIsoRestrict_hom_comp_ofRestrict` read at a
point, the inclusions of open subspaces being the subtype inclusions. -/
theorem restrictNestedIsoRestrict_base_val (hUW : U ≤ W)
    (z : ((X.restrict W.isOpenEmbedding).restrict
      (nestedOpenOfLE U W).isOpenEmbedding).carrier) :
    Subtype.val ((restrictNestedIsoRestrict U W hUW).hom.hom.base z) =
      Subtype.val (Subtype.val z) :=
  congrArg (fun φ : ((X.restrict W.isOpenEmbedding).restrict
      (nestedOpenOfLE U W).isOpenEmbedding) ⟶ X => φ.hom.base z)
    (restrictNestedIsoRestrict_hom_comp_ofRestrict U W hUW)

/-! ### Extension by zero from `U` to `W` -/

/-- **A perfect object supported on a closed subset of `U` extends from `U` to `W`.** Let `U ≤ W`
be opens of a ringed space and `T` a closed subset with `T ∩ W ⊆ U`. Then a perfect object `F` of
`D(𝒪_U)` whose cohomology is supported on the preimage of `T` is the restriction, to the copy `Z`
of `U` inside `W`, of a perfect object of `D(𝒪_W)` whose cohomology is supported on the preimage
of `T`.

The object is the derived pushforward of `F` along `Z ⟶ W`. It is perfect by
[Stacks, Tag 08DP], whose hypothesis — that the image of the support in `W` is closed — is
`Stacks.Cohomology.ClosedSupportPerfect.isClosed_image_nestedPreimage` and is where `T ∩ W ⊆ U`
is used; it keeps the support and restricts back to `F` by part (2) of [Stacks, Tag 08DF], in the
form of `Stacks.Perfect.SupportedPushforward`. Over `X` instead of `W` none of this is available:
`T ∩ U` need not be closed in `X`. -/
theorem exists_isPerfect_supported_restrictNested (hUW : U ≤ W) (T : Set X) (hT : IsClosed T)
    (hTWU : T ∩ (W : Set X) ⊆ (U : Set X))
    (F : DerivedCategory (OXMod.{u, u} (X.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := X.restrict U.isOpenEmbedding) F)
    (hFT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (X.restrict U.isOpenEmbedding)) (Subtype.val ⁻¹' T) F) :
    ∃ G : DerivedCategory (OXMod.{u, u} (X.restrict W.isOpenEmbedding)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect
          (X := X.restrict W.isOpenEmbedding) G ∧
        AlgebraicGeometry.CohomologySupportedOn
            (structureSheafRing (X.restrict W.isOpenEmbedding)) (Subtype.val ⁻¹' T) G ∧
          Nonempty ((AlgebraicGeometry.RingedSpace.derivedRestrictModules
              (X.restrict W.isOpenEmbedding) (nestedOpenOfLE U W)).obj G ≅
            (derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj F) := by
  have hT' : IsClosed (Subtype.val ⁻¹' T :
      Set (X.restrict W.isOpenEmbedding).carrier) :=
    hT.preimage continuous_subtype_val
  have hT'Z : (Subtype.val ⁻¹' T : Set (X.restrict W.isOpenEmbedding).carrier) ⊆
      ((nestedOpenOfLE U W : Opens (X.restrict W.isOpenEmbedding)) :
        Set (X.restrict W.isOpenEmbedding).carrier) :=
    fun y hy => hTWU ⟨hy, y.2⟩
  have hF' : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (X.restrict W.isOpenEmbedding).restrict (nestedOpenOfLE U W).isOpenEmbedding)
      ((derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj F) :=
    (Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff
      (restrictNestedIsoRestrict U W hUW) F).2 hF
  have hF'T : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing ((X.restrict W.isOpenEmbedding).restrict
        (nestedOpenOfLE U W).isOpenEmbedding))
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' T : Set (X.restrict W.isOpenEmbedding).carrier))
      ((derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj F) := by
    have h := Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback
      (restrictNestedIsoRestrict U W hUW).hom (Subtype.val ⁻¹' T) F hFT
    have hset : Stacks.Cohomology.SupportedComplexes.closedSubsetPreimage
        (restrictNestedIsoRestrict U W hUW).hom (Subtype.val ⁻¹' T) =
        Subtype.val ⁻¹' (Subtype.val ⁻¹' T :
          Set (X.restrict W.isOpenEmbedding).carrier) := by
      ext z
      show Subtype.val ((restrictNestedIsoRestrict U W hUW).hom.hom.base z) ∈ T ↔
        Subtype.val (Subtype.val z) ∈ T
      rw [restrictNestedIsoRestrict_base_val]
    exact hset ▸ h
  have hR : (derivedPushforward ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding)).IsRightDerivedFunctor
      (derivedPushforwardUnit ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing
        ((X.restrict W.isOpenEmbedding).restrict (nestedOpenOfLE U W).isOpenEmbedding)))
        (ComplexShape.up ℤ)) :=
    inferInstance
  refine ⟨(derivedPushforward ((X.restrict W.isOpenEmbedding).ofRestrict
    (nestedOpenOfLE U W).isOpenEmbedding)).obj
      ((derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj F), ?_, ?_, ?_⟩
  · exact isPerfect_derivedPushforward_of_closedSupport (X.restrict W.isOpenEmbedding)
      (nestedOpenOfLE U W) _ (isClosed_image_nestedPreimage U W T hT hTWU) _
      (derivedPushforwardUnit _) _ hF' hF'T
  · refine @cohomologySupportedOn_derivedPushforward_of_supported
      _ (structureSheafRing (X.restrict W.isOpenEmbedding)) (nestedOpenOfLE U W) _ hT' hT'Z _ _
      (derivedPushforward ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding))
      (derivedPushforwardUnit ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding)) ?_ _ hF'T
    exact hR
  · refine ⟨@derivedRestriction_derivedPushforward_isoOfSupported
      _ (structureSheafRing (X.restrict W.isOpenEmbedding)) (nestedOpenOfLE U W) _ hT' hT'Z
      (derivedPushforward ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding))
      (derivedPushforwardUnit ((X.restrict W.isOpenEmbedding).ofRestrict
        (nestedOpenOfLE U W).isOpenEmbedding)) ?_ _ hF'T⟩
    exact hR

/-- **Restricting to `W` and then to the copy of `U` inside `W` is restricting to `U`**, at one
object, transported along the comparison of the two presentations of `X|_U`.

Each derived restriction is the derived pullback along the inclusion of its open, derived
pullbacks along composable morphisms compose by [Stacks, Tag 0D5S], and the two routes to `X`
agree by
`Stacks.Perfect.SupportedBiprodShift.restrictNestedIsoRestrict_hom_comp_ofRestrict`. -/
def derivedRestrictNestedObjIso (hUW : U ≤ W) (P : DerivedCategory (OXMod.{u, u} X)) :
    (AlgebraicGeometry.RingedSpace.derivedRestrictModules (X.restrict W.isOpenEmbedding)
          (nestedOpenOfLE U W)).obj
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X W).obj P) ≅
      (derivedPullback (restrictNestedIsoRestrict U W hUW).hom).obj
        ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X U).obj P) :=
  (AlgebraicGeometry.RingedSpace.derivedRestrictModules (X.restrict W.isOpenEmbedding)
        (nestedOpenOfLE U W)).mapIso
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback X W).app P) ≪≫
    (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback
        (X.restrict W.isOpenEmbedding) (nestedOpenOfLE U W)).app _ ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        ((X.restrict W.isOpenEmbedding).ofRestrict (nestedOpenOfLE U W).isOpenEmbedding)
        (X.ofRestrict W.isOpenEmbedding)).app P ≪≫
    eqToIso (congrArg (fun f : ((X.restrict W.isOpenEmbedding).restrict
        (nestedOpenOfLE U W).isOpenEmbedding) ⟶ X => (derivedPullback f).obj P)
      (restrictNestedIsoRestrict_hom_comp_ofRestrict U W hUW).symm) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (restrictNestedIsoRestrict U W hUW).hom (X.ofRestrict U.isOpenEmbedding)).app P).symm ≪≫
    (derivedPullback (restrictNestedIsoRestrict U W hUW).hom).mapIso
      ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback X U).app P).symm

/-! ### A comparison of two functors carried to `· ⊕ ·⟦1⟧` -/

/-- **Two additive, shift-commuting functors into one category agreeing at `G` and `F` agree at
`G ⊕ G[1]` and `F ⊕ F[1]`.** Both functors distribute over the biproduct by
`CategoryTheory.Functor.biprodIsoOfAdditive` and over the shift by their commutation with it, and
the given isomorphism is carried across the two summands.

The additivity and the shift-commutation are explicit arguments rather than instance arguments,
and the common codomain is a variable: that is what makes this applicable to the derived
restriction and the derived pullback at once, whose declared codomains spell the structure sheaf
of a ringed space differently. See the implementation notes of this module. -/
def biprodShiftIsoOfFunctorIso {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    [HasBinaryBiproducts C₁] [HasBinaryBiproducts C₂] [HasBinaryBiproducts C₃]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    (H : C₁ ⥤ C₃) (K : C₂ ⥤ C₃) (hH : H.Additive) (hK : K.Additive)
    (cH : H.CommShift ℤ) (cK : K.CommShift ℤ)
    {G : C₁} {F : C₂} (e : H.obj G ≅ K.obj F) :
    H.obj (G ⊞ G⟦(1 : ℤ)⟧) ≅ K.obj (F ⊞ F⟦(1 : ℤ)⟧) :=
  letI := hH
  letI := hK
  letI := cH
  letI := cK
  Functor.biprodIsoOfAdditive H G (G⟦(1 : ℤ)⟧) ≪≫
    biprod.mapIso (Iso.refl _) ((Functor.commShiftIso H (1 : ℤ)).app G) ≪≫
    biprod.mapIso e ((shiftFunctor C₃ (1 : ℤ)).mapIso e) ≪≫
    biprod.mapIso (Iso.refl _) ((Functor.commShiftIso K (1 : ℤ)).app F).symm ≪≫
    (Functor.biprodIsoOfAdditive K F (F⟦(1 : ℤ)⟧)).symm

/-! ### The conclusion over an affine scheme -/

/-- **`F ⊕ F[1]` is the restriction of a perfect object supported on `T`.** Let `X = Spec A`, let
`T ⊆ X` be closed with `X ∖ T` quasi-compact, and let `U ⊆ X` be a quasi-compact open. For every
perfect object `F` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` there is a perfect object
`P` of `D(𝒪_X)` whose cohomology is supported on `T`, with `F ⊕ F[1] ≅ P|_U`.

`W = U ∪ (X ∖ T)` is quasi-compact and satisfies `T ∩ W ⊆ U`, so
`Stacks.Perfect.SupportedBiprodShift.exists_isPerfect_supported_restrictNested` extends `F` to a
perfect `G` on `W` supported on `T ∩ W`, and [Stacks, Tag 08EI] lifts `G` from the quasi-compact
open `W` of `Spec A` to a perfect `P` on `Spec A` with `G ⊕ G[1] ≅ P|_W`. The support of `P` is
read off that isomorphism by
`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_compl_subset`, whose
hypothesis `X ∖ T ⊆ W` is how `W` was chosen; and `P|_U` is computed from `P|_W` by
`Stacks.Perfect.SupportedBiprodShift.derivedRestrictNestedObjIso` together with
`Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso`.

The registration of [Stacks, Tag 08EK] is on another declaration, so no tag
attribute is placed here. -/
theorem exists_isPerfect_supported_biprod_shift_iso_restrict {A : CommRingCat.{u}}
    (T : Set ↥(Spec A)) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : (Spec A).Opens) (hU : IsCompact ((U : (Spec A).Opens) : Set ↥(Spec A)))
    (F : DerivedCategory (OXMod.{u, u}
      ((Spec A).toRingedSpace.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace.restrict U.isOpenEmbedding) F)
    (hFT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing ((Spec A).toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) F) :
    ∃ P : DerivedCategory (OXMod.{u, u} (Spec A).toRingedSpace),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P ∧
        AlgebraicGeometry.CohomologySupportedOn
            (structureSheafRing (Spec A).toRingedSpace) T P ∧
          Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules
              (Spec A).toRingedSpace U).obj P) := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : (Spec A).Opens, W = U ⊔ ⟨Tᶜ, hT.isOpen_compl⟩ := ⟨_, rfl⟩
  have hUW : U ≤ W := hWdef ▸ le_sup_left
  have hW : IsCompact ((W :
      (Spec A).Opens) : Set ↥(Spec A)) := by
    rw [hWdef, Opens.coe_sup]; exact hU.union hTc
  have hTWU : T ∩ ((W :
      (Spec A).Opens) : Set ↥(Spec A)) ⊆ ((U : (Spec A).Opens) : Set ↥(Spec A)) := by
    rintro x ⟨hxT, hxW⟩
    rw [hWdef, Opens.coe_sup] at hxW
    rcases hxW with h | h
    · exact h
    · exact absurd hxT h
  have hCW : Tᶜ ⊆ ((W :
      (Spec A).Opens) : Set ↥(Spec A)) := by
    rw [hWdef, Opens.coe_sup]; exact Set.subset_union_right
  obtain ⟨G, hG, hGT, ⟨eG⟩⟩ := exists_isPerfect_supported_restrictNested U
    W hUW T hT hTWU F hF hFT
  obtain ⟨P, hP, ⟨eP⟩⟩ := Stacks.DerivedQCoh.OpenLift.exists_isPerfect_biprod_shift_iso_restrict
    W hW G hG
  refine ⟨P, hP, ?_, ?_⟩
  · refine Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_compl_subset
      (structureSheafRing (Spec A).toRingedSpace)
      W T hCW P ?_
    exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ _ eP
      (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_biprod _ _ _ _ hGT
        (Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_shift _ _ _ hGT))
  · have hchain := biprodShiftIsoOfFunctorIso
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules
        ((Spec A).toRingedSpace.restrict
          W.isOpenEmbedding)
        (nestedOpenOfLE U W))
      (derivedPullback (restrictNestedIsoRestrict U
        W hUW).hom)
      inferInstance
      (Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive
        (restrictNestedIsoRestrict U
          W hUW).hom)
      inferInstance
      (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift
        (restrictNestedIsoRestrict U
          W hUW).hom) eG
    have hstep := hchain.symm ≪≫
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules
        ((Spec A).toRingedSpace.restrict
          W.isOpenEmbedding)
        (nestedOpenOfLE U W)).mapIso eP ≪≫
      derivedRestrictNestedObjIso U W hUW P
    exact ⟨((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackHomInvIso
        (restrictNestedIsoRestrict U
          W hUW)).app _).symm ≪≫
      (derivedPullback (restrictNestedIsoRestrict U
        W hUW).inv).mapIso hstep ≪≫
      (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackHomInvIso
        (restrictNestedIsoRestrict U
          W hUW)).app _⟩

end Stacks.Perfect.SupportedBiprodShift

end
