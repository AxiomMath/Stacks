module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CoherenceFromPointClosures
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.NagataPushforward
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.NormalizationPointClosureMono
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.NormalizationStalkDimension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCoherence
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic

/-!
# Coherence of a direct image over a Nagata universally catenary scheme

Let `X` be a locally Noetherian scheme, let `j : U ⟶ X` be the inclusion of an open subscheme
with complement `Z`, and let `F` be a coherent `𝒪_U`-module. [Stacks, Tag 0AWA] asserts that
`j_*F` is coherent as soon as

1. `X` is Nagata,
2. `X` is universally catenary, and
3. `dim(𝒪_{closure{x}, z}) ≥ 2` for every `x ∈ Ass(F)` and every `z ∈ Z ∩ closure{x}`.

This file states that lemma and proves it on those three assumptions alone:
`isCoherent_pushforward_of_isNagataScheme` carries no hypothesis beyond them. Everything the
lemma needs is proved here or already available.

The construction the source runs at an associated point `x` is the normalization `π : Y ⟶ X` of
`X` in `Spec κ(x)`; `residueFieldNormalizationPushforward X x` is the coherent `𝒪_X`-module
`G = π_*𝒪_Y` it produces. Assumption (1) is what makes `π` finite and hence `G` coherent, and
that implication is proved below.

## Main definitions

* `Stacks.LocalCohomology.residueFieldNormalizationPushforward`: the module `G = π_*𝒪_Y` for
  `π : Y ⟶ X` the normalization of `X` in `Spec κ(x)`.
* `Stacks.LocalCohomology.TwoLePointClosureDim`: assumption (3) of [Stacks, Tag 0AWA] at one
  associated point.

## Main results

* `Stacks.LocalCohomology.isFinite_fromNormalization_fromSpecResidueField`: over a Nagata scheme
  the normalization of `X` in `Spec κ(x)` is finite over `X`. This is [Stacks, Tag 0AVK] at the
  canonical morphism `Spec κ(x) ⟶ X`.
* `Stacks.LocalCohomology.isCoherent_residueFieldNormalizationPushforward`: consequently
  `G = π_*𝒪_Y` is a coherent `𝒪_X`-module, by [Stacks, Tag 01Y6].
* `Stacks.LocalCohomology.isCoherent_pushforward_of_isNagataScheme`: **[Stacks, Tag 0AWA]**, on
  the tag's own three assumptions.

## Implementation notes

`Z` is the complement of `U`, so "`z ∈ Z`" is `z ∉ (U : Set X)`; the inclusion of an open
subscheme is `V.ι` for `V : X.Opens`, which is the shape the depth-two theorem
`AlgebraicGeometry.isCoherent_pushforward_of_mono_of_depth_ge_two` is stated at. The module
`i_{x,*}𝒪_{W_x}` is `AlgebraicGeometry.pointClosureStructureSheaf`, and `closure{x}` is the
reduced closed subscheme `Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})`, whose
points are the points of the closure; quantifying over its points `w` with `ι w ∉ U` is
therefore the source's "`z ∈ Z ∩ closure{x}`". Assumption (3) is kept as a condition at each
associated point and is **not** replaced by a bound on the codimension of `Z`, which would be
strictly stronger.

### The inputs, and which tags they are

Two of the three inputs this lemma once took are now proved. The implication (1) ⇒ (2) of
[Stacks, Tag 0BJZ] — coherence of `j_*i_{x,*}𝒪_{W_x}` at every associated point of `F` gives
coherence of `j_*F` — is `isCoherent_pushforward_of_forall_isAssociatedPoint'` of the namespace
`Stacks.AlgebraicGeometry.CoherenceFromPointClosures`; it rests on [Stacks, Tag 01YB] only with
a principal ideal, which is the form the library carries, and its affine reduction supplies the
Noetherian quasi-affine hypotheses that form needs. The depth-two conclusion of the source's
last paragraph is
`AlgebraicGeometry.hasDepthTwoOutside_pushforwardUnitModule_fromSpecResidueField`.

The comparison morphism of the source's second paragraph — the identity `W_x = U ∩ π(Y)` makes
`π` restricted over `U` factor through `i_x`, yielding `i_{x,*}𝒪_{W_x} ⟶ G|_U` — is
`Stacks.LocalCohomology.exists_mono_pullback_residueFieldNormalizationPushforward`. It rests on
cartesianness of the point-closure square of [Stacks, Tag 0BK2] and on scheme-theoretic
dominance of the factored normalization.
The source's last paragraph, which turns assumptions (2) and (3) into `depth(G_z) ≥ 2` for
`z ∈ Z`, is no longer a hypothesis either. Its inputs are the `(S₂)` consequence of
[Stacks, Tag 0345] — used through
`AlgebraicGeometry.two_le_depth_stalk_of_isNormal_of_two_le_ringKrullDim`, which carries no
attribute of its own, the tag itself being at
`AlgebraicGeometry.isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one` —
[Stacks, Tag 02JU] in its universally catenary equality form,
`AlgebraicGeometry.localDimension_add_trdeg_eq`, and the scheme-level form of
[Stacks, Tag 0AUK], `AlgebraicGeometry.Scheme.Hom.depth_pushforwardStalk_eq_iInf`. They are
assembled in `AlgebraicGeometry.hasDepthTwoOutside_pushforwardUnitModule_fromSpecResidueField`.

Assumptions (2) and (3) enter through that assembly, and assumption (1) through
`isCoherent_residueFieldNormalizationPushforward` and the finiteness of the normalization.
Dropping any one of the three numbered assumptions makes the statement below unprovable from
its remaining hypotheses.

## References

* [Stacks Project, Tag 0AWA](https://stacks.math.columbia.edu/tag/0AWA)
* [Stacks Project, Tag 0AVK](https://stacks.math.columbia.edu/tag/0AVK)
* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.LocalCohomology

/-! ### The normalization of `X` in the spectrum of a residue field -/

/-- A space with at most one point has finitely many irreducible components, and so does every
subset of it. -/
private theorem finite_irreducibleComponents_of_subsingleton {T : Type*} [TopologicalSpace T]
    [Subsingleton T] (s : Set T) : (irreducibleComponents s).Finite := by
  have : Finite s := Finite.of_subsingleton
  exact NoetherianSpace.finite_irreducibleComponents

/-- **[Stacks, Tag 0AVK] at the spectrum of a residue field.** For a point `x` of a Nagata
scheme `X`, the normalization of `X` in `Spec κ(x)` is finite over `X`.

`Spec κ(x)` is reduced and has one point, so the two combinatorial hypotheses of
[Stacks, Tag 0AVK] are automatic, and the canonical morphism `Spec κ(x) ⟶ X` is surjective on
stalks, so each residue field extension it induces is finitely generated. -/
theorem isFinite_fromNormalization_fromSpecResidueField {X : Scheme.{u}} (x : X)
    (hX : IsNagataScheme X) : IsFinite (X.fromSpecResidueField x).fromNormalization := by
  refine isFinite_fromNormalization (X.fromSpecResidueField x) hX
    (fun U _ => finite_irreducibleComponents_of_subsingleton _) fun y => ?_
  let := ((X.fromSpecResidueField x).residueFieldMap y.1).hom.toAlgebra
  have : Algebra.EssFiniteType (X.residueField ((X.fromSpecResidueField x).base y.1))
      ((Spec (X.residueField x)).residueField y.1) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact (RingHom.FiniteType.of_surjective _
      (AlgebraicGeometry.surjective_residueFieldMap_of_surjectiveOnStalks
        (X.fromSpecResidueField x) y.1)).essFiniteType
  exact IntermediateField.fg_top _ _

/-- The `𝒪_X`-module `G = π_*𝒪_Y` of the proof of [Stacks, Tag 0AWA], for `π : Y ⟶ X` the
normalization of `X` in `Spec κ(x)`. -/
noncomputable abbrev residueFieldNormalizationPushforward (X : Scheme.{u}) (x : X) : X.Modules :=
  (Scheme.Modules.pushforward (X.fromSpecResidueField x).fromNormalization).obj
    (SheafOfModules.unit.{u} (X.fromSpecResidueField x).normalization.ringCatSheaf)

/-- **Assumption (1) of [Stacks, Tag 0AWA] makes `G = π_*𝒪_Y` coherent.** On a locally
Noetherian Nagata scheme the normalization of `X` in `Spec κ(x)` is finite over `X`, so the
direct image of its structure sheaf is coherent by [Stacks, Tag 01Y6]. -/
theorem isCoherent_residueFieldNormalizationPushforward {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) (hX : IsNagataScheme X) :
    (residueFieldNormalizationPushforward X x).IsCoherent := by
  have : IsFinite (X.fromSpecResidueField x).fromNormalization :=
    isFinite_fromNormalization_fromSpecResidueField x hX
  have : IsLocallyNoetherian (X.fromSpecResidueField x).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (X.fromSpecResidueField x).fromNormalization
  exact _root_.Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
    _ _

/-! ### Assumption (3) -/

/-- **Assumption (3) of [Stacks, Tag 0AWA] at a single point `x` of the open subscheme `V`.**
Every point `z` of the reduced closure of `{x}` in `X` which lies outside `V` — that is, every
`z ∈ Z ∩ closure{x}` — has `dim(𝒪_{closure{x}, z}) ≥ 2`.

This is a condition at `x`, not a bound on the codimension of `Z` in `X`; [Stacks, Tag 0AWA]
asks for it only at the associated points of the given coherent module. -/
abbrev TwoLePointClosureDim {X : Scheme.{u}} (V : X.Opens) (x : V.toScheme) : Prop :=
  ∀ w : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({V.ι.base x} : Set X))).subscheme,
    (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({V.ι.base x} : Set X))).subschemeι.base w ∉ (V : Set X) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({V.ι.base x} : Set X))).subscheme.presheaf.stalk w)

/-! ### The lemma -/

open _root_.Stacks.AlgebraicGeometry.CoherenceFromPointClosures in
/-- **[Stacks, Tag 0AWA].** Let `X` be a locally Noetherian scheme, let `j : U ⟶ X` be the
inclusion of an open subscheme with complement `Z`, and let `F` be a coherent `𝒪_U`-module.
Assume (1) `X` is Nagata, (2) `X` is universally catenary, and
(3) `dim(𝒪_{closure{x}, z}) ≥ 2` for `x ∈ Ass(F)` and `z ∈ Z ∩ closure{x}`. Then `j_*F` is
coherent.

The proof runs the source's argument on the tag's own three assumptions. Assumption (1) makes
the normalization `π : Y ⟶ X` of `X` in `Spec κ(x)` finite, hence `G = π_*𝒪_Y` coherent;
`Stacks.LocalCohomology.exists_mono_pullback_residueFieldNormalizationPushforward` supplies the
comparison monomorphism `i_{x,*}𝒪_{W_x} ⟶ G|_U`; assumptions (2) and (3) give `depth(G_z) ≥ 2`
on `Z` through
`AlgebraicGeometry.hasDepthTwoOutside_pushforwardUnitModule_fromSpecResidueField`; the depth-two
theorem `AlgebraicGeometry.isCoherent_pushforward_of_mono_of_depth_ge_two` then makes
`j_*i_{x,*}𝒪_{W_x}` coherent at each associated point, which is the hypothesis of the
implication (1) ⇒ (2) of [Stacks, Tag 0BJZ]. -/
@[stacks 0AWA, ega "IV 5.11.1" "c) ⇒ a), special case"]
theorem isCoherent_pushforward_of_isNagataScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V : X.Opens) (F : V.toScheme.Modules) [F.IsCoherent]
    (hNagata : IsNagataScheme X)
    (hCat : X.IsUniversallyCatenary)
    (hdim : ∀ x : V.toScheme, x ∈ Stacks.Divisors.associatedPoints F →
      TwoLePointClosureDim V x) :
    ((Scheme.Modules.pushforward V.ι).obj F).IsCoherent := by
  refine isCoherent_pushforward_of_forall_isAssociatedPoint' V.ι F fun x hx => ?_
  obtain ⟨φ, hφ⟩ :=
    exists_mono_pullback_residueFieldNormalizationPushforward V x
  have : (residueFieldNormalizationPushforward X (V.ι.base x)).IsCoherent :=
    isCoherent_residueFieldNormalizationPushforward (V.ι.base x) hNagata
  have : (pointClosureStructureSheaf x).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_pointClosureStructureSheaf x
  have := hφ
  exact AlgebraicGeometry.isCoherent_pushforward_of_mono_of_depth_ge_two X V _
    (AlgebraicGeometry.hasDepthTwoOutside_pushforwardUnitModule_fromSpecResidueField hCat V
      (V.ι.base x) (isFinite_fromNormalization_fromSpecResidueField (V.ι.base x) hNagata)
      (hdim x hx)) _ φ

end Stacks.LocalCohomology

end
