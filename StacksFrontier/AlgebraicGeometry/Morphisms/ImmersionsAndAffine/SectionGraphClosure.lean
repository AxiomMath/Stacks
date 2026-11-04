module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage
import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The scheme-theoretic closure of the graph of a section over an open of the base

Let `f : X ⟶ S` and `g : P ⟶ S` be morphisms, let `U` be an open subscheme of `X`, and let
`j : U ⟶ P` be a morphism over `S`. The pair `(U.ι, j)` induces a morphism `U ⟶ X ×_S P`, which
is a section of the first projection over `U`. When `g` is separated and `U` is retrocompact in
`X`, the scheme-theoretic image of that morphism — a closed subscheme of `X ×_S P` — maps
isomorphically onto `U` under the first projection, and in particular has a point above every
point of `U`.

This is the geometric starting point of the Noetherian case of [Stacks, Tag 0CSJ] (derived
Chow's lemma), where `S = Spec A`, `P = ℙⁿ_A`, `U` is an affine open neighbourhood of a point of
`X`, and `j` is a closed immersion of `U` into a standard affine chart `𝔸ⁿ_A ⊆ ℙⁿ_A`. Proved
below are clause (2) of that lemma, both halves of it, and the closedness of the graph itself:
the graph is a closed immersion into the part of `X ×_S P` lying over `U` as soon as `g` is
separated, and into the whole of `X ×_S P` once `j` is a closed immersion and `f` is separated.

Nothing here is tagged. Tag 0CSJ asserts the existence of a *derived* Chow datum, of which only
one of six clauses is proved below, and tag 0CNG — which supplies the isomorphism — already
carries its tag at its own statement.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_iff_isIso_pullback_snd`: a morphism is an isomorphism
  over an open subset of its target exactly when the second projection from the corresponding
  pullback is an isomorphism. This is the translation between the two spellings of "isomorphism
  over an open".
* `AlgebraicGeometry.isIso_morphismRestrict_imageι_comp_of_section`: [Stacks, Tag 0CNG] in the
  restriction spelling — the scheme-theoretic image of a section, defined over an open, of a
  separated morphism maps isomorphically onto the domain of the section.
* `AlgebraicGeometry.isIso_morphismRestrict_imageι_comp_fst_of_isSeparated`: the same for the
  graph of a morphism over a base, which is the shape [Stacks, Tag 0CSJ] clause (2) asks for.
* `AlgebraicGeometry.exists_base_eq_of_isIso_morphismRestrict`: a morphism that is an isomorphism
  over an open subset of its target hits every point of that open subset. Composed with the
  previous result this is the second half of clause (2): the closure of the graph has a point
  above the chosen point of `X`.
* `AlgebraicGeometry.isClosedImmersion_morphismRestrict_pullbackLift_of_isSeparated`: the graph
  of a morphism over a base separated along `g` is a closed immersion into the part of `X ×_S P`
  lying over `U`; equivalently the graph is closed in `U ×_S P`.
* `AlgebraicGeometry.isClosedImmersion_pullbackLift_of_isClosedImmersion`: if moreover `j` is a
  closed immersion and `f` is separated, the graph is a closed immersion into the whole of
  `X ×_S P`.

## Implementation notes

`AlgebraicGeometry.isIso_morphismRestrict_iff_isIso_pullback_snd` is
`AlgebraicGeometry.prop_morphismRestrict_iff_pullback_snd` at the property of being an
isomorphism. It is given a name because [Stacks, Tag 0CNG] concludes in the `pullback.snd`
spelling while its consumers ask in the `∣_` spelling, so the specialisation would else be
repeated at every use.

The graph itself is `CategoryTheory.Limits.pullback.lift U.ι j h` and is deliberately **not**
given a name here: `Stacks.Chow.sectionGraph` is already that morphism for `P = ℙ¹_S` with `j`
determined by a section of the structure sheaf, and a second, more general definition of the
same construction would be a duplicate. The statements below therefore quantify over `j` and
mention `pullback.lift` directly, which also makes them applicable to
`Stacks.Chow.sectionGraph` by unfolding it.

Retrocompactness of `U` is carried as a hypothesis, exactly as [Stacks, Tag 0CNG] carries it;
it holds for a quasi-compact open of a quasi-separated scheme, which is the case arising in
[Stacks, Tag 0CSJ].

## References

* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
* [Stacks Project, Tag 0CSJ](https://stacks.math.columbia.edu/tag/0CSJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism is an isomorphism over an open subset of its target exactly when the second
projection from the pullback along that open subset is an isomorphism. This is
`AlgebraicGeometry.prop_morphismRestrict_iff_pullback_snd` at the property of being an
isomorphism. -/
public theorem isIso_morphismRestrict_iff_isIso_pullback_snd {X Y : Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens) : IsIso (g ∣_ U) ↔ IsIso (pullback.snd g U.ι) :=
  prop_morphismRestrict_iff_pullback_snd (MorphismProperty.isomorphisms Scheme.{u}) g U

/-- **Stacks 0CNG, in the restriction spelling.** The scheme-theoretic image of a section of a
separated morphism, defined over a retrocompact open subset of the target, maps isomorphically
onto that open subset. -/
@[ega "IV 20.4.1" "For Y separated over S"]
public theorem isIso_morphismRestrict_imageι_comp_of_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] (V : Y.Opens) (hV : IsRetrocompact (V : Set Y))
    (s : V.toScheme ⟶ X) (hs : s ≫ f = V.ι) :
    IsIso ((s.imageι ≫ f) ∣_ V) :=
  (isIso_morphismRestrict_iff_isIso_pullback_snd (s.imageι ≫ f) V).2
    (isIso_pullback_snd_imageι_comp_of_section f V hV s hs)

/-- **Clause (2) of [Stacks, Tag 0CSJ], first half.** Let `g : P ⟶ S` be separated, let `U` be a
retrocompact open subscheme of `X`, and let `j : U ⟶ P` be a morphism over `S`. The
scheme-theoretic closure of the graph `(U.ι, j) : U ⟶ X ×_S P` maps isomorphically onto `U`
under the first projection.

The closure is the scheme-theoretic image of `pullback.lift U.ι j h`, and its inclusion into
`X ×_S P` is a closed immersion by Mathlib's instance for
`AlgebraicGeometry.Scheme.Hom.imageι`. -/
@[ega "IV 20.4.1" "For Y separated over S"]
public theorem isIso_morphismRestrict_imageι_comp_fst_of_isSeparated {X S P : Scheme.{u}}
    (f : X ⟶ S) (g : P ⟶ S) [IsSeparated g] (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    (j : U.toScheme ⟶ P) (h : U.ι ≫ f = j ≫ g) :
    IsIso (((pullback.lift U.ι j h).imageι ≫ pullback.fst f g) ∣_ U) :=
  isIso_morphismRestrict_imageι_comp_of_section (pullback.fst f g) U hU
    (pullback.lift U.ι j h) (pullback.lift_fst _ _ _)

/-- The graph `(U.ι, j) : U ⟶ X ×_S P` of a morphism `j : U ⟶ P` over `S`, read as a morphism
into the part of `X ×_S P` lying over `U`, is a closed immersion when `g : P ⟶ S` is separated:
it is a section of the separated morphism `pullback.fst f g ∣_ U`. -/
@[sga "3 VIB 5.6.3" "(i) ⇒ (ii)"]
public theorem isClosedImmersion_morphismRestrict_pullbackLift_of_isSeparated
    {X S P : Scheme.{u}} (f : X ⟶ S) (g : P ⟶ S) [IsSeparated g] (U : X.Opens)
    (j : U.toScheme ⟶ P) (h : U.ι ≫ f = j ≫ g) :
    IsClosedImmersion (pullback.lift U.ι j h ∣_ pullback.fst f g ⁻¹ᵁ U) := by
  have e : (pullback.lift U.ι j h ∣_ pullback.fst f g ⁻¹ᵁ U) ≫ (pullback.fst f g ∣_ U) =
      (pullback.lift U.ι j h ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U)).ι := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      pullback.lift_fst]
  have hdom : pullback.lift U.ι j h ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst]
    exact U.ι_preimage_self
  have : IsIso (pullback.lift U.ι j h ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U)).ι := by
    rw [hdom]
    change IsIso (Scheme.topIso U.toScheme).hom
    infer_instance
  have : IsClosedImmersion ((pullback.lift U.ι j h ∣_ pullback.fst f g ⁻¹ᵁ U) ≫
      (pullback.fst f g ∣_ U)) := by
    rw [e]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst f g ∣_ U)

/-- If `j : U ⟶ P` is itself a closed immersion and `f : X ⟶ S` is separated, then the graph
`(U.ι, j) : U ⟶ X ×_S P` is a closed immersion into the whole of `X ×_S P`, not merely into the
part lying over `U`: composing it with the separated projection to `P` recovers `j`. -/
public theorem isClosedImmersion_pullbackLift_of_isClosedImmersion {X S P : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] (g : P ⟶ S) (U : X.Opens) (j : U.toScheme ⟶ P)
    [IsClosedImmersion j] (h : U.ι ≫ f = j ≫ g) :
    IsClosedImmersion (pullback.lift U.ι j h) := by
  have : IsClosedImmersion (pullback.lift U.ι j h ≫ pullback.snd f g) := by
    rw [pullback.lift_snd]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f g)

/-- A morphism that is an isomorphism over an open subset of its target hits every point of that
open subset. -/
public theorem exists_base_eq_of_isIso_morphismRestrict {Y Z : Scheme.{u}} (p : Z ⟶ Y)
    (V : Y.Opens) [IsIso (p ∣_ V)] {y : Y} (hy : y ∈ V) :
    ∃ z : Z, p.base z = y := by
  obtain ⟨w, hw⟩ := (p ∣_ V).surjective (⟨y, hy⟩ : V.toScheme)
  refine ⟨w.1, ?_⟩
  have h : ((p ∣_ V) w).1 = p.base w.1 := morphismRestrict_base_coe p V w
  rw [hw] at h
  exact h.symm

end AlgebraicGeometry

end
