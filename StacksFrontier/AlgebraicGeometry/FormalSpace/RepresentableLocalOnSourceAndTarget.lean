module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas

/-!
# Representability by algebraic spaces is local on the source and the target

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0AN4** compares the following ways of asking that
`f` be representable by algebraic spaces:

1. `f` is representable by algebraic spaces;
2. there is one commutative square with `U`, `V` formal algebraic spaces, vertical arrows
   representable by algebraic spaces, `U ⟶ X` surjective étale, and `U ⟶ V` representable by
   algebraic spaces;
3. every commutative square with `U`, `V` formal algebraic spaces and vertical arrows
   representable by algebraic spaces has `U ⟶ V` representable by algebraic spaces;
4. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uⱼᵢ ⟶ Vⱼ` representable by algebraic
   spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRepresentableOnSomeSquare`,
  `AlgebraicGeometry.FormalSpace.IsRepresentableOnEverySquare` and
  `AlgebraicGeometry.FormalSpace.IsRepresentableAfterTargetCover`: conditions (2), (3) and (4)
  of **Stacks 0AN4**.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_id`: an identity morphism of fppf sheaves
  is representable by algebraic spaces and étale.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace`: an
  affine formal algebraic space is a formal algebraic space, its own identity being an atlas.
* `AlgebraicGeometry.FormalSpace.isRepresentableOnSomeSquare_of_isRepresentable`: **Stacks
  0AN4**, condition (1) implies condition (2).
* `AlgebraicGeometry.FormalSpace.isRepresentableOnEverySquare_of_isRepresentable`: **Stacks
  0AN4**, condition (1) implies condition (3).
* `AlgebraicGeometry.FormalSpace.isRepresentable_of_isRepresentableOnEverySquare`: **Stacks
  0AN4**, condition (3) implies condition (1), so conditions (1) and (3) are equivalent.
* `AlgebraicGeometry.FormalSpace.isRepresentableAfterTargetCover_of_everySquare`: **Stacks
  0AN4**, condition (3) implies condition (4).
* `AlgebraicGeometry.FormalSpace.isRepresentable_of_forall_surjective_etale_cover`:
  **representability by algebraic spaces is local on the target**, in the form consumed by an
  affine open covering of a scheme-valued point of the target.
* `AlgebraicGeometry.FormalSpace.isRepresentable_of_siteSurjectiveEtaleChart`: **Stacks 0AN4**,
  condition (2) implies condition (1), for a source column representable by objects of the
  site.

## Implementation notes

Surjectivity of `U ⟶ X` in condition (2) is surjectivity of the morphism of sheaves, that is
`CategoryTheory.Sheaf.IsLocallySurjective`, which is how Definition 0AIM records surjectivity
of an atlas; étaleness is the representable étaleness of
`AlgebraicGeometry.FormalSpace.IsRepresentableEtale`.

The steps from condition (1) to condition (3) and from condition (3) to condition (4) are
stated here with two inputs of the source as explicit arguments, so that they can be used in
contexts where those inputs are supplied in another form. Both inputs are theorems of this
library. The step from condition (1) to condition (3) uses Stacks 0AQ0, that a morphism of
formal algebraic spaces whose composite with a further morphism is representable by algebraic
spaces is itself representable by algebraic spaces; it is the argument `h0AQ0`, proved as
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`.
The step from condition (3) to condition (4) needs the fibre products `Vⱼ ×_Y X` to be formal
algebraic spaces, which is Stacks 0AJ3; it is the argument `h0AJ3`, proved as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`.
The full equivalence of the conditions, with both inputs discharged, is
`AlgebraicGeometry.FormalSpace.isRepresentable_tfae`. Everything else — that the chart
`Uⱼᵢ` maps to `X` by a morphism representable by algebraic spaces, and that the square it forms
with `f` and `Vⱼ ⟶ Y` commutes — is proved here, from Stacks 0APY and the base change
stability of representable étale morphisms.

The implication from condition (3) to condition (1) needs nothing: the square formed by the
identities of `X` and of `Y` is a square as in condition (3) whose upper horizontal map is `f`.

The implication from condition (2) to condition (1) is the one the source closes with Stacks
0AMP, which this library proves for presheaves of the base universe as
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_comp_of_flat_surjective_unconditional`.
What is proved here is the étale case with the source column representable by objects of the site rather
than by algebraic spaces, which runs on Stacks 0BGR, a theorem of this library; the step into
the value universe of a formal algebraic space is
`AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale`. Locality on the
target is the same statement read at one scheme-valued point of the target at a time, the
covering morphism being a morphism of the site, where representability by objects of the site
is automatic.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AMP](https://stacks.math.columbia.edu/tag/0AMP)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0APY](https://stacks.math.columbia.edu/tag/0APY)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An identity morphism of fppf sheaves is representable by algebraic spaces and étale: its
base change along a scheme-valued point is that point, and the projection of the base change
is an isomorphism. -/
theorem isRepresentableEtale_id (X : FppfSheaf B S hS) : IsRepresentableEtale B S hS (𝟙 X) := by
  have hid : IsIso ((𝟙 X : X ⟶ X).hom) := inferInstanceAs (IsIso (𝟙 X.obj))
  have hiso : ∀ (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ X.obj),
      IsIso (pullback.fst ξ ((𝟙 X : X ⟶ X).hom)) :=
    fun T ξ ↦ (IsPullback.of_hasPullback ξ ((𝟙 X : X ⟶ X).hom)).isIso_fst_of_isIso
  refine ⟨fun T ξ ↦ ?_, fun T ξ ↦ ?_⟩
  · have _ := hiso T ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS
      (asIso (pullback.fst ξ ((𝟙 X : X ⟶ X).hom))).symm
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS T)
  · have _ := hiso T ξ
    exact fun T' φ hφ ↦
      MorphismProperty.RespectsIso.postcomp _ (pullback.fst ξ ((𝟙 X : X ⟶ X).hom)) φ hφ

/-- An affine formal algebraic space over `S` is a formal algebraic space over `S`: the
one-member family consisting of its identity is an atlas. -/
theorem isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : IsFormalAlgebraicSpace B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨hX.1, PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ hX,
    fun _ ↦ isRepresentableEtale_id B S hS X, ?_⟩
  have hsplit : IsSplitEpi (Sigma.desc (fun _ : PUnit.{u + 2} ↦ (𝟙 X : X ⟶ X))) :=
    ⟨⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ X) PUnit.unit, by simp⟩⟩
  have _ := hsplit
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance

/-- **Stacks 0AN4, condition (2).** There is a commutative square whose source column is a
surjective representable étale map from a formal algebraic space, whose target column is
representable by algebraic spaces, and whose upper horizontal map is representable by
algebraic spaces. -/
abbrev IsRepresentableOnSomeSquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (U V : FppfSheaf B S hS) (p : U ⟶ X) (q : V ⟶ Y) (t : U ⟶ V),
    IsFormalAlgebraicSpace B S hS U ∧ IsFormalAlgebraicSpace B S hS V ∧
      IsRepresentableEtale B S hS p ∧ Sheaf.IsLocallySurjective p ∧
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS q.hom ∧
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ∧ p ≫ f = t ≫ q

/-- **Stacks 0AN4, condition (3).** Every commutative square whose vertical maps are
representable by algebraic spaces and whose corners are formal algebraic spaces has its upper
horizontal map representable by algebraic spaces. -/
abbrev IsRepresentableOnEverySquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS) (p : U ⟶ X) (q : V ⟶ Y) (t : U ⟶ V),
    IsFormalAlgebraicSpace B S hS U → IsFormalAlgebraicSpace B S hS V →
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom →
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS q.hom →
    p ≫ f = t ≫ q → Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom

/-- **Stacks 0AN4, condition (4).** There is an affine étale covering of the target and, for
each of its members, an affine étale covering of the fibre product of that member with the
source whose members are representable by algebraic spaces over that member. -/
abbrev IsRepresentableAfterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v ∧
      ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (w : ∀ i, U i ⟶ pullback (v j) f),
        IsAffineEtaleCover B S hS U w ∧
          ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
            (w i ≫ pullback.fst (v j) f).hom

/-- **Stacks 0AN4, condition (1) implies condition (2).** The square formed by the identities
of `X` and of `Y` witnesses condition (2). -/
theorem isRepresentableOnSomeSquare_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsRepresentableOnSomeSquare B S hS f :=
  ⟨X, Y, 𝟙 X, 𝟙 Y, f, hX, hY, isRepresentableEtale_id B S hS X,
    (Sheaf.isLocallySurjective_iff_epi (𝟙 X)).mpr inferInstance,
    (isRepresentableEtale_id B S hS Y).1, hf, by simp⟩

/-- **Stacks 0AN4, condition (1) implies condition (3).** In a square as in condition (3) the
composite `U ⟶ X ⟶ Y` is representable by algebraic spaces by Stacks 0APY, and it factors
through `V`, so Stacks 0AQ0 applies to `U ⟶ V ⟶ Y`.

The argument `h0AQ0` is Stacks 0AQ0, a theorem of this library
(`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`);
`AlgebraicGeometry.FormalSpace.isRepresentable_tfae` discharges it. -/
theorem isRepresentableOnEverySquare_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (h0AQ0 : ∀ {A A' A'' : FppfSheaf B S hS} (s : A ⟶ A') (r : A' ⟶ A''),
      IsFormalAlgebraicSpace B S hS A → IsFormalAlgebraicSpace B S hS A' →
      IsFormalAlgebraicSpace B S hS A'' →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (s ≫ r).hom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS s.hom)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsRepresentableOnEverySquare B S hS f := by
  intro U V p q t hU hV hp hq hcomm
  have h1 : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS p.hom f.hom hp hf
  rw [hcomm] at h1
  exact h0AQ0 t q hU hV hY h1

/-- **Stacks 0AN4, condition (3) implies condition (1).** The square formed by the identities
of `X` and of `Y` is a square as in condition (3) whose upper horizontal map is `f`. -/
theorem isRepresentable_of_isRepresentableOnEverySquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsRepresentableOnEverySquare B S hS f) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  hf X Y (𝟙 X) (𝟙 Y) f hX hY (isRepresentableEtale_id B S hS X).1
    (isRepresentableEtale_id B S hS Y).1 (by simp)

/-- **Stacks 0AN4, condition (3) implies condition (4).** The atlas of the target and the
atlases of the fibre products of its members with the source witness condition (4): a chart
`Uⱼᵢ` of `Vⱼ ×_Y X` maps to `X` by a morphism representable by algebraic spaces, because the
second projection is a base change of `Vⱼ ⟶ Y`, and the square it forms with `f` and `Vⱼ ⟶ Y`
commutes by the universal property of the fibre product.

The argument `h0AJ3` is the assertion of Stacks 0AJ3 that `Vⱼ ×_Y X` is a formal algebraic
space, a theorem of this library
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`);
`AlgebraicGeometry.FormalSpace.isRepresentable_tfae` discharges it. -/
theorem isRepresentableAfterTargetCover_of_everySquare {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (h0AJ3 : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (hf : IsRepresentableOnEverySquare B S hS f) :
    IsRepresentableAfterTargetCover B S hS f := by
  obtain ⟨-, J, V, v, hVaffine, hVetale, hVsurj⟩ := hY
  refine ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, I, U, w, hUaffine, hUetale, hUsurj⟩ := h0AJ3 (V j) (v j) (hVaffine j) (hVetale j)
  refine ⟨I, U, w, ⟨hUaffine, hUetale, hUsurj⟩, fun i ↦ ?_⟩
  refine hf (U i) (V j) (w i ≫ pullback.snd (v j) f) (v j) (w i ≫ pullback.fst (v j) f)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hUaffine i))
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hVaffine j))
    ((IsRepresentableEtale.comp B S hS (hUetale i)
      (isRepresentableEtale_pullback_snd B S hS (v j) f (hVetale j))).1) (hVetale j).1 ?_
  rw [Category.assoc, Category.assoc, ← pullback.condition]

/-! ### Locality on the target -/

/-- **Representability by algebraic spaces is local on the target.** A morphism of fppf sheaves
on the big fppf site of `S` is representable by algebraic spaces as soon as every scheme-valued
point `ξ : T ⟶ Y` of its target admits a surjective étale covering `T' ⟶ T` by an object of the
site over which the base change of the morphism is an algebraic space.

This is the shape in which an affine open covering of a scheme-valued point of the target is
used: the disjoint union of the members of the covering is one object of the site mapping to
`T` by a surjective étale — indeed Zariski — morphism, and the hypothesis is representability
after base change along it. Nothing is asked of `X` or `Y` beyond the sheaf condition, and the
conclusion is the full representability of `f`. -/
theorem isRepresentable_of_forall_surjective_etale_cover {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Y.obj),
      ∃ (T' : BigFppfOver B S hS) (q : T' ⟶ T),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        Space.IsAlgebraicSpaceULift.{u + 1} B S hS
          (pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom)) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  Space.isRepresentableByAlgebraicSpacesULift_of_forall_surjective_etale_cover B S hS f.hom
    X.property Y.property h

/-- **Stacks 0AN4, condition (2) implies condition (1)**, for a source column which is
representable by objects of the site and not merely by algebraic spaces.

Condition (2) of Stacks 0AN4 asks for a square with `U ⟶ X` surjective étale and `U ⟶ V`,
`V ⟶ Y` representable by algebraic spaces; the composite `U ⟶ X ⟶ Y` is then representable by
algebraic spaces by Stacks 0APY, which is the only use the implication makes of the right-hand
column, so it is that composite which appears here. The source closes the implication with
Stacks 0AMP, whose hypothesis on `U ⟶ X` is that it be representable by algebraic spaces,
surjective, flat and locally of finite presentation; this library does not have Stacks 0AMP,
which `StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent`
records as equivalent to the bootstrap theorem Stacks 04S6, part (3). Strengthening the
hypothesis on `U ⟶ X` from representability by algebraic spaces to representability by objects
of the site replaces that input by Stacks 0BGR, which this library proves outright. -/
theorem isRepresentable_of_siteSurjectiveEtaleChart {X Y U : FppfSheaf B S hS} (f : X ⟶ Y)
    (p : U ⟶ X)
    (hs : (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) p.hom)
    (he : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) p.hom)
    (hpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (p ≫ f).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  Space.isRepresentableByAlgebraicSpacesULift_of_comp_of_surjective_etale B S hS p.hom f.hom
    X.property Y.property hs he hpf

end AlgebraicGeometry.FormalSpace

end
