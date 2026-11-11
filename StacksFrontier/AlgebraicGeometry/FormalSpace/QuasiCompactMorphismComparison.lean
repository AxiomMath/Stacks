module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismDecomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaSupplement

/-!
# Quasi-compactness of Stacks 0AJC against the bootstrap notion of Stacks 03XZ

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S` which is representable by algebraic spaces. There are two
notions of quasi-compactness available for `f`: the fibre product condition of
**Stacks 0AJC** — every fibre product of `f` with an affine scheme over `S` in the site is a
quasi-compact formal algebraic space — and the bootstrap condition of Bootstrap,
Definition 03XZ, that every base change of `f` to a scheme over `S` in the site be a
quasi-compact morphism of algebraic spaces. **Stacks 0AM2** is their agreement, and
**Stacks 0AJJ** is the same agreement for finite type: a morphism is of finite type in the
sense of Definition 0AM4, part (2), exactly when it is of finite type in the bootstrap sense.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_iff_isQuasiCompactSpaceULift'`: for a
  morphism representable by algebraic spaces, a fibre product of it with a scheme-valued point
  of its target is a quasi-compact formal algebraic space exactly when the fibre product of the
  underlying presheaves is a quasi-compact algebraic space.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_hasPropertyULift'`: **Stacks 0AM2**,
  with no hypothesis beyond representability by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`: **Stacks 0AJJ**.

## What is assumed

Nothing: both results are unconditional. Each rests on two inputs, and both are proved. The
agreement of the two notions of a quasi-compact *space* on an algebraic space is
`AlgebraicGeometry.FormalSpace.quasiCompactSpaceAgreesOnAlgebraicSpaces` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria`. The implication (3) ⇒ (2)
of **Stacks 0AJB** for the morphism at hand — that the fibre product condition of Stacks 0AJC
over the affine schemes of the site implies the same condition over the quasi-compact ones — is
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismDecomposition`.

## Implementation notes

The proof of Stacks 0AM2 uses, as a local step, that a morphism of presheaves is quasi-compact
in the sense of Stacks 03HE as soon as its fibre product with every scheme-valued point of its
target whose underlying scheme is quasi-compact is a quasi-compact algebraic space.

Both results live here rather than beside the notions they compare — Definition 0AJC in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism` and Definition 0AM4, part (2),
in `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeQuasiCompact` — because the agreement
they consume rests on the equivalence of the three conditions of Stacks 0AJ9, which is proved
further down the import order, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria`.

Neither statement uses the witnesses that the source and the target are formal algebraic
spaces, so both are for an arbitrary morphism of fppf sheaves; each condition of Stacks 0AJJ
carries its own representability witness, so representability is a hypothesis of Stacks 0AM2
only.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AJJ](https://stacks.math.columbia.edu/tag/0AJJ)
* [Stacks Project, Tag 0AM2](https://stacks.math.columbia.edu/tag/0AM2)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism of fppf sheaves on the big fppf site of `S` which is representable by
algebraic spaces, a fibre product of it with a scheme-valued point of its target is a
quasi-compact formal algebraic space over `S` exactly when the fibre product of the underlying
presheaves is a quasi-compact algebraic space over `S`: the fibre product is an algebraic
space by representability, and the two notions agree there by
`AlgebraicGeometry.FormalSpace.quasiCompactSpaceAgreesOnAlgebraicSpaces`. -/
theorem isQuasiCompactSpace_iff_isQuasiCompactSpaceULift' {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    {T : BigFppfOver B S hS} {g : yonedaSheaf B S hS T ⟶ Y} {W : FppfSheaf B S hS}
    {p : W ⟶ yonedaSheaf B S hS T} {q : W ⟶ X} (sq : IsPullback p q g f) :
    IsQuasiCompactSpace B S hS W ↔
      Space.IsQuasiCompactSpaceULift.{u + 1} B S hS (pullback g.hom f.hom) := by
  have hsq : IsPullback p.hom q.hom g.hom f.hom :=
    sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  refine (quasiCompactSpaceAgreesOnAlgebraicSpaces B S hS W
    (Space.isAlgebraicSpaceULift_of_iso B S hS hsq.isoPullback.symm
      (hf T g.hom))).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Space.isQuasiCompactSpaceULift_of_iso B S hS hsq.isoPullback h
  · exact Space.isQuasiCompactSpaceULift_of_iso B S hS hsq.isoPullback.symm h

/-- **Stacks 0AM2.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` which
is representable by algebraic spaces. Then `f` is quasi-compact in the sense of Stacks 0AJC —
every fibre product of it with an affine scheme over `S` in the site is a quasi-compact formal
algebraic space — exactly when it is quasi-compact in the sense of Bootstrap, Definition
03XZ: every fibre product of it with a scheme over `S` in the site is quasi-compact over that
scheme as a morphism of algebraic spaces.

Both directions pass through the agreement of the two notions of quasi-compactness of a space
on an algebraic space, which is
`AlgebraicGeometry.FormalSpace.quasiCompactSpaceAgreesOnAlgebraicSpaces`. For the remaining
direction the bootstrap condition must be tested against the quasi-compact, not only the
affine, schemes over `S` in the site, which is the implication (3) ⇒ (2) of Stacks 0AJB,
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges`. The witnesses
that the source and the target are formal algebraic spaces are not used, so the statement is
for an arbitrary morphism of fppf sheaves. -/
@[stacks 0AM2 "both directions, for an arbitrary morphism of fppf sheaves representable by \
algebraic spaces"]
theorem isQuasiCompact_iff_hasPropertyULift' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsQuasiCompact B S hS f ↔
      Space.HasPropertyULift.{u + 1} B S hS
        (Space.quasiCompactPropertyULift.{u + 1} B S hS) f.hom hf := by
  have qcOfCompact : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (p : F ⟶ G),
      (∀ (V : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj V) →
        ∀ η : (uliftYoneda.{u + 1}).obj V ⟶ G,
          Space.IsQuasiCompactSpaceULift.{u + 1} B S hS (pullback η p)) →
      Space.IsQuasiCompactULift.{u + 1} B S hS p := by
    rintro F G p h Z _ ⟨V, c, hVc, hcSurj, hcEtale⟩ g
    have hcE := (Space.isEtaleULift_iff_relative_etale B S hS c).mp hcEtale
    let k : pullback (c ≫ g) p ⟶ pullback g p :=
      pullback.lift (pullback.fst (c ≫ g) p ≫ c) (pullback.snd (c ≫ g) p)
        (by rw [Category.assoc]; exact pullback.condition)
    have hbig : IsPullback (pullback.fst (c ≫ g) p) (k ≫ pullback.snd g p) (c ≫ g) p := by
      simpa only [k, pullback.lift_snd] using IsPullback.of_hasPullback (c ≫ g) p
    have hsquare : IsPullback k (pullback.fst (c ≫ g) p) (pullback.fst g p) c :=
      (hbig.of_bot (by dsimp only [k]; rw [pullback.lift_fst])
        (IsPullback.of_hasPullback g p)).flip
    obtain ⟨W, γ, hWc, hγSurj, hγEtale⟩ := h V hVc (c ≫ g)
    exact ⟨W, γ ≫ k, hWc,
      Space.relative_comp B S hS hγSurj (Space.relative_of_isPullback B S hS hsquare hcSurj),
      (Space.isEtaleULift_iff_relative_etale B S hS (γ ≫ k)).mpr
        (Space.relative_comp B S hS
          ((Space.isEtaleULift_iff_relative_etale B S hS γ).mp hγEtale)
          (Space.relative_of_isPullback B S hS hsquare hcE))⟩
  constructor
  · intro hqc U ξ
    change Space.IsQuasiCompactULift.{u + 1} B S hS (pullback.fst ξ f.hom)
    refine qcOfCompact _ (fun V hV η => ?_)
    refine Space.isQuasiCompactSpaceULift_of_iso B S hS
      (pullbackRightPullbackFstIso ξ f.hom η).symm ?_
    exact (isQuasiCompactSpace_iff_isQuasiCompactSpaceULift' B S hS hf
      (IsPullback.of_hasPullback (⟨η ≫ ξ⟩ : yonedaSheaf B S hS V ⟶ Y) f)).mp
      (IsQuasiCompact.isQuasiCompactOnSchemeBaseChanges B S hS hqc V hV _ _ _ _
        (IsPullback.of_hasPullback _ f))
  · intro h T hT g W p q sq
    refine (isQuasiCompactSpace_iff_isQuasiCompactSpaceULift' B S hS hf sq).mpr ?_
    refine Space.isQuasiCompactSpaceULift_of_iso B S hS
      (IsPullback.of_id_snd (f := pullback.fst g.hom f.hom)).isoPullback.symm ?_
    exact h T g.hom _ (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)
      (Space.isQuasiCompactSpaceULift_uliftYoneda.{u + 1} B S hS T
        (@Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj T) hT)) (𝟙 _)

/-! ### Stacks 0AJJ -/

/-- **Stacks 0AJJ.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S`. Then
`f` is of finite type — locally of finite type and quasi-compact in the sense of Definition
0AJC — exactly when it is representable by algebraic spaces and of finite type in the
Bootstrap sense of Stacks 03XZ.

Both conditions contain being locally of finite type: the Bootstrap condition for being of
finite type is the conjunction of the Bootstrap condition for being locally of finite type
with the Bootstrap condition for being quasi-compact, which is the content of Stacks 03XF,
part (3), in the universe-lifted form of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType`. What is left is the comparison
of Definition 0AJC with the Bootstrap condition for being quasi-compact, which is Stacks 0AM2
above. The witnesses that the source and the
target are formal algebraic spaces are not used, so the statement is for an arbitrary
morphism of fppf sheaves; each condition carries its own representability witness, so
representability is not a hypothesis. -/
@[stacks 0AJJ "the equivalence of conditions (1) and (2), for an arbitrary morphism of fppf \
sheaves, representability by algebraic spaces being part of both conditions rather than a \
hypothesis"]
theorem isFiniteType_iff_isBootstrapFiniteType {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsFiniteType' B S hS f ↔ IsBootstrapFiniteType B S hS f := by
  constructor
  · rintro ⟨⟨hrep, hlft⟩, hqc⟩
    have hqc' := (isQuasiCompact_iff_hasPropertyULift' B S hS f hrep).mp hqc
    exact ⟨hrep, fun U ξ => ⟨hlft U ξ, hqc' U ξ⟩⟩
  · rintro ⟨hrep, hprop⟩
    exact ⟨⟨hrep, fun U ξ => (hprop U ξ).1⟩,
      (isQuasiCompact_iff_hasPropertyULift' B S hS f hrep).mpr fun U ξ => (hprop U ξ).2⟩
end AlgebraicGeometry.FormalSpace

end
