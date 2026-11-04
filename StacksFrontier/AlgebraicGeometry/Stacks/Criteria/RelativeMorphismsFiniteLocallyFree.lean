module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsEtale

/-!
# Algebraicity of the relative morphism functor for a finite locally free source (Stacks 05Y7)

Let `S` be a scheme contained in a big fppf site, let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms
of algebraic spaces over `S` — the source writes the base `Q` as `B`, a name that here belongs to
the site — and let `Mor_Q(Z, X)` be the relative morphism functor of Stacks 05Y2. Stacks 05Y7
asserts that `Mor_Q(Z, X)` is an algebraic space over `S` when `z` is finite locally free.

The source's proof has three steps: a reduction to an affine base along an étale covering of `Q`,
a reduction to a target that is a disjoint union of affines along an étale covering of `X`, and
the main case, where the functor is built out of Stacks 05Y6 and glued by the open covering of
Stacks 02WR. This file proves the **second** step and assembles it into the statement of the
proposition.

The reduction on the target is exactly where the finite locally free hypothesis on `z` enters: it
is a hypothesis of Stacks 05Y5, which makes `Mor_Q(Z, X') ⟶ Mor_Q(Z, X)` representable by
algebraic spaces, étale and surjective for `X' ⟶ X` étale and surjective. Combined with Stacks
03Y3 that transports algebraicity down such a morphism, and with the sheaf property of Stacks
05Y3, it reduces the proposition to the case of a target that is an object of the site. Since an
algebraic space has a surjective étale chart by an object of the site, that single reduction
replaces the source's two-step reduction to a disjoint union of affines.

## Main results

* `AlgebraicGeometry.Space.hasProperty_surjectiveMorphismProperty_of_isSurjective`: a morphism of
  presheaves representable by algebraic spaces and surjective on the point sets of Stacks 03BU is
  surjective after every representable base change.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget`: algebraicity of
  `Mor_Q(Z, X)` descends along an étale surjective morphism `X' ⟶ X` of targets, when `z` is
  finite locally free.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree`: **Stacks 05Y7**,
  with the representable-target case carried.

## Implementation notes

Stacks 03Y3 is available here in the unconditional form
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale`,
and **not** through Stacks 04S6, which the source uses at this point. That matters: the library's
Stacks 04S6 is conditional on `IsBootstrapAlgebraicSpaceAlongFlatSurjection`, the whole Bootstrap
chapter, which is not proved here, whereas 03Y3 needs only effective fppf descent at the
monomorphisms locally of finite type and is a theorem. The source may use the flat bootstrap
because its reductions are stated for flat coverings; the coverings used here are étale, so the
weaker and available input suffices.

Stacks 03Y3 consumes surjectivity of the comparison morphism in the base-changed form
`AlgebraicGeometry.Space.HasProperty`, while Stacks 05Y5 supplies it as surjectivity on the point
sets of Stacks 03BU. The passage between the two is
`AlgebraicGeometry.Space.hasProperty_surjectiveMorphismProperty_of_isSurjective` below, proved
from Stacks 03H4 in its presheaf form
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf`: no algebraicity of the target is
available at that stage of the argument, since being an algebraic space is what is being proved,
and the presheaf form of 03H4 needs none.

The hypothesis `h05XR` is the one input that the form of Stacks 05Y5 reached from this file still
names — the main assertion of Stacks 05XR for a non-separated `w`. It is **not** a missing
result: it holds outright by `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`, exactly as
its companion clause `AlgebraicGeometry.Space.IsFibreSectionsSurjective` holds outright by
`AlgebraicGeometry.Space.isFibreSectionsSurjective`, and the surjectivity conclusion of
Stacks 05Y5 is used here in its unconditional form
`AlgebraicGeometry.Space.isSurjective_relativeHomPostcompose_of_isFiniteLocallyFree`. It is
quantified over the chart of `X` in the final theorem because the chart is produced inside the
proof. The conclusion of this file with `h05XR` discharged — so that the only hypothesis besides
the source's is `hrepresentable` — is
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_representable`,
stated in `StacksFrontier/AlgebraicGeometry/Spaces/FibreSectionsAlgebraicEtale.lean`, which is
downstream of this file because the proof of Stacks 05XR for the fibre data needs the finiteness
input from Stacks 03ZU.

## References

* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 05Y5](https://stacks.math.columbia.edu/tag/05Y5)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves on the big fppf site of `S` which is representable by algebraic
spaces and surjective on the point sets of Stacks 03BU is surjective after every representable
base change, in the sense of `AlgebraicGeometry.Space.HasProperty`.

Neither the source nor the target is assumed to be an algebraic space: the lift of a point of
`yoneda.obj U` to the fibre product is supplied by Stacks 03H4 in its presheaf form
`AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf`, whose cartesian square is one of
presheaves. -/
theorem hasProperty_surjectiveMorphismProperty_of_isSurjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a) (hsurj : IsSurjective B S hS a) :
    HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha := by
  intro U ξ pt
  obtain ⟨w, hw⟩ := hsurj (pointsMap B S hS (yoneda.obj U) ξ pt)
  obtain ⟨v, hv, -⟩ :=
    exists_point_of_isPullback_presheaf B S hS (IsPullback.of_hasPullback ξ a) pt w hw.symm
  exact ⟨v, hv⟩

variable {B S hS}

/-- **The reduction on the target in the proof of Stacks 05Y7.** Let `z : Z ⟶ Q` be finite
locally free and let `g : X' ⟶ X` be an étale surjective morphism of algebraic spaces over `Q`.
If `Mor_Q(Z, X')` is an algebraic space over `S` and `Mor_Q(Z, X)` is a sheaf, then
`Mor_Q(Z, X)` is an algebraic space over `S`.

The comparison morphism `Mor_Q(Z, X') ⟶ Mor_Q(Z, X)` is representable by algebraic spaces, étale
and surjective by the three conclusions of Stacks 05Y5 — this is where the finite locally free
hypothesis on `z` is used — and Stacks 03Y3 transports algebraicity down a morphism of that
kind. -/
theorem isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Q} {x : X ⟶ Q} {z : Z ⟶ Q}
    (HX' : RelativeHomConstruction B S hS Z.obj X'.obj Q.obj z.hom x'.hom)
    (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom x.hom)
    (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom)
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z)
    (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z)
    (hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) HX.functor)
    (hX' : IsAlgebraicSpace B S hS HX'.functor) :
    IsAlgebraicSpace B S hS HX.functor := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      (relativeHomPostcompose HX' HX g.hom hg) :=
    isRepresentableByAlgebraicSpaces_relativeHomPostcompose HX' HX g hg hg_etale hz h05XR
  have hetale := hasProperty_isEtale_relativeHomPostcompose HX' HX g hg hg_etale hz h05XR
  have hsurj : IsSurjective B S hS (relativeHomPostcompose HX' HX g.hom hg) :=
    isSurjective_relativeHomPostcompose_of_isFiniteLocallyFree B S hS HX' HX g hg hg_etale
      hg_surjective hz
  exact isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale hsheaf hX'
    (relativeHomPostcompose HX' HX g.hom hg) hrep
    (hasProperty_surjectiveMorphismProperty_of_isSurjective _ _ _ _ hrep hsurj) hetale

variable (B S hS)

/-- **Stacks 05Y7.** Let `S` be a scheme contained in a big fppf site, and let `z : Z ⟶ Q` and
`x : X ⟶ Q` be morphisms of algebraic spaces over `S`. If `z` is finite locally free then the
relative morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is an algebraic space over `S`.

The proof is the source's reduction on the target, in the form
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget`, applied to a
surjective étale chart `yoneda.obj U ⟶ X` of the algebraic space `X`; the sheaf property of
`Mor_Q(Z, X)` is Stacks 05Y3. What remains is the case of a target that is an object of the
site, which is carried as `hrepresentable`.

This is the general form, which takes that input as a hypothesis, and it carries no Stacks tag.
Stacks 05Y7 is registered on
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_source`,
which proves the same conclusion at the hypotheses of the source, with nothing carried. -/
theorem isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hz : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)))
    (h05XR : ∀ (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ X),
      IsFibreSectionsAlgebraicEtale B S hS
        (ObjectProperty.homMk c :
          (schemeSpace U : AlgebraicSpaces B S hS) ⟶
            (⟨X, hX⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.homMk z :
          (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)))
    (hrepresentable : ∀ (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ Q),
      IsAlgebraicSpace B S hS
        (relativeHom B S hS Z (yoneda.obj U) Q z u hZ (isAlgebraicSpace_yoneda B S hS U) hQ)) :
    IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ) := by
  obtain ⟨U, c, hcS, hcE⟩ := hX.exists_atlas
  exact isAlgebraicSpace_relativeHom_of_etaleSurjectiveTarget
    (X' := (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS))
    (Z := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS))
    (Q := (⟨Q, hQ⟩ : AlgebraicSpaces B S hS))
    (x' := ObjectProperty.homMk (c ≫ x)) (x := ObjectProperty.homMk x)
    (z := ObjectProperty.homMk z)
    (relativeHomData B S hS Z (yoneda.obj U) Q z (c ≫ x) hZ
      (isAlgebraicSpace_yoneda B S hS U) hQ)
    (relativeHomData B S hS Z X Q z x hZ hX hQ)
    (ObjectProperty.homMk c) rfl
    (isEtale_of_presheaf_etale B S hS hcE) (isSurjective_of_presheafSurjective B S hS c hcS)
    hz (h05XR U c)
    (isSheaf_relativeHom B S hS Z X Q z x hZ hX hQ)
    (hrepresentable U (c ≫ x))

end AlgebraicGeometry.Space

end
