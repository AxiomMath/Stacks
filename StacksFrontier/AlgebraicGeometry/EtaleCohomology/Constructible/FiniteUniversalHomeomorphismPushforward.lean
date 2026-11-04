module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along a finite universal homeomorphism preserves constructible sheaves

**Stacks 095R, the universal homeomorphism case.** Let `p : T ⟶ S` be a finite morphism of a big
étale site which is in addition a universal homeomorphism. If `ℱ` is a constructible sheaf of
sets on `T_étale`, then so is `p_*ℱ` on `S_étale`. No hypothesis is imposed on `S` or `T`, and
the finite presentation of the source's statement is not needed.

Such a `p` is exactly a finite, surjective and universally injective morphism, so the case covers
every thickening of finite presentation, and more generally every purely inseparable finite
morphism; it is the degenerate half of the source's proof, complementary to the finite étale half
which is Stacks 095H.

The argument is not the source's reduction through Stacks 095K, which this library cannot run
(see the implementation notes). It is instead the direct one that the universal homeomorphism
case permits. Over a quasi-compact and quasi-separated base, `p` is itself a surjection to which
Stacks 095Q (1) applies, so `p_*ℱ` is constructible as soon as `p⁻¹p_*ℱ` is; and for a finite
universal homeomorphism the counit `p⁻¹p_*ℱ ⟶ ℱ` is an isomorphism, because a geometric point of
`S` has exactly one lift to `T`, so the product formula of Stacks 03QP for the stalk of a finite
direct image has exactly one factor. Stacks 095F then globalizes over the affine opens of `S`,
exactly as in Stacks 095H.

## Main results

* `AlgebraicGeometry.subsingleton_lift_of_universalHomeomorphism` — a morphism from a reduced
  scheme into the source of a universal homeomorphism is determined by its composite with that
  morphism. The diagonal of a universal homeomorphism is a surjective closed immersion, hence so
  is its base change along the morphism into the fibre square determined by two factorizations;
  a surjective closed immersion onto a reduced scheme is an isomorphism, so that morphism factors
  through the diagonal and the two factorizations agree.
* `AlgebraicGeometry.subsingleton_geometricPointLift_of_universalHomeomorphism` — a geometric
  point of `S` has at most one lift through a universal homeomorphism `p : T ⟶ S`.
* `AlgebraicGeometry.bijective_pushforwardEtaleStalkComponent_self` — for a finite universal
  homeomorphism the component of the product formula of Stacks 03QP at a geometric point of the
  source is bijective, being its only factor.
* `AlgebraicGeometry.isIso_counit_smallPullbackAdjunction_of_universalHomeomorphism` — the counit
  `p⁻¹p_*ℱ ⟶ ℱ` is an isomorphism.
* `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_universalHomeomorphism_of_compactSpace`
  — the tag over a quasi-compact and quasi-separated base.
* `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_universalHomeomorphism` —
  **Stacks 095R for sheaves of sets and `p` a finite universal homeomorphism**, with no
  hypothesis on `S` or `T`.

## What is granted, and what is not

One hypothesis is carried, `AlgebraicGeometry.SetConstructibilityDescendsAlongSurjective`: the
converse half of Stacks 095Q (1). It is the same hypothesis that the library's Stacks 095H for
sheaves of sets carries, and is discharged there by
`AlgebraicGeometry.isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback`. It quantifies
over the surjective morphisms of quasi-compact quasi-separated schemes of `B` and over sheaves on
their targets, and mentions neither `p` nor `ℱ`, so it cannot supply the content below, which is
the computation of the counit of `p⁻¹ ⊣ p_*`. The finiteness of `p` and its being a universal
homeomorphism are assumed in full and never dropped.

## Implementation notes

The tag's own statement is about an arbitrary finite morphism of finite presentation, and this
file does **not** prove that. The source reduces the general case to the finite étale case of
Stacks 095H by base changing to an affine scheme surjective over the target and replacing the
pullback by a finite étale thickening of it (Stacks 095K, which this library does have, as
`AlgebraicGeometry.exists_surjective_affine_baseChange_thickening_finiteEtale`); the replacement
is harmless because a thickening induces an equivalence of small étale sites, Stacks 04DZ. That
last input is what is missing on the size-bounded étale site of a big étale site. The equivalence
is available for the *étale categories* of a surjective closed immersion
(`Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion`) and, on Mathlib's
small étale site, for the *topoi* of a universal homeomorphism
(`Stacks.EtaleCohomology.smallEtaleInverseImage_isEquivalence_of_universalHomeomorphism`), but
for neither on `AlgebraicGeometry.smallEtaleBaseChange`; and the étale base change of a finite
direct image, Stacks 0959, is carried here only for sheaves of sets. The universal homeomorphism
case needs none of that: it replaces the equivalence of topoi by the one instance of it the
argument uses, namely that the counit is an isomorphism, and reads that off the stalk formula.

The coefficient category is `Type (u + 1)`, which is the universe at which Stacks 03QP, Stacks
03PU and Stacks 095Q (1) are available on the size-bounded site, so the statements are about
sheaves of sets only.

Uniqueness of the lift is proved for an arbitrary reduced test scheme rather than for a geometric
point, because that is the form in which the diagonal argument runs; the spectrum of an
algebraically closed field is reduced, which is how it is applied.

## References

* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 095H](https://stacks.math.columbia.edu/tag/095H)
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A universal homeomorphism is a monomorphism on reduced test schemes.** Let `f : X ⟶ Y` be a
universal homeomorphism and let `Z` be a reduced scheme. Then a morphism `Z ⟶ Y` admits at most
one factorization through `f`. -/
public theorem subsingleton_lift_of_universalHomeomorphism {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] [IsReduced Z] (h : Z ⟶ Y) :
    Subsingleton {g : Z ⟶ X // g ≫ f = h} := by
  refine ⟨fun g₁ g₂ => Subtype.ext ?_⟩
  have hci : IsClosedImmersion (pullback.diagonal f) :=
    Stacks.Etale.isClosedImmersion_diagonal_of_universalHomeomorphism f
  have hsurj : Surjective (pullback.diagonal f) :=
    ⟨Stacks.Etale.surjective_diagonal_of_universalHomeomorphism f⟩
  obtain ⟨s, hs⟩ : ∃ s : Z ⟶ X,
      s ≫ pullback.diagonal f = pullback.lift g₁.1 g₂.1 (g₁.2.trans g₂.2.symm) := by
    set k : Z ⟶ pullback f f := pullback.lift g₁.1 g₂.1 (g₁.2.trans g₂.2.symm) with hk
    have hsq : IsPullback (pullback.fst (pullback.diagonal f) k)
        (pullback.snd (pullback.diagonal f) k) (pullback.diagonal f) k :=
      IsPullback.of_hasPullback (pullback.diagonal f) k
    have _ : IsClosedImmersion (pullback.snd (pullback.diagonal f) k) :=
      MorphismProperty.of_isPullback hsq hci
    have _ : Surjective (pullback.snd (pullback.diagonal f) k) :=
      MorphismProperty.of_isPullback hsq hsurj
    have _ : IsIso (pullback.snd (pullback.diagonal f) k) :=
      isIso_of_isClosedImmersion_of_surjective _
    refine ⟨inv (pullback.snd (pullback.diagonal f) k) ≫
      pullback.fst (pullback.diagonal f) k, ?_⟩
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have h₁ := congrArg (fun m => m ≫ pullback.fst f f) hs
  have h₂ := congrArg (fun m => m ≫ pullback.snd f f) hs
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, ← h₂]

section Counit

variable (B : BigEtaleSite.{u}) {T S : B.Scheme} (p : T ⟶ S)

/-- **A geometric point has at most one lift through a universal homeomorphism.** -/
public theorem subsingleton_geometricPointLift_of_universalHomeomorphism
    [UniversalHomeomorphism (B.inclusion.map p)] (y : GeometricPoint S.1) :
    Subsingleton {g : y.source ⟶ T.1 // g ≫ B.inclusion.map p = y.hom} :=
  subsingleton_lift_of_universalHomeomorphism (B.inclusion.map p) y.hom

/-- **The product formula of Stacks 03QP has a single factor.** For a finite universal
homeomorphism `p : T ⟶ S`, a geometric point `x` of `T` and a sheaf of sets `ℱ` on the small
étale site of `T`, the canonical map from the stalk of `p_*ℱ` at `x ∘ p` to the stalk of `ℱ` at
`x` is bijective: it is the only component of the product decomposition of Stacks 03QP, since `x`
is the only lift of `x ∘ p`. -/
public theorem bijective_pushforwardEtaleStalkComponent_self
    [IsFinite (B.inclusion.map p)] [UniversalHomeomorphism (B.inclusion.map p)]
    (x : GeometricPoint T.1)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))) :
    Function.Bijective
      (pushforwardEtaleStalkComponent B p x (x.map (B.inclusion.map p)) rfl F) := by
  have hsub := subsingleton_geometricPointLift_of_universalHomeomorphism B p
    (x.map (B.inclusion.map p))
  let _ : Unique {g : (x.map (B.inclusion.map p)).source ⟶ T.1 //
      g ≫ B.inclusion.map p = (x.map (B.inclusion.map p)).hom} :=
    uniqueOfSubsingleton ⟨x.hom, rfl⟩
  have hone := (Equiv.piUnique
    (fun l : {g : (x.map (B.inclusion.map p)).source ⟶ T.1 //
        g ≫ B.inclusion.map p = (x.map (B.inclusion.map p)).hom} =>
      etaleStalk B T.1 T.property
        (geometricPointLift (B.inclusion.map p)
          (x.map (B.inclusion.map p)) l) F.obj)).bijective
  exact hone.comp (finitePushforwardStalkToProduct_bijective B p (x.map (B.inclusion.map p)) F)

/-- **The counit of `p⁻¹ ⊣ p_*` is an isomorphism for a finite universal homeomorphism.** Let
`p : T ⟶ S` be a finite morphism of a big étale site which is a universal homeomorphism and let
`ℱ` be a sheaf of sets on the small étale site of `T`. Then `p⁻¹p_*ℱ ⟶ ℱ` is an isomorphism.

By Stacks 03PU it suffices to check this on the stalk at every geometric point `x` of `T`. There
the stalk map of the counit, precomposed with the comparison of Stacks 03Q1 identifying the stalk
of `p⁻¹p_*ℱ` at `x` with the stalk of `p_*ℱ` at `x ∘ p`, is the component of Stacks 03QP at the
lift `x`, and that component is bijective because `x` is the only lift. -/
public theorem isIso_counit_smallPullbackAdjunction_of_universalHomeomorphism
    [IsFinite (B.inclusion.map p)] [UniversalHomeomorphism (B.inclusion.map p)]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))) :
    IsIso ((B.smallPullbackAdjunction p (Type (u + 1))).counit.app F) := by
  refine isIso_of_bijective_etaleStalkMap B T.1 T.property _ fun x => ?_
  have hfac : ∀ z, (etaleStalkFunctor.{u, u + 1} B T.1 T.property x).map
        ((B.smallPullbackAdjunction p (Type (u + 1))).counit.app F)
        ((smallEtalePullbackStalkIso B p x).inv.app
          ((B.smallPushforward p (Type (u + 1))).obj F) z) =
      pushforwardEtaleStalkComponent B p x (x.map (B.inclusion.map p)) rfl F z := by
    intro z
    have hcu := pushforwardEtaleStalkComponent_counit_comp B p x
      (ψ := 𝟙 ((B.smallPushforward p (Type (u + 1))).obj F)) z
    simpa using hcu
  have hinv : ∀ v, (smallEtalePullbackStalkIso B p x).inv.app
        ((B.smallPushforward p (Type (u + 1))).obj F)
        (((smallEtalePullbackStalkIso B p x).app
          ((B.smallPushforward p (Type (u + 1))).obj F)).toEquiv v) = v := fun v =>
    Equiv.symm_apply_apply (((smallEtalePullbackStalkIso B p x).app
      ((B.smallPushforward p (Type (u + 1))).obj F)).toEquiv) v
  have hb := bijective_pushforwardEtaleStalkComponent_self B p x F
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · have ha := hfac ((((smallEtalePullbackStalkIso B p x).app
      ((B.smallPushforward p (Type (u + 1))).obj F)).toEquiv) a)
    have hc := hfac ((((smallEtalePullbackStalkIso B p x).app
      ((B.smallPushforward p (Type (u + 1))).obj F)).toEquiv) b)
    rw [hinv a] at ha
    rw [hinv b] at hc
    refine (((smallEtalePullbackStalkIso B p x).app
      ((B.smallPushforward p (Type (u + 1))).obj F)).toEquiv).injective (hb.1 ?_)
    rw [← ha, ← hc]
    exact hab
  · obtain ⟨z, hz⟩ := hb.2 w
    exact ⟨(smallEtalePullbackStalkIso B p x).inv.app
      ((B.smallPushforward p (Type (u + 1))).obj F) z, (hfac z).trans hz⟩

end Counit

section Constructible

variable (B : BigEtaleSite.{u}) {T S : B.Scheme} (p : T ⟶ S)

/-- **Stacks 095R for sheaves of sets and a finite universal homeomorphism, over a quasi-compact
and quasi-separated base.** Let `p : T ⟶ S` be a finite morphism of a big étale site which is a
universal homeomorphism, with `S` and `T` quasi-compact and quasi-separated, and let `ℱ` be a
constructible sheaf of sets on `T_étale`. Then `p_*ℱ` is constructible.

A universal homeomorphism is surjective, so Stacks 095Q (1) applies to `p` itself: `p_*ℱ` is
constructible as soon as `p⁻¹p_*ℱ` is, and the latter is isomorphic to `ℱ` by
`AlgebraicGeometry.isIso_counit_smallPullbackAdjunction_of_universalHomeomorphism`.

Stacks 095Q (1) is carried as the hypothesis `h095Q`, in the form
`AlgebraicGeometry.SetConstructibilityDescendsAlongSurjective`. -/
public theorem isConstructibleSetSheaf_pushforward_of_universalHomeomorphism_of_compactSpace
    [IsFinite (B.inclusion.map p)] [UniversalHomeomorphism (B.inclusion.map p)]
    (hTc : CompactSpace (B.inclusion.obj T)) (hTq : QuasiSeparatedSpace (B.inclusion.obj T))
    (hSc : CompactSpace (B.inclusion.obj S)) (hSq : QuasiSeparatedSpace (B.inclusion.obj S))
    (h095Q : SetConstructibilityDescendsAlongSurjective B)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  have _ := isIso_counit_smallPullbackAdjunction_of_universalHomeomorphism B p F
  refine h095Q T S p
    (Stacks.Etale.surjective_of_universalHomeomorphism (B.inclusion.map p)).surj
    hTc hTq hSc hSq _ ?_
  exact isConstructibleSetSheaf_congr B _
    (asIso ((B.smallPullbackAdjunction p (Type (u + 1))).counit.app F)).symm hF

/-- **Stacks 095R for sheaves of sets and a finite universal homeomorphism.** Let `p : T ⟶ S` be a
finite morphism of a big étale site which is in addition a universal homeomorphism, and let `ℱ`
be a constructible sheaf of sets on `T_étale`. Then `p_*ℱ` is a constructible sheaf of sets on
`S_étale`. No hypothesis is imposed on `S` or `T`, and no finite presentation of `p` is needed.

By Stacks 095F constructibility may be checked on the covering of `S` by its affine opens, and
over an affine open `U` the restriction of `p_*ℱ` is the direct image of the restriction of `ℱ`
along the base change of `p` to `U`, which is again finite and a universal homeomorphism; the
source of that base change is finite over the affine `U`, hence affine, so both are quasi-compact
and quasi-separated and
`AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_universalHomeomorphism_of_compactSpace`
applies.

Stacks 095Q (1) is carried as the hypothesis `h095Q`, exactly as in that theorem; it quantifies
over all morphisms of the site, so the Zariski reduction does not add to what is granted. -/
@[stacks 095R "sheaves of sets, and only the case of a finite universal homeomorphism — \
equivalently of a finite, surjective and universally injective morphism; the finite presentation \
of the tag's hypothesis is not needed and is dropped. The general finite, finitely presented case \
is NOT proved: it needs the thickening reduction of Stacks 095K together with the equivalence of \
small étale topoi of Stacks 04DZ on the size-bounded site, which this library does not carry. \
Stacks 095Q (1)'s descent is granted as the only hypothesis, and nothing is assumed of S or T."]
public theorem isConstructibleSetSheaf_pushforward_of_universalHomeomorphism
    [IsFinite (B.inclusion.map p)] [UniversalHomeomorphism (B.inclusion.map p)]
    (h095Q : SetConstructibilityDescendsAlongSurjective B)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  classical
  have hUaff : ∀ i, IsAffine ((B.inclusion.obj S).affineOpenCover.openCover.X i) := fun i =>
    Scheme.isAffine_affineCover (B.inclusion.obj S) i
  have hUopen : ∀ i, IsOpenImmersion ((B.inclusion.obj S).affineOpenCover.openCover.f i) :=
    fun i => (B.inclusion.obj S).affineOpenCover.openCover.map_prop i
  have hUc : ∀ i, B.Contains ((B.inclusion.obj S).affineOpenCover.openCover.X i) := by
    intro i
    have := hUopen i
    exact Scheme.size_lt_of_isOpenImmersion
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) S.property
  let W : (B.inclusion.obj S).affineOpenCover.openCover.I₀ →
      SmallEtale B S.1 S.property := fun i =>
    ⟨Over.mk (ObjectProperty.homMk
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) :
        B.obj _ (hUc i) ⟶ B.obj S.1 S.property), by
      have := hUopen i
      change Etale ((B.inclusion.obj S).affineOpenCover.openCover.f i)
      infer_instance⟩
  refine isConstructibleFiniteSheaf_of_openCover B S _
    (fun i => (W i).obj.left) (fun i => (W i).obj.hom) (fun i => hUopen i) ?_ fun i => ?_
  · exact ((B.inclusion.obj S).affineOpenCover.openCover.iUnion_range).symm
  · have hEtW : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
    have _ : IsFinite (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
      MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
    have hUH : UniversalHomeomorphism (B.inclusion.map p) := inferInstance
    have _ : UniversalHomeomorphism (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
      ⟨MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i))
        hUH.universally_isHomeomorph⟩
    have _ : IsAffine (B.inclusion.obj (W i).obj.left) := hUaff i
    have _ : IsAffine (B.inclusion.obj ((smallEtaleBaseChange B p).obj (W i)).obj.left) :=
      isAffine_of_isAffineHom (B.inclusion.map (baseChangedEtaleProjection B p (W i)))
    refine isConstructibleSetSheaf_congr B _
      ((smallInverseImageIsoPostcomposePushforward B (W i).obj.hom
        (Type (u + 1))).app _).symm ?_
    refine isConstructibleSetSheaf_congr B _
      ((smallEtaleRestrictionPushforwardBaseChangeIso B p (W i) (Type (u + 1))).app F) ?_
    exact isConstructibleSetSheaf_pushforward_of_universalHomeomorphism_of_compactSpace B
      (baseChangedEtaleProjection B p (W i))
      (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _)
      (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) h095Q _
      (isConstructibleFiniteSheaf_smallEtaleRestriction B T
        ((smallEtaleBaseChange B p).obj (W i)) F hF)

end Constructible

end AlgebraicGeometry

end
