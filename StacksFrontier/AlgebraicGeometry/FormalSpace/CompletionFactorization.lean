module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePointwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Glueing a factorization across a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of algebraic spaces over `S` and let `T ⊆ |X|` be a closed set of points.
**Stacks 0AR6** says that if `X` is locally Noetherian, `g` is a monomorphism and locally of
finite type, and `f` factors through `g` both on the open complement `X ∖ T` and on the
completion `X_{/T}`, then `f` factors through `g`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factorization_of_openComplement_and_completion`:
  **Stacks 0AR6**.

## Implementation notes

A factorization is the bare existential `∃ v, v ≫ g = f`; there is no predicate for it. The
open complement `X ∖ T` is the open subspace corresponding to `Tᶜ` under the correspondence of
Stacks 03BZ, `AlgebraicGeometry.Space.openSubspacesOrderIso`.

### Why the completion hypothesis is stated on the subfunctor

The completion `AlgebraicGeometry.Space.completionSheaf` of Stacks 0AMC lands in
`CategoryTheory.Sheaf` of `Type (u + 1)`, one universe above the value universe of `Y`, so
there is no morphism `X_{/T} ⟶ Y` in this library to factor. The hypothesis is therefore
stated on the unsheafified `AlgebraicGeometry.Space.completionSubfunctor`, the subfunctor of
sections of the universe lift of `X` whose point-set image lies in `T`, with the maps to `Y`
and `Z` universe-lifted by `CategoryTheory.Functor.whiskerRight · uliftFunctor.{u + 1}`. By
Stacks 0AIZ the completion is the sheafification of exactly that subfunctor, so a morphism out
of the completion restricts along the unit to a morphism out of the subfunctor and the
hypothesis used here is implied by the factorization the source assumes; conversely the
universe lift of `Z` is a sheaf, because `Z` is, so the universal property of sheafification
turns the hypothesis used here back into a factorization on the completion. Only the first
implication is used: it makes the hypothesis used here the weaker one, so no generality is lost.

### The proof

The source forms `E = X ×_Y Z` and argues that `E ⟶ X` is étale above `T` by Stacks 0APQ,
applied to the base changes of `E ⟶ X` to the infinitesimal neighbourhoods of the closed
subspace supported on `T`. Those neighbourhoods are not needed here, because the subfunctor
formulation of the completion hypothesis gives the factorization directly where the proof uses
it. The projection `p : E ⟶ X` is a monomorphism and locally of finite type, being a base change
of `g`, hence unramified by [Stacks Project, Tag 05W6]; so by Stacks 02GK at a point,
`AlgebraicGeometry.Space.isEtaleAt_of_isSmoothAt_of_isUnramifiedAt`, only smoothness at each
point of `E` is left, and that is the lifting criterion of Stacks 0APN,
`AlgebraicGeometry.Space.isSmoothAt_of_liftsAt_isSmallExtension`. A lifting problem for `p` along
a small extension `R' ⟶ R` presents its outer morphism as `β : Spec R' ⟶ X`; since `R'` is
Artinian local, `Spec R'` has one point, so `β` has point-set image either inside `T` — and then
it is a section of the completion subfunctor, which the completion hypothesis sends into `Z`, so
`β` factors through `E` — or inside `Tᶜ`, and then it factors through the open complement, which
the other hypothesis sends into `Z`. Either way `β` lifts to `E`, and because `p` is a
monomorphism that lift automatically restricts to the inner morphism of the square.

So `p` is étale at every point, hence étale by Stacks 03XT, and universally injective because
it is a monomorphism, hence an open immersion by the open-immersion clause of Stacks 05W5. It
is surjective on points: above `Tᶜ` through the open complement, and above `T` through the
reduced closed subspace of Stacks 03IQ supported on `T`, whose inclusion has point-set image
`T` and therefore factors through `E` by the completion hypothesis again. An open immersion
which is surjective on points is an isomorphism, and inverting it exhibits the factorization
as `p⁻¹ ≫ pullback.snd f g`.

Closedness of `T` is used only to form the reduced closed subspace and the open complement.

## References

* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
* [Stacks Project, Tag 0APQ](https://stacks.math.columbia.edu/tag/0APQ)
* [Stacks Project, Tag 0AR6](https://stacks.math.columbia.edu/tag/0AR6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring a morphism with image in `T` through the fibre product -/

/-- The universe lift of a presheaf mapping to `X` with point-set image in `T`, mapped into the
subfunctor of sections of the universe lift of `X` whose point-set image lies in `T`. -/
private theorem range_whiskerRight_le_completionSubfunctor
    {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (i : W ⟶ X)
    (hrange : Set.range (Space.pointsMap B S hS W i) ⊆ T) :
    Subfunctor.range (Functor.whiskerRight i uliftFunctor.{u + 1}) ≤
      Space.completionSubfunctor B S hS X T := by
  rintro U _ ⟨z, rfl⟩
  exact hasImageIn_of_range_pointsMap_subset B S hS T i hrange U.unop z.down

/-- A morphism `i : W ⟶ X` whose point-set image lies in `T` factors through `g` after
composing with `f`, granted a factorization of `f` through `g` on the subfunctor of sections
with point-set image in `T`.

The sections of `W` are sections of `X` with point-set image in `T`, so the universe lift of
`i` factors through that subfunctor; composing with the given factorization gives a morphism
from the universe lift of `W` to the universe lift of `Z` over the universe lift of `i ≫ f`,
and universe lifting is a fully faithful operation on these presheaves. -/
private theorem exists_hom_of_range_pointsMap_subset
    {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (f : X ⟶ Y) (g : Z ⟶ Y) (i : W ⟶ X)
    (hrange : Set.range (Space.pointsMap B S hS W i) ⊆ T)
    (v : (Space.completionSubfunctor B S hS X T).toFunctor ⟶ Z ⋙ uliftFunctor.{u + 1})
    (hv : v ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
      (Space.completionSubfunctor B S hS X T).ι ≫
        Functor.whiskerRight f uliftFunctor.{u + 1}) :
    ∃ w : W ⟶ Z, w ≫ g = i ≫ f := by
  let c := Subfunctor.lift (Functor.whiskerRight i uliftFunctor.{u + 1})
    (range_whiskerRight_le_completionSubfunctor B S hS T i hrange)
  let Φ := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  refine ⟨Φ.preimage (c ≫ v), Φ.map_injective ?_⟩
  rw [Φ.map_comp, Φ.map_comp, Φ.map_preimage]
  change (c ≫ v) ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
    Functor.whiskerRight i uliftFunctor.{u + 1} ≫
      Functor.whiskerRight f uliftFunctor.{u + 1}
  rw [Category.assoc, hv, ← Category.assoc, Subfunctor.lift_ι]

/-! ### The spectrum of an Artinian local ring has one point -/

/-- The presheaf represented by an object of the site whose underlying scheme is the spectrum
of an Artinian local ring has at most one point: its scheme has one point, by Stacks 03BX the
points of the presheaf are the points of the scheme, and an Artinian local ring has one
prime. -/
private theorem subsingleton_points_yoneda_of_isArtinianRing
    {R : CommRingCat.{u}} (hloc : IsLocalRing R) (hart : IsArtinianRing R)
    (V : BigFppfOver B S hS) (e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec R) :
    Subsingleton (Space.points B S hS (yoneda.obj V)) := by
  have := hloc
  have := hart
  have hspec : Subsingleton ↥(Spec R) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  have hV : Subsingleton ((BigFppfOver.toScheme B S hS).obj V) := by
    refine ⟨fun z w => ?_⟩
    have hz : e.inv.base (e.hom.base z) = z := by simp
    have hw : e.inv.base (e.hom.base w) = w := by simp
    rw [← hz, ← hw, hspec.elim (e.hom.base z) (e.hom.base w)]
  exact (Space.pointsEquivScheme B S hS V).subsingleton

/-! ### Stacks 0AR6 -/

/-- **Stacks 0AR6.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic spaces over `S`
and let `T ⊆ |X|` be closed. Assume that `X` is locally Noetherian, that `g` is a monomorphism
and locally of finite type, that `f` restricted to the open complement of `T` factors through
`g`, and that `f` factors through `g` on the subfunctor of sections with point-set image in
`T`. Then `f` factors through `g`.

The last hypothesis is the factorization on the completion `X_{/T}` of Stacks 0AMC, stated on
the subfunctor whose sheafification that completion is by Stacks 0AIZ; see the module
documentation. -/
@[stacks 0AR6 "the completion hypothesis is stated on the unsheafified subfunctor of sections \
with point-set image in `T` (`AlgebraicGeometry.Space.completionSubfunctor`), whose \
sheafification is the completion `X_{/T}` of Tag 0AMC by Tag 0AIZ, because the completion \
lands one universe above `Y` and so admits no morphism to `Y` in this library; no other \
hypothesis is carried"]
theorem exists_factorization_of_openComplement_and_completion
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hgmono : Mono g) (hgft : Space.IsLocallyOfFiniteType B S hS g)
    (hopen : ∃ v : ((Space.openSubspacesOrderIso B S hS X hX).symm
        ⟨Tᶜ, hT.isOpen_compl⟩).1.toFunctor ⟶ Z,
      v ≫ g = ((Space.openSubspacesOrderIso B S hS X hX).symm
        ⟨Tᶜ, hT.isOpen_compl⟩).1.ι ≫ f)
    (hcompletion : ∃ v : (Space.completionSubfunctor B S hS X T).toFunctor ⟶
        Z ⋙ uliftFunctor.{u + 1},
      v ≫ Functor.whiskerRight g uliftFunctor.{u + 1} =
        (Space.completionSubfunctor B S hS X T).ι ≫
          Functor.whiskerRight f uliftFunctor.{u + 1}) :
    ∃ v : X ⟶ Z, v ≫ g = f := by
  classical
  set Uo := (Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩ with hUo
  obtain ⟨vCompletion, hvCompletion⟩ := hcompletion
  obtain ⟨vOpen, hvOpen⟩ := hopen
  have hUrange : Set.range (Space.pointsMap B S hS Uo.1.toFunctor Uo.1.ι) = Tᶜ := by
    rw [← Space.openSubspacesOrderIso_apply B S hS X hX Uo, hUo]
    simp
  -- The fibre product and its projection.
  have hE : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hZ hY
  have hpMono : Mono (pullback.fst f g) :=
    (IsPullback.of_hasPullback f g).mono_fst_of_mono hgmono
  have hpFT : Space.IsLocallyOfFiniteType B S hS (pullback.fst f g) :=
    (Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hgft
  have hUnram : Space.IsUnramified B S hS (pullback.fst f g) :=
    Space.isUnramified_of_isLocallyOfFiniteType_of_mono B S hS _ hpFT hpMono
  -- Anything with point-set image in `T` factors through the fibre product.
  have key : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : W ⟶ X),
      Set.range (Space.pointsMap B S hS W i) ⊆ T →
      ∃ w : W ⟶ pullback f g, w ≫ pullback.fst f g = i := by
    intro W i hi
    obtain ⟨z, hz⟩ := exists_hom_of_range_pointsMap_subset B S hS T f g i hi
      vCompletion hvCompletion
    exact ⟨pullback.lift i z hz.symm, pullback.lift_fst _ _ _⟩
  -- So does the open complement, through the other hypothesis.
  obtain ⟨ell, hell⟩ :
      ∃ w : Uo.1.toFunctor ⟶ pullback f g, w ≫ pullback.fst f g = Uo.1.ι :=
    ⟨pullback.lift Uo.1.ι vOpen hvOpen.symm, pullback.lift_fst _ _ _⟩
  -- The projection is étale at every point.
  have hUnramAt : ∀ y, Space.IsUnramifiedAt B S hS (pullback.fst f g) y :=
    ((Space.isUnramified_tfae B S hS hE hX (pullback.fst f g)).out 1 2).mp hUnram
  have hEtaleAt : ∀ x, Space.IsEtaleAt B S hS (pullback.fst f g) x := by
    intro x
    refine Space.isEtaleAt_of_isSmoothAt_of_isUnramifiedAt B S hS hE hX _ x ?_ (hUnramAt x)
    refine Space.isSmoothAt_of_liftsAt_isSmallExtension B S hS hE hX _ x hXnoeth hpFT ?_
    intro R' R φ hφ V V' i e e' hi hRloc q hq α β hqx hcomm
    have := hRloc
    have hsub : Subsingleton (Space.points B S hS (yoneda.obj V')) :=
      subsingleton_points_yoneda_of_isArtinianRing B S hS hφ.1 hφ.2.2.1 V' e'
    have hcentre : Space.pointsMap B S hS (yoneda.obj V') β
        (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map i)
          (q.class B S hS (yoneda.obj V))) =
        Space.pointsMap B S hS (pullback f g) (pullback.fst f g) x := by
      rw [← Space.pointsMap_comp_apply, ← hcomm, Space.pointsMap_comp_apply, hqx]
    have hβrange : ∀ W : Set (Space.points B S hS X),
        Space.pointsMap B S hS (pullback f g) (pullback.fst f g) x ∈ W →
        Set.range (Space.pointsMap B S hS (yoneda.obj V') β) ⊆ W := by
      intro W hW y hy
      obtain ⟨w, rfl⟩ := hy
      rw [hsub.elim w (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map i)
        (q.class B S hS (yoneda.obj V))), hcentre]
      exact hW
    obtain ⟨γ, hγ⟩ : ∃ γ : yoneda.obj V' ⟶ pullback f g, γ ≫ pullback.fst f g = β := by
      by_cases hx : Space.pointsMap B S hS (pullback f g) (pullback.fst f g) x ∈ T
      · exact key β (hβrange T hx)
      · obtain ⟨βU, hβU⟩ := (Space.factorsThrough_openSubspace_iff_points B S hS hX
          (isAlgebraicSpace_yoneda B S hS V') Uo.1 Uo.2 β).2
          (by rw [hUrange]; exact hβrange Tᶜ hx)
        exact ⟨βU ≫ ell, by rw [Category.assoc, hell, hβU]⟩
    refine ⟨γ, ?_, hγ⟩
    rw [← cancel_mono (pullback.fst f g), Category.assoc, hγ]
    exact hcomm.symm
  -- An étale universally injective morphism is an open immersion.
  have hOI : Space.IsOpenImmersion B S hS (pullback.fst f g) :=
    Space.isOpenImmersion_of_isEtale_of_universallyInjective B S hS hE hX _
      (Space.isEtale_of_forall_isEtaleAt B S hS hE hX _ hEtaleAt)
      (Space.universallyInjective_of_mono B S hS _ hpMono)
  -- It is surjective on points.
  have hrange : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : W ⟶ X) (w : W ⟶ pullback f g),
      w ≫ pullback.fst f g = i → Set.range (Space.pointsMap B S hS W i) ⊆
        Set.range (Space.pointsMap B S hS (pullback f g) (pullback.fst f g)) := by
    rintro W _ w rfl
    rw [Space.pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  have hSurj : Function.Surjective
      (Space.pointsMap B S hS (pullback f g) (pullback.fst f g)) := by
    intro x
    by_cases hx : x ∈ T
    · have hred := Space.range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT
      obtain ⟨w, hw⟩ := key _ hred.le
      exact hrange _ w hw (by rwa [hred])
    · exact hrange _ ell hell (by rwa [hUrange])
  have : IsIso (pullback.fst f g) :=
    Space.isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS _ hOI hSurj
  exact ⟨inv (pullback.fst f g) ≫ pullback.snd f g, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

end AlgebraicGeometry.FormalSpace

end
