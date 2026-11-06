module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.FibreProducts
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening

/-!
# A sequence of thickenings witnessing failure of versality at infinitely many points

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S`, satisfying (RS*), and let `x` be an object of `𝒳` over an affine scheme `U` of
finite type over `S`. Suppose given finite type points `u 0, u 1, …` of `U`, no one of which
specializes to another, at none of which `x` is versal. Then the one-point thickenings of
Tag 0G2J at the separate points can be assembled into a single increasing chain: there are
morphisms `x ⟶ x₁ ⟶ x₂ ⟶ …` of `𝒳` lying over `U ⟶ U₁ ⟶ U₂ ⟶ …` over `S` such that each
`U ⟶ Uₙ₊₁` is a first order thickening, the `n`-th step adds a copy of the residue field at
`u n`, and no `x ⟶ xₙ₊₁` admits a retraction over a neighbourhood of `u n`.

## Main results

* `Deformation.Artin.exists_sequence_firstOrderThickenings_without_localRetraction`:
  **Stacks 0G2S**.
* `Deformation.Artin.affineSiteObj` and `Deformation.Artin.affineSiteHom` — an affine scheme
  over `S` inside the site, and a morphism of such, as an object and a morphism of the big
  affine fppf site, together with
  `Deformation.Artin.affineSiteHom_toScheme`,
  `Deformation.Artin.affineSiteHom_comp`, `Deformation.Artin.affineSiteHom_square`,
  `Deformation.Artin.affineSiteHom_appTop_isPullback`,
  `Deformation.Artin.affineSiteHom_appTop_surjective` and
  `Deformation.Artin.affineSiteHom_appTop_kernel_sq`, which carry a square of affine schemes
  over `S` to the affine site unchanged on global sections. This is the bridge by which a
  cartesian square of rings is fed to axiom (RS\*) in the shape
  `Deformation.Artin.exists_fiber_of_satisfiesRSStar` states it, namely at
  `((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map _).appTop` rather than at
  `(Spec.map _).appTop`.
* `Deformation.Artin.exists_compatible_maps_over_affine_pushout`,
  `Deformation.Artin.exists_compatible_maps_over_scheme_square` and
  `Deformation.Artin.affineSiteHom_actual_lift` — axiom (RS\*) gluing two objects of the fibred
  category over a cartesian square, with the glued object delivered as an object of the *fibre*
  over the fourth corner and the two arrows to it as `IsHomLift`s of the site morphisms. This is
  the form the direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] needs, where the glued object has to
  be presented as a lift of `x` across a deformation situation; the scheme-level
  `Deformation.Artin.exists_compatible_maps_over_square` below, which only records the
  underlying morphisms of schemes, does not determine the site object the glued family lies
  over.

## Implementation notes

The chain is indexed from zero with `x₀ = x`, so that the `n`-th assertion concerns the
point `u n`, the thickening `U ⟶ Uₙ₊₁` and the step `Uₙ ⟶ Uₙ₊₁`. The short exact sequence
`0 ⟶ κ(u n) ⟶ 𝒪_{Uₙ₊₁} ⟶ 𝒪_{Uₙ} ⟶ 0` is expressed in the idiom of Tag 0G2J: surjectivity of
the structure sheaf map together with an isomorphism of its kernel with the direct image of
the structure sheaf of the spectrum of the residue field along the canonical inclusion of
the point.

Each step is the pushout `Uₙ₊₁ = Uₙ ⨿_U Tₙ₊₁` of the thickening supplied by Tag 0G2J, formed
in the category of schemes over `S`. All four schemes are affine — the ambient scheme of a
first-order thickening of an affine scheme is affine — so the affine local model of
Tag 07RT applies and the general form of Tag 06AD is not needed here; the pushout
also stays inside the site because its ring of global sections embeds in the product of the
two given ones. The ideal of `U ⟶ Uₙ₊₁` is the direct sum of the ideals of `U ⟶ Uₙ` and of
`U ⟶ Tₙ₊₁`, hence again square-zero, which is why every `U ⟶ Uₙ` is a *first* order
thickening and not merely a finite order one. Axiom (RS*) applied to the square of global
sections glues `xₙ` and the object over `Tₙ₊₁` into `xₙ₊₁`, and the cartesian square of
structure sheaves identifies the ideal of `Uₙ ⟶ Uₙ₊₁` with the direct image of the ideal of
`U ⟶ Tₙ₊₁`, whose residue field is carried along because a closed immersion induces an
isomorphism on residue fields.

The absence of a local retraction transfers from `Tₙ₊₁` to `Uₙ₊₁` along the other leg of the
pushout square: a retraction over an open neighbourhood of `u n` in `Uₙ₊₁` restricts, over
the base change of that leg, to one over `Tₙ₊₁`. The hypothesis that no `u n` specializes to
another is recorded as the source states it; it is what would be needed to shrink to an open
meeting only the `n`-th point, which this route replaces by the base change just described.

## References

* [Stacks Project, Tag 0G2S](https://stacks.math.columbia.edu/tag/0G2S)
* [Stacks Project, Tag 0G2J](https://stacks.math.columbia.edu/tag/0G2J)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom TopCat.Sheaf
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback

section AffinePushout

variable {X X' Y : Scheme.{u}}

/-- In the affine local model the cocartesian square of locally ringed spaces is available
with no appeal to affineness of a general thickening: every point of the apex lies in the
open `⊤`, whose preimages are the affine schemes `X'` and `Y`. -/
private theorem exists_isPushout_forgetToLRS_of_isAffine
    (i : X ⟶ X') (f : X ⟶ Y) [IsClosedImmersion i] [IsAffine X'] [IsAffine Y] :
    ∃ (Q : Scheme.{u}) (A : X' ⟶ Q) (B : Y ⟶ Q),
      IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)
        (Scheme.forgetToLocallyRingedSpace.map A)
        (Scheme.forgetToLocallyRingedSpace.map B) := by
  have hcol : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.left)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.right) :=
    IsPushout.of_isColimit_cocone (colimit.isColimit
      (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)))
  obtain ⟨Q, A, B, h, -⟩ :=
    Stacks.Pushout.exists_scheme_isPushout_of_isPushout i f hcol
      (fun _ => ⟨⊤, trivial, isAffineOpen_top X', isAffineOpen_top Y⟩)
  exact ⟨Q, A, B, h⟩

/-- **The structure sheaf of an affine pushout, over an arbitrary open.** For a closed immersion
`i : X ⟶ X'` with `X'` and `Y` affine, the sections of `𝒪_{Y ⨿_X X'}` over any open form the
fibre product of the sections over the two preimages above those over their common preimage. -/
private theorem affinePushout_structureSheaf_isPullback
    (i : X ⟶ X') (f : X ⟶ Y) [IsClosedImmersion i] [IsAffine X'] [IsAffine Y]
    [HasPushout i f] (U : (pushout i f).Opens)
    (e : i ⁻¹ᵁ (pushout.inl i f ⁻¹ᵁ U) = f ⁻¹ᵁ (pushout.inr i f ⁻¹ᵁ U)) :
    IsPullback ((pushout.inr i f).app U) ((pushout.inl i f).app U)
      (f.app (pushout.inr i f ⁻¹ᵁ U))
      (i.app (pushout.inl i f ⁻¹ᵁ U) ≫
        eqToHom (congrArg (fun V : X.Opens ↦ Γ(X, V)) e)) := by
  obtain ⟨Q, A, B, hcol⟩ := exists_isPushout_forgetToLRS_of_isAffine i f
  have hpo : IsPushout i f A B :=
    IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hcol
  have hcol' : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (Scheme.forgetToLocallyRingedSpace.map (pushout.inl i f))
      (Scheme.forgetToLocallyRingedSpace.map (pushout.inr i f)) :=
    hcol.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Scheme.forgetToLocallyRingedSpace.mapIso hpo.isoPushout).symm
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Scheme.forgetToLocallyRingedSpace.map_comp, hpo.inl_isoPushout_inv])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Scheme.forgetToLocallyRingedSpace.map_comp, hpo.inr_isoPushout_inv])
  exact Stacks.Pushout.isPullback_app_of_isPushout_forgetToLocallyRingedSpace hcol' U e

end AffinePushout

section RingLemmas

/-- In a cartesian square of rings, two elements of the corner `R` with the same images in both
`A` and `B` agree: the square separates the two evaluations at them on a polynomial ring. -/
private theorem eq_of_isPullback_of_map_eq {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] {f : CommRingCat.of R ⟶ CommRingCat.of A}
    {g : CommRingCat.of R ⟶ CommRingCat.of B} {h : CommRingCat.of A ⟶ CommRingCat.of C}
    {k : CommRingCat.of B ⟶ CommRingCat.of C} (sq : IsPullback f g h k) {x y : R}
    (hx : f.hom x = f.hom y) (hy : g.hom x = g.hom y) : x = y := by
  let ex : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (Polynomial.evalRingHom x)
  let ey : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (Polynomial.evalRingHom y)
  have hxf : ex ≫ f = ey ≫ f := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp [ex, ey]
    · simpa [ex, ey] using hx
  have hxyg : ex ≫ g = ey ≫ g := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp [ex, ey]
    · simpa [ex, ey] using hy
  have hev := congrArg (fun z => z.hom Polynomial.X) (sq.hom_ext hxf hxyg)
  simpa [ex, ey] using hev

/-- A ring sitting in a cartesian square injects into the product of the two other corners. -/
private theorem mk_le_prod_of_isPullback {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] (f : CommRingCat.of R ⟶ CommRingCat.of A)
    (g : CommRingCat.of R ⟶ CommRingCat.of B)
    (h : CommRingCat.of A ⟶ CommRingCat.of C)
    (k : CommRingCat.of B ⟶ CommRingCat.of C)
    (sq : IsPullback f g h k) : Cardinal.mk R ≤ Cardinal.mk (A × B) :=
  Cardinal.mk_le_of_injective (f := fun r => (f.hom r, g.hom r)) fun _ _ hxy =>
    eq_of_isPullback_of_map_eq sq (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

/-- Two elements of a square-zero kernel multiply to zero. -/
private theorem ker_sq_mul_eq_zero {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hker : RingHom.ker f ^ 2 = ⊥)
    {x y : R} (hx : x ∈ RingHom.ker f) (hy : y ∈ RingHom.ker f) : x * y = 0 := by
  have hxy : x * y ∈ (RingHom.ker f) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  rw [hker] at hxy
  simpa using hxy

/-- **The kernel of a composite out of a fibre product of rings is square-zero** when both
kernels of the square's far legs are: a product of two of its elements has both components
zero, hence vanishes because the square is cartesian. -/
private theorem pullback_comp_ker_sq {P A B R : Type u} [CommRing P] [CommRing A]
    [CommRing B] [CommRing R] (f : P →+* A) (g : P →+* B)
    (h : A →+* R) (k : B →+* R)
    (hsq : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hA : RingHom.ker h ^ 2 = ⊥) (hB : RingHom.ker k ^ 2 = ⊥) :
    RingHom.ker (h.comp f) ^ 2 = ⊥ := by
  apply le_antisymm
  · rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    have hcomp : (h.comp f) = (k.comp g) := by
      apply RingHom.ext
      intro x
      have heq := congrArg
        (fun φ : CommRingCat.of P ⟶ CommRingCat.of R => φ.hom x) hsq.w
      simpa using heq
    have hxA : f x ∈ RingHom.ker h := by
      show h (f x) = 0
      change (h.comp f) x = 0 at hx
      exact hx
    have hyA : f y ∈ RingHom.ker h := by
      show h (f y) = 0
      change (h.comp f) y = 0 at hy
      exact hy
    have hxB : g x ∈ RingHom.ker k := by
      show k (g x) = 0
      show (k.comp g) x = 0
      rw [← hcomp]
      exact hx
    have hyB : g y ∈ RingHom.ker k := by
      show k (g y) = 0
      show (k.comp g) y = 0
      rw [← hcomp]
      exact hy
    have hxyA := ker_sq_mul_eq_zero h hA hxA hyA
    have hxyB := ker_sq_mul_eq_zero k hB hxB hyB
    exact eq_of_isPullback_of_map_eq hsq (by simpa using hxyA) (by simpa using hxyB)
  · exact bot_le

end RingLemmas

section PushoutOver

variable {S : Scheme.{u}} (U A T : Over S) (i : U ⟶ A) (f : U ⟶ T)

/-- **The pushout of two affine schemes in the site stays in the site.** Its ring of global
sections injects into the product of the two given ones, so its cardinal size is bounded by
theirs and the strong limit cutoff is not reached. -/
private theorem pushout_scheme_size_lt {B : AlgebraicGeometry.BigFppfSite.{u}}
    {U A T : Scheme.{u}} (i : U ⟶ A) (f : U ⟶ T)
    [IsClosedImmersion i] [IsAffine A] [IsAffine T] [HasPushout i f]
    (hA : A.size < B.cutoff) (hT : T.size < B.cutoff) :
    (pushout i f).size < B.cutoff := by
  let : IsAffine (pushout i f) :=
    Stacks.Pushout.isAffine_pushout_of_isClosedImmersion_of_isAffine i f
  have hcard : Cardinal.mk (Γ(pushout i f, ⊤)) ≤ max A.size T.size := by
    calc
      Cardinal.mk (Γ(pushout i f, ⊤)) ≤ Cardinal.mk (Γ(T, ⊤) × Γ(A, ⊤)) :=
        mk_le_prod_of_isPullback _ _ _ _
          (Stacks.Pushout.isPullback_appTop_pushout_of_isAffine i f)
      _ ≤ max A.size T.size := by
        rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
        have hA' : Cardinal.mk (Γ(A, ⊤)) ≤ A.size :=
          Scheme.mk_sections_le_size A ⟨⊤, isAffineOpen_top A⟩
        have hT' : Cardinal.mk (Γ(T, ⊤)) ≤ T.size :=
          Scheme.mk_sections_le_size T ⟨⊤, isAffineOpen_top T⟩
        rcases le_total A.size T.size with h | h
        · calc
            Cardinal.mk (Γ(T, ⊤)) * Cardinal.mk (Γ(A, ⊤)) ≤ T.size * T.size :=
              mul_le_mul' hT' (hA'.trans h)
            _ ≤ T.size :=
              (Cardinal.mul_le_max_of_aleph0_le_left
                (Scheme.aleph0_le_size T)).trans_eq (by rw [max_self])
            _ ≤ max A.size T.size := le_max_of_le_right le_rfl
        · calc
            Cardinal.mk (Γ(T, ⊤)) * Cardinal.mk (Γ(A, ⊤)) ≤ A.size * A.size :=
              mul_le_mul' (hT'.trans h) hA'
            _ ≤ A.size :=
              (Cardinal.mul_le_max_of_aleph0_le_left
                (Scheme.aleph0_le_size A)).trans_eq (by rw [max_self])
            _ ≤ max A.size T.size := le_max_left _ _
  rcases le_total A.size T.size with h | h
  · refine Scheme.size_lt_of_isAffine_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hT
      (hcard.trans ?_)
    rw [max_eq_right h]
    exact Cardinal.self_le_power _ Cardinal.one_le_aleph0
  · refine Scheme.size_lt_of_isAffine_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hA
      (hcard.trans ?_)
    rw [max_eq_left h]
    exact Cardinal.self_le_power _ Cardinal.one_le_aleph0

/-- The pushout `A ⨿_U T` formed in the category of schemes over `S`. -/
private noncomputable def pushoutOver [HasPushout i.left f.left] : Over S :=
  Over.mk (pushout.desc A.hom T.hom (i.w.trans f.w.symm))

/-- The leg of the pushout square coming from `A`. -/
private noncomputable def pushoutOverInl [HasPushout i.left f.left] :
    A ⟶ pushoutOver U A T i f :=
  Over.homMk (pushout.inl i.left f.left) (by
    change pushout.inl i.left f.left ≫
      pushout.desc A.hom T.hom (i.w.trans f.w.symm) = A.hom
    exact pushout.inl_desc _ _ _)

/-- The leg of the pushout square coming from `T`. -/
private noncomputable def pushoutOverInr [HasPushout i.left f.left] :
    T ⟶ pushoutOver U A T i f :=
  Over.homMk (pushout.inr i.left f.left) (by
    change pushout.inr i.left f.left ≫
      pushout.desc A.hom T.hom (i.w.trans f.w.symm) = T.hom
    exact pushout.inr_desc _ _ _)

/-- The pushout square over `S` commutes. -/
private theorem pushoutOver_condition [HasPushout i.left f.left] :
    i ≫ pushoutOverInl U A T i f = f ≫ pushoutOverInr U A T i f :=
  Over.OverMorphism.ext pushout.condition

/-- On global sections the pushout square of a closed immersion of affines is cartesian. -/
private theorem pushoutOver_appTop_isPullback [HasPushout i.left f.left]
    [IsClosedImmersion i.left] [IsAffine A.left] [IsAffine T.left] :
    IsPullback (pushoutOverInr U A T i f).left.appTop
      (pushoutOverInl U A T i f).left.appTop f.left.appTop i.left.appTop :=
  Stacks.Pushout.isPullback_appTop_pushout_of_isAffine i.left f.left

/-- The leg of the pushout square coming from `T` is a thickening. -/
private theorem pushoutOver_inr_isThickening [HasPushout i.left f.left]
    (hi : Stacks.Thickenings.IsThickening i.left) [IsAffine A.left] [IsAffine T.left] :
    Stacks.Thickenings.IsThickening (pushoutOverInr U A T i f).left :=
  Stacks.Pushout.isThickening_pushout_inr_of_isAffine i.left f.left hi

/-- The pushout of a closed immersion of affine schemes is affine. -/
private theorem pushoutOver_isAffine [HasPushout i.left f.left]
    [IsClosedImmersion i.left] [IsAffine A.left] [IsAffine T.left] :
    IsAffine (pushoutOver U A T i f).left :=
  Stacks.Pushout.isAffine_pushout_of_isClosedImmersion_of_isAffine i.left f.left

/-- The pushout of two objects of the site is again an object of the site. -/
private theorem pushoutOver_contains (B : AlgebraicGeometry.BigFppfSite.{u})
    [HasPushout i.left f.left] [IsClosedImmersion i.left]
    [IsAffine A.left] [IsAffine T.left]
    (hA : B.Contains A.left) (hT : B.Contains T.left) :
    B.Contains (pushoutOver U A T i f).left :=
  pushout_scheme_size_lt i.left f.left hA hT

end PushoutOver

section SiteObjects

/-- A scheme over `S` whose size meets the cutoff, regarded as an object of the big fppf
site over `S`. -/
@[implicit_reducible] public noncomputable def overSiteObj (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (A : Over S) (hA : B.Contains A.left) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage (X := B.obj hA) (Y := B.obj hS)
    (show B.inclusion.obj (B.obj hA) ⟶ B.inclusion.obj (B.obj hS) from A.hom))

/-- The underlying scheme over `S` of a site object built from a scheme over `S` is that
scheme again. -/
public theorem overSiteObj_post (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (A : Over S) (hA : B.Contains A.left) :
    (Over.post B.inclusion).obj (overSiteObj B S hS A hA) = A := by
  dsimp [overSiteObj, Over.post]
  congr 1
  show B.inclusion.map (B.inclusion.preimage
    (show B.inclusion.obj (B.obj hA) ⟶ B.inclusion.obj (B.obj hS) from A.hom)) =
      (show B.inclusion.obj (B.obj hA) ⟶ B.inclusion.obj (B.obj hS) from A.hom)
  exact B.inclusion.map_preimage _

/-- Building a site object from the underlying scheme over `S` of a site object returns it. -/
public theorem overSiteObj_post_inverse (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (Z : AlgebraicGeometry.BigFppfOver B S hS) :
    overSiteObj B S hS ((Over.post B.inclusion).obj Z) Z.left.property = Z :=
  Comma.ext rfl rfl (heq_of_eq (B.inclusion.map_injective (B.inclusion.map_preimage _)))

/-- An affine scheme over `S` in the site, as an object of the big affine fppf site. -/
@[implicit_reducible] public noncomputable def affineSiteObj
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (A : Over S)
    (hA : B.Contains A.left) [IsAffine A.left] :
    AlgebraicGeometry.BigAffineFppf B S hS :=
  ⟨overSiteObj B S hS A hA, by
    change IsAffine A.left
    infer_instance⟩

/-- A morphism of schemes over `S` between site objects, as a morphism of site objects. -/
public noncomputable def overSiteHom (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    (f : A ⟶ T) : overSiteObj B S hS A hA ⟶ overSiteObj B S hS T hT := by
  refine Over.homMk (B.inclusion.preimage
    (X := B.obj hA) (Y := B.obj hT) (show _ ⟶ _ from f.left)) ?_
  apply B.inclusion.map_injective
  change B.inclusion.map (B.inclusion.preimage
      (X := B.obj hA) (Y := B.obj hT) (show _ ⟶ _ from f.left) ≫
      B.inclusion.preimage (X := B.obj hT) (Y := B.obj hS) (show _ ⟶ _ from T.hom)) =
    B.inclusion.map (B.inclusion.preimage
      (X := B.obj hA) (Y := B.obj hS) (show _ ⟶ _ from A.hom))
  simp only [B.inclusion.map_comp, B.inclusion.map_preimage]
  exact f.w

/-- The underlying morphism of schemes over `S` of a site morphism built from one is it
again, up to the identifications of the two underlying objects. -/
public theorem overSiteHom_post (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    (f : A ⟶ T) :
    (Over.post B.inclusion).map (overSiteHom B S hS
      (hA := hA) (hT := hT) f) =
      eqToHom (overSiteObj_post B S hS A hA) ≫ f ≫
        eqToHom (overSiteObj_post B S hS T hT).symm := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  show B.inclusion.map (B.inclusion.preimage
    (X := B.obj hA) (Y := B.obj hT) (show _ ⟶ _ from f.left)) =
      (eqToHom (congrArg Over.left (overSiteObj_post B S hS A hA))) ≫
      f.left ≫
      (eqToHom (congrArg Over.left (overSiteObj_post B S hS T hT).symm))
  simp only [B.inclusion.map_preimage]
  show f.left = (eqToHom (show A.left = A.left from rfl)) ≫
    f.left ≫ (eqToHom (show T.left = T.left from rfl))
  simp

/-- A morphism of affine schemes over `S` in the site, as a morphism of the affine site. -/
public noncomputable def affineSiteHom (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    [IsAffine A.left] [IsAffine T.left] (f : A ⟶ T) :
    affineSiteObj B S hS A hA ⟶ affineSiteObj B S hS T hT :=
  (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).preimage
    (overSiteHom B S hS (hA := hA) (hT := hT) f)

/-- The underlying scheme of an affine site object is the given scheme. -/
public theorem affineSiteObj_toScheme (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (A : Over S) (hA : B.Contains A.left) [IsAffine A.left] :
    (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).obj
      (affineSiteObj B S hS A hA) = A.left := rfl

/-- An affine site morphism includes back into the site as the morphism it was built from. -/
public theorem affineSiteHom_inclusion (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    [IsAffine A.left] [IsAffine T.left] (f : A ⟶ T) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
      (affineSiteHom B S hS (hA := hA) (hT := hT) f) =
      overSiteHom B S hS (hA := hA) (hT := hT) f :=
  (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map_preimage _

/-- The underlying morphism of schemes of an affine site morphism is the given one. -/
public theorem affineSiteHom_toScheme (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    [IsAffine A.left] [IsAffine T.left] (f : A ⟶ T) :
    (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (affineSiteHom B S hS (hA := hA) (hT := hT) f) = f.left := by
  show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
    ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
      (affineSiteHom B S hS (hA := hA) (hT := hT) f)) = f.left
  rw [affineSiteHom_inclusion]
  show B.inclusion.map (B.inclusion.preimage
    (X := B.obj hA) (Y := B.obj hT) (show _ ⟶ _ from f.left)) = f.left
  exact B.inclusion.map_preimage _

/-- Passing to the affine site is compatible with composition. -/
public theorem affineSiteHom_comp (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T R : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    {hR : B.Contains R.left}
    [IsAffine A.left] [IsAffine T.left] [IsAffine R.left]
    (f : A ⟶ T) (g : T ⟶ R) :
    affineSiteHom B S hS (hA := hA) (hT := hT) f ≫
      affineSiteHom B S hS (hA := hT) (hT := hR) g =
      affineSiteHom B S hS (hA := hA) (hT := hR) (f ≫ g) := by
  apply (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map_injective
  apply (Over.post B.inclusion).map_injective
  apply Over.OverMorphism.ext
  simp only [Functor.map_comp, Over.comp_left]
  show (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (affineSiteHom B S hS (hA := hA) (hT := hT) f) ≫
      (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hT) (hT := hR) g) =
      (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hA) (hT := hR) (f ≫ g))
  rw [affineSiteHom_toScheme, affineSiteHom_toScheme, affineSiteHom_toScheme]
  rfl

/-- A commuting square of affine schemes over `S` gives a commuting square of the affine
site. -/
public theorem affineSiteHom_square (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {U A T P : Over S} {hU : B.Contains U.left} {hA : B.Contains A.left}
    {hT : B.Contains T.left} {hP : B.Contains P.left}
    [IsAffine U.left] [IsAffine A.left] [IsAffine T.left] [IsAffine P.left]
    (f : U ⟶ A) (g : U ⟶ T) (i : A ⟶ P) (j : T ⟶ P)
    (h : f ≫ i = g ≫ j) :
    affineSiteHom B S hS (hA := hU) (hT := hA) f ≫
      affineSiteHom B S hS (hA := hA) (hT := hP) i =
      affineSiteHom B S hS (hA := hU) (hT := hT) g ≫
        affineSiteHom B S hS (hA := hT) (hT := hP) j := by
  rw [affineSiteHom_comp, affineSiteHom_comp, h]

/-- A cartesian square of global sections is unchanged by passing to the affine site. -/
public theorem affineSiteHom_appTop_isPullback (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {U A T P : Over S} {hU : B.Contains U.left} {hA : B.Contains A.left}
    {hT : B.Contains T.left} {hP : B.Contains P.left}
    [IsAffine U.left] [IsAffine A.left] [IsAffine T.left] [IsAffine P.left]
    (f : U ⟶ A) (g : U ⟶ T) (i : A ⟶ P) (j : T ⟶ P)
    (hsq : IsPullback i.left.appTop j.left.appTop f.left.appTop g.left.appTop) :
    IsPullback
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hA) (hT := hP) i)).appTop)
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hT) (hT := hP) j)).appTop)
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hU) (hT := hA) f)).appTop)
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hU) (hT := hT) g)).appTop) := by
  rw [affineSiteHom_toScheme, affineSiteHom_toScheme, affineSiteHom_toScheme,
    affineSiteHom_toScheme]
  exact hsq

/-- Surjectivity on global sections is unchanged by passing to the affine site. -/
public theorem affineSiteHom_appTop_surjective (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    [IsAffine A.left] [IsAffine T.left]
    (f : A ⟶ T) (hf : Function.Surjective f.left.appTop.hom) :
    Function.Surjective
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hA) (hT := hT) f)).appTop.hom) := by
  rw [affineSiteHom_toScheme]
  exact hf

/-- Square-zeroness of the kernel on global sections is unchanged by passing to the affine
site. -/
public theorem affineSiteHom_appTop_kernel_sq (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A T : Over S} {hA : B.Contains A.left} {hT : B.Contains T.left}
    [IsAffine A.left] [IsAffine T.left]
    (f : A ⟶ T) (hf : RingHom.ker f.left.appTop.hom ^ 2 = ⊥) :
    RingHom.ker
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
        (affineSiteHom B S hS (hA := hA) (hT := hT) f)).appTop.hom) ^ 2 = ⊥ := by
  rw [affineSiteHom_toScheme]
  exact hf

end SiteObjects

section RimSchlessinger

/-- **Axiom (RS\*) applied to a square of affine site objects.** The comparison functor from
the fibre over the pushout to the two-fibre product of the other three fibres is an
equivalence as soon as the square of global sections is cartesian with one leg a square-zero
surjection. -/
private theorem fiberSquareComparison_equiv_of_RS
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) [p.IsFibered]
    (hRS : SatisfiesRSStar B S hS p hp)
    {U V W Z : AlgebraicGeometry.BigAffineFppf B S hS}
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j)
    (hsq : IsPullback
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map i).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map j).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map f).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g).appTop)
    (hsurj : Function.Surjective
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g).appTop.hom))
    (hker : RingHom.ker
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g).appTop.hom) ^ 2 = ⊥) :
    (fiberSquareComparison p (Functor.chosenPullbacks p)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map f)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map g)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map i)
      ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map j)
      (by simpa only [Functor.map_comp] using
        congrArg (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map h)).IsEquivalence :=
  hRS U V W Z f g i j h hsq hsurj hker

end RimSchlessinger

section StructureSheaf

/-- On an affine ambient scheme a first-order thickening has square-zero kernel on global
sections. -/
private theorem firstOrder_appTop_kernel_sq {X Y : Scheme.{u}} [IsAffine Y]
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    (RingHom.ker i.appTop.hom) ^ 2 = ⊥ := by
  let : IsClosedImmersion i := hi.1
  have h := congrArg (fun J : Scheme.IdealSheafData Y => J.ideal ⟨⊤, isAffineOpen_top Y⟩) hi.2
  change (i.ker.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ 2 = ⊥ at h
  rwa [Scheme.Hom.ker_apply] at h

/-- A first-order thickening of an affine scheme is surjective on global sections. -/
private theorem firstOrder_appTop_surjective {X Y : Scheme.{u}} [IsAffine Y]
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    Function.Surjective i.appTop.hom := by
  let : IsClosedImmersion i := hi.1
  exact IsClosedImmersion.isAffine_surjective_of_isAffine i |>.2

variable {S : Scheme.{u}} (U A T : Over S) (f : U ⟶ A) (g : U ⟶ T)

/-- **The leg of an affine pushout square coming from `A` is a closed immersion.** It becomes
one after composing with the symmetry of the pushout, which exchanges the two legs. -/
private theorem isClosedImmersion_pushout_inl_of_isAffine {U A T : Scheme.{u}}
    (f : U ⟶ A) (g : U ⟶ T) (hg : Stacks.Thickenings.IsThickening g)
    [IsClosedImmersion f] [IsAffine A] [IsAffine T] [HasPushout f g] :
    IsClosedImmersion (pushout.inl f g) := by
  let : IsClosedImmersion g := hg.1
  let : HasPushout g f := Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine g f
  have hrev : Stacks.Thickenings.IsThickening (pushout.inr g f) :=
    Stacks.Pushout.isThickening_pushout_inr_of_isAffine g f hg
  let : IsClosedImmersion (pushout.inl f g ≫ (pushoutSymmetry f g).hom) := by
    simpa only [inl_comp_pushoutSymmetry_hom] using hrev.1
  let : IsClosedImmersion (pushoutSymmetry f g).hom :=
    IsClosedImmersion.instOfIsIsoScheme _
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (pushoutSymmetry f g).hom

/-- **The base of the pushout square remains a first-order thickening.** The ideal of
`U ⟶ A ⨿_U T` is the direct sum of the two square-zero ideals, so it squares to zero. -/
private theorem pushoutOver_base_firstOrder
    [IsAffine U.left] [IsAffine A.left] [IsAffine T.left]
    (hf : Stacks.Thickenings.IsFirstOrderThickening f.left)
    (hg : Stacks.Thickenings.IsFirstOrderThickening g.left) :
    Stacks.Thickenings.IsFirstOrderThickening
      (letI : IsClosedImmersion f.left := hf.1
       letI : HasPushout f.left g.left :=
         Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine f.left g.left
       f.left ≫ (pushoutOverInl U A T f g).left) := by
  let : IsClosedImmersion f.left := hf.1
  let : IsClosedImmersion g.left := hg.1
  let : HasPushout f.left g.left :=
    Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine f.left g.left
  let : HasPushout g.left f.left :=
    Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine g.left f.left
  let : IsAffine (pushoutOver U A T f g).left := pushoutOver_isAffine U A T f g
  let inl := pushoutOverInl U A T f g
  let inr := pushoutOverInr U A T f g
  have hinl : IsClosedImmersion (pushout.inl f.left g.left) :=
    isClosedImmersion_pushout_inl_of_isAffine f.left g.left hg.isThickening
  have hclosed : IsClosedImmersion (f.left ≫ inl.left) := by
    let := hinl
    show IsClosedImmersion (f.left ≫ pushout.inl f.left g.left)
    infer_instance
  have hsq := pushoutOver_appTop_isPullback U A T f g
  have hsqRing : IsPullback (CommRingCat.ofHom inr.left.appTop.hom)
      (CommRingCat.ofHom inl.left.appTop.hom) (CommRingCat.ofHom g.left.appTop.hom)
      (CommRingCat.ofHom f.left.appTop.hom) := by
    simpa [inl, inr] using hsq
  have hkerTotal := pullback_comp_ker_sq inr.left.appTop.hom inl.left.appTop.hom
    g.left.appTop.hom f.left.appTop.hom hsqRing
    (firstOrder_appTop_kernel_sq g.left hg) (firstOrder_appTop_kernel_sq f.left hf)
  have hcomm : g.left.appTop.hom.comp inr.left.appTop.hom =
      f.left.appTop.hom.comp inl.left.appTop.hom :=
    RingHom.ext fun x => congrArg
      (fun k : CommRingCat.of (Γ(pushout f.left g.left, ⊤)) ⟶
        CommRingCat.of (Γ(U.left, ⊤)) => k.hom x) hsqRing.w
  have hkerBase : RingHom.ker (f.left ≫ inl.left).appTop.hom ^ 2 = ⊥ := by
    rwa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← hcomm]
  have hker : (f.left ≫ inl.left).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simpa [Scheme.ker_of_isAffine] using hkerBase
  exact ⟨hclosed, hker⟩

/-- Transporting a section along an equality of opens is restriction along the corresponding
inclusion. -/
private theorem transport_sections_apply {X : Scheme.{u}} {V W : X.Opens} (e : V = W)
    (a : Γ(X, V)) :
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (eqToHom (congrArg (fun Z : X.Opens ↦ Γ(X, Z)) e))).hom a =
      (X.presheaf.map (eqToHom e.symm).op).hom a := by
  subst e
  simp

/-- A square of natural transformations is cartesian as soon as it is cartesian at every
object. -/
private theorem isPullback_natTrans_of_app
    {C D : Type*} [Category C] [Category D]
    {P A T R : C ⥤ D} (f : P ⟶ A) (g : P ⟶ T) (h : A ⟶ R) (k : T ⟶ R)
    (hsq : ∀ V, IsPullback (f.app V) (g.app V) (h.app V) (k.app V)) :
    IsPullback f g h k := by
  have hw : f ≫ h = g ≫ k := NatTrans.ext (funext fun V => (hsq V).w)
  exact IsPullback.of_isLimit (c := PullbackCone.mk f g hw)
    (evaluationJointlyReflectsLimits _ fun V =>
      (PullbackCone.isLimitMapConeEquiv _ ((evaluation C D).obj V)).symm (hsq V).isLimit)

/-- The comorphism `𝒪_Y ⟶ f_*𝒪_X` of a morphism of schemes, as a map of sheaves of modules
over `𝒪_Y`. -/
private abbrev structureUnitMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The two ways of pushing forward around a commuting square agree. -/
private noncomputable def pushforwardSquareIso
    {U A T P : Scheme.{u}} (f : U ⟶ A) (g : U ⟶ T)
    (a : A ⟶ P) (b : T ⟶ P) (h : f ≫ a = g ≫ b) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward a ≅
      Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward b :=
  Scheme.Modules.pushforwardComp f a ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp g b).symm

/-- The comorphism of the far leg of a commuting square, pushed forward to the apex. -/
private noncomputable def pushforwardStructureMap
    {U A T P : Scheme.{u}} (f : U ⟶ A) (g : U ⟶ T)
    (a : A ⟶ P) (b : T ⟶ P) (h : f ≫ a = g ≫ b) :=
  (Scheme.Modules.pushforward a).map (structureUnitMap f) ≫
    (pushforwardSquareIso f g a b h).hom.app (SheafOfModules.unit U.ringCatSheaf)

/-- **The structure sheaf of an affine pushout is a fibre product of sheaves of modules.**
This upgrades the sections statement, which holds over every open, to a cartesian square in
the modules over the structure sheaf of the pushout. -/
private theorem pushout_modules_isPullback
    {U A T : Scheme.{u}} (f : U ⟶ A) (g : U ⟶ T)
    [IsClosedImmersion f] [IsAffine A] [IsAffine T] [HasPushout f g] :
    IsPullback (structureUnitMap (pushout.inr f g))
      (structureUnitMap (pushout.inl f g))
      ((Scheme.Modules.pushforward (pushout.inr f g)).map (structureUnitMap g))
      (pushforwardStructureMap f g (pushout.inl f g) (pushout.inr f g)
        pushout.condition) := by
  apply IsPullback.of_map_of_faithful (SheafOfModules.toSheaf (pushout f g).ringCatSheaf)
  apply IsPullback.of_map_of_faithful
    (sheafToPresheaf (Opens.grothendieckTopology ↥(pushout f g)) AddCommGrpCat)
  apply isPullback_natTrans_of_app
  intro V
  have hs := (affinePushout_structureSheaf_isPullback f g V.unop
      (Stacks.Pushout.preimage_preimage_eq_of_comm f g (pushout.inl f g) (pushout.inr f g)
        pushout.condition V.unop)).map
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  refine IsPullback.of_eq hs rfl rfl rfl ?_
  apply AddCommGrpCat.hom_ext
  ext s
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  exact transport_sections_apply
    (Stacks.Pushout.preimage_preimage_eq_of_comm f g (pushout.inl f g) (pushout.inr f g)
      pushout.condition V.unop) _

/-- **The ideal of the far leg of an affine pushout is the direct image of the given one.**
Taking kernels along the cartesian square of structure sheaves identifies the two ideals. -/
private noncomputable def pushoutKernelIso
    {U A T : Scheme.{u}} (f : U ⟶ A) (g : U ⟶ T)
    [IsClosedImmersion f] [IsAffine A] [IsAffine T] [HasPushout f g] :
    kernel (structureUnitMap (pushout.inl f g)) ≅
      (Scheme.Modules.pushforward (pushout.inr f g)).obj
        (kernel (structureUnitMap g)) := by
  let sq := (pushout_modules_isPullback f g).flip
  haveI := isIso_kernel_map_of_isPullback sq
  exact asIso (kernel.map _ _ _ _ sq.w) ≪≫
    (PreservesKernel.iso (Scheme.Modules.pushforward (pushout.inr f g))
      (structureUnitMap g)).symm

open Stacks.AlgebraicGeometry.ClosedImmersionTFAE in
/-- The structure sheaf map of the leg of an affine pushout coming from `A` is surjective,
that leg being a closed immersion. -/
private theorem pushout_structureUnitMap_epi
    {U A T : Scheme.{u}} (f : U ⟶ A) (g : U ⟶ T)
    (hg : Stacks.Thickenings.IsThickening g)
    [IsClosedImmersion f] [IsAffine A] [IsAffine T] [HasPushout f g] :
    Epi (structureUnitMap (pushout.inl f g)) := by
  have := isClosedImmersion_pushout_inl_of_isAffine f g hg
  exact epi_unitToPushforwardObjUnit_of_isClosedImmersion (pushout.inl f g)

variable {S : Scheme.{u}} (U A T : Over S) (f : U ⟶ A) (g : U ⟶ T)

/-- The structure sheaf map of `A ⟶ A ⨿_U T` is surjective. -/
private theorem pushoutOver_inl_structureUnitMap_epi
    [IsClosedImmersion f.left] [IsAffine A.left] [IsAffine T.left]
    [HasPushout f.left g.left] (hg : Stacks.Thickenings.IsThickening g.left) :
    Epi (structureUnitMap (pushoutOverInl U A T f g).left) :=
  pushout_structureUnitMap_epi f.left g.left hg

/-- A closed immersion induces an isomorphism on residue fields: the map is injective
between fields and surjective because the stalk map is. -/
private theorem residueFieldMap_bijective_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have hs : Function.Surjective (f.stalkMap x ≫ X.residue x) :=
    (X.residue_surjective x).comp (f.stalkMap_surjective x)
  rw [← Scheme.residue_residueFieldMap] at hs
  exact Function.Surjective.of_comp (show Function.Surjective
    ((f.residueFieldMap x) ∘ Y.residue (f x)) from hs)

/-- **The residue-field sheaf at a point is carried to the one at its image by a closed
immersion.** The two spectra of residue fields are identified, the residue field map being
an isomorphism, and the two structure morphisms agree over the ambient scheme. -/
private noncomputable def pushforwardResidueFieldUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) :
    (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (X.fromSpecResidueField x)).obj
          (SheafOfModules.unit (Spec (X.residueField x)).ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (Y.fromSpecResidueField (f x))).obj
        (SheafOfModules.unit (Spec (Y.residueField (f x))).ringCatSheaf) := by
  letI : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (residueFieldMap_bijective_of_isClosedImmersion f x)
  letI : IsIso (Spec.map (f.residueFieldMap x)) := inferInstance
  refine (Scheme.Modules.pushforwardComp (X.fromSpecResidueField x) f).app _ ≪≫ ?_
  refine (Scheme.Modules.pushforwardCongr
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm).app _ ≪≫ ?_
  refine (Scheme.Modules.pushforwardComp (Spec.map (f.residueFieldMap x))
    (Y.fromSpecResidueField (f x))).symm.app _ ≪≫ ?_
  exact (Scheme.Modules.pushforward (Y.fromSpecResidueField (f x))).mapIso
    (AlgebraicGeometry.pushforwardUnitIso (Spec.map (f.residueFieldMap x)))

/-- The ideal of `A ⟶ A ⨿_U T` is the direct image of the ideal of `U ⟶ T`. -/
private noncomputable def pushoutOver_inl_kernelIso
    [IsClosedImmersion f.left] [IsAffine A.left] [IsAffine T.left]
    [HasPushout f.left g.left] :
    kernel (structureUnitMap (pushoutOverInl U A T f g).left) ≅
      (Scheme.Modules.pushforward (pushoutOverInr U A T f g).left).obj
        (kernel (structureUnitMap g.left)) :=
  pushoutKernelIso f.left g.left

/-- **The ideal of `A ⟶ A ⨿_U T` is the residue field at the point of `U ⟶ T`.** The ideal
is carried over from `T` by the direct image along the other leg, which is a closed
immersion and so identifies the residue fields at corresponding points. -/
private theorem pushoutOver_inl_kernelResidueFieldUnit
    [IsAffine A.left] [IsAffine T.left]
    (hf : Stacks.Thickenings.IsThickening f.left) (x : U.left)
    (hker : Nonempty (kernel (structureUnitMap g.left) ≅
      (Scheme.Modules.pushforward (T.left.fromSpecResidueField (g.left x))).obj
        (SheafOfModules.unit (Spec (T.left.residueField (g.left x))).ringCatSheaf))) :
    Nonempty (kernel (structureUnitMap
        (letI : IsClosedImmersion f.left := hf.1
         letI : HasPushout f.left g.left :=
           Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine f.left g.left
         (pushoutOverInl U A T f g).left)) ≅
      (letI : IsClosedImmersion f.left := hf.1
       letI : HasPushout f.left g.left :=
         Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine f.left g.left
       (Scheme.Modules.pushforward
          ((pushoutOver U A T f g).left.fromSpecResidueField
            ((pushoutOverInr U A T f g).left (g.left x)))).obj
        (SheafOfModules.unit (Spec ((pushoutOver U A T f g).left.residueField
          ((pushoutOverInr U A T f g).left (g.left x)))).ringCatSheaf))) := by
  let : IsClosedImmersion f.left := hf.1
  let : HasPushout f.left g.left :=
    Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine f.left g.left
  let : IsClosedImmersion (pushoutOverInr U A T f g).left :=
    (pushoutOver_inr_isThickening U A T f g hf).1
  obtain ⟨e⟩ := hker
  exact ⟨pushoutOver_inl_kernelIso U A T f g ≪≫
    (Scheme.Modules.pushforward (pushoutOverInr U A T f g).left).mapIso e ≪≫
    pushforwardResidueFieldUnitIso (pushoutOverInr U A T f g).left (g.left x)⟩

end StructureSheaf

section CompatibleMaps

/-- The chosen pullback along two equal morphisms is compatible with the induced
isomorphism of pullback functors. -/
private theorem pullback_eqToHom_fac
    {C : Type*} [Category C] {F : Type*} [Category F]
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks) {U Z : C}
    {f g : U ⟶ Z} (h : f = g) (z : p.Fiber Z) :
    Functor.Fiber.fiberInclusion.map
        ((eqToIso (congrArg c.pullbackFunctor h)).hom.app z) ≫ c.map g z = c.map f z := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

/-- The structural isomorphism of the comparison functor is compatible with the two chosen
iterated pullbacks around the square. -/
private theorem fiberSquareComparison_iso_fac
    {C : Type*} [Category C] {F : Type*} [Category F]
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (z : p.Fiber Z) :
    Functor.Fiber.fiberInclusion.map
        ((fiberSquareComparison p c f g i j h).obj z).iso.hom ≫
      c.map g (c.obj j z) ≫ c.map j z = c.map f (c.obj i z) ≫ c.map i z := by
  show Functor.Fiber.fiberInclusion.map
    ((c.objCompIso f i z).inv ≫
      (eqToIso (congrArg c.pullbackFunctor h)).hom.app z ≫
      (c.objCompIso g j z).hom) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc, Functor.ChoiceOfPullbacks.objCompIso_hom_fac]
  rw [pullback_eqToHom_fac p c h]
  have he := c.objCompIso_hom_fac f i z
  rw [← he, ← Category.assoc, ← Functor.map_comp]
  simp

/-- **Gluing two objects along a commuting square whose comparison functor is an
equivalence.** Given arrows out of a common object over the two near legs, there is an
object over the far corner receiving compatible arrows from both. -/
private theorem exists_compatible_maps_of_fiberSquareComparison
    {C : Type*} [Category C] {F : Type*} [Category F]
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (he : (fiberSquareComparison p c f g i j h).IsEquivalence)
    (x : p.Fiber U) (a : p.Fiber V) (b : p.Fiber W)
    (α : x.1 ⟶ a.1) (hα : p.IsHomLift f α)
    (β : x.1 ⟶ b.1) (hβ : p.IsHomLift g β) :
    ∃ z : p.Fiber Z, ∃ ai : a.1 ⟶ z.1, ∃ bj : b.1 ⟶ z.1,
      p.IsHomLift i ai ∧ p.IsHomLift j bj ∧ α ≫ ai = β ≫ bj := by
  let := c.isFibered
  let := hα
  let := hβ
  let : IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid U
  let da : x ⟶ c.obj f a :=
    ⟨Functor.IsCartesian.map p f (c.map f a) α, inferInstance⟩
  let db : x ⟶ c.obj g b :=
    ⟨Functor.IsCartesian.map p g (c.map g b) β, inferInstance⟩
  let e := (asIso da).symm ≪≫ asIso db
  let pair : CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g) := ⟨a, b, e⟩
  obtain ⟨z, ⟨ez⟩⟩ := he.essSurj.mem_essImage pair
  let η := ez.inv
  let ai := Functor.Fiber.fiberInclusion.map η.fst ≫ c.map i z
  let bj := Functor.Fiber.fiberInclusion.map η.snd ≫ c.map j z
  refine ⟨z, ai, bj, ?_, ?_, ?_⟩
  · dsimp [ai]
    infer_instance
  · dsimp [bj]
    infer_instance
  · have hw := congrArg (Functor.Fiber.fiberInclusion.map) η.w
    have hda : Functor.Fiber.fiberInclusion.map da ≫ c.map f a = α :=
      Functor.IsCartesian.fac p f (c.map f a) α
    have hdb : Functor.Fiber.fiberInclusion.map db ≫ c.map g b = β :=
      Functor.IsCartesian.fac p g (c.map g b) β
    have hdem : Functor.Fiber.fiberInclusion.map da ≫
        Functor.Fiber.fiberInclusion.map e.hom =
          Functor.Fiber.fiberInclusion.map db := by
      rw [← Functor.map_comp]
      simp [e]
    have hfac := fiberSquareComparison_iso_fac p c f g i j h z
    have hwa := c.homMap_fac f η.fst
    have hwb := c.homMap_fac g η.snd
    change Functor.Fiber.fiberInclusion.map ((c.pullbackFunctor f).map η.fst ≫ _) =
      Functor.Fiber.fiberInclusion.map (e.hom ≫ (c.pullbackFunctor g).map η.snd) at hw
    simp only [Functor.map_comp] at hw
    calc
      α ≫ ai = Functor.Fiber.fiberInclusion.map da ≫
          Functor.Fiber.fiberInclusion.map ((c.pullbackFunctor f).map η.fst) ≫
          c.map f (c.obj i z) ≫ c.map i z := by
        simpa only [ai, ← hda, Category.assoc, pair,
          Functor.ChoiceOfPullbacks.pullbackFunctor, Functor.Fiber.fiberInclusion,
          fiberSquareComparison,
          CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback] using
          congrArg (fun k => Functor.Fiber.fiberInclusion.map da ≫ k ≫ c.map i z) hwa.symm
      _ = Functor.Fiber.fiberInclusion.map da ≫
          (Functor.Fiber.fiberInclusion.map ((c.pullbackFunctor f).map η.fst) ≫
          Functor.Fiber.fiberInclusion.map
            ((fiberSquareComparison p c f g i j h).obj z).iso.hom) ≫
          c.map g (c.obj j z) ≫ c.map j z := by simp only [Category.assoc, hfac]
      _ = Functor.Fiber.fiberInclusion.map db ≫ c.map g b ≫
          Functor.Fiber.fiberInclusion.map η.snd ≫ c.map j z := by
        rw [hw]
        simp only [Category.assoc]
        rw [← Category.assoc (Functor.Fiber.fiberInclusion.map da)
          (Functor.Fiber.fiberInclusion.map e.hom), hdem]
        simpa only [Category.assoc, pair, Functor.ChoiceOfPullbacks.pullbackFunctor,
          Functor.Fiber.fiberInclusion, fiberSquareComparison,
          CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback] using
          congrArg (fun k => Functor.Fiber.fiberInclusion.map db ≫ k ≫ c.map j z) hwb
      _ = β ≫ bj := by simp only [← Category.assoc, hdb, bj]

/-- A functor carries a morphism conjugated by identity-valued transports to its image. -/
private theorem map_eqToHom_comp_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X Y : C} (h₁ : X = X) (h₂ : Y = Y) (u : X ⟶ Y) :
    G.map (eqToHom h₁ ≫ u ≫ eqToHom h₂) = G.map u := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- A factorisation through identity-valued transports is a plain factorisation. -/
private theorem comp_eqToHom_of_id_comp {C : Type*} [Category C] {X Y Y' : C}
    (hY : Y = Y') {u : X ⟶ Y} {v : X ⟶ Y'}
    (h : eqToHom (rfl : X = X) ≫ u ≫ eqToHom hY = v) : u ≫ eqToHom hY = v := by
  rw [eqToHom_refl, Category.id_comp] at h
  exact h

/-- Axiom (RS\*) glues two objects over a cartesian square of affine site objects. -/
public theorem exists_compatible_maps_over_affine_pushout
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {U V W Z : AlgebraicGeometry.BigAffineFppf B S hS}
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j)
    (hsq : IsPullback
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map i).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map j).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map f).appTop
      ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g).appTop)
    (hsurj : Function.Surjective
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g).appTop.hom))
    (hker : RingHom.ker
      (((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map g).appTop.hom) ^ 2 = ⊥)
    (x : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj U))
    (a : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj V))
    (b : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj W))
    (α : x.1 ⟶ a.1)
    (hα : p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map f) α)
    (β : x.1 ⟶ b.1)
    (hβ : p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map g) β) :
    ∃ z : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj Z),
      ∃ ai : a.1 ⟶ z.1, ∃ bj : b.1 ⟶ z.1,
        p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map i) ai ∧
        p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map j) bj ∧
        α ≫ ai = β ≫ bj := by
  let : p.IsFibered := hp.isFibered
  let ι := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  exact exists_compatible_maps_of_fiberSquareComparison p hp
    (Functor.chosenPullbacks p) (ι.map f) (ι.map g) (ι.map i) (ι.map j)
    (by simpa only [Functor.map_comp] using congrArg ι.map h)
    (fiberSquareComparison_equiv_of_RS B S hS p hp hRS f g i j h hsq hsurj hker)
    x a b α hα β hβ

/-- Axiom (RS\*) glues two objects over a cartesian square of affine schemes over `S`
lying in the site. -/
public theorem exists_compatible_maps_over_scheme_square
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {U A T P : Over S} {hU : B.Contains U.left} {hA : B.Contains A.left}
    {hT : B.Contains T.left} {hP : B.Contains P.left}
    [IsAffine U.left] [IsAffine A.left] [IsAffine T.left] [IsAffine P.left]
    (f : U ⟶ A) (g : U ⟶ T) (i : A ⟶ P) (j : T ⟶ P)
    (h : f ≫ i = g ≫ j)
    (hsq : IsPullback i.left.appTop j.left.appTop f.left.appTop g.left.appTop)
    (hsurj : Function.Surjective g.left.appTop.hom)
    (hker : RingHom.ker g.left.appTop.hom ^ 2 = ⊥)
    (x : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineSiteObj B S hS U hU)))
    (a : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineSiteObj B S hS A hA)))
    (b : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (affineSiteObj B S hS T hT)))
    (α : x.1 ⟶ a.1)
    (hα : p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
      (affineSiteHom B S hS (hA := hU) (hT := hA) f)) α)
    (β : x.1 ⟶ b.1)
    (hβ : p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
      (affineSiteHom B S hS (hA := hU) (hT := hT) g)) β) :
    ∃ z : p.Fiber ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
        (affineSiteObj B S hS P hP)),
      ∃ ai : a.1 ⟶ z.1, ∃ bj : b.1 ⟶ z.1,
        p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
          (affineSiteHom B S hS (hA := hA) (hT := hP) i)) ai ∧
        p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
          (affineSiteHom B S hS (hA := hT) (hT := hP) j)) bj ∧
        α ≫ ai = β ≫ bj :=
  exists_compatible_maps_over_affine_pushout B S hS p hp hRS
    (affineSiteHom B S hS (hA := hU) (hT := hA) f)
    (affineSiteHom B S hS (hA := hU) (hT := hT) g)
    (affineSiteHom B S hS (hA := hA) (hT := hP) i)
    (affineSiteHom B S hS (hA := hT) (hT := hP) j)
    (affineSiteHom_square B S hS f g i j h)
    (affineSiteHom_appTop_isPullback B S hS f g i j hsq)
    (affineSiteHom_appTop_surjective B S hS g hsurj)
    (affineSiteHom_appTop_kernel_sq B S hS g hker)
    x a b α hα β hβ

/-- A morphism of the fibred category lies over the affine site morphism built from its
image, the two underlying site objects being the ones it was built from. -/
public theorem affineSiteHom_actual_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {x y : F}
    [IsAffine ((p ⋙ Over.post B.inclusion).obj x).left]
    [IsAffine ((p ⋙ Over.post B.inclusion).obj y).left] (f : x ⟶ y) :
    p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
      (affineSiteHom B S hS
        (A := (p ⋙ Over.post B.inclusion).obj x)
        (T := (p ⋙ Over.post B.inclusion).obj y)
        (hA := (p.obj x).left.property)
        (hT := (p.obj y).left.property) ((p ⋙ Over.post B.inclusion).map f))) f := by
  apply IsHomLift.of_fac p _ f
    (overSiteObj_post_inverse B S hS (p.obj x)).symm
    (overSiteObj_post_inverse B S hS (p.obj y)).symm
  apply (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map_injective
  show (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map _ = _
  rw [affineSiteHom_toScheme]
  simp only [Functor.map_comp, eqToHom_map]
  show ((p ⋙ Over.post B.inclusion).map f).left =
    eqToHom (show ((p ⋙ Over.post B.inclusion).obj x).left = _ from rfl) ≫
      ((p ⋙ Over.post B.inclusion).map f).left ≫ eqToHom (show _ = _ from rfl)
  rfl

/-- **Axiom (RS\*) glues two objects of the fibred category over a cartesian square.**
Given `x ⟶ a` and `x ⟶ b` whose images complete to a square over `P` which is cartesian on
global sections, with `x ⟶ b` a first-order thickening, there is an object over `P`
receiving compatible morphisms from `a` and from `b`. -/
private theorem exists_compatible_maps_over_square
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {x a b : F}
    [IsAffine ((p ⋙ Over.post B.inclusion).obj x).left]
    [IsAffine ((p ⋙ Over.post B.inclusion).obj a).left]
    [IsAffine ((p ⋙ Over.post B.inclusion).obj b).left]
    (α : x ⟶ a) (β : x ⟶ b) (P : Over S) (hP : B.Contains P.left)
    [IsAffine P.left]
    (i : (p ⋙ Over.post B.inclusion).obj a ⟶ P)
    (j : (p ⋙ Over.post B.inclusion).obj b ⟶ P)
    (h : (p ⋙ Over.post B.inclusion).map α ≫ i =
      (p ⋙ Over.post B.inclusion).map β ≫ j)
    (hsq : IsPullback i.left.appTop j.left.appTop
      ((p ⋙ Over.post B.inclusion).map α).left.appTop
      ((p ⋙ Over.post B.inclusion).map β).left.appTop)
    (hβ : Stacks.Thickenings.IsFirstOrderThickening
      ((p ⋙ Over.post B.inclusion).map β).left) :
    ∃ (z : F) (ai : a ⟶ z) (bj : b ⟶ z)
      (e : ((p ⋙ Over.post B.inclusion).obj z).left = P.left),
      ((p ⋙ Over.post B.inclusion).map ai).left ≫ eqToHom e = i.left ∧
      ((p ⋙ Over.post B.inclusion).map bj).left ≫ eqToHom e = j.left ∧
      α ≫ ai = β ≫ bj := by
  let q := p ⋙ Over.post B.inclusion
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨z, ai, bj, hai, hbj, hc⟩ := exists_compatible_maps_over_scheme_square B S hS
    p hp hRS (U := q.obj x) (A := q.obj a) (T := q.obj b) (P := P)
    (hU := (p.obj x).left.property) (hA := (p.obj a).left.property)
    (hT := (p.obj b).left.property) (hP := hP) (q.map α) (q.map β) i j h hsq
    (firstOrder_appTop_surjective _ hβ) (firstOrder_appTop_kernel_sq _ hβ)
    ⟨x, (overSiteObj_post_inverse B S hS (p.obj x)).symm⟩
    ⟨a, (overSiteObj_post_inverse B S hS (p.obj a)).symm⟩
    ⟨b, (overSiteObj_post_inverse B S hS (p.obj b)).symm⟩
    α (affineSiteHom_actual_lift B S hS p α)
    β (affineSiteHom_actual_lift B S hS p β)
  let e : (q.obj z.1).left = P.left := congrArg V.obj z.2
  have key : ∀ {c : F} {hc : B.Contains (q.obj c).left} [IsAffine (q.obj c).left]
      (k : c ⟶ z.1) (m : q.obj c ⟶ P),
      p.IsHomLift ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
        (affineSiteHom B S hS (hA := hc) (hT := hP) m)) k →
      (q.map k).left ≫ eqToHom e = m.left := by
    intro c _ _ k m hk
    let := hk
    have hh := congrArg V.map (@IsHomLift.fac _ _ _ _ p _ _ _ _ _ k hk)
    change (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (affineSiteHom B S hS m) = _ at hh
    rw [affineSiteHom_toScheme] at hh
    simp only [Functor.map_comp, eqToHom_map] at hh
    exact comp_eqToHom_of_id_comp _ hh.symm
  exact ⟨z.1, ai, bj, e, key ai i hai, key bj j hbj, hc⟩

end CompatibleMaps

section NoLocalRetraction

/-- An object `x` over `U` admits **no local retraction** along `f : x ⟶ a` at a point `u₀`
of `U` if there is no open neighbourhood of the image of `u₀` in the scheme of `a`, with a
morphism from the restriction of `a` to it back to `x`, compatible with `f` over the
intersection with `U`. -/
private abbrev HasNoLocalRetraction {F : Type*} [Category F]
    (q : F ⥤ Scheme.{u}) {x a : F} (f : x ⟶ a) (u₀ : q.obj x) : Prop :=
  ∀ (y : F) (r : y ⟶ a), IsOpenImmersion (q.map r) →
    (∃ z : q.obj y, q.map r z = q.map f u₀) →
    ∀ (z : F) (t : z ⟶ x) (s : z ⟶ y),
      IsPullback (q.map t) (q.map s) (q.map f) (q.map r) →
      ¬ ∃ b : y ⟶ x, s ≫ b = t ∧ t ≫ f = s ≫ r

/-- A category fibred in groupoids over a base with pullbacks has pullbacks. -/
private theorem hasPullbacks_of_isFiberedInGroupoids
    {C : Type*} [Category C] [HasPullbacks C]
    {F : Type*} [Category F] (p : F ⥤ C)
    (hp : p.IsFiberedInGroupoids) : HasPullbacks F := by
  let : ∀ {X Y Z : F} {f : X ⟶ Z} {g : Y ⟶ Z}, HasPullback f g :=
    fun {_ _ _} {f} {g} =>
      Functor.IsFiberedInGroupoids.hasPullback p hp f g
  exact hasPullbacks_of_hasLimit_cospan F

/-- **Absence of a local retraction is inherited by a further morphism.** A retraction on a
neighbourhood over the later object restricts, along the base change of the later morphism,
to one over the earlier object. -/
private theorem noLocalRetraction_comp
    {F : Type*} [Category F] [HasPullbacks F] (q : F ⥤ Scheme.{u})
    (hmap : ∀ {v x y z : F} {a : v ⟶ x} {b : v ⟶ y} {c : x ⟶ z} {d : y ⟶ z},
      IsPullback a b c d → IsPullback (q.map a) (q.map b) (q.map c) (q.map d))
    (hreflect : ∀ {v x y z : F} {a : v ⟶ x} {b : v ⟶ y} {c : x ⟶ z} {d : y ⟶ z},
      a ≫ c = b ≫ d → IsPullback (q.map a) (q.map b) (q.map c) (q.map d) →
      IsPullback a b c d)
    {x a b : F} (f : x ⟶ a) (g : a ⟶ b) (u₀ : q.obj x)
    (hf : HasNoLocalRetraction q f u₀) : HasNoLocalRetraction q (f ≫ g) u₀ := by
  intro y r hr hy z t s hs hret
  obtain ⟨β, hβ, hcomm⟩ := hret
  let r' : pullback g r ⟶ a := pullback.fst g r
  let k : pullback g r ⟶ y := pullback.snd g r
  have hP : IsPullback (q.map r') (q.map k) (q.map g) (q.map r) :=
    hmap (IsPullback.of_hasPullback g r)
  have hr' : IsOpenImmersion (q.map r') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hP.flip hr
  obtain ⟨w, hw⟩ := hy
  obtain ⟨w', hw', -⟩ := Scheme.exists_preimage_of_isPullback hP
    (q.map f u₀) w (by simpa only [Functor.map_comp, Scheme.Hom.comp_apply] using hw.symm)
  let t' : pullback f r' ⟶ x := pullback.fst f r'
  let s' : pullback f r' ⟶ pullback g r := pullback.snd f r'
  have hQ : IsPullback (q.map t') (q.map s') (q.map f) (q.map r') :=
    hmap (IsPullback.of_hasPullback f r')
  have hOld : IsPullback t s (f ≫ g) r := hreflect hcomm hs
  have ht' : t' ≫ f = s' ≫ r' := pullback.condition
  have hk : r' ≫ g = k ≫ r := pullback.condition
  have hc : t' ≫ (f ≫ g) = (s' ≫ k) ≫ r := by
    rw [← Category.assoc, ht', Category.assoc, hk, ← Category.assoc]
  obtain ⟨l, hl₁, hl₂⟩ := hOld.exists_lift t' (s' ≫ k) hc
  exact hf _ r' hr' ⟨w', hw'⟩ _ t' s' hQ
    ⟨k ≫ β, by rw [← Category.assoc, ← hl₂, Category.assoc, hβ, hl₁], ht'⟩

/-- Absence of a local retraction is inherited by a further morphism, for a category fibred
in groupoids over the big fppf site. -/
private theorem noLocalRetraction_comp_onSite
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {x a b : F} (f : x ⟶ a) (g : a ⟶ b)
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hf : HasNoLocalRetraction (p ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS) f u₀) :
    HasNoLocalRetraction
      (p ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS) (f ≫ g) u₀ := by
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : HasPullbacks F := hasPullbacks_of_isFiberedInGroupoids p hp
  refine noLocalRetraction_comp (p ⋙ V)
    (fun h => (hp.map_isPullback p _ _ _ _ h).map V)
    (fun h hs => hp.isPullback_of_map_isPullback h
      (IsPullback.of_map V (by simpa only [← Functor.map_comp] using congrArg p.map h) hs))
    f g u₀ hf

end NoLocalRetraction

section Extension

/-- Being a first-order thickening is transported along an identification of the target. -/
private theorem firstOrderThickening_of_comp_eqToHom
    {X Y Z : Scheme.{u}} (e : Y = Z) (f : X ⟶ Y) (g : X ⟶ Z)
    (h : f ≫ eqToHom e = g)
    (hg : Stacks.Thickenings.IsFirstOrderThickening g) :
    Stacks.Thickenings.IsFirstOrderThickening f := by
  subst e
  simp only [eqToHom_refl, Category.comp_id] at h
  exact h.symm ▸ hg

/-- The short exact sequence of structure sheaves is transported along an identification of
the target, together with the corresponding point. -/
private theorem structureUnitMap_exact_of_comp_eqToHom
    {X Y Z : Scheme.{u}} (e : Y = Z) (f : X ⟶ Y) (g : X ⟶ Z)
    (h : f ≫ eqToHom e = g) (y : Y) (z : Z) (hy : eqToHom e y = z)
    (hepi : Epi (structureUnitMap g))
    (hker : Nonempty (kernel (structureUnitMap g) ≅
      (Scheme.Modules.pushforward (Z.fromSpecResidueField z)).obj
        (SheafOfModules.unit (Spec (Z.residueField z)).ringCatSheaf))) :
    Epi (structureUnitMap f) ∧ Nonempty (kernel (structureUnitMap f) ≅
      (Scheme.Modules.pushforward (Y.fromSpecResidueField y)).obj
        (SheafOfModules.unit (Spec (Y.residueField y)).ringCatSheaf)) := by
  subst e
  simp only [eqToHom_refl, Category.comp_id] at h
  subst h
  change y = z at hy
  subst hy
  exact ⟨hepi, hker⟩

/-- **One step of the construction.** Given a first-order thickening `x ⟶ a` and a
first-order thickening `x ⟶ b` whose ideal is the residue field at `u₀` and which admits no
local retraction there, the pushout `a ⨿_x b` carries an object `z` such that `x ⟶ z` is
again a first-order thickening, the ideal of `a ⟶ z` is the residue field at `u₀`, and
`x ⟶ z` still admits no local retraction at `u₀`. -/
private theorem exists_extension_by_pushout
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {x a b : F} [IsAffine ((p ⋙ Over.post B.inclusion).obj x).left]
    (α : x ⟶ a) (β : x ⟶ b)
    (hα : Stacks.Thickenings.IsFirstOrderThickening
      ((p ⋙ Over.post B.inclusion).map α).left)
    (hβ : Stacks.Thickenings.IsFirstOrderThickening
      ((p ⋙ Over.post B.inclusion).map β).left)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hker : Nonempty (kernel (structureUnitMap
        ((p ⋙ Over.post B.inclusion).map β).left) ≅
      (Scheme.Modules.pushforward
          (((p ⋙ Over.post B.inclusion).obj b).left.fromSpecResidueField
            (((p ⋙ Over.post B.inclusion).map β).left u₀))).obj
        (SheafOfModules.unit (Spec
          (((p ⋙ Over.post B.inclusion).obj b).left.residueField
            (((p ⋙ Over.post B.inclusion).map β).left u₀))).ringCatSheaf)))
    (hbad : HasNoLocalRetraction
      (p ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS) β u₀) :
    ∃ (z : F) (ai : a ⟶ z),
      Stacks.Thickenings.IsFirstOrderThickening
        ((p ⋙ Over.post B.inclusion).map (α ≫ ai)).left ∧
      (Epi (structureUnitMap ((p ⋙ Over.post B.inclusion).map ai).left) ∧
        Nonempty (kernel (structureUnitMap
            ((p ⋙ Over.post B.inclusion).map ai).left) ≅
          (Scheme.Modules.pushforward
              (((p ⋙ Over.post B.inclusion).obj z).left.fromSpecResidueField
                (((p ⋙ Over.post B.inclusion).map (α ≫ ai)).left u₀))).obj
            (SheafOfModules.unit (Spec
              (((p ⋙ Over.post B.inclusion).obj z).left.residueField
                (((p ⋙ Over.post B.inclusion).map (α ≫ ai)).left u₀))).ringCatSheaf))) ∧
      HasNoLocalRetraction
        (p ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS) (α ≫ ai) u₀ := by
  let q := p ⋙ Over.post B.inclusion
  let U := q.obj x
  let A := q.obj a
  let T := q.obj b
  let fα := q.map α
  let gβ := q.map β
  let : IsClosedImmersion fα.left := hα.1
  let : IsAffine A.left := Stacks.Thickenings.isAffine_of_isFirstOrderThickening hα
  let : IsAffine T.left := Stacks.Thickenings.isAffine_of_isFirstOrderThickening hβ
  let : HasPushout fα.left gβ.left :=
    Stacks.Pushout.hasPushout_of_isClosedImmersion_of_isAffine fα.left gβ.left
  let P := pushoutOver U A T fα gβ
  let i := pushoutOverInl U A T fα gβ
  let j := pushoutOverInr U A T fα gβ
  have hP : B.Contains P.left :=
    pushoutOver_contains U A T fα gβ B (p.obj a).left.property (p.obj b).left.property
  let : IsAffine P.left := pushoutOver_isAffine U A T fα gβ
  have hc : fα ≫ i = gβ ≫ j := pushoutOver_condition U A T fα gβ
  obtain ⟨z, ai, bj, e, hai, hbj, hab⟩ :=
    exists_compatible_maps_over_square B S hS p hp hRS α β P hP i j hc
      (pushoutOver_appTop_isPullback U A T fα gβ).flip hβ
  have hcomp : (q.map (α ≫ ai)).left ≫ eqToHom e = fα.left ≫ i.left := by
    show (q.map (α ≫ ai)).left ≫ eqToHom e = (q.map α).left ≫ i.left
    rw [q.map_comp, Over.comp_left, Category.assoc]
    exact congrArg ((q.map α).left ≫ ·) hai
  have hpoint : eqToHom e ((q.map (α ≫ ai)).left u₀) = j.left (gβ.left u₀) := by
    rw [← Scheme.Hom.comp_apply, hcomp,
      show fα.left ≫ i.left = gβ.left ≫ j.left from congrArg (·.left) hc, Scheme.Hom.comp_apply]
  have hfirst := firstOrderThickening_of_comp_eqToHom e _ _ hcomp
    (pushoutOver_base_firstOrder U A T fα gβ hα hβ)
  have hexact := structureUnitMap_exact_of_comp_eqToHom e _ _ hai
    ((q.map (α ≫ ai)).left u₀) (j.left (gβ.left u₀)) hpoint
    (pushoutOver_inl_structureUnitMap_epi U A T fα gβ hβ.isThickening)
    (pushoutOver_inl_kernelResidueFieldUnit U A T fα gβ hα.isThickening u₀ hker)
  refine ⟨z, ai, hfirst, hexact, ?_⟩
  rw [hab]
  exact noLocalRetraction_comp_onSite B S hS p hp β bj u₀ hbad

end Extension

/-- **Stacks Project, Tag 0G2S.** Let `𝒳` be a category fibred in groupoids over the big
fppf site of a locally Noetherian scheme `S`, satisfying (RS*), and let `x` be an object of
`𝒳` over an affine scheme `U` of finite type over `S`. Let `u 0, u 1, …` be finite type
points of `U` with no specializations between distinct ones, at none of which `x` is versal.
Then there are morphisms `x ⟶ x₁ ⟶ x₂ ⟶ …` of `𝒳` over `U ⟶ U₁ ⟶ U₂ ⟶ …` over `S` such
that each `U ⟶ Uₙ₊₁` is a first order thickening, the ideal of `Uₙ ⟶ Uₙ₊₁` is the residue
field `κ(u n)`, and `x ⟶ xₙ₊₁` admits no retraction over any open neighbourhood of `u n`. -/
@[stacks 0G2S]
public theorem exists_sequence_firstOrderThickenings_without_localRetraction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (U : Over S) [IsAffine U.left] [IsLocallyNoetherian S]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U)
    (u : ℕ → U.left)
    (hfinite : ∀ n, AlgebraicGeometry.IsFiniteTypePoint (u n))
    (hincomparable : ∀ n m, n ≠ m → ¬ (u n ⤳ u m))
    (hnonversal : ∀ n,
      ¬ Deformation.Artin.IsVersalAt U (p ⋙ Over.post B.inclusion) (u n) x hx) :
    let q : F ⥤ Over S := p ⋙ Over.post B.inclusion
    ∃ (xs : ℕ → F)
      (step : ∀ n, xs n ⟶ xs (n + 1))
      (fromX : ∀ n, x ⟶ xs n),
      ∃ hzero : xs 0 = x,
        fromX 0 = eqToHom hzero.symm ∧
        (∀ n, fromX (n + 1) = fromX n ≫ step n) ∧
        (let j : ∀ n, U.left ⟶ (q.obj (xs n)).left :=
          fun n ↦ eqToHom (congrArg Over.left hx).symm ≫ (q.map (fromX n)).left
        ∀ n,
          Stacks.Thickenings.IsFirstOrderThickening (j (n + 1)) ∧
          (let i : (q.obj (xs n)).left ⟶ (q.obj (xs (n + 1))).left :=
              (q.map (step n)).left
           Epi (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ∧
           Nonempty (kernel (SheafOfModules.unitToPushforwardObjUnit
               i.toRingCatSheafHom) ≅
             (Scheme.Modules.pushforward
                 ((q.obj (xs (n + 1))).left.fromSpecResidueField (j (n + 1) (u n)))).obj
               (SheafOfModules.unit (Spec ((q.obj (xs (n + 1))).left.residueField
                 (j (n + 1) (u n)))).ringCatSheaf))) ∧
          (∀ (y : F) (r : y ⟶ xs (n + 1)),
            IsOpenImmersion (q.map r).left →
            (∃ z : (q.obj y).left,
              (q.map r).left z = j (n + 1) (u n)) →
            ∀ (z : F) (t : z ⟶ x) (s : z ⟶ y),
              IsPullback (q.map t).left (q.map s).left
                (q.map (fromX (n + 1))).left (q.map r).left →
              ¬ ∃ β : y ⟶ x,
                s ≫ β = t ∧ t ≫ fromX (n + 1) = s ≫ r)) := by
  classical
  let q : F ⥤ Over S := p ⋙ Over.post B.inclusion
  cases hx
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)) := by
    show IsAffine (q.obj x).left
    infer_instance
  let : LocallyOfFiniteType ((Over.post B.inclusion).obj (p.obj x)).hom := by
    show LocallyOfFiniteType (q.obj x).hom
    infer_instance
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Pr : ∀ {a : F}, (x ⟶ a) → Prop := fun {_} α =>
    Stacks.Thickenings.IsFirstOrderThickening (q.map α).left
  let Qr : ∀ (n : ℕ) {a b : F}, (x ⟶ a) → (a ⟶ b) → Prop :=
    fun n {_ b} α δ =>
      (Epi (structureUnitMap (q.map δ).left) ∧
        Nonempty (kernel (structureUnitMap (q.map δ).left) ≅
          (Scheme.Modules.pushforward ((q.obj b).left.fromSpecResidueField
              ((q.map (α ≫ δ)).left (u n)))).obj
            (SheafOfModules.unit (Spec ((q.obj b).left.residueField
              ((q.map (α ≫ δ)).left (u n)))).ringCatSheaf))) ∧
      HasNoLocalRetraction (p ⋙ V) (α ≫ δ) (u n)
  have hsingle (n : ℕ) : ∃ (b : F) (β : x ⟶ b),
      Stacks.Thickenings.IsFirstOrderThickening (q.map β).left ∧
      (Epi (structureUnitMap (q.map β).left) ∧
        Nonempty (kernel (structureUnitMap (q.map β).left) ≅
          (Scheme.Modules.pushforward ((q.obj b).left.fromSpecResidueField
              ((q.map β).left (u n)))).obj
            (SheafOfModules.unit (Spec ((q.obj b).left.residueField
              ((q.map β).left (u n)))).ringCatSheaf))) ∧
      HasNoLocalRetraction (p ⋙ V) β (u n) := by
    obtain ⟨T, i, b, hb, β, hβ, hi, hepi, hker, hbad⟩ :=
      exists_firstOrderThickening_without_localRetraction
        B S hS p hp hRS (p.obj x) x rfl (u n) (hfinite n) (hnonversal n)
    cases hb
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hβ
    subst hβ
    refine ⟨b, β, hi, ⟨hepi, hker⟩, ?_⟩
    intro z k hk hpoint z₀ t s hs hret
    obtain ⟨w, hw⟩ := hpoint
    obtain ⟨γ, hγ, hcc⟩ := hret
    have := hp.isStronglyCartesian k
    have := hp.isStronglyCartesian t
    have := hp.isStronglyCartesian s
    apply hbad (p.obj z) (p.map k) w hw hk z rfl k (by simp) inferInstance
    exact ⟨γ, z₀, t, s, inferInstance, inferInstance, by simpa [V] using hs, hcc, hγ⟩
  let Ar := Σ a : F, {α : x ⟶ a // Pr α}
  have hnext (n : ℕ) (a : Ar) : ∃ (b : F) (δ : a.1 ⟶ b),
      Pr (a.2.1 ≫ δ) ∧ Qr n a.2.1 δ := by
    obtain ⟨b, β, hβ, hexact, hbad⟩ := hsingle n
    exact exists_extension_by_pushout B S hS p hp hRS a.2.1 β a.2.2 hβ (u n)
      hexact.2 hbad
  choose nextObj nextMap nextFirst nextGood using hnext
  have hId : Pr (𝟙 x) := by
    show Stacks.Thickenings.IsFirstOrderThickening (q.map (𝟙 x)).left
    have hid : (q.map (𝟙 x)).left = 𝟙 (q.obj x).left :=
      congrArg (fun f : q.obj x ⟶ q.obj x => f.left) (q.map_id x)
    rw [hid]
    refine ⟨inferInstance, ?_⟩
    rw [Scheme.Hom.ker_eq_bot_of_isIso]
    ext W
    simp
  let initial : Ar := ⟨x, 𝟙 x, hId⟩
  let next (n : ℕ) (a : Ar) : Ar :=
    ⟨nextObj n a, a.2.1 ≫ nextMap n a, nextFirst n a⟩
  let seq : ℕ → Ar := Nat.rec initial next
  let xs : ℕ → F := fun n => (seq n).1
  let fromX : ∀ n, x ⟶ xs n := fun n => (seq n).2.1
  let step : ∀ n, xs n ⟶ xs (n + 1) := fun n => nextMap n (seq n)
  refine ⟨xs, step, fromX, rfl, rfl, fun _ => rfl, ?_⟩
  dsimp only
  intro n
  exact ⟨(seq (n + 1)).2.2, nextGood n (seq n)⟩

end Deformation.Artin

end
