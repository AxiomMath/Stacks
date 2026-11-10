module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.Chart
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.RingTheory.FibreProduct.IntegralClosedFibre

/-!
# Squeezing a closed subscheme of an integral morphism to its base

Let `f : X ⟶ Y` be an integral morphism of schemes and let `y : T ⟶ Y` be a closed immersion.
The fibre `X_T = X ×_Y T` sits in `X` as a closed subscheme and is integral over `T`, so the
pushout

`X' = T ⨿_{X_T} X`

exists as a scheme by [Stacks Project, Tag 0E25].  This file assembles that pushout into the
factorization `X ⟶ X' ⟶ Y` of `f` which [Stacks Project, Tag 0EDM] constructs, and proves the
three properties the source asserts of it, together with the final finiteness statement.

[Stacks Project, Tag 0EDM] is the case `T = Spec k` for a field `k`, where `y` represents a
point of `Y` with residue field `k`; the construction is carried out for a general closed
immersion because the lift of the tag to an algebraic-space target applies it over an étale
chart `U ⟶ Y`, where the point `y` pulls back to the closed subscheme `T = Spec k ×_Y U` of
`U`, which is étale over `k` and so has in general several points.  Nothing in the argument
uses that `T` is the spectrum of a field except the statement that the fibre is a *single*
point, which is `subsingleton_fibre_glueingToBase` and asks `Subsingleton T`.

## Main definitions

* `AlgebraicGeometry.glueingSituation` is the situation of [Stacks Project, Tag 0ECI] attached
  to `f` and `y`: the closed immersion `X_y ⟶ X` and the integral morphism `X_y ⟶ Spec k`.
* `AlgebraicGeometry.glueingScheme` is the pushout `X'`, with
  `AlgebraicGeometry.glueingToSource` the morphism `X ⟶ X'`,
  `AlgebraicGeometry.glueingToBase` the morphism `X' ⟶ Y`, and
  `AlgebraicGeometry.glueingPoint` the closed immersion `Spec k ⟶ X'`.

## Main results

* `AlgebraicGeometry.glueingToSource_comp_glueingToBase` and
  `AlgebraicGeometry.glueingPoint_comp_glueingToBase`: the factorization of `f`, and that the
  distinguished point lies over `y`.
* `AlgebraicGeometry.isIso_glueingToSource_restrict`: **clause (2)**, that `X ⟶ X'` is an
  isomorphism over the open complement of the fibre.
* `AlgebraicGeometry.range_glueingPoint`: **clause (3)**, that the fibre of `X' ⟶ Y` over the
  image of `y` is exactly the image of the closed immersion `T ⟶ X'`; with `T = Spec k` this
  says the fibre is a single point with residue field `k`.

## Implementation notes

The fibrewise affineness condition of Tag 0ECI is free here: the fibre of `X_T ⟶ T` over a
point `t` is carried by `X_T ⟶ X` into the preimage `f ⁻¹ᵁ V` of any affine open `V` of `Y`
containing the image of `t`, and that preimage is affine because an integral morphism is
affine.

Clause (2) is read as the source states it — `X ⟶ X'` is an isomorphism over `X' \ X'_y` —
with `X' \ X'_y` taken to be the preimage under `X' ⟶ Y` of the open complement of the closed
point which `y` represents, which is exactly the complement of the fibre.  In that form it is
`AlgebraicGeometry.pushoutInl_isIso_morphismRestrict`: the pushout agrees with `X` over every
open disjoint from the image of `Spec k`.

Clause (3) is read as an equality of subsets of `X'`, rather than as a statement about residue
fields of points: the fibre is the range of `AlgebraicGeometry.glueingPoint`, a closed
immersion whose source is `T`.  For `T = Spec k` that source has a unique point, so the fibre
is one point, and the morphism realizing it is a closed immersion from `Spec k`, so its
residue field is `k`.  Both halves are recorded separately,
`AlgebraicGeometry.subsingleton_fibre_glueingToBase` and the instance that
`AlgebraicGeometry.glueingPoint` is a closed immersion.

## References

* [Stacks Project, Tag 0EDM](https://stacks.math.columbia.edu/tag/0EDM)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
  (y : T ⟶ Y) [IsClosedImmersion y]

/-- The situation of [Stacks Project, Tag 0ECI] attached to an integral morphism `f : X ⟶ Y`
and a closed immersion `y : Spec k ⟶ Y`: the fibre `X_y` sits in `X` as a closed subscheme and
is integral over `Spec k`, over the base `Y`. -/
abbrev glueingSituation : PushoutAlongClosedImmersionAndIntegralSituation.{u} where
  S := Y
  X := X
  Y := T
  Z := pullback f y
  pX := f
  pY := y
  pZ := pullback.fst f y ≫ f
  i := pullback.fst f y
  j := pullback.snd f y
  i_over := rfl
  j_over := pullback.condition.symm
  fiber_preimage_subset_affine := by
    intro pt
    obtain ⟨V, hV, hmemV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := y pt) (U := ⊤) trivial
    refine ⟨f ⁻¹ᵁ V, hV.preimage f, fun z hz => ?_⟩
    change f (pullback.fst f y z) ∈ V
    have hfy : f (pullback.fst f y z) = y (pullback.snd f y z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [hfy, hz]
    exact hmemV

/-- The scheme `X'` of [Stacks Project, Tag 0EDM]: the pushout `Spec k ⨿_{X_y} X`. -/
abbrev glueingScheme : Scheme.{u} := pushoutScheme (glueingSituation f y)

/-- The morphism `X ⟶ X'` of [Stacks Project, Tag 0EDM]. -/
abbrev glueingToSource : X ⟶ glueingScheme f y := pushoutInl (glueingSituation f y)

/-- The morphism `X' ⟶ Y` of [Stacks Project, Tag 0EDM]. -/
abbrev glueingToBase : glueingScheme f y ⟶ Y := pushoutToBase (glueingSituation f y)

/-- The distinguished closed immersion `x' : T ⟶ X'` of [Stacks Project, Tag 0EDM], whose
source is the spectrum of the residue field `k` in the case of the source. -/
abbrev glueingPoint : T ⟶ glueingScheme f y := pushoutInr (glueingSituation f y)

/-- The factorization of `f` through `X'`. -/
theorem glueingToSource_comp_glueingToBase :
    glueingToSource f y ≫ glueingToBase f y = f :=
  (pushoutAlongClosedImmersionAndIntegral (glueingSituation f y)).isPushout.inl_desc _ _ _

/-- The distinguished point of `X'` lies over the point represented by `y`. -/
theorem glueingPoint_comp_glueingToBase :
    glueingPoint f y ≫ glueingToBase f y = y :=
  (pushoutAlongClosedImmersionAndIntegral (glueingSituation f y)).isPushout.inr_desc _ _ _

/-- The open complement in `Y` of the closed point represented by `y`. -/
def glueingAwayOpen : Y.Opens :=
  ⟨(Set.range y)ᶜ, y.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- **Clause (2) of [Stacks Project, Tag 0EDM].** The morphism `X ⟶ X'` is an isomorphism over
the open complement of the fibre `X'_y`, which is the preimage under `X' ⟶ Y` of the open
complement of the point represented by `y`. -/
theorem isIso_glueingToSource_restrict :
    IsIso (glueingToSource f y ∣_ (glueingToBase f y ⁻¹ᵁ glueingAwayOpen y)) := by
  refine pushoutInl_isIso_morphismRestrict (glueingSituation f y) _ ?_
  apply TopologicalSpace.Opens.ext
  ext pt
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hpt
  have hpt' : (glueingPoint f y ≫ glueingToBase f y) pt ∈ glueingAwayOpen y := by
    rw [Scheme.Hom.comp_apply]; exact hpt
  rw [glueingPoint_comp_glueingToBase] at hpt'
  exact hpt' ⟨pt, rfl⟩

/-- **Clause (3) of [Stacks Project, Tag 0EDM].** The fibre of `X' ⟶ Y` over the point
represented by `y` is exactly the image of the distinguished closed immersion
`Spec k ⟶ X'`. -/
theorem range_glueingPoint :
    Set.range (glueingPoint f y) =
      (glueingToBase f y) ⁻¹' Set.range y := by
  apply Set.eq_of_subset_of_subset
  · rintro p ⟨pt, rfl⟩
    refine ⟨pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, glueingPoint_comp_glueingToBase]
  · rintro p ⟨pt, hpt⟩
    rcases pushoutInl_inr_jointly_surjective (glueingSituation f y) p with ⟨x, hx⟩ | h
    · -- `p` comes from `X`; then `x` lies in the fibre, so `p` is the distinguished point.
      have hfx : f x = y pt := by
        rw [hpt, ← hx, ← Scheme.Hom.comp_apply, glueingToSource_comp_glueingToBase]
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x pt hfx
      refine ⟨pullback.snd f y z, ?_⟩
      have := (pushoutAlongClosedImmersionAndIntegral (glueingSituation f y)).isPushout.w
      have hcomm : ((glueingSituation f y).i ≫ glueingToSource f y) z =
          ((glueingSituation f y).j ≫ glueingPoint f y) z := by
        rw [this]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcomm
      change glueingPoint f y (pullback.snd f y z) = p
      rw [← hcomm, hz1, hx]
    · exact h

/-- The fibre of `X' ⟶ Y` over the image of `y` has at most one element as soon as the source
of `y` does -- in particular when it is the spectrum of a field, which is the case of
[Stacks Project, Tag 0EDM]. -/
theorem subsingleton_fibre_glueingToBase [Subsingleton T] :
    ((glueingToBase f y) ⁻¹' Set.range y).Subsingleton := by
  rw [← range_glueingPoint]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [Subsingleton.elim a b]

/-! ### Affineness and integrality of the structure morphism of a general pushout -/

section PushoutBase

variable (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})

/-- An open of the pushout whose two preimages are affine is itself affine.  This is
`Stacks.Pushout.exists_affineChart_of_isPushout` with the open prescribed rather than chosen
around a point, together with the passage from the locally ringed space chart to a scheme
chart carried out in `AlgebraicGeometry.exists_chart`. -/
theorem isAffineOpen_of_isAffineOpen_preimages (W : (pushoutScheme s).Opens)
    (hU : IsAffineOpen (pushoutInl s ⁻¹ᵁ W)) (hV : IsAffineOpen (pushoutInr s ⁻¹ᵁ W)) :
    IsAffineOpen W := by
  obtain ⟨R, -, -, g, -, -, -, -, -, hgoi, hgr⟩ :=
    Stacks.Pushout.exists_affineChart_of_isPushout s.i s.j
      (Stacks.Pushout.isPushout_map_pushoutObj s) W (pushoutInl s ⁻¹ᵁ W) (pushoutInr s ⁻¹ᵁ W)
      rfl rfl hU hV (Stacks.Pushout.pushout_preimage_eq s W)
  obtain ⟨gS, hgS⟩ : ∃ gS : Spec R ⟶ pushoutScheme s,
      Scheme.forgetToLocallyRingedSpace.map gS = g :=
    ⟨Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage g,
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _⟩
  have hoi : IsOpenImmersion gS := by rw [← hgS] at hgoi; exact hgoi
  have hrange : Set.range gS.base = (W : Set (pushoutScheme s)) :=
    (congrArg (fun k : Scheme.forgetToLocallyRingedSpace.obj (Spec R) ⟶
      Scheme.forgetToLocallyRingedSpace.obj (pushoutScheme s) ↦ Set.range k.base) hgS).trans hgr
  have hWeq : gS.opensRange = W := TopologicalSpace.Opens.ext hrange
  exact hWeq ▸ isAffineOpen_opensRange gS

/-- The first leg of the pushout followed by the structure morphism is the first structure
morphism of the span. -/
private theorem pushoutInl_comp_pushoutToBase :
    pushoutInl s ≫ pushoutToBase s = s.pX := by simp [pushoutToBase]

/-- The second leg of the pushout followed by the structure morphism is the second structure
morphism of the span. -/
private theorem pushoutInr_comp_pushoutToBase :
    pushoutInr s ≫ pushoutToBase s = s.pY := by simp [pushoutToBase]

/-- The structure morphism of the pushout is affine as soon as the two structure morphisms of
the span are: the preimage of an affine open of the base has affine preimages in `X` and in
`Y`, hence is affine. -/
theorem pushoutToBase_isAffineHom [IsAffineHom s.pX] [IsAffineHom s.pY] :
    IsAffineHom (pushoutToBase s) := by
  refine ⟨fun U hU => ?_⟩
  refine isAffineOpen_of_isAffineOpen_preimages s _ ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, pushoutInl_comp_pushoutToBase]
    exact hU.preimage s.pX
  · rw [← Scheme.Hom.comp_preimage, pushoutInr_comp_pushoutToBase]
    exact hU.preimage s.pY

/-! #### The cone-point identification -/

/-- Transporting an equality of opens through `AlgebraicGeometry.Scheme.Hom.appLE`. -/
private theorem appLE_trans_eqToHom
    {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    {V W : X.Opens} (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U) (e : V = W) :
    g.appLE U V hV ≫ eqToHom (congrArg (fun V ↦ Γ(X, V)) e) = g.appLE U W hW := by
  subst W
  simp

/-- **The cone-point identification.**  An `R`-algebra `P` sitting at the apex of a cartesian
square of rings over `f : A →ₐ[R] C` and `g : B →ₐ[R] C` is the fibre product `A ×_C B`, as an
`R`-algebra.

The same construction appears as a private step of `finiteType_of_isPullback` in
`StacksFrontier.AlgebraicGeometry.Pushout.FiniteType`; it is factored out here because the
integrality statement needs it too. -/
noncomputable def algEquivPullbackOfIsPullback
    {R A B C P : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R P]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (pA : P →ₐ[R] A) (pB : P →ₐ[R] B)
    (hPB : IsPullback (CommRingCat.ofHom pA.toRingHom) (CommRingCat.ofHom pB.toRingHom)
      (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)) :
    (f.pullback g) ≃ₐ[R] P := by
  let pc := CommRingCat.pullbackCone (CommRingCat.ofHom f.toRingHom)
    (CommRingCat.ofHom g.toRingHom)
  let lim := CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom f.toRingHom)
    (CommRingCat.ofHom g.toRingHom)
  let iso : CommRingCat.of (↥(f.pullback g)) ≅ CommRingCat.of P :=
    lim.conePointUniqueUpToIso hPB.isLimit
  let er : (↥(f.pullback g)) ≃+* P := iso.commRingCatIsoToRingEquiv
  have hIsoA : iso.hom ≫ CommRingCat.ofHom pA.toRingHom = pc.fst :=
    lim.conePointUniqueUpToIso_hom_comp hPB.isLimit WalkingCospan.left
  have hIsoB : iso.hom ≫ CommRingCat.ofHom pB.toRingHom = pc.snd :=
    lim.conePointUniqueUpToIso_hom_comp hPB.isLimit WalkingCospan.right
  have her : er.toRingHom = iso.hom.hom := rfl
  have hIsoA' : pA.toRingHom.comp er.toRingHom = pc.fst.hom := by
    rw [her]; exact congrArg CommRingCat.Hom.hom hIsoA
  have hIsoB' : pB.toRingHom.comp er.toRingHom = pc.snd.hom := by
    rw [her]; exact congrArg CommRingCat.Hom.hom hIsoB
  have hmaps : CommRingCat.ofHom (er.toRingHom.comp (algebraMap R (↥(f.pullback g)))) =
      CommRingCat.ofHom (algebraMap R P) := by
    apply hPB.hom_ext
    · apply CommRingCat.hom_ext
      change pA.toRingHom.comp (er.toRingHom.comp (algebraMap R (↥(f.pullback g)))) =
        pA.toRingHom.comp (algebraMap R P)
      rw [← RingHom.comp_assoc, hIsoA']
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]
      ext r
      rfl
    · apply CommRingCat.hom_ext
      change pB.toRingHom.comp (er.toRingHom.comp (algebraMap R (↥(f.pullback g)))) =
        pB.toRingHom.comp (algebraMap R P)
      rw [← RingHom.comp_assoc, hIsoB']
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]
      ext r
      rfl
  have he : ∀ r : R, er (algebraMap R (↥(f.pullback g)) r) = algebraMap R P r := fun r =>
    congrArg (fun h : R →+* P => h r) (congrArg CommRingCat.Hom.hom hmaps)
  exact AlgEquiv.ofRingEquiv (f := er) he

/-- The apex of a cartesian square of rings is integral over the base as soon as the two
algebras it maps to are: it is the fibre product, and
`RingFibreProduct.isIntegral_pullback` -- clause (1) of [Stacks Project, Tag 0EDM] in its local
form -- makes that integral, being a subalgebra of the product. -/
theorem isIntegral_of_isPullback
    {R A B C P : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R P]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (pA : P →ₐ[R] A) (pB : P →ₐ[R] B)
    (hPB : IsPullback (CommRingCat.ofHom pA.toRingHom) (CommRingCat.ofHom pB.toRingHom)
      (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom))
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B] :
    Algebra.IsIntegral R P :=
  have : Algebra.IsIntegral R ↥(f.pullback g) := RingFibreProduct.isIntegral_pullback f g
  Algebra.IsIntegral.of_injective
    (algEquivPullbackOfIsPullback f g pA pB hPB).symm.toAlgHom
    (algEquivPullbackOfIsPullback f g pA pB hPB).symm.injective

/-- The sections maps of two composable morphisms compose to that of any morphism equal to the
composite. -/
private theorem appLE_comp_appLE_of_comp_eq {X Y Z : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z)
    (g₃ : X ⟶ Z) (h : g₁ ≫ g₂ = g₃) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ g₂ ⁻¹ᵁ U) (e₂ : W ≤ g₁ ⁻¹ᵁ V) (e₃ : W ≤ g₃ ⁻¹ᵁ U) :
    g₂.appLE U V e₁ ≫ g₁.appLE V W e₂ = g₃.appLE U W e₃ := by
  subst h
  exact Scheme.Hom.appLE_comp_appLE ..

/-- The sections of an integral morphism over an affine open, restricted to a subset equal to the
preimage, form an integral algebra over the sections of the base. -/
private theorem isIntegral_appLE_of_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIntegralHom g]
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : V = g ⁻¹ᵁ U) :
    @Algebra.IsIntegral Γ(Y, U) Γ(X, V) _ _ (g.appLE U V hV.le).hom.toAlgebra := by
  subst hV
  let := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  refine ⟨fun x => ?_⟩
  have h := IsIntegralHom.isIntegral_app g U hU
  rw [Scheme.Hom.app_eq_appLE] at h
  exact h x

/-- **Integrality of the structure morphism of a pushout.**  In the standing situation of
[Stacks Project, Tag 0ECI], if `X` and `Y` are integral over the base then so is the pushout
`Y ⨿_Z X`.

The preimage of an affine open `U` of the base is affine by
`AlgebraicGeometry.pushoutToBase_isAffineHom`, and its ring of sections is the fibre product of
the sections on `X` and on `Y` over those on `Z` by
`AlgebraicGeometry.pushoutStructureSheaf_isPullback`; a fibre product of two integral algebras
is integral, being a subalgebra of their product. -/
theorem pushoutToBase_isIntegralHom [IsIntegralHom s.pX] [IsIntegralHom s.pY] :
    IsIntegralHom (pushoutToBase s) := by
  have hAff : IsAffineHom (pushoutToBase s) := pushoutToBase_isAffineHom s
  refine { toIsAffineHom := hAff, isIntegral_app := fun U hU => ?_ }
  set V : (pushoutScheme s).Opens := pushoutToBase s ⁻¹ᵁ U with hVdef
  have hV : IsAffineOpen V := hU.preimage (pushoutToBase s)
  set Vx : s.X.Opens := pushoutInl s ⁻¹ᵁ V with hVxdef
  set Vy : s.Y.Opens := pushoutInr s ⁻¹ᵁ V with hVydef
  set Vz : s.Z.Opens := s.j ⁻¹ᵁ Vy with hVzdef
  have hVx : IsAffineOpen Vx := hV.preimage (pushoutInl s)
  have hVy : IsAffineOpen Vy := hV.preimage (pushoutInr s)
  have he : s.i ⁻¹ᵁ Vx = Vz :=
    congrArg (fun m : s.Z ⟶ pushoutScheme s ↦ m ⁻¹ᵁ V)
      (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  have hcompX := pushoutInl_comp_pushoutToBase s
  have hcompY := pushoutInr_comp_pushoutToBase s
  have hVU : V ≤ pushoutToBase s ⁻¹ᵁ U := le_rfl
  -- `Vx` is exactly `s.pX ⁻¹ᵁ U`, and `Vy` exactly `s.pY ⁻¹ᵁ U`.
  have hVxEq : Vx = s.pX ⁻¹ᵁ U := by
    rw [hVxdef, hVdef, ← Scheme.Hom.comp_preimage, hcompX]
  have hVyEq : Vy = s.pY ⁻¹ᵁ U := by
    rw [hVydef, hVdef, ← Scheme.Hom.comp_preimage, hcompY]
  have hXbase : Vx ≤ s.pX ⁻¹ᵁ U := hVxEq.le
  have hYbase : Vy ≤ s.pY ⁻¹ᵁ U := hVyEq.le
  have hZbase : Vz ≤ s.pZ ⁻¹ᵁ U := by
    intro z hz
    change s.pZ z ∈ U
    rw [← s.j_over]
    exact hYbase hz
  have hZxbase : s.i ⁻¹ᵁ Vx ≤ s.pZ ⁻¹ᵁ U := by
    intro z hz
    change s.pZ z ∈ U
    rw [← s.i_over]
    exact hXbase hz
  let R := Γ(s.S, U)
  let A := Γ(s.X, Vx)
  let Bring := Γ(s.Y, Vy)
  let Cring := Γ(s.Z, Vz)
  let Pring := Γ(pushoutScheme s, V)
  let α : R →+* A := (s.pX.appLE U Vx hXbase).hom
  let β : R →+* Bring := (s.pY.appLE U Vy hYbase).hom
  let γ : R →+* Cring := (s.pZ.appLE U Vz hZbase).hom
  let δ : R →+* Pring := ((pushoutToBase s).appLE U V hVU).hom
  let fRing : A →+* Cring :=
    (s.i.appLE Vx (s.i ⁻¹ᵁ Vx) le_rfl ≫
      eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he)).hom
  let gRing : Bring →+* Cring := (s.j.appLE Vy Vz le_rfl).hom
  let pARing : Pring →+* A := ((pushoutInl s).appLE V Vx le_rfl).hom
  let pBRing : Pring →+* Bring := ((pushoutInr s).appLE V Vy le_rfl).hom
  let _ : Algebra R A := α.toAlgebra
  let _ : Algebra R Bring := β.toAlgebra
  let _ : Algebra R Cring := γ.toAlgebra
  let _ : Algebra R Pring := δ.toAlgebra
  have hfcomp : fRing.comp α = γ := by
    dsimp [fRing, α, γ]
    change (s.pX.appLE U Vx hXbase ≫
      s.i.appLE Vx (s.i ⁻¹ᵁ Vx) le_rfl ≫
      eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he)).hom =
      (s.pZ.appLE U Vz hZbase).hom
    apply congrArg CommRingCat.Hom.hom
    calc
      _ = ((s.i ≫ s.pX).appLE U (s.i ⁻¹ᵁ Vx) _ ≫
          eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he)) :=
        congrArg (fun m : Γ(s.S, U) ⟶ Γ(s.Z, s.i ⁻¹ᵁ Vx) ↦
          m ≫ eqToHom (congrArg (fun W : s.Z.Opens ↦ Γ(s.Z, W)) he))
          (Scheme.Hom.appLE_comp_appLE s.i s.pX U Vx (s.i ⁻¹ᵁ Vx) hXbase le_rfl)
      _ = s.pZ.appLE U Vz hZbase := by
        simpa only [s.i_over] using appLE_trans_eqToHom s.pZ U hZxbase hZbase he
  have hgcomp : gRing.comp β = γ :=
    congrArg CommRingCat.Hom.hom (appLE_comp_appLE_of_comp_eq _ _ _ s.j_over _ _ _ _ _ _)
  let fAlg : A →ₐ[R] Cring := AlgHom.mk fRing (fun r =>
    congrArg (fun m : R →+* Cring ↦ m r) hfcomp)
  let gAlg : Bring →ₐ[R] Cring := AlgHom.mk gRing (fun r =>
    congrArg (fun m : R →+* Cring ↦ m r) hgcomp)
  have hδα : pARing.comp δ = α :=
    congrArg CommRingCat.Hom.hom (appLE_comp_appLE_of_comp_eq _ _ _ hcompX _ _ _ _ _ _)
  have hδβ : pBRing.comp δ = β :=
    congrArg CommRingCat.Hom.hom (appLE_comp_appLE_of_comp_eq _ _ _ hcompY _ _ _ _ _ _)
  let pAAlg : Pring →ₐ[R] A := AlgHom.mk pARing (fun r =>
    congrArg (fun m : R →+* A ↦ m r) hδα)
  let pBAlg : Pring →ₐ[R] Bring := AlgHom.mk pBRing (fun r =>
    congrArg (fun m : R →+* Bring ↦ m r) hδβ)
  have hPB : IsPullback (CommRingCat.ofHom pAAlg.toRingHom) (CommRingCat.ofHom pBAlg.toRingHom)
      (CommRingCat.ofHom fAlg.toRingHom) (CommRingCat.ofHom gAlg.toRingHom) := by
    have hPB' := (pushoutStructureSheaf_isPullback s V).flip
    simpa [pAAlg, pBAlg, fAlg, gAlg, pARing, pBRing, fRing, gRing, Vx, Vy, Vz,
      Scheme.Hom.app_eq_appLE] using hPB'
  have hAint : Algebra.IsIntegral R A := isIntegral_appLE_of_eq s.pX U hU Vx hVxEq
  have hBint : Algebra.IsIntegral R Bring := isIntegral_appLE_of_eq s.pY U hU Vy hVyEq
  let := hAint
  let := hBint
  have hP : Algebra.IsIntegral R Pring :=
    isIntegral_of_isPullback fAlg gAlg pAAlg pBAlg hPB
  rw [Scheme.Hom.app_eq_appLE]
  exact fun x => hP.isIntegral x

/-! #### Base change of the base -/

section BaseChange

variable {Rbase : Scheme.{u}} (a : Rbase ⟶ s.S)
  [Flat a] [IsSeparated a] [LocallyOfFiniteType a] [LocallyQuasiFinite a]

/-- The base change of the pushout along `a`, as an object over the pushout. -/
abbrev pushoutSpanBaseChangeOver : Over (pushoutScheme s) :=
  Over.mk (pullback.fst (pushoutToBase s) a)

/-- The base change of the pushout along `a` is flat, separated, locally of finite type and
locally quasi-finite over the pushout, being a base change of `a`. -/
theorem pushoutSpanBaseChangeOver_props :
    Flat (pullback.fst (pushoutToBase s) a) ∧ IsSeparated (pullback.fst (pushoutToBase s) a) ∧
      LocallyOfFiniteType (pullback.fst (pushoutToBase s) a) ∧
      LocallyQuasiFinite (pullback.fst (pushoutToBase s) a) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The cartesian diagram over `s` obtained by base change along `a`. -/
noncomputable abbrev pushoutSpanBaseChangeDiagram : CartesianDiagram s :=
  pushoutBaseChangeDiagram s (pushoutSpanBaseChangeOver s a) (pushoutSpanBaseChangeOver_props s a)

/-- **The pushout of [Stacks Project, Tag 0E25] commutes with flat, separated, locally
quasi-finite base change of the base.**  Base changing the whole span along
`a : Rbase ⟶ s.S` and then forming the pushout gives the base change of the pushout, compatibly
with the projection to the original pushout.

This is [Stacks Project, Tag 0ECL], `AlgebraicGeometry.isIso_pushoutBaseChangeMap`, applied to
the base change of the pushout itself, which is flat, separated and locally quasi-finite over
the pushout because `a` is over `s.S`.

It is the step that a construction of the pushout over an étale chart of an algebraic space
needs in order to descend: the two legs of the kernel pair of the chart are separated étale
after refinement, and this identifies the pushout over the kernel pair with the base change of
the pushout over the chart. -/
theorem exists_iso_pushoutScheme_baseChange :
    ∃ e : pushoutScheme (inducedSituation s (pushoutSpanBaseChangeDiagram s a)) ≅
        pullback (pushoutToBase s) a,
      e.hom ≫ pullback.fst (pushoutToBase s) a =
        pushoutMap s (pushoutSpanBaseChangeDiagram s a) := by
  have : IsIso (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
      (pushoutSpanBaseChangeOver_props s a)) :=
    isIso_pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
      (pushoutSpanBaseChangeOver_props s a)
  refine ⟨asIso (pushoutBaseChangeMap s (pushoutSpanBaseChangeOver s a)
    (pushoutSpanBaseChangeOver_props s a)), ?_⟩
  exact pushoutBaseChangeMap_comp_hom s (pushoutSpanBaseChangeOver s a)
    (pushoutSpanBaseChangeOver_props s a)

/-! #### The pushout depends only on the span -/

/-- **The pushout of an induced situation depends only on the span, not on the vertical
morphisms of the cartesian diagram.**  Two cartesian diagrams over `s` with the same three
corners and the same closed immersion and integral morphism between them give *definitionally
equal* pushout schemes, however different their vertical morphisms to `s`.

The reason is structural: `AlgebraicGeometry.inducedSituation` takes its closed immersion and
its integral morphism from the diagram's span (`i := d.i'`, `j := d.j'`) and its structure
morphisms from the verticals, while the pushout is built from
`AlgebraicGeometry.pushoutScheme`, whose underlying span `pushoutSpan` mentions only `i` and
`j`.  The remaining difference between the two induced situations is the fibrewise affineness
condition, which is a proposition.

This is what makes a relation on a pushout a single scheme carrying two legs.  Given an
equivalence relation `R ⇉ U` downstairs whose two legs agree after composing to the base, the
span over `R` is the same for either leg, so the two base-changed diagrams share their corners
and span and differ only in their verticals; the two induced morphisms
`AlgebraicGeometry.pushoutMap` are then two morphisms out of one and the same scheme, with no
identification of situations needed.

**Why this is stated as a lemma although it is `rfl`.**  The equality holds definitionally, but
unification does not exploit it when it has to *infer* the implicit diagram.  Ascribing
`AlgebraicGeometry.triplePushoutMap m`, for `m : CartesianTripleHom dα dβ`, a type whose source
is `pushoutScheme (inducedSituation s dα)` makes the elaborator solve
`inducedSituation s ?e ≟ inducedSituation s dα` structurally, hence `?e := dα`, which
contradicts the type of `m`.  So wherever the relation morphism has to be *viewed* as an
endomorphism of the single relation scheme — which is what the transitivity and joint-monicity
conditions of an equivalence relation require — the transport along this equality has to be
written explicitly, and a bare `rfl` at the use site will not do it.  That is the reason to keep
the statement rather than inline it. -/
theorem pushoutScheme_inducedSituation_eq_of_span {XR KR ZR : Scheme.{u}} (iR : ZR ⟶ XR)
    (jR : ZR ⟶ KR) {fa fb : XR ⟶ s.X} {ga gb : KR ⟶ s.Y} {ha hb : ZR ⟶ s.Z}
    (la : IsPullback iR ha fa s.i) (ra : IsPullback jR ha ga s.j)
    (lb : IsPullback iR hb fb s.i) (rb : IsPullback jR hb gb s.j)
    [IsSeparated fa] [IsSeparated ga] [IsSeparated ha]
    [LocallyOfFiniteType fa] [LocallyOfFiniteType ga] [LocallyOfFiniteType ha]
    [LocallyQuasiFinite fa] [LocallyQuasiFinite ga] [LocallyQuasiFinite ha]
    [IsSeparated fb] [IsSeparated gb] [IsSeparated hb]
    [LocallyOfFiniteType fb] [LocallyOfFiniteType gb] [LocallyOfFiniteType hb]
    [LocallyQuasiFinite fb] [LocallyQuasiFinite gb] [LocallyQuasiFinite hb] :
    pushoutScheme (inducedSituation s
        { X' := XR, Y' := KR, Z' := ZR, i' := iR, j' := jR, f := fa, g := ga, h := ha,
          left_isPullback := la, right_isPullback := ra }) =
      pushoutScheme (inducedSituation s
        { X' := XR, Y' := KR, Z' := ZR, i' := iR, j' := jR, f := fb, g := gb, h := hb,
          left_isPullback := lb, right_isPullback := rb }) := rfl

end BaseChange

end PushoutBase

/-- **Clause (1) of [Stacks Project, Tag 0EDM].** The morphism `X' ⟶ Y` is integral. -/
theorem isIntegralHom_glueingToBase : IsIntegralHom (glueingToBase f y) :=
  pushoutToBase_isIntegralHom (glueingSituation f y)

/-- **The final statement of [Stacks Project, Tag 0EDM].** If `f` is finite and `Y` is locally
Noetherian, then `X' ⟶ Y` is finite.

A finite morphism is an integral morphism which is locally of finite type, so this is clause
(1) together with Tag 0E27, `AlgebraicGeometry.pushoutToBase_locallyOfFiniteType`: the three
schemes of the span are locally of finite type over `Y` because `f` is finite, `y` is a closed
immersion, and the fibre `X_y` maps to `X` by a closed immersion. -/
theorem isFinite_glueingToBase [IsFinite f] [IsLocallyNoetherian Y] :
    IsFinite (glueingToBase f y) := by
  have hX : LocallyOfFiniteType (glueingSituation f y).pX := inferInstanceAs
    (LocallyOfFiniteType f)
  have hY : LocallyOfFiniteType (glueingSituation f y).pY := inferInstanceAs
    (LocallyOfFiniteType y)
  have hZ : LocallyOfFiniteType (glueingSituation f y).pZ := inferInstanceAs
    (LocallyOfFiniteType (pullback.fst f y ≫ f))
  have hN : IsLocallyNoetherian (glueingSituation f y).S := inferInstanceAs
    (IsLocallyNoetherian Y)
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨isIntegralHom_glueingToBase f y, pushoutToBase_locallyOfFiniteType _⟩

end AlgebraicGeometry

end
