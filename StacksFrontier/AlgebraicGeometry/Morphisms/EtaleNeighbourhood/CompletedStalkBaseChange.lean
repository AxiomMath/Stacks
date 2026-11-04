module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletionMapBijective
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StalkHomAtHelpers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change to the completed local ring does not change the completed local ring

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, let `x ∈ X` lie over
`s ∈ S`, and let `b : Spec 𝒪^∧_{S, s} ⟶ S` be the canonical morphism. Then there is a point
`xσ` of `Z := X ×_S Spec 𝒪^∧_{S, s}` lying over `x` and over the closed point, at which the
first projection induces an *isomorphism* of completed local rings
`𝒪^∧_{X, x} ≅ 𝒪^∧_{Z, xσ}`.

## Main results

* `StacksDraft.ArtinApproximation.exists_point_bijective_completionMapAt_pullback_fst`: base
  change along `Spec 𝒪^∧_{S, s} ⟶ S` does not change the completed local ring.
* `StacksDraft.ArtinApproximation.ofHom_stalkHomAt_of_eq_specMap_fromSpecStalk`: the map of local
  rings that the morphism attached to a local homomorphism `φ : 𝒪_{Y, y} ⟶ R` induces at the
  closed point is `φ` read through `AlgebraicGeometry.stalkClosedPointIso`.

## Implementation notes

The whole argument is morphism bookkeeping; no commutative algebra is needed beyond the
uniqueness principle for maps out of an adic completion.

*The point.* Write `A := 𝒪_{X, x}`, `A^ := 𝒪^∧_{X, x}` and `Λ := 𝒪^∧_{S, s}`. The completion
`λ : Λ →+* A^` of the map of local rings of `f` makes `A^` a `Λ`-algebra, and the square of ring
maps `𝒪_{S, s} → Λ → A^` versus `𝒪_{S, s} → A → A^` commutes. Applying `Spec` and the
naturality of `fromSpecStalk` turns this into a commuting square of schemes, hence a morphism
`r : Spec A^ ⟶ Z`; the point is `xσ := r (closedPoint A^)`.

*The retraction.* The local homomorphism `ρ : 𝒪_{Z, xσ} →+* A^` attached to `r` satisfies
`ρ ∘ g^♯ = algebraMap A A^` for `g` the first projection. Since `A^` is `𝔪`-adically complete,
`ρ` extends over the completion of `𝒪_{Z, xσ}` to a map `ρ̂`, and `ρ̂` is a two-sided inverse of
`g.completionMapAt`: both composites agree with the identity on the image of the base ring, and
a map out of an adic completion along a finitely generated ideal is determined by that
restriction (`eq_adicCompletionMap_of_apply_algebraMap`).

*Why the proofs avoid `rw`.* As explained in the module docstring of
`FiniteTypeBaseApproximation.lean`, goals mentioning `Spec.map f (closedPoint R)` are not
type-correct at the transparency at which `rw` abstracts its pattern, so `congrArg`, `Eq.trans`
and `change` are used instead; that is why the two statements computing the image of the closed
point are assembled from `congrArg` and `Eq.trans` rather than rewritten.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- The completion map of the local ring of a scheme at a point, as a morphism of `CommRingCat`. -/
private abbrev completionHom (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ⟶ completedStalkObj X x :=
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))

/-- The map induced on completed local rings by a morphism carrying `x` to `y`, as a morphism of
`CommRingCat`. -/
private abbrev completionMapHom {X Y : Scheme.{u}} {x : X} {y : Y} (q : X ⟶ Y) (hq : q x = y) :
    completedStalkObj Y y ⟶ completedStalkObj X x :=
  CommRingCat.ofHom (q.completionMapAt hq)

/-- The completion map of the local ring at a point is a local homomorphism. -/
private theorem isLocalHom_completionHom (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    IsLocalHom (completionHom X x).hom :=
  inferInstanceAs (IsLocalHom (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))))

/-- **Naturality of `fromSpecStalk`, in the `stalkHomAt` spelling.** For a morphism `g` carrying
`x` to `y`, the square relating the induced map of local rings to the two canonical morphisms out
of spectra of local rings commutes. -/
private theorem specMap_stalkHomAt_fromSpecStalk {X Y : Scheme.{u}} (g : X ⟶ Y) {x : X} {y : Y}
    (hg : g x = y) :
    Spec.map (CommRingCat.ofHom (g.stalkHomAt hg)) ≫ Y.fromSpecStalk y =
      X.fromSpecStalk x ≫ g := by
  subst hg
  have h : CommRingCat.ofHom (g.stalkHomAt (rfl : g x = g x)) = g.stalkMap x := by
    simp only [Scheme.Hom.stalkHomAt, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, CommRingCat.ofHom_hom]
  rw [h]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk g

/-- `adicCompletionMap f J I hf` sends the image of `a` to the image of `f a`. -/
private theorem adicCompletionMap_apply_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (I : Ideal B) (hf : J.map f ≤ I) (a : A) :
    adicCompletionMap f J I hf (algebraMap A (AdicCompletion J A) a) =
      algebraMap B (AdicCompletion I B) (f a) :=
  RingHom.congr_fun (adicCompletionMap_comp_algebraMap f J I hf) a

/-- Two ring homomorphisms out of `AdicCompletion J A`, `J` finitely generated, which both send the
image of `a` to the image of `f a`, are equal. -/
private theorem eq_of_apply_algebraMap_eq {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (I : Ideal B) (hf : J.map f ≤ I) (hJ : J.FG)
    (g₁ g₂ : AdicCompletion J A →+* AdicCompletion I B)
    (h₁ : ∀ a, g₁ (algebraMap A (AdicCompletion J A) a) = algebraMap B (AdicCompletion I B) (f a))
    (h₂ : ∀ a, g₂ (algebraMap A (AdicCompletion J A) a) = algebraMap B (AdicCompletion I B) (f a)) :
    g₁ = g₂ :=
  (eq_adicCompletionMap_of_apply_algebraMap f J I hf hJ g₁ h₁).trans
    (eq_adicCompletionMap_of_apply_algebraMap f J I hf hJ g₂ h₂).symm

/-- **The induced map on completed local rings on the image of the base.** The map of completed
local rings of a morphism agrees, on the image of the uncompleted local ring, with the induced
map of local rings. -/
private theorem completionMapAt_algebraMap {U Y : Scheme.{u}} {u : U} {y : Y} (q : U ⟶ Y)
    (hq : q u = y) (a : Y.presheaf.stalk y) :
    q.completionMapAt hq (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) a) =
      algebraMap (U.presheaf.stalk u)
        (AdicCompletion (maximalIdeal (U.presheaf.stalk u)) (U.presheaf.stalk u))
        (q.stalkHomAt hq a) :=
  adicCompletionMap_apply_algebraMap (q.stalkHomAt hq) _ _ (IsLocalRing.map_maximalIdeal_le _) a

/-- **A local homomorphism out of a stalk is determined by the morphism it induces.** The map
`φ ↦ Spec.map φ ≫ X.fromSpecStalk x` is injective on local homomorphisms out of `𝒪_{X, x}`. -/
private theorem specMap_fromSpecStalk_injective {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (φ₁ φ₂ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ₁.hom] [IsLocalHom φ₂.hom]
    (h : Spec.map φ₁ ≫ X.fromSpecStalk x = Spec.map φ₂ ≫ X.fromSpecStalk x) : φ₁ = φ₂ :=
  (stalkCongr_comp_stalkClosedPointTo φ₁ (specMap_fromSpecStalk_closedPoint φ₁)).symm.trans
    ((stalkCongr_comp_stalkClosedPointTo_congr _ _ h
        (specMap_fromSpecStalk_closedPoint φ₁) (specMap_fromSpecStalk_closedPoint φ₂)).trans
      (stalkCongr_comp_stalkClosedPointTo φ₂ (specMap_fromSpecStalk_closedPoint φ₂)))

/-- **The map of local rings of a canonical morphism out of the spectrum of a local ring.** If
`m : Spec R' ⟶ Y` is the morphism attached to a local homomorphism `φ : 𝒪_{Y, y} ⟶ R'`, then the
map of local rings that `m` induces at the closed point is `φ` read through the identification
`𝒪_{Spec R', closedPoint R'} ≅ R'`. -/
@[ega "I 3.4.5" "partial"]
public theorem ofHom_stalkHomAt_of_eq_specMap_fromSpecStalk {Y : Scheme.{u}} {y : Y}
    {R' : CommRingCat.{u}} [IsLocalRing R'] (φ : Y.presheaf.stalk y ⟶ R') [IsLocalHom φ.hom]
    (m : Spec R' ⟶ Y) (hm : m = Spec.map φ ≫ Y.fromSpecStalk y) (h : m (closedPoint R') = y) :
    CommRingCat.ofHom (m.stalkHomAt h) = φ ≫ (stalkClosedPointIso R').inv := by
  subst hm
  refine (Iso.eq_comp_inv _).mpr ?_
  exact (Category.assoc _ _ _).trans (stalkCongr_comp_stalkClosedPointTo φ h)

/-- **A retraction on local rings completes to a two-sided inverse.** Let `h : A →+* B` be a local
homomorphism of Noetherian local rings and let `ρ : B →+* A^` be a local homomorphism into the
completion of `A` which retracts `h` (first hypothesis) and whose composite with the induced map
on completions is the completion map of `B` (second hypothesis). Then the induced map on
completions `A^ →+* B^` is bijective.

Both composites of that map with the extension of `ρ` over `B^` are the identity, because each
agrees with the identity on the image of the base ring, and a homomorphism out of an adic
completion along a finitely generated ideal is determined by that restriction. -/
private theorem bijective_adicCompletionMap_of_retraction
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (h : A →+* B) [IsLocalHom h]
    (ρ : B →+* AdicCompletion (maximalIdeal A) A) [IsLocalHom ρ]
    (hρh : ρ.comp h = algebraMap A (AdicCompletion (maximalIdeal A) A))
    (hhρ : (adicCompletionMap h (maximalIdeal A) (maximalIdeal B)
          (map_maximalIdeal_le h)).comp ρ =
      algebraMap B (AdicCompletion (maximalIdeal B) B)) :
    Function.Bijective
      (adicCompletionMap h (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le h)) := by
  have hcomplete : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal A) A))
      (AdicCompletion (maximalIdeal A) A) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact AdicCompletion.isAdicComplete_self _ (maximalIdeal A).fg_of_isNoetherianRing
  have hofbij : Function.Bijective (algebraMap (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal (AdicCompletion (maximalIdeal A) A))
        (AdicCompletion (maximalIdeal A) A))) :=
    AdicCompletion.of_bijective _ _
  obtain ⟨einv, heinv⟩ :
      ∃ einv : AdicCompletion (maximalIdeal (AdicCompletion (maximalIdeal A) A))
          (AdicCompletion (maximalIdeal A) A) →+* AdicCompletion (maximalIdeal A) A,
        ∀ y : AdicCompletion (maximalIdeal A) A,
          einv (algebraMap (AdicCompletion (maximalIdeal A) A) _ y) = y :=
    ⟨(RingEquiv.ofBijective _ hofbij).symm,
      fun y => (RingEquiv.ofBijective _ hofbij).symm_apply_apply y⟩
  obtain ⟨ρhat, hρhat⟩ :
      ∃ ρhat : AdicCompletion (maximalIdeal B) B →+* AdicCompletion (maximalIdeal A) A,
        ∀ c : B, ρhat (algebraMap B (AdicCompletion (maximalIdeal B) B) c) = ρ c := by
    refine ⟨einv.comp (adicCompletionMap ρ (maximalIdeal B)
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (map_maximalIdeal_le ρ)),
      fun c => ?_⟩
    show einv (adicCompletionMap ρ _ _ _ (algebraMap B _ c)) = ρ c
    rw [adicCompletionMap_apply_algebraMap]
    exact heinv (ρ c)
  have hidA : (maximalIdeal A).map (RingHom.id A) ≤ maximalIdeal A :=
    le_of_eq (Ideal.map_id _)
  have hidB : (maximalIdeal B).map (RingHom.id B) ≤ maximalIdeal B :=
    le_of_eq (Ideal.map_id _)
  have hleft : ρhat.comp (adicCompletionMap h (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le h)) = RingHom.id (AdicCompletion (maximalIdeal A) A) := by
    refine eq_of_apply_algebraMap_eq (RingHom.id A) (maximalIdeal A) (maximalIdeal A) hidA
      (maximalIdeal A).fg_of_isNoetherianRing _ _ (fun a => ?_) (fun _ => rfl)
    show ρhat (adicCompletionMap h _ _ _
      (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) = _
    rw [adicCompletionMap_apply_algebraMap, hρhat (h a)]
    exact RingHom.congr_fun hρh a
  have hright : (adicCompletionMap h (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le h)).comp ρhat = RingHom.id (AdicCompletion (maximalIdeal B) B) := by
    refine eq_of_apply_algebraMap_eq (RingHom.id B) (maximalIdeal B) (maximalIdeal B) hidB
      (maximalIdeal B).fg_of_isNoetherianRing _ _ (fun c => ?_) (fun _ => rfl)
    show adicCompletionMap h (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le h)
      (ρhat (algebraMap B (AdicCompletion (maximalIdeal B) B) c)) = _
    rw [hρhat c]
    exact RingHom.congr_fun hhρ c
  exact Function.bijective_iff_has_inverse.mpr
    ⟨ρhat, fun z => RingHom.congr_fun hleft z, fun z => RingHom.congr_fun hright z⟩

/-- **Base change along `Spec 𝒪^∧_{S, s} ⟶ S` does not change the completed local ring.** Let
`f : X ⟶ S` be locally of finite type with `S` locally Noetherian, let `x ∈ X` lie over `s ∈ S`,
and let `b : Spec 𝒪^∧_{S, s} ⟶ S` be the canonical morphism. Then `X ×_S Spec 𝒪^∧_{S, s}` has a
point `xσ` lying over `x` and over the closed point of `Spec 𝒪^∧_{S, s}`, at which the first
projection induces a bijection `𝒪^∧_{X, x} → 𝒪^∧_{X ×_S Spec 𝒪^∧_{S, s}, xσ}`. -/
public theorem exists_point_bijective_completionMapAt_pullback_fst
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (x : X) (s : S) (hfx : f x = s)
    (b : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s))) ⟶ S)
    (hb : b = Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s) :
    ∃ (xσ : ↥(pullback f b)) (hxσ : pullback.fst f b xσ = x),
      pullback.snd f b xσ = closedPoint _ ∧
      Function.Bijective ((pullback.fst f b).completionMapAt hxσ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (pullback f b) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f b)
  have := isLocalHom_completionHom X x
  have := isLocalHom_completionHom S s
  have : IsLocalHom (completionMapHom f hfx).hom :=
    AdicCompletion.isLocalHom_adicCompletionMap (f.stalkHomAt hfx)
  have hb' : b = Spec.map (completionHom S s) ≫ S.fromSpecStalk s := hb
  have hbs : b (closedPoint (completedStalkObj S s)) = s :=
    (congrArg (fun φ : Spec (completedStalkObj S s) ⟶ S =>
        φ (closedPoint (completedStalkObj S s))) hb').trans
      (specMap_fromSpecStalk_closedPoint (completionHom S s))
  have hring : CommRingCat.ofHom (f.stalkHomAt hfx) ≫ completionHom X x =
      completionHom S s ≫ completionMapHom f hfx :=
    congrArg CommRingCat.ofHom
      (adicCompletionMap_comp_algebraMap (f.stalkHomAt hfx)
        (maximalIdeal (S.presheaf.stalk s)) (maximalIdeal (X.presheaf.stalk x))
        (IsLocalRing.map_maximalIdeal_le _)).symm
  have hsq : (Spec.map (completionHom X x) ≫ X.fromSpecStalk x) ≫ f =
      Spec.map (completionMapHom f hfx) ≫ b := by
    rw [hb', Category.assoc, ← specMap_stalkHomAt_fromSpecStalk f hfx,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
  obtain ⟨r, hrfst, hrsnd⟩ :
      ∃ r : Spec (completedStalkObj X x) ⟶ pullback f b,
        r ≫ pullback.fst f b = Spec.map (completionHom X x) ≫ X.fromSpecStalk x ∧
          r ≫ pullback.snd f b = Spec.map (completionMapHom f hfx) :=
    ⟨pullback.lift _ _ hsq, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  set xσ := r (closedPoint (completedStalkObj X x)) with hxσdef
  have hxσ : pullback.fst f b xσ = x :=
    (congrArg (fun φ : Spec (completedStalkObj X x) ⟶ X =>
        φ (closedPoint (completedStalkObj X x))) hrfst).trans
      (specMap_fromSpecStalk_closedPoint (completionHom X x))
  have hπ : pullback.snd f b xσ = closedPoint (completedStalkObj S s) :=
    (congrArg (fun φ : Spec (completedStalkObj X x) ⟶ Spec (completedStalkObj S s) =>
      φ (closedPoint (completedStalkObj X x))) hrsnd).trans Spec_closedPoint
  refine ⟨xσ, hxσ, hπ, ?_⟩
  have : IsLocalHom (Scheme.stalkClosedPointTo r).hom :=
    Scheme.isLocalHom_stalkClosedPointTo r
  have : IsLocalHom (completionMapHom (pullback.fst f b) hxσ).hom :=
    AdicCompletion.isLocalHom_adicCompletionMap ((pullback.fst f b).stalkHomAt hxσ)
  have := isLocalHom_completionHom (pullback f b) xσ
  have : IsLocalHom (Scheme.stalkClosedPointTo r ≫
      completionMapHom (pullback.fst f b) hxσ).hom := RingHom.isLocalHom_comp _ _
  have : IsLocalHom (((pullback.fst f b).stalkHomAt hxσ).comp (f.stalkHomAt hfx)) :=
    RingHom.isLocalHom_comp _ _
  have hbstalk : CommRingCat.ofHom (b.stalkHomAt hbs) =
      completionHom S s ≫ (stalkClosedPointIso (completedStalkObj S s)).inv :=
    ofHom_stalkHomAt_of_eq_specMap_fromSpecStalk (completionHom S s) b hb' hbs
  have hcond : pullback.snd f b ≫ b = pullback.fst f b ≫ f := pullback.condition.symm
  have hpt1 : (pullback.snd f b ≫ b) xσ = s := (congrArg (fun z => b z) hπ).trans hbs
  have hpt2 : (pullback.fst f b ≫ f) xσ = s := (congrArg (fun z => f z) hxσ).trans hfx
  have hτeq : ((pullback.snd f b).stalkHomAt hπ).comp (b.stalkHomAt hbs) =
      ((pullback.fst f b).stalkHomAt hxσ).comp (f.stalkHomAt hfx) :=
    (Scheme.Hom.stalkHomAt_comp (pullback.snd f b) b hπ hbs).symm.trans
      ((stalkHomAt_congr hcond hpt1 hpt2).trans
        (Scheme.Hom.stalkHomAt_comp (pullback.fst f b) f hxσ hfx))
  have hτle : (maximalIdeal (S.presheaf.stalk s)).map
      (((pullback.fst f b).stalkHomAt hxσ).comp (f.stalkHomAt hfx)) ≤
      maximalIdeal ((pullback f b).presheaf.stalk xσ) := IsLocalRing.map_maximalIdeal_le _
  have hsndlegRing : ((pullback.fst f b).completionMapAt hxσ).comp (f.completionMapAt hfx) =
      (algebraMap ((pullback f b).presheaf.stalk xσ)
          (AdicCompletion (maximalIdeal ((pullback f b).presheaf.stalk xσ))
            ((pullback f b).presheaf.stalk xσ))).comp
        (((pullback.snd f b).stalkHomAt hπ).comp
          (stalkClosedPointIso (completedStalkObj S s)).inv.hom) := by
    refine eq_of_apply_algebraMap_eq
      (((pullback.fst f b).stalkHomAt hxσ).comp (f.stalkHomAt hfx))
      (maximalIdeal (S.presheaf.stalk s)) (maximalIdeal ((pullback f b).presheaf.stalk xσ)) hτle
      (maximalIdeal (S.presheaf.stalk s)).fg_of_isNoetherianRing _ _ (fun a => ?_) (fun a => ?_)
    · show (pullback.fst f b).completionMapAt hxσ
        (f.completionMapAt hfx (algebraMap (S.presheaf.stalk s) _ a)) = _
      rw [completionMapAt_algebraMap f hfx a,
        completionMapAt_algebraMap (pullback.fst f b) hxσ (f.stalkHomAt hfx a)]
      rfl
    · have e3 : (stalkClosedPointIso (completedStalkObj S s)).inv.hom
          (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) a) =
          b.stalkHomAt hbs a :=
        (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hbstalk) a).symm
      show algebraMap ((pullback f b).presheaf.stalk xσ) _
        ((pullback.snd f b).stalkHomAt hπ
          ((stalkClosedPointIso (completedStalkObj S s)).inv.hom
            (algebraMap (S.presheaf.stalk s) _ a))) = _
      rw [e3]
      exact congrArg (fun z => algebraMap ((pullback f b).presheaf.stalk xσ)
        (AdicCompletion (maximalIdeal ((pullback f b).presheaf.stalk xσ))
          ((pullback f b).presheaf.stalk xσ)) z) (RingHom.congr_fun hτeq a)
  have hsndleg : completionMapHom f hfx ≫ completionMapHom (pullback.fst f b) hxσ =
      ((stalkClosedPointIso (completedStalkObj S s)).inv ≫
          CommRingCat.ofHom ((pullback.snd f b).stalkHomAt hπ)) ≫
        completionHom (pullback f b) xσ :=
    CommRingCat.hom_ext_iff.mpr hsndlegRing
  have hkey : Scheme.stalkClosedPointTo r ≫ completionMapHom (pullback.fst f b) hxσ =
      completionHom (pullback f b) xσ := by
    refine specMap_fromSpecStalk_injective _ _ ?_
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hrfst, ← specMap_stalkHomAt_fromSpecStalk (pullback.fst f b) hxσ,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      exact congrArg (fun z => Spec.map z ≫ X.fromSpecStalk x) (congrArg CommRingCat.ofHom
        (adicCompletionMap_comp_algebraMap ((pullback.fst f b).stalkHomAt hxσ)
          (maximalIdeal (X.presheaf.stalk x))
          (maximalIdeal ((pullback f b).presheaf.stalk xσ))
          (IsLocalRing.map_maximalIdeal_le _)))
    · simp only [Category.assoc]
      rw [hrsnd, ← specMap_stalkHomAt_fromSpecStalk (pullback.snd f b) hπ,
        ← Spec_stalkClosedPointIso]
      simp only [← Spec.map_comp]
      exact congrArg (fun z => Spec.map z) hsndleg
  exact bijective_adicCompletionMap_of_retraction ((pullback.fst f b).stalkHomAt hxσ)
    (Scheme.stalkClosedPointTo r).hom
    (stalkClosedPointTo_comp_stalkHomAt r (pullback.fst f b) (completionHom X x) hrfst hxσ)
    (CommRingCat.hom_ext_iff.mp hkey)

end StacksDraft.ArtinApproximation

end
