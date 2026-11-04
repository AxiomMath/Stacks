module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximationComplete
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StalkHomAtHelpers
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# A common elementary étale neighbourhood over the completed local ring of the base

This file performs the step of Tag 0GDX which chooses the pointed scheme `(U, u)` sitting in a
diagram `(X_σ, x_σ) ← (U, u) → (Y_σ, y_σ)` of elementary étale neighbourhoods, where `X_σ` and
`Y_σ` are the base changes of `X ⟶ S` and `Y ⟶ T` along the two morphisms
`Spec Λ ⟶ S` and `Spec Λ ⟶ T` out of the spectrum of the completed local ring
`Λ := 𝒪^∧_{S, s}`.

## Main results

* `StacksDraft.ArtinApproximation.exists_common_neighborhood_of_bijective_completionMapAt`: Tag
  0CAV applied over the base `Spec Λ`, with its hypothesis on the completed local rings supplied
  by an isomorphism `φ` recorded over `S` instead.

## Implementation notes

Tag 0CAV over `Spec Λ` is
`StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_over_spec_complete`; the
base `Spec Λ` is the spectrum of a complete Noetherian local ring, so that specialization applies
with no side conditions. Its hypothesis `hΦ` asks the isomorphism of completed local rings to be
compatible with the two maps out of the local ring of the *base* `Spec Λ` at the common image
point, while the datum available from Tag 0GDX is the compatibility `hφ` with the two maps out of
`𝒪_{S, s}`. Three ingredients bridge them.

*The isomorphism itself.* The first projection `X_σ ⟶ X` induces a bijection of completed local
rings by hypothesis (`hbij`), so `φ` transports to an isomorphism `𝒪^∧_{X_σ, x_σ} ≅
𝒪^∧_{Y_σ, y_σ}` along its inverse.

*The local ring of `Spec Λ` at the closed point is `Λ`.* This is Mathlib's
`AlgebraicGeometry.stalkClosedPointIso`; the two maps of 0CAV's hypothesis are maps out of the
stalk at the image point, which is the closed point by hypothesis, so the comparison may be
tested after composition with the surjection `Λ → 𝒪_{Spec Λ, closed point}`. Transporting the
stalk from the image point to the closed point is `comp_stalkHomAt_eq_of_comp_stalkHomAt_eq`,
which is stated for a *variable* point so that `subst` can fire — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteTypeBaseApproximation` for why
`rw` cannot be used on goals mentioning `closedPoint`.

*Agreement on `𝒪_{S, s}` implies agreement on `Λ`.* A ring homomorphism out of
`AdicCompletion J A` is determined by its restriction to the image of `A` when `J` is finitely
generated (`eq_adicCompletionMap_of_apply_algebraMap`), and `𝔪_{S, s}` is finitely generated
because `S` is locally Noetherian. The two maps `Λ → 𝒪^∧_{Y_σ, y_σ}` to be compared therefore
agree as soon as they agree on the image of `𝒪_{S, s}`, which is what `hφ` provides once the
compatibility `pullback.condition` of the base change is read on local rings. This reduction is
isolated as the purely ring-theoretic `adicCompletion_comp_eq_of_comp_algebraMap_eq`.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CAV](https://stacks.math.columbia.edu/tag/0CAV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- **The stalk map of the canonical morphism `Spec R ⟶ X` attached to `f : 𝒪_{X, x} ⟶ R`.** At
the closed point of `Spec R` it is `f` followed by the canonical identification of `R` with the
local ring of `Spec R` at its closed point. -/
private theorem stalkHomAt_specMap_fromSpecStalk {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom]
    (h : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x) :
    (Spec.map f ≫ X.fromSpecStalk x).stalkHomAt h =
      (stalkClosedPointIso R).inv.hom.comp f.hom :=
  congrArg CommRingCat.Hom.hom ((Iso.eq_comp_inv _).mpr
    ((Category.assoc _ _ _).trans (stalkCongr_comp_stalkClosedPointTo f h)))

/-- The map of local rings induced by a morphism at the image of a point, read with the trivial
transport, is the stalk map itself. -/
private theorem stalkHomAt_rfl {W V : Scheme.{u}} (q : W ⟶ V) (w : W) :
    q.stalkHomAt (rfl : q w = q w) = (q.stalkMap w).hom := by
  refine congrArg CommRingCat.Hom.hom ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]

/-- **Transporting an equality of maps out of a stalk along an equality of points.** Two
composites out of the local ring at a point `p`, read through transports from two morphisms
hitting `p`, agree as soon as they agree when `p` is replaced by a point `z` equal to it.

The target point is a variable so that `subst` can fire; the statement is used with `z` the closed
point of the spectrum of a local ring, where `rw` would not. -/
private theorem comp_stalkHomAt_eq_of_comp_stalkHomAt_eq {V W W' : Scheme.{u}} {C : Type u}
    [CommRing C] {q : W ⟶ V} {q' : W' ⟶ V} {w : W} {w' : W'} {p z : V}
    (h : q w = p) (h' : q' w' = p) (hz : p = z)
    {g : W.presheaf.stalk w →+* C} {g' : W'.presheaf.stalk w' →+* C}
    (hcomp : g.comp (q.stalkHomAt (h.trans hz)) = g'.comp (q'.stalkHomAt (h'.trans hz))) :
    g.comp (q.stalkHomAt h) = g'.comp (q'.stalkHomAt h') := by
  subst hz
  exact hcomp

/-- **The ring-theoretic core of the comparison.** Let `J ⊆ A` be a finitely generated ideal, let
`a₁ : A →+* P`, `a₂ : P →+* Q` and `a₃ : A →+* B` be ring homomorphisms, and let
`ρ : AdicCompletion J A →+* B` and `ρ' : AdicCompletion J A →+* Q` restrict on the image of `A`
to `a₃` and to `a₂ ∘ a₁`. Suppose `ι : P^∧ →+* Q^∧` is bijective and compatible with `a₂`, and
`φ : P^∧ ≃+* B^∧` is compatible with `a₁` and `a₃`. Then the isomorphism `φ ∘ ι⁻¹ : Q^∧ ≅ B^∧` is
compatible with `ρ'` and `ρ`.

Both sides are ring homomorphisms out of `AdicCompletion J A` agreeing with `a₃` on the image of
`A`, hence both are `adicCompletionMap a₃` by
`eq_adicCompletionMap_of_apply_algebraMap`. -/
private theorem adicCompletion_comp_eq_of_comp_algebraMap_eq
    {A P Q B : Type u} [CommRing A] [CommRing P] [CommRing Q] [CommRing B]
    (J : Ideal A) (hJ : J.FG) {IP : Ideal P} {IQ : Ideal Q} {IB : Ideal B}
    {a₁ : A →+* P} {a₂ : P →+* Q} {a₃ : A →+* B}
    {ρ' : AdicCompletion J A →+* Q} {ρ : AdicCompletion J A →+* B}
    (hρ' : ρ'.comp (algebraMap A (AdicCompletion J A)) = a₂.comp a₁)
    (hρ : ρ.comp (algebraMap A (AdicCompletion J A)) = a₃) (ha₃ : J.map a₃ ≤ IB)
    {ι : AdicCompletion IP P →+* AdicCompletion IQ Q} (hbij : Function.Bijective ι)
    (hι : ι.comp (algebraMap P (AdicCompletion IP P)) =
      (algebraMap Q (AdicCompletion IQ Q)).comp a₂)
    (φ : AdicCompletion IP P ≃+* AdicCompletion IB B)
    (hφ : φ.toRingHom.comp ((algebraMap P (AdicCompletion IP P)).comp a₁) =
      (algebraMap B (AdicCompletion IB B)).comp a₃) :
    ((RingEquiv.ofBijective ι hbij).symm.trans φ).toRingHom.comp
        ((algebraMap Q (AdicCompletion IQ Q)).comp ρ') =
      (algebraMap B (AdicCompletion IB B)).comp ρ := by
  have hleft : ∀ a : A,
      ((RingEquiv.ofBijective ι hbij).symm.trans φ).toRingHom.comp
          ((algebraMap Q (AdicCompletion IQ Q)).comp ρ')
            (algebraMap A (AdicCompletion J A) a) =
        algebraMap B (AdicCompletion IB B) (a₃ a) := fun a => by
    have h1 : ρ' (algebraMap A (AdicCompletion J A) a) = a₂ (a₁ a) :=
      RingHom.congr_fun hρ' a
    have h2 : algebraMap Q (AdicCompletion IQ Q) (a₂ (a₁ a)) =
        ι (algebraMap P (AdicCompletion IP P) (a₁ a)) :=
      (RingHom.congr_fun hι (a₁ a)).symm
    have h3 : (RingEquiv.ofBijective ι hbij).symm
        (ι (algebraMap P (AdicCompletion IP P) (a₁ a))) =
        algebraMap P (AdicCompletion IP P) (a₁ a) :=
      (RingEquiv.ofBijective ι hbij).symm_apply_apply _
    have h4 : φ (algebraMap P (AdicCompletion IP P) (a₁ a)) =
        algebraMap B (AdicCompletion IB B) (a₃ a) := RingHom.congr_fun hφ a
    show φ ((RingEquiv.ofBijective ι hbij).symm
      (algebraMap Q (AdicCompletion IQ Q) (ρ' (algebraMap A (AdicCompletion J A) a)))) = _
    rw [h1, h2, h3, h4]
  have hright : ∀ a : A, (algebraMap B (AdicCompletion IB B)).comp ρ
      (algebraMap A (AdicCompletion J A) a) = algebraMap B (AdicCompletion IB B) (a₃ a) :=
    fun a => congrArg (algebraMap B (AdicCompletion IB B)) (RingHom.congr_fun hρ a)
  rw [eq_adicCompletionMap_of_apply_algebraMap a₃ J IB ha₃ hJ _ hleft,
    eq_adicCompletionMap_of_apply_algebraMap a₃ J IB ha₃ hJ _ hright]

/-- A morphism carrying a point to a point, followed by a morphism carrying that point to a
third, carries the first point to the third. -/
private theorem comp_apply_eq {W V Z : Scheme.{u}} (m : W ⟶ V) (n : V ⟶ Z) {w : W} {v : V}
    {z : Z} (hm : m w = v) (hn : n v = z) : (m ≫ n) w = z := by
  subst hm
  exact hn

/-- **The hypothesis of Tag 0CAV over the base `V`, from the compatibility over `S`.** Let
`bS : V ⟶ S` carry a point `c` to `s`, let `Xσ ⟶ V` and `Yσ ⟶ V` carry points `xσ` and `yσ` to
`c`, and let `Xσ ⟶ X` be compatible with `fX : X ⟶ S`, as in a base change along `bS`. Suppose
the local ring of `V` at `c` receives `𝒪^∧_{S, s}` surjectively, compatibly with `bS` on local
rings — which happens for `V = Spec 𝒪^∧_{S, s}` and `c` its closed point. Then an isomorphism
`φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Yσ, yσ}` compatible with the two maps from `𝒪_{S, s}`, together with a
bijection `ι : 𝒪^∧_{X, x} → 𝒪^∧_{Xσ, xσ}` compatible with `Xσ ⟶ X`, yield the compatibility of
`φ ∘ ι⁻¹` with the two maps from the local ring of `V` at `c` which Tag 0CAV asks for. -/
private theorem comp_algebraMap_stalkHomAt_eq {S V X Xσ Yσ : Scheme.{u}} {s : S}
    (hJ : (maximalIdeal (S.presheaf.stalk s)).FG)
    (fX : X ⟶ S) {x : X} (hfx : fX x = s) (bS : V ⟶ S) {c : V} (hbS : bS c = s)
    (pX1 : Xσ ⟶ X) (pX2 : Xσ ⟶ V) (pY2 : Yσ ⟶ V) {xσ : Xσ} {yσ : Yσ}
    (hxσ : pX1 xσ = x) (hxσ' : pX2 xσ = c) (hyσ : pY2 yσ = c)
    (hcond : pX2 ≫ bS = pX1 ≫ fX) (hbase : (pY2 ≫ bS) yσ = s)
    (ν : AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) →+*
      V.presheaf.stalk c)
    (hνsurj : Function.Surjective ν)
    (hν : bS.stalkHomAt hbS = ν.comp (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
    {ι : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+*
      AdicCompletion (maximalIdeal (Xσ.presheaf.stalk xσ)) (Xσ.presheaf.stalk xσ)}
    (hbij : Function.Bijective ι)
    (hι : ι.comp (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))) =
      (algebraMap (Xσ.presheaf.stalk xσ)
        (AdicCompletion (maximalIdeal (Xσ.presheaf.stalk xσ))
          (Xσ.presheaf.stalk xσ))).comp (pX1.stalkHomAt hxσ))
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ)) (Yσ.presheaf.stalk yσ))
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (fX.stalkHomAt hfx)) =
      (algebraMap (Yσ.presheaf.stalk yσ)
        (AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ))
          (Yσ.presheaf.stalk yσ))).comp ((pY2 ≫ bS).stalkHomAt hbase)) :
    ((RingEquiv.ofBijective ι hbij).symm.trans φ).toRingHom.comp
        ((algebraMap (Xσ.presheaf.stalk xσ)
            (AdicCompletion (maximalIdeal (Xσ.presheaf.stalk xσ))
              (Xσ.presheaf.stalk xσ))).comp
          (((V.presheaf.stalkCongr (.of_eq (hyσ.trans hxσ'.symm))).hom ≫
            pX2.stalkMap xσ).hom)) =
      (algebraMap (Yσ.presheaf.stalk yσ)
        (AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ))
          (Yσ.presheaf.stalk yσ))).comp (pY2.stalkMap yσ).hom := by
  have key : ∀ {W : Scheme.{u}} (m : W ⟶ V) {w : W} (hw : m w = c),
      ((m.stalkHomAt hw).comp ν).comp (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) =
      (m ≫ bS).stalkHomAt (comp_apply_eq m bS hw hbS) := fun m _ hw =>
    (congrArg (fun z => (m.stalkHomAt hw).comp z) hν.symm).trans
      (Scheme.Hom.stalkHomAt_comp m bS hw hbS).symm
  have hρ := key pY2 hyσ
  have hρ' := (key pX2 hxσ').trans ((stalkHomAt_congr hcond (comp_apply_eq pX2 bS hxσ' hbS)
    (comp_apply_eq pX1 fX hxσ hfx)).trans (Scheme.Hom.stalkHomAt_comp pX1 fX hxσ hfx))
  have hstar := adicCompletion_comp_eq_of_comp_algebraMap_eq
    (maximalIdeal (S.presheaf.stalk s)) hJ hρ' hρ (map_maximalIdeal_le _) hbij hι φ hφ
  have hcancel : (((RingEquiv.ofBijective ι hbij).symm.trans φ).toRingHom.comp
        (algebraMap (Xσ.presheaf.stalk xσ)
          (AdicCompletion (maximalIdeal (Xσ.presheaf.stalk xσ))
            (Xσ.presheaf.stalk xσ)))).comp (pX2.stalkHomAt hxσ') =
      (algebraMap (Yσ.presheaf.stalk yσ)
        (AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ))
          (Yσ.presheaf.stalk yσ))).comp (pY2.stalkHomAt hyσ) :=
    RingHom.ext fun z => by
      obtain ⟨a, rfl⟩ := hνsurj z
      exact RingHom.congr_fun hstar a
  refine (comp_stalkHomAt_eq_of_comp_stalkHomAt_eq (hyσ.trans hxσ'.symm).symm rfl hyσ
    hcancel).trans ?_
  exact congrArg (fun z => (algebraMap (Yσ.presheaf.stalk yσ)
    (AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ))
      (Yσ.presheaf.stalk yσ))).comp z) (stalkHomAt_rfl pY2 yσ)

/-- **A common elementary étale neighbourhood over the completed local ring of the base.** Let
`S` be locally Noetherian, let `fX : X ⟶ S` and `gY : Y ⟶ T` be locally of finite type, let
`x ∈ X` lie over `s ∈ S`, and let `σ : 𝒪_{T, t} → Λ := 𝒪^∧_{S, s}` be a local homomorphism. Form
the two morphisms `bS : Spec Λ ⟶ S` and `bσ : Spec Λ ⟶ T` out of the spectrum of the completed
local ring and the two base changes `Xσ := X ×_S Spec Λ` and `Yσ := Y ×_T Spec Λ`. Let
`xσ ∈ Xσ` lie over `x` and the closed point, with the induced map
`𝒪^∧_{X, x} → 𝒪^∧_{Xσ, xσ}` bijective, and let `yσ ∈ Yσ` lie over the closed point. Then an
isomorphism `φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Yσ, yσ}` of `𝒪_{S, s}`-algebras is approximated, for every
`N ≥ 1`, by a diagram `(Xσ, xσ) ← (U, u) → (Yσ, yσ)` over `Spec Λ` in which both legs are
elementary étale neighbourhoods.

This is Tag 0CAV over the base `Spec Λ`, which is the spectrum of a complete Noetherian local
ring; its hypothesis on the base is supplied by `comp_algebraMap_stalkHomAt_eq`. The congruence
modulo `𝔪_u ^ N` which Tag 0CAV also provides is discarded; `N` is kept because the diagram
depends on it. -/
public theorem exists_common_neighborhood_of_bijective_completionMapAt
    {S T X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (fX : X ⟶ S) (gY : Y ⟶ T) [LocallyOfFiniteType fX] [LocallyOfFiniteType gY]
    (x : X) (s : S) (hfx : fX x = s) (t : T)
    (σ : T.presheaf.stalk t →+* AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (yσ : ↥(pullback gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)))
    (hyσ : pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) yσ =
      closedPoint _)
    (xσ : ↥(pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s)))
    (hxσ : pullback.fst fX _ xσ = x)
    (hxσ' : pullback.snd fX _ xσ = closedPoint _)
    (hbij : Function.Bijective ((pullback.fst fX _).completionMapAt hxσ))
    (N : ℕ) (hN : 1 ≤ N)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
          T.fromSpecStalk t)).presheaf.stalk yσ))
        ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)).presheaf.stalk yσ))
    (hbase : (pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s) yσ = s)
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (fX.stalkHomAt hfx)) =
      (algebraMap ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
            T.fromSpecStalk t)).presheaf.stalk yσ)
          (AdicCompletion (maximalIdeal ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk t)).presheaf.stalk yσ))
            ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk t)).presheaf.stalk yσ))).comp
        ((pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
          S.fromSpecStalk s).stalkHomAt hbase)) :
    ∃ (U : EtaleNeighborhood (pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
          T.fromSpecStalk t)) yσ)
      (q : U.scheme ⟶ pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.fromSpecStalk s)) (hqEt : Etale q) (hq : q U.point = xσ),
      U.IsElementary ∧ (U.along q hqEt hq).IsElementary ∧
        q ≫ pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
          S.fromSpecStalk s) =
          U.toBase ≫ pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) := by
  -- that `σ` is local is part of the data of Tag 0GDX; this step does not use it
  have _hσ := hσ
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
  have hbS := specMap_fromSpecStalk_closedPoint (CommRingCat.ofHom (algebraMap
    (S.presheaf.stalk s) (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))))
  obtain ⟨U, q, hqEt, hq, hUel, hUal, hover, -⟩ :=
    exists_common_elementaryEtaleNeighborhood_over_spec_complete
      (pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t))
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.fromSpecStalk s)) yσ xσ (hyσ.trans hxσ'.symm) N hN
      ((RingEquiv.ofBijective ((pullback.fst fX _).completionMapAt hxσ) hbij).symm.trans φ)
      (comp_algebraMap_stalkHomAt_eq (maximalIdeal (S.presheaf.stalk s)).fg_of_isNoetherianRing
        fX hfx _ hbS (pullback.fst fX _) _ _ hxσ hxσ' hyσ pullback.condition.symm
        hbase ((stalkClosedPointIso (CommRingCat.of (AdicCompletion
          (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).inv.hom)
        (ConcreteCategory.bijective_of_isIso _).2
        (stalkHomAt_specMap_fromSpecStalk _ hbS) hbij
        (adicCompletionMap_comp_algebraMap _ _ _ _) φ hφ)
  exact ⟨U, q, hqEt, hq, hUel, hUal, hover⟩

end StacksDraft.ArtinApproximation

end
