module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.FlatBaseChange
public import StacksFrontier.RingTheory.Smooth.PerfectDiagonal
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Smoothness through the diagonal

Let `f : X ⟶ Y` be a morphism of finite type between locally Noetherian schemes and let
`Δ : X ⟶ X ×_Y X` be its diagonal. Then `f` is smooth exactly when it is flat and `Δ` is a
regular immersion, exactly when it is flat and `Δ` is a local complete intersection morphism,
and exactly when it is flat and `Δ` is perfect. This is **Stacks 0FDP**.

## Main results

* `AlgebraicGeometry.smooth_of_flat_of_perfect_diagonal`: the implication the source calls the
  interesting one, from flatness together with perfectness of the diagonal to smoothness.
* `AlgebraicGeometry.smooth_tfae_diagonal`: **Stacks 0FDP**, the four equivalent conditions.

## Implementation notes

The fibre product is the categorical pullback `AlgebraicGeometry.Scheme`'s `pullback` and the
diagonal is `CategoryTheory.Limits.pullback.diagonal`, which is an immersion by a Mathlib
instance, so regularity of it is `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion`
with no extra hypothesis. Finite type is spelled, as elsewhere in this library, as
`AlgebraicGeometry.LocallyOfFiniteType` together with `AlgebraicGeometry.QuasiCompact`.

The three easy implications are the cited lemmas: smoothness gives flatness and makes the
diagonal a section of the smooth first projection, hence a regular immersion (Stacks 067R); a
regular immersion is a local complete intersection morphism (Stacks 069L); and such a morphism
is perfect (Stacks 069H, part (3)).

The remaining implication is local: smoothness of `f` is smoothness of every
`Γ(Y, U) ⟶ Γ(X, V)` with `V ≤ f ⁻¹ᵁ U` affine, and that map is handed to Stacks 0FCX, which
needs perfectness of the multiplication map `Γ(X, V) ⊗_{Γ(Y, U)} Γ(X, V) → Γ(X, V)`. The chart
on `X ×_Y X` that realizes the tensor product is the range of
`CategoryTheory.Limits.pullback.map` from `V ×_U V`, an affine open on which the diagonal
restricts to `pullback.diagonal (f.resLE U V _)`; the sections there are identified with
`Γ(X, V) ⊗_{Γ(Y, U)} Γ(X, V)` by comparing two pushout squares of rings, and under that
identification the map on sections of the diagonal is the multiplication map. Perfectness of
the latter is then transported from `AlgebraicGeometry.Perfect.perfect_appLE` along that ring
equivalence, using that an isomorphism is a flat base change
(`RingHom.isPerfectRingMap_of_isPushout_of_flat`).

The derived categories of modules come from `HasDerivedCategory.standard`, which is only ever a
local instance, so it is re-declared here.

## References

* [The Stacks Project, Lemma 37.62.18 (0FDP)](https://stacks.math.columbia.edu/tag/0FDP)
* [The Stacks Project, Lemma 31.23.8 (067R)](https://stacks.math.columbia.edu/tag/067R)
* [The Stacks Project, Lemma 37.62.9 (069L)](https://stacks.math.columbia.edu/tag/069L)
* [The Stacks Project, Lemma 37.62.4 (069H)](https://stacks.math.columbia.edu/tag/069H)
* [The Stacks Project, Lemma 23.10.2 (0FCX)](https://stacks.math.columbia.edu/tag/0FCX)
* [The Stacks Project, Lemma 29.35.9 (01VF)](https://stacks.math.columbia.edu/tag/01VF)
* [The Stacks Project, Lemma 29.35.5 (01VB)](https://stacks.math.columbia.edu/tag/01VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.TorAmplitude
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

/-- Perfectness of a ring map is read off the source only up to isomorphism: if `g : A' →+* B`
becomes `f : A →+* B` after precomposition with a ring isomorphism `e : A ≃+* A'` and `f` is
perfect, then so is `g`.

An isomorphism is flat and makes `B` the pushout of `A → B` along `A → A'`, so this is the
base-change statement `RingHom.isPerfectRingMap_of_isPushout_of_flat`, the algebra content of
Stacks 0688. -/
private theorem isPerfectRingMap_of_ringEquiv_source {A A' B : Type u} [CommRing A]
    [CommRing A'] [CommRing B] (f : A →+* B) (g : A' →+* B) (e : A ≃+* A')
    (hcomp : g.comp e.toRingHom = f)
    (h : ∀ D : CertifiedDerivedTensoring.{u, u} A,
      letI := f.toAlgebra
      RingHom.IsPerfectRingMap A B D.tensor D.comparison D.isLeftDerived) :
    letI := g.toAlgebra
    ∀ D : CertifiedDerivedTensoring.{u, u} A',
      RingHom.IsPerfectRingMap A' B D.tensor D.comparison D.isLeftDerived := by
  let : Algebra A A' := e.toRingHom.toAlgebra
  let : Algebra A B := f.toAlgebra
  let : Algebra A' B := g.toAlgebra
  have : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : IsScalarTower A B B := IsScalarTower.of_algebraMap_eq' (by simp)
  have hcat : IsPushout (CommRingCat.ofHom e.toRingHom) (CommRingCat.ofHom f)
      (CommRingCat.ofHom g) (𝟙 (CommRingCat.of B)) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 e.bijective
    refine IsPushout.of_horiz_isIso ⟨?_⟩
    ext x
    exact congrArg (fun φ : A →+* B => φ x) hcomp
  have : Algebra.IsPushout A A' B B := CommRingCat.isPushout_iff_isPushout.mp hcat
  have : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective e.bijective)
  exact RingHom.isPerfectRingMap_of_isPushout_of_flat h

/-- The affine-chart form of the interesting implication of Stacks 0FDP: for `f` flat with
perfect diagonal, the map on sections over a compatible pair of affine opens is smooth.

On the affine chart `V ⊆ X` over `U ⊆ Y` the pullback `V ×_U V` is an affine open of
`X ×_Y X` whose sections are `Γ(X, V) ⊗_{Γ(Y, U)} Γ(X, V)`, and the diagonal restricts to the
diagonal of `f|_V`, whose map on sections is the multiplication map. Perfectness of the
diagonal therefore gives perfectness of the multiplication map, and Stacks 0FCX turns that,
with flatness, into smoothness. -/
private theorem smooth_appLE_of_flat_of_perfect_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (hflat : Flat f)
    (hperf : Perfect (pullback.diagonal f)) (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) : (f.appLE U V hVU).hom.Smooth := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let fV : V.toScheme ⟶ U.toScheme := f.resLE U V hVU
  let P : Scheme.{u} := pullback fV fV
  let Q : Scheme.{u} := pullback.diagonalObj f
  let q : P ⟶ Q :=
    pullback.map fV fV f f V.ι V.ι U.ι
      (Scheme.Hom.resLE_comp_ι f hVU)
      (Scheme.Hom.resLE_comp_ι f hVU)
  have : IsOpenImmersion q :=
    Scheme.pullback_map_isOpenImmersion fV fV f f V.ι V.ι U.ι
      (Scheme.Hom.resLE_comp_ι f hVU)
      (Scheme.Hom.resLE_comp_ι f hVU)
  let W : Q.Opens := q.opensRange
  have hP : IsAffine P := by
    let : IsAffine U.toScheme := hU
    let : IsAffine V.toScheme := hV
    infer_instance
  let : IsAffine P := hP
  have hW : IsAffineOpen W := isAffineOpen_opensRange q
  let d : V.toScheme ⟶ P := pullback.diagonal fV
  have hdq : d ≫ q = V.ι ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;>
      simp [d, q, pullback.map, Category.assoc]
  have hdelta : V ≤ (pullback.diagonal f) ⁻¹ᵁ W := by
    intro x hx
    change pullback.diagonal f (V.ι ⟨x, hx⟩) ∈ Set.range q
    refine ⟨d ⟨x, hx⟩, ?_⟩
    have he := congrArg (fun k : V.toScheme ⟶ Q => k ⟨x, hx⟩) hdq
    change q (d ⟨x, hx⟩) = pullback.diagonal f (V.ι ⟨x, hx⟩) at he
    simpa using he
  let A := Γ(Y, U)
  let B := Γ(X, V)
  let C := Γ(P, ⊤)
  let α := f.appLE U V hVU
  let : Algebra A B := α.hom.toAlgebra
  -- `Γ(P, ⊤)` is the tensor product `B ⊗[A] B`: both are the pushout of `α` along itself.
  have hTensor := CommRingCat.isPushout_tensorProduct A B B
  let inl := V.topIso.inv ≫ (pullback.fst fV fV).appTop
  let inr := V.topIso.inv ≫ (pullback.snd fV fV).appTop
  let hpo₀ : IsPushout fV.appTop fV.appTop (pullback.fst fV fV).appTop
      (pullback.snd fV fV).appTop :=
    isPushout_appTop_of_isPullback (IsPullback.of_hasPullback fV fV)
  let hpo : IsPushout α α inl inr := by
    apply IsPushout.of_iso hpo₀ U.topIso V.topIso V.topIso (Iso.refl _)
    · exact (arrowResLEAppIso f U V hVU).hom.w.symm
    · exact (arrowResLEAppIso f U V hVU).hom.w.symm
    · change (pullback.fst fV fV).appTop =
        V.topIso.hom ≫ V.topIso.inv ≫ (pullback.fst fV fV).appTop
      exact (Iso.hom_inv_id_assoc V.topIso _).symm
    · change (pullback.snd fV fV).appTop =
        V.topIso.hom ≫ V.topIso.inv ≫ (pullback.snd fV fV).appTop
      exact (Iso.hom_inv_id_assoc V.topIso _).symm
  have hα : α = CommRingCat.ofHom (algebraMap A B) := by
    apply CommRingCat.hom_ext
    rfl
  let hpo' : IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A B)) inl inr := by
    simpa [hα] using hpo
  let ePushCat := hTensor.isoPushout ≪≫ hpo'.isoPushout.symm
  let ePush : TensorProduct A B B ≃+* C := ePushCat.commRingCatIsoToRingEquiv
  have hIsoApp : IsIso q.isoOpensRange.hom.appTop := by
    refine ⟨⟨q.isoOpensRange.inv.appTop, ?_, ?_⟩⟩
    · rw [← Scheme.Hom.comp_appTop]
      simp
    · rw [← Scheme.Hom.comp_appTop]
      simp
  let eOpen : Γ(Q, W) ≃+* C :=
    W.topIso.symm.commRingCatIsoToRingEquiv.trans
      (asIso q.isoOpensRange.hom.appTop).commRingCatIsoToRingEquiv
  let e : Γ(Q, W) ≃+* TensorProduct A B B := eOpen.trans ePush.symm
  let μ := (Algebra.TensorProduct.lmul' (R := A) (S := B)).toRingHom
  -- `ePush` carries `b ⊗ 1` to `inl b` and `1 ⊗ b` to `inr b`, read off the two pushout
  -- squares at the element `x` rather than as an identity of morphisms, so that no rewrite
  -- has to match the inclusions up to the `AlgHom`-to-`RingHom` coercion.
  have hleft (x : B) :
      ePush (Algebra.TensorProduct.includeLeftRingHom (A := B) x) = inl.hom x := by
    have h₁ := congrArg (fun k => k.hom x) hTensor.inl_isoPushout_hom
    have h₂ := congrArg (fun k => k.hom x) hpo'.inl_isoPushout_inv
    exact (congrArg hpo'.isoPushout.inv.hom h₁).trans h₂
  have hright (x : B) :
      ePush (Algebra.TensorProduct.includeRight (A := B) x) = inr.hom x := by
    have h₁ := congrArg (fun k => k.hom x) hTensor.inr_isoPushout_hom
    have h₂ := congrArg (fun k => k.hom x) hpo'.inr_isoPushout_inv
    exact (congrArg hpo'.isoPushout.inv.hom h₁).trans h₂
  -- The map on sections of the diagonal of `f|_V` retracts both inclusions, so it is `μ`.
  let dRing : C →+* B := (d.appTop ≫ V.topIso.hom).hom
  have hretract (p : P ⟶ V.toScheme) (hp : d ≫ p = 𝟙 V.toScheme) :
      dRing.comp (V.topIso.inv ≫ p.appTop).hom = RingHom.id B := by
    have hcat : (V.topIso.inv ≫ p.appTop) ≫ (d.appTop ≫ V.topIso.hom) = 𝟙 B := by
      change V.topIso.inv ≫ (p.appTop ≫ d.appTop) ≫ V.topIso.hom = 𝟙 B
      rw [← Scheme.Hom.comp_appTop d p, hp, Scheme.Hom.id_appTop]
      simp only [Category.id_comp]
      exact Iso.inv_hom_id V.topIso
    have h := congrArg CommRingCat.Hom.hom hcat
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at h
    exact h
  have hleftDiag : dRing.comp inl.hom = RingHom.id B := hretract _ (pullback.diagonal_fst fV)
  have hrightDiag : dRing.comp inr.hom = RingHom.id B := hretract _ (pullback.diagonal_snd fV)
  -- Both inclusions are retracted by `μ` and by `dRing ∘ ePush`, which therefore agree.
  have hmul' (i : B →+* TensorProduct A B B) (j : B →+* C) (hij : ∀ x, ePush (i x) = j x)
      (hj : dRing.comp j = RingHom.id B) (hi : μ.comp i = RingHom.id B) :
      μ.comp i = (dRing.comp ePush.toRingHom).comp i := by
    rw [hi, ← hj]
    ext x
    exact congrArg dRing (hij x).symm
  have hmul : μ = dRing.comp ePush.toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · exact hmul' _ inl.hom hleft hleftDiag (by ext; simp [μ])
    · exact hmul' _ inr.hom hright hrightDiag (by ext; simp [μ])
  have hdiag : μ.comp e.toRingHom = ((pullback.diagonal f).appLE W V hdelta).hom := by
    let qW := q.isoOpensRange.hom
    have hdW : d ≫ qW = (pullback.diagonal f).resLE W V hdelta := by
      apply (cancel_mono W.ι).1
      calc
        d ≫ qW ≫ W.ι = d ≫ q := by rw [Scheme.Hom.isoOpensRange_hom_ι]
        _ = V.ι ≫ pullback.diagonal f := hdq
        _ = (pullback.diagonal f).resLE W V hdelta ≫ W.ι :=
          (Scheme.Hom.resLE_comp_ι (pullback.diagonal f) hdelta).symm
    have hApp : qW.appTop ≫ d.appTop =
        ((pullback.diagonal f).resLE W V hdelta).appTop := by
      rw [← Scheme.Hom.comp_appTop, hdW]
    have hdiagOpen : W.topIso.symm.hom ≫ qW.appTop ≫ d.appTop ≫ V.topIso.hom =
        (pullback.diagonal f).appLE W V hdelta := by
      calc
        W.topIso.symm.hom ≫ qW.appTop ≫ d.appTop ≫ V.topIso.hom =
            W.topIso.symm.hom ≫ (qW.appTop ≫ d.appTop) ≫ V.topIso.hom := by
          congr 1
        _ = W.topIso.symm.hom ≫
            ((pullback.diagonal f).resLE W V hdelta).appTop ≫ V.topIso.hom := by rw [hApp]
        _ = (pullback.diagonal f).appLE W V hdelta := by
          have hArrow :=
            (arrowResLEAppIso (pullback.diagonal f) W V hdelta).hom.w.symm
          calc
            W.topIso.symm.hom ≫
                ((pullback.diagonal f).resLE W V hdelta).appTop ≫ V.topIso.hom =
                W.topIso.symm.hom ≫ (W.topIso.hom ≫
                  (pullback.diagonal f).appLE W V hdelta) := by
              exact congrArg (fun g => W.topIso.symm.hom ≫ g) hArrow
            _ = (pullback.diagonal f).appLE W V hdelta := by
              simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
    have hmul' : μ.comp ePush.symm.toRingHom = dRing := by
      rw [hmul]
      simp [dRing, RingHom.comp_assoc]
    change (μ.comp ePush.symm.toRingHom).comp eOpen.toRingHom =
      ((pullback.diagonal f).appLE W V hdelta).hom
    rw [hmul']
    have heOpen : eOpen.toRingHom = (W.topIso.symm.hom ≫ qW.appTop).hom := by
      change (qW.appTop).hom.comp (W.topIso.symm.hom).hom =
        (W.topIso.symm.hom ≫ qW.appTop).hom
      exact (CommRingCat.hom_comp W.topIso.symm.hom qW.appTop).symm
    rw [heOpen]
    calc
      (d.appTop ≫ V.topIso.hom).hom.comp
          (W.topIso.symm.hom ≫ qW.appTop).hom =
        (W.topIso.symm.hom ≫ qW.appTop ≫ d.appTop ≫ V.topIso.hom).hom := by
          rw [← CommRingCat.hom_comp]
          congr 1
      _ = ((pullback.diagonal f).appLE W V hdelta).hom :=
        congrArg CommRingCat.Hom.hom hdiagOpen
  have hperfect : ∀ D : CertifiedDerivedTensoring.{u, u} Γ(Q, W),
      let := ((pullback.diagonal f).appLE W V hdelta).hom.toAlgebra
      RingHom.IsPerfectRingMap Γ(Q, W) B D.tensor D.comparison D.isLeftDerived := by
    intro D
    let : Algebra Γ(Q, W) B := ((pullback.diagonal f).appLE W V hdelta).hom.toAlgebra
    exact hperf.perfect_appLE V hV W hW hdelta D
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Algebra.FiniteType A B :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hU hV hVU)
  let : Module.Flat A B :=
    RingHom.flat_algebraMap_iff.mp (hflat.flat_appLE hU hV hVU)
  have hperfμ := isPerfectRingMap_of_ringEquiv_source
    ((pullback.diagonal f).appLE W V hdelta).hom μ e hdiag hperfect
  have hs : Algebra.Smooth A B :=
    StacksDraft.Smooth.smooth_of_flat_of_isPerfect_diagonal A B
      (canonicalCertifiedDerivedTensoring _) (hperfμ _)
  exact RingHom.smooth_algebraMap.mpr hs

/-- **Stacks 0FDP, the implication (4) ⇒ (1).** A morphism of finite type between locally
Noetherian schemes which is flat and whose diagonal is perfect is smooth.

Smoothness is checked on affine charts, where it is Stacks 0FCX applied to the multiplication
map of the chart; see `AlgebraicGeometry.smooth_appLE_of_flat_of_perfect_diagonal`. -/
theorem smooth_of_flat_of_perfect_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (hflat : Flat f)
    (hperf : Perfect (pullback.diagonal f)) : Smooth f := by
  refine ⟨?_⟩
  intro U hU V hV hVU
  exact smooth_appLE_of_flat_of_perfect_diagonal f hflat hperf U hU V hV hVU

/-- **Stacks 0FDP.** Let `f : X ⟶ Y` be a morphism of finite type between locally Noetherian
schemes and let `Δ : X ⟶ X ×_Y X` be its diagonal. The following are equivalent:

1. `f` is smooth;
2. `f` is flat and `Δ` is a regular immersion;
3. `f` is flat and `Δ` is a local complete intersection morphism;
4. `f` is flat and `Δ` is perfect.

A smooth morphism is flat and its diagonal is a section of the smooth first projection, hence a
regular immersion by Stacks 067R; a regular immersion is a local complete intersection morphism
by Stacks 069L; such a morphism is perfect by Stacks 069H; and the interesting implication back
to smoothness is `AlgebraicGeometry.smooth_of_flat_of_perfect_diagonal`, which runs Stacks 0FCX
on affine charts. -/
@[stacks 0FDP, sga "1 II 4.18" "(1) ⇒ (2), special case", sga "6 VII 1.10" "special case"]
theorem smooth_tfae_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] :
    List.TFAE
      [Smooth f,
        Flat f ∧ Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion
          (pullback.diagonal f),
        Flat f ∧ IsLocalCompleteIntersectionMorphism (pullback.diagonal f),
        Flat f ∧ Perfect (pullback.diagonal f)] := by
  tfae_have 1 → 2 := by
    intro hf
    refine ⟨inferInstance, ?_⟩
    exact Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
      (pullback.fst f f) (pullback.diagonal f) (by simp)
  tfae_have 2 → 3 := fun ⟨hflat, hreg⟩ =>
    ⟨hflat, isLocalCompleteIntersectionMorphism_of_isRegularImmersion (pullback.diagonal f) hreg⟩
  tfae_have 3 → 4 := fun ⟨hflat, hlci⟩ =>
    ⟨hflat, perfect_of_isLocalCompleteIntersectionMorphism hlci⟩
  tfae_have 4 → 1 := fun ⟨hflat, hperf⟩ => smooth_of_flat_of_perfect_diagonal f hflat hperf
  tfae_finish

end AlgebraicGeometry

end
