module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistLimitVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.FiniteType
public import StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction

/-!
# Finite presentation of the truncated section ring, by Noetherian approximation

Let `g : Y ⟶ S` be proper, flat and of finite presentation, `ℳ` an invertible `𝒪_Y`-module ample
relative to `g`, and `e > 0` a cut such that the sections of `g_* ℳ^{⊗ n}` over an affine open
`U ⊆ S` are finitely presented `Γ(S, U)`-modules for every `n ≥ e`.  Then the ring of sections

`Γ(U, 𝒪_S ⊕ ⨁_{n ≥ e} g_* ℳ^{⊗ n})`

of the tail truncation is a finitely presented `Γ(S, U)`-algebra.  This is clause (3) of
[Stacks, Tag 0D4F], proved as the source proves it:

* restrict to the affine scheme `U` (the section rings over `U` and over all of `U` agree,
  `U ⟶ S` being an open immersion);
* write the affine base as a limit of spectra of Noetherian rings and descend `(g, ℳ)` to a
  stage `g_i : Y_i ⟶ Spec R_i` ([Stacks, Tag 0D43], `exists_stage_polarizedModel`);
* over the Noetherian model the tail ring is of finite type, hence finitely presented
  ([Stacks, Tag 0B5T], `finiteType_tailAlgebra_strHom`);
* above the vanishing bound of the model (Serre vanishing, [Stacks, Tag 02O1]) the sections of the
  tensor powers commute with base change ([Stacks, Tag 0D4E] (2),
  `exists_bijective_squarePieceMap_tmul`);
* steps (c)–(i) of the source (`finitePresentation_strHom_of_isBaseChange`) conclude.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.finitePresentation_tailAlgebra_strHom`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.SectionAlgebra
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Transport of finite presentation along isomorphisms -/

/-- A module carried bijectively and semilinearly over a ring isomorphism onto another module is
finitely presented as soon as the source is. -/
theorem moduleFinitePresentation_of_bijective_semilinear {R R' M M' : Type u} [CommRing R]
    [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
    (ρ : R →+* R') (hρ : Function.Bijective ρ) (Φ : M →+ M') (hΦ : Function.Bijective Φ)
    (hsmul : ∀ (r : R) (m : M), Φ (r • m) = ρ r • Φ m) [Module.FinitePresentation R M] :
    Module.FinitePresentation R' M' := by
  let := ρ.toAlgebra
  let : Module R M' := Module.compHom M' ρ
  have : IsScalarTower R R' M' := ⟨fun r r' m => by
    change (ρ r * r') • m = ρ r • (r' • m)
    exact mul_smul _ _ _⟩
  let L : M ≃ₗ[R] M' := { AddEquiv.ofBijective Φ hΦ with map_smul' := fun r m => hsmul r m }
  have : Module.FinitePresentation R M' := Module.FinitePresentation.of_equiv L
  have : Algebra.FiniteType R R' := RingHom.FiniteType.of_surjective ρ hρ.2
  exact Module.FinitePresentation.of_restrictScalars_of_finiteType R R' M'

/-- A bijective ring homomorphism is of finite presentation. -/
theorem finitePresentation_of_bijective {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : f.FinitePresentation := by
  refine RingHom.FinitePresentation.of_surjective f hf.2 ?_
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf.1]
  exact Submodule.fg_bot

/-- **Finite presentation descends along a commutative square of ring isomorphisms.** -/
theorem finitePresentation_of_bijective_square {A A' B B' : Type u} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] (f : A →+* B) (f' : A' →+* B') (ρ : A →+* A') (Φ : B →+* B')
    (hρ : Function.Bijective ρ) (hΦ : Function.Bijective Φ) (hcomm : ∀ a, Φ (f a) = f' (ρ a))
    (hf' : f'.FinitePresentation) : f.FinitePresentation := by
  let eΦ := RingEquiv.ofBijective Φ hΦ
  have hf : f = (eΦ.symm.toRingHom.comp f').comp ρ := RingHom.ext fun a =>
    (eΦ.symm_apply_apply (f a)).symm.trans (congrArg eΦ.symm (hcomm a))
  exact hf ▸ (RingHom.FinitePresentation.comp
    (finitePresentation_of_bijective _ eΦ.symm.bijective) hf').comp
      (finitePresentation_of_bijective ρ hρ)

/-! ### The tail pieces as sections of the direct images -/

section Pieces

variable {Y T : Scheme.{u}} (g : Y ⟶ T) [QuasiCompact g] [QuasiSeparated g] (M : Y.Modules)
  [Stacks.Ample.IsInvertibleModule Y M] (e : ℕ) (he : 0 < e) (V : T.Opens)

/-- In a degree `n ≥ e`, the degree-`n` sections of the tail truncation are those of
`g_* ℳ^{⊗ n}`. -/
def tailSectionsEquiv (n : ℕ) (hn : e ≤ n) :
    Γ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)),
        V) ≃ₗ[Γ(T, V)] (tailAlgebra g M e he).sectionPieces V n :=
  LinearEquiv.ofBijective
    (Scheme.Modules.sectionsLinearMap (X := T)
      (M := (Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)))
      (N := tailPiece (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        g (Stacks.RelativeAmple.laurentPowers M)) e (n : ℤ))
      (eqToHom (tailPiece_eq_piece
        (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
          g (Stacks.RelativeAmple.laurentPowers M)) e he
            (show (e : ℤ) ≤ (n : ℤ) by omega)).symm) V)
    (bijective_iso_hom_app' (eqToIso (tailPiece_eq_piece
      (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        g (Stacks.RelativeAmple.laurentPowers M)) e he
          (show (e : ℤ) ≤ (n : ℤ) by omega)).symm) (op V))

/-- The inverse direction of `tailSectionsEquiv`, written as the transport itself. -/
def tailSectionsEquiv' (n : ℕ) (hn : e ≤ n) :
    (tailAlgebra g M e he).sectionPieces V n ≃ₗ[Γ(T, V)]
      Γ((Scheme.Modules.pushforward g).obj ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)),
        V) :=
  LinearEquiv.ofBijective
    (Scheme.Modules.sectionsLinearMap (X := T)
      (M := tailPiece (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        g (Stacks.RelativeAmple.laurentPowers M)) e (n : ℤ))
      (N := (Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)))
      (eqToHom (tailPiece_eq_piece
        (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
          g (Stacks.RelativeAmple.laurentPowers M)) e he
            (show (e : ℤ) ≤ (n : ℤ) by omega))) V)
    (bijective_iso_hom_app' (eqToIso (tailPiece_eq_piece
      (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra
        g (Stacks.RelativeAmple.laurentPowers M)) e he
          (show (e : ℤ) ≤ (n : ℤ) by omega))) (op V))

/-- The band and the tail pieces of the tail truncation are finitely presented as soon as the
sections of `g_* ℳ^{⊗ n}` are for `n ≥ e`. -/
theorem moduleFinitePresentation_tailAlgebra_sectionPieces
    (hband : ∀ n : ℕ, e ≤ n → Module.FinitePresentation Γ(T, V)
      Γ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), V)) (n : ℕ) (hn : 0 < n) :
    Module.FinitePresentation Γ(T, V) ((tailAlgebra g M e he).sectionPieces V n) := by
  by_cases hen : e ≤ n
  · have := hband n hen
    exact Module.FinitePresentation.of_equiv (tailSectionsEquiv g M e he V n hen)
  · have : Subsingleton ((tailAlgebra g M e he).sectionPieces V n) :=
      subsingleton_of_forall_eq 0 fun z => eq_zero_of_tailPiece _ e (show (n : ℤ) ≠ 0 by omega)
        (show ¬ (e : ℤ) ≤ (n : ℤ) by omega) _ z
    infer_instance

end Pieces

/-! ### Over a Noetherian model -/

section Model

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {Yi Y T : Scheme.{u}} [IsAffine T]
  (gi : Yi ⟶ Spec (CommRingCat.of R)) (Li : Yi.Modules) [Stacks.Ample.IsInvertibleModule Yi Li]

omit [IsNoetherianRing R] in
/-- Serre vanishing for the model, read on the pieces of the Laurent algebra. -/
theorem exists_isZero_laurentPowers (hpr : IsProper gi) (hfl : Flat gi)
    (hfpi : _root_.AlgebraicGeometry.FinitePresentation gi)
    (hampi : Stacks.RelativeAmple.IsRelativelyAmple gi Li) :
    ∃ d₁ : ℕ, ∀ n : ℕ, d₁ ≤ n → ∀ i : ℤ, 0 < i →
      IsZero (((Scheme.Modules.pushforward gi).rightDerivedPlus i).obj
        ((Stacks.RelativeAmple.laurentPowers Li).piece (n : ℤ))) := by
  obtain ⟨d₁, hd₁⟩ :=
    AmpleTwistLimitVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule_of_isAffine
      gi hfpi Li hampi
  exact ⟨d₁, fun n hn i hi => (hd₁ n hn i hi).of_iso
    (((Scheme.Modules.pushforward gi).rightDerivedPlus i).mapIso
      (Stacks.PowerFamilyBridge.tensorPowerModuleIso Yi Li (n : ℤ)))⟩

variable (q : Y ⟶ Yi) (g : Y ⟶ T) [QuasiCompact g] [QuasiSeparated g]
  (h : T ⟶ Spec (CommRingCat.of R)) (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]

/-- **Clause (3) of [Stacks, Tag 0D4F] over an affine base carrying a Noetherian model.**  If
`(g, ℳ)` is the base change of a polarized family `(g_i, ℒ_i)` over a Noetherian ring, proper,
flat and of finite presentation with `ℒ_i` relatively ample, then the tail ring
`Γ(T, 𝒪_T ⊕ ⨁_{n ≥ e} g_* ℳ^{⊗ n})` is finitely presented over `Γ(T, 𝒪_T)` as soon as the
sections of `g_* ℳ^{⊗ n}`, `n ≥ e`, are finitely presented modules. -/
theorem finitePresentation_tailAlgebra_strHom_of_isPullback (hpr : IsProper gi) (hfl : Flat gi)
    (hfpi : _root_.AlgebraicGeometry.FinitePresentation gi)
    (hampi : Stacks.RelativeAmple.IsRelativelyAmple gi Li) (hpb : IsPullback q g gi h)
    (ε : (Scheme.Modules.pullback q).obj Li ≅ M) (e : ℕ) (he : 0 < e)
    (hband : ∀ n : ℕ, e ≤ n → Module.FinitePresentation Γ(T, ⊤)
      Γ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), ⊤)) :
    ((tailAlgebra g M e he).strHom ⊤).FinitePresentation := by
  classical
  have := hpr
  have := hfl
  obtain ⟨d₁, hd₁⟩ := exists_isZero_laurentPowers gi Li hpr hfl hfpi hampi
  obtain ⟨E, hEe, hEd, hE⟩ : ∃ E : ℕ, e ≤ E ∧ d₁ ≤ E ∧ 0 < E :=
    ⟨max e d₁, le_max_left _ _, le_max_right _ _, lt_of_lt_of_le he (le_max_left _ _)⟩
  have hampi' : Stacks.Ample.IsAmple Yi Li :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple gi Li).mp hampi
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    AlgebraicGeometry.isLocallyNoetherian_Spec.mpr inferInstance
  have : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hBfp : ((tailAlgebra gi Li E hE).strHom ⊤).FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp (finiteType_tailAlgebra_strHom gi Li hampi' E hE)
  let : Algebra Γ(Spec (CommRingCat.of R), ⊤) Γ(T, ⊤) := (h.appLE ⊤ ⊤ le_top).hom.toAlgebra
  refine finitePresentation_strHom_of_isBaseChange (tailAlgebra g M e he) ⊤
    (tailAlgebra gi Li E hE) ⊤ E (bijective_smul_one_tail _ e he _ _ ⊤)
    (fun n hn _ => moduleFinitePresentation_tailAlgebra_sectionPieces g M e he ⊤ hband n hn)
    (bijective_smul_one_tail _ E hE _ _ ⊤).2
    (fun n hn hnE b => eq_zero_of_tailPiece _ E (show (n : ℤ) ≠ 0 by omega)
      (show ¬ (E : ℤ) ≤ (n : ℤ) by omega) _ b) hBfp
    (squareRingHom q gi g h hpb.w Li M ε E e hE he hEe ⊤ ⊤ le_top)
    (fun r => squareRingHom_strHom q gi g h hpb.w Li M ε E e hE he hEe ⊤ ⊤ le_top r)
    (fun n => tailMapApp
      (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra gi
        (Stacks.RelativeAmple.laurentPowers Li))
      (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
        (Stacks.RelativeAmple.laurentPowers M)) E e hE he hEe ⊤ ⊤ (h.appLE ⊤ ⊤ le_top).hom
      (squarePieceMap q gi g h hpb.w Li M ε ⊤ ⊤ le_top) (n : ℤ))
    (fun n x => squareRingHom_of q gi g h hpb.w Li M ε E e hE he hEe ⊤ ⊤ le_top x) ?_
  intro n hn
  obtain ⟨G₀, hG₀, hG₀1⟩ := exists_bijective_squarePieceMap_tmul q gi g h Li M ε hpb hfpi
    (n : ℤ) (fun i hi => hd₁ n (by omega) i hi)
  let eB := tailSectionsEquiv' gi Li E hE ⊤ n hn
  let eA := tailSectionsEquiv g M e he ⊤ n (by omega)
  let G := (ModuleCat.extendScalars (h.appLE ⊤ ⊤ le_top).hom).map
      (ModuleCat.ofHom (eB.toLinearMap : (tailAlgebra gi Li E hE).sectionPieces ⊤ n →ₗ[_] _)) ≫
    G₀ ≫ ModuleCat.ofHom (eA.toLinearMap :
      Γ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), ⊤) →ₗ[Γ(T, ⊤)] _)
  have i1 : IsIso ((ModuleCat.extendScalars (h.appLE ⊤ ⊤ le_top).hom).map
      (ModuleCat.ofHom (eB.toLinearMap : (tailAlgebra gi Li E hE).sectionPieces ⊤ n →ₗ[_] _))) :=
    Functor.map_isIso _ (LinearEquiv.toModuleIso eB).hom
  refine ⟨G, (eA.bijective.comp hG₀).comp
    (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ i1), fun x => ?_⟩
  have e1 : G ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(Spec (CommRingCat.of R), ⊤), (h.appLE ⊤ ⊤ le_top).hom] x) =
      eA (G₀ ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(Spec (CommRingCat.of R), ⊤), (h.appLE ⊤ ⊤ le_top).hom]
        (eB x))) := rfl
  refine e1.trans ?_
  rw [hG₀1]
  exact (tailMapApp_tail (show ¬ (n : ℤ) = 0 by omega) (show (E : ℤ) ≤ (n : ℤ) by omega) x).symm

end Model

/-! ### Over an affine base -/

/-- **Clause (3) of [Stacks, Tag 0D4F] over an affine base.**  For `g : Y ⟶ T` proper, flat and
of finite presentation onto an affine scheme and `ℳ` invertible and ample relative to `g`, the
tail ring `Γ(T, 𝒪_T ⊕ ⨁_{n ≥ e} g_* ℳ^{⊗ n})` is finitely presented over `Γ(T, 𝒪_T)` as soon as
the sections of `g_* ℳ^{⊗ n}`, `n ≥ e`, are finitely presented modules.

`T` is the limit of the spectra of the finitely generated subrings of `Γ(T, ⊤)`, and
[Stacks, Tag 0D43] descends `(g, ℳ)` to a Noetherian stage. -/
theorem finitePresentation_tailAlgebra_strHom_of_isAffine {Y T : Scheme.{u}} [IsAffine T]
    (g : Y ⟶ T) [IsProper g] [Flat g] (hfp : _root_.AlgebraicGeometry.FinitePresentation g)
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) (e : ℕ) (he : 0 < e)
    (hband : ∀ n : ℕ, e ≤ n → Module.FinitePresentation Γ(T, ⊤)
      Γ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), ⊤)) :
    ((tailAlgebra g M e he).strHom ⊤).FinitePresentation := by
  -- The instances are supplied positionally, as in
  -- `exists_isZero_rightDerivedPlus_pushforward_tensorPowModule_of_isAffine` (in the namespace
  -- `AmpleTwistLimitVanishing`).
  obtain ⟨i, Yi, gi, Li, hLiinv, q, hpr, hfl, hfpi, hampi, hpb, ⟨eL⟩⟩ :=
    @_root_.AlgebraicGeometry.exists_stage_polarizedModel _ _ _
      (_root_.AlgebraicGeometry.specAdjoinFinsetDiagram Γ(T, ⊤)) _
      (_root_.AlgebraicGeometry.affineStageCone T)
      (_root_.AlgebraicGeometry.isLimit_affineStageCone T) _ g ‹IsProper g› ‹Flat g› hfp M
      (‹Stacks.Ample.IsInvertibleModule Y M›) hM
  have _hLiinv : Stacks.Ample.IsInvertibleModule Yi Li := hLiinv
  have := _root_.AlgebraicGeometry.isNoetherianRing_adjoinFinset_int Γ(T, ⊤) i.unop
  exact finitePresentation_tailAlgebra_strHom_of_isPullback
    (R := Algebra.adjoin ℤ ((i.unop : Finset Γ(T, ⊤)) : Set Γ(T, ⊤))) gi Li q g
    ((_root_.AlgebraicGeometry.affineStageCone T).π.app i) M hpr hfl hfpi hampi hpb eL e he hband

/-! ### Over an affine open of an arbitrary base -/

section Restrict

variable {Y S : Scheme.{u}} (g : Y ⟶ S) [IsProper g] [Flat g]
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (U : S.Opens)

/-- The restriction `Γ(S, U) ⟶ Γ(U, ⊤)` of sections along the open immersion `U.ι : U ⟶ S` is
bijective. -/
theorem bijective_ι_appLE_self :
    Function.Bijective
      (U.ι.appLE U ⊤ (Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U)).hom := by
  rw [Scheme.Opens.ι_appLE]
  exact bijective_map_homOfLE_of_eq (SheafOfModules.unit S.ringCatSheaf) _
    (by rw [Scheme.Opens.ι_image_top])

/-- **Clause (3) of [Stacks, Tag 0D4F].**  For `g : Y ⟶ S` proper, flat and of finite
presentation, `ℳ` an invertible `𝒪_Y`-module ample relative to `g`, `e > 0` and `U ⊆ S` an affine
open over which the sections of `g_* ℳ^{⊗ n}`, `n ≥ e`, are finitely presented, the tail ring
`Γ(U, 𝒪_S ⊕ ⨁_{n ≥ e} g_* ℳ^{⊗ n})` is a finitely presented `Γ(S, U)`-algebra.

Restricting to the affine scheme `U` identifies the tail ring over `U` with that of
`g ∣_ U : g⁻¹U ⟶ U` over all of `U` (`U ⟶ S` is an open immersion), and the affine case
`finitePresentation_tailAlgebra_strHom_of_isAffine` applies there. -/
theorem finitePresentation_tailAlgebra_strHom
    (hfp : _root_.AlgebraicGeometry.FinitePresentation g)
    (hM : Stacks.RelativeAmple.IsRelativelyAmple g M) (e : ℕ) (he : 0 < e) (hU : IsAffineOpen U)
    (hband : ∀ n : ℕ, e ≤ n → Module.FinitePresentation Γ(S, U)
      Γ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), U)) :
    ((tailAlgebra g M e he).strHom U).FinitePresentation := by
  have : IsAffine U := hU
  have hV := Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U
  have := hfp.1
  have := hfp.2.1
  have := hfp.2.2
  have := isInvertible_tensorPower_of_isInvertibleModule Y M
  have hM' : Stacks.Ample.IsInvertibleModule (g ⁻¹ᵁ U).toScheme
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (g ⁻¹ᵁ U).ι.toLRSHom.toShHom M
  have w : (g ⁻¹ᵁ U).ι ≫ g = (g ∣_ U) ≫ U.ι := (morphismRestrict_ι g U).symm
  have hW : (g ⁻¹ᵁ U).ι ''ᵁ ((g ⁻¹ᵁ U).ι ⁻¹ᵁ (g ⁻¹ᵁ U)) = g ⁻¹ᵁ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
  have hΦ : ∀ n : ℤ, Function.Bijective (squarePieceMap (g ⁻¹ᵁ U).ι g (g ∣_ U) U.ι w M
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M) (Iso.refl _) U ⊤ hV n) :=
    fun n => bijective_sectionPull_of_isOpenImmersion M (g ⁻¹ᵁ U).ι n (g ⁻¹ᵁ U) hW _
      (fun x _ => x.2) (fun _ _ => trivial)
  have hρ := bijective_ι_appLE_self U
  refine finitePresentation_of_bijective_square _ _ _ _ hρ ?_
    (fun r => squareRingHom_strHom (g ⁻¹ᵁ U).ι g (g ∣_ U) U.ι w M
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M) (Iso.refl _) e e he he le_rfl U ⊤
        hV r) ?_
  · exact bijective_tailMapRingHom _ _ _ _ _ _ rfl hρ fun n _ => hΦ n
  refine finitePresentation_tailAlgebra_strHom_of_isAffine (g ∣_ U)
    ⟨inferInstance, inferInstance, inferInstance⟩ _
    ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (g ∣_ U) _).mpr
      (hM.2 U hU)) e he fun n hn => ?_
  have := hband n hn
  exact moduleFinitePresentation_of_bijective_semilinear
    (M := Γ((Scheme.Modules.pushforward g).obj
        ((Stacks.RelativeAmple.laurentPowers M).piece (n : ℤ)), U))
    (M' := Γ((Scheme.Modules.pushforward (g ∣_ U)).obj
        ((Stacks.RelativeAmple.laurentPowers
          ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M)).piece (n : ℤ)), ⊤))
    _ hρ _ (hΦ (n : ℤ))
    (fun r x => squarePieceMap_smul (g ⁻¹ᵁ U).ι g (g ∣_ U) U.ι w M
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M) (Iso.refl _) U ⊤ hV
        (n : ℤ) r x)

end Restrict

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
