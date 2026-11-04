module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedGradingRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothRelativeDimensionShift

/-!
# Base change of the localized Chern classes of an object whose Chern classes are defined

Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S`, let
`i : Z ⟶ X` be a closed immersion and let `E ∈ D(𝒪_X)` be perfect, with `E|_{X ∖ Z}` finite
locally free of rank `< p` in degree `0` and with defined Chern classes. Remark 0GUK defines
`c_p(Z ⟶ X, E) ∈ A^p(Z ⟶ X)` as the unique class whose restriction along the envelope `g` of a
chosen presentation of `E` is the class of Stacks 0FB2 upstairs
(`Stacks.Chow.LocalizedChernData.localizedChern`). This file proves that the class is compatible
with base change, as in Stacks 0FB3: for every morphism `f : X' ⟶ X` locally of finite type,

  `f^* c_p(Z ⟶ X, E) = c_p(Z' ⟶ X', Lf^*E)`,   `Z' = Z ×_X X'`,

and, in particular, that `c_p(Z ⟶ X, E)` restricts along the envelope of *every* presentation of
`E` to the class of Stacks 0FB2 there.

Both statements reduce to the following. Let `m : W ⟶ X` be locally of finite type and let
`g : Y ⟶ X` be the chosen envelope; on `W₀ = Y ×_X W` the two classes `ρ^* (g^* c_p(Z ⟶ X, E))`
and `σ^* (m^* c_p(Z ⟶ X, E))`, for the two projections `ρ : W₀ ⟶ Y` and `σ : W₀ ⟶ W`, cap every
class as `c_p(Z ⟶ X, E)` does on `W₀ ⟶ X`, read through canonical isomorphisms of fibre
products, so they agree; the first is the class of Stacks 0FB2 on `W₀` by Stacks 0FB3 and its
invariance under isomorphisms
(`Stacks.Chow.bivariantTransport_bivariantRestriction_graphChernClass_of_eq`).
The comparison of cap operations is organized by the predicate
`Stacks.Chow.BivariantClass.IsRestrictionAlong`.

## Main definitions

* `Stacks.Chow.BivariantClass.IsRestrictionAlong` — a class caps as the restriction of a given
  class along a given morphism, read on a closed subscheme identified with the base change.

## Main results

* `Stacks.Chow.BivariantClass.IsRestrictionAlong.eq` — the predicate determines the class.
* `Stacks.Chow.LocalizedChernData.supportedRestriction_supportedRestriction_localizedChern` — the
  comparison of the restrictions of `c_p(Z ⟶ X, E)` on `Y₀ ×_X W` (the restriction along the
  envelope of any presentation is
  `Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedChern_envelope`,
  LocalizedChern/DefinedChernClasses.lean).
* `Stacks.Chow.LocalizedChernData.properPushforwardChowCohomology_localizedChern` —
  `i_* ∘ c_p(Z ⟶ X, E) = c_p(E)` (Stacks 0FB2, equation 0FB1) for the classes of Remark 0GUK.
* `Stacks.Chow.LocalizedChernData.supportedRestriction_localizedChern` — Stacks 0FB3 for the
  classes of Remark 0GUK.

## References

* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

/-! ### Classes capping as a restriction -/

section IsRestrictionAlong

variable {C : ChowSituation.{u}} {G : GysinSystem C} {Z X : Scheme.{u}} {sZ : Z ⟶ C.S}
  [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {i : Z ⟶ X}
  [LocallyOfFiniteType i] {hi : i ≫ sX = sZ} {p : ℤ}

/-- **A class capping as the restriction of `c` along `m`.** Let `c ∈ A^p(Z ⟶ X)`, let
`m : W ⟶ X` and let `z : Z_W ⟶ W` come with `ζ : Z_W ⟶ Z`. A class `y ∈ A^p(Z_W ⟶ W)` caps as the
restriction of `c` along `m`, read on `Z_W` through `ζ`, when on every test scheme `t : T ⟶ W` its
cap operation is that of `c` on `t ≫ m`, pushed forward along an isomorphism
`Z ×_X T ≅ Z_W ×_W T` over `T` and over `Z`. When `Z_W` is the base change of `Z` along `m`,
through `ζ`, such a class is unique (`Stacks.Chow.BivariantClass.IsRestrictionAlong.eq`): it is the
restriction of Stacks 0F9Z, read on `Z_W`. -/
def BivariantClass.IsRestrictionAlong (c : BivariantClass C G sZ sX i hi p) {W ZW : Scheme.{u}}
    {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {sZW : ZW ⟶ C.S} [LocallyOfFiniteType sZW]
    {z : ZW ⟶ W} [LocallyOfFiniteType z] {hz : z ≫ sW = sZW} (m : W ⟶ X)
    [LocallyOfFiniteType m] (hm : m ≫ sX = sW) (ζ : ZW ⟶ Z)
    (y : BivariantClass C G sZW sW z hz p) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sW) k),
    ∃ (ψ : pullback i (t ≫ m) ⟶ pullback z t) (_ : IsIso ψ)
      (hψ : ψ ≫ (pullback.fst z t ≫ sZW) = pullback.fst i (t ≫ m) ≫ sZ),
      ψ ≫ pullback.snd z t = pullback.snd i (t ≫ m) ∧
        ψ ≫ pullback.fst z t ≫ ζ = pullback.fst i (t ≫ m) ∧
        y.cap t k α ≍ chowPushforwardOfIso C _ _ ψ hψ (k - p)
          (c.cap (t ≫ m) k (chowGroupCongr C (by rw [Category.assoc, hm]) k α))

variable {c : BivariantClass C G sZ sX i hi p} {W ZW : Scheme.{u}} {sW : W ⟶ C.S}
  [LocallyOfFiniteType sW] {sZW : ZW ⟶ C.S} [LocallyOfFiniteType sZW] {z : ZW ⟶ W}
  [LocallyOfFiniteType z] {hz : z ≫ sW = sZW} {m : W ⟶ X} [LocallyOfFiniteType m]
  {hm : m ≫ sX = sW} {ζ : ZW ⟶ Z}

/-- **A class capping as a restriction is determined**, when `Z_W` is the base change of `Z`
along `m`: the comparison isomorphisms of the definition are then forced. -/
theorem BivariantClass.IsRestrictionAlong.eq (hpb : IsPullback ζ z i m)
    {y y' : BivariantClass C G sZW sW z hz p} (hy : c.IsRestrictionAlong m hm ζ y)
    (hy' : c.IsRestrictionAlong m hm ζ y') : y = y' := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  obtain ⟨ψ, _, hψ, h₁, h₂, h₃⟩ := hy T t k α
  obtain ⟨ψ', _, hψ', h₁', h₂', h₃'⟩ := hy' T t k α
  obtain rfl : ψ = ψ' := by
    refine pullback.hom_ext (hpb.hom_ext ?_ ?_) (h₁.trans h₁'.symm)
    · simpa only [Category.assoc] using h₂.trans h₂'.symm
    · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h₁,
        ← Category.assoc, h₁']
  exact eq_of_heq (h₃.trans h₃'.symm)

/-- The restriction of Stacks 0F9Z of `c` along `m` caps as the restriction of `c` along `m`, read
on `Z ×_X W` through the first projection. -/
theorem BivariantClass.isRestrictionAlong_bivariantRestriction
    (hgys : G.IsNaturalUnderBaseChangeIso) (c : BivariantClass C G sZ sX i hi p) (m : W ⟶ X)
    [LocallyOfFiniteType m] :
    c.IsRestrictionAlong m rfl (pullback.fst i m)
      (bivariantRestriction C G sZ sX i hi m p hgys c) := fun T t _ k α ↦
  ⟨(pullbackLeftPullbackSndIso i m t).inv, inferInstance, by simp, by simp, by simp, HEq.rfl⟩

/-- A class capping as the restriction of `c` along `m` caps, read against equal structure
morphisms (`Stacks.Chow.bivariantClassCongrBase`), as the restriction of `c` along `m`. -/
theorem BivariantClass.IsRestrictionAlong.bivariantClassCongrBase
    {y : BivariantClass C G sZW sW z hz p} (hy : c.IsRestrictionAlong m hm ζ y)
    {sZW' : ZW ⟶ C.S} [LocallyOfFiniteType sZW'] {sW' : W ⟶ C.S} [LocallyOfFiniteType sW']
    (hsA : sZW = sZW') (hsW : sW = sW') {hz' : z ≫ sW' = sZW'} :
    c.IsRestrictionAlong m (hm.trans hsW) ζ
      (Stacks.Chow.bivariantClassCongrBase C G z hsA hsW (hv := hz) (hv' := hz') p y) := by
  subst hsA hsW
  exact hy

/-- A class capping as the restriction of `c` along `m` caps as the restriction of `c` along any
morphism equal to `m`. -/
theorem BivariantClass.IsRestrictionAlong.of_eq {y : BivariantClass C G sZW sW z hz p}
    (hy : c.IsRestrictionAlong m hm ζ y) {m' : W ⟶ X} [LocallyOfFiniteType m'] (hmm : m = m') :
    c.IsRestrictionAlong m' (by rw [← hmm]; exact hm) ζ y := by
  subst hmm
  exact hy

/-- **The restriction of a class capping as a restriction.** If `y` caps as the restriction of `c`
along `m`, then its restriction of Stacks 0F9Z along `h : V ⟶ W` caps as the restriction of `c`
along `h ≫ m`. -/
theorem BivariantClass.IsRestrictionAlong.bivariantRestriction
    {y : BivariantClass C G sZW sW z hz p} (hy : c.IsRestrictionAlong m hm ζ y)
    (hgys : G.IsNaturalUnderBaseChangeIso) {V : Scheme.{u}} (h : V ⟶ W) [LocallyOfFiniteType h] :
    c.IsRestrictionAlong (h ≫ m) (by rw [Category.assoc, hm]) (pullback.fst z h ≫ ζ)
      (Stacks.Chow.bivariantRestriction C G sZW sW z hz h p hgys y) := by
  intro T t _ k α
  obtain ⟨ψ, _, hψ, h₁, h₂, h₃⟩ :=
    hy T (t ≫ h) k (chowGroupCongr C (Category.assoc t h sW).symm k α)
  have e : t ≫ (h ≫ m) = (t ≫ h) ≫ m := (Category.assoc _ _ _).symm
  set κ := (pullback.congrHom (rfl : i = i) e).hom
  set w := (pullbackLeftPullbackSndIso z h t).inv
  have hw : w ≫ (pullback.fst (pullback.snd z h) t ≫ (pullback.fst z h ≫ sZW)) =
      pullback.fst z (t ≫ h) ≫ sZW := by simp [w]
  have hκ : κ ≫ (pullback.fst i ((t ≫ h) ≫ m) ≫ sZ) = pullback.fst i (t ≫ (h ≫ m)) ≫ sZ := by
    simp [κ]
  refine ⟨κ ≫ ψ ≫ w, inferInstance, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc, hw]
    rw [hψ, hκ]
  · have : w ≫ pullback.snd (pullback.snd z h) t = pullback.snd z (t ≫ h) := by simp [w]
    simp only [Category.assoc]
    rw [this, h₁]
    simp [κ]
  · have : w ≫ pullback.fst (pullback.snd z h) t ≫ pullback.fst z h = pullback.fst z (t ≫ h) := by
      simp [w]
    simp only [Category.assoc, reassoc_of% this, h₂]
    simp [κ]
  · refine (chowPushforwardOfIso_heq_comp_of_comp_eq ψ w (ψ ≫ w) rfl hψ hw rfl rfl rfl _ _
      h₃).trans (heq_of_eq ?_)
    rw [chowGroupCongr_chowGroupCongr,
      ← chowPushforwardOfIso_congrHom_cap C G sZ sX i hi p c e hκ k α
        (by simp only [Category.assoc, hm]) (by simp only [Category.assoc, hm]),
      chowPushforwardOfIso_comp_apply]

/-- **The transport of a class capping as a restriction.** If `y` caps as the restriction of `c`
along `m`, read on `Z_W` through `ζ`, then its transport (`Stacks.Chow.bivariantTransport`) along
an isomorphism `θ : Z_W ≅ Z'_W` over `W` caps as the restriction of `c` along `m`, read on `Z'_W`
through `θ⁻¹ ≫ ζ`. -/
theorem BivariantClass.IsRestrictionAlong.bivariantTransport
    {y : BivariantClass C G sZW sW z hz p} (hy : c.IsRestrictionAlong m hm ζ y)
    (hgys : G.IsNaturalUnderBaseChangeIso) {ZW' : Scheme.{u}} {sZW' : ZW' ⟶ C.S}
    [LocallyOfFiniteType sZW'] (z' : ZW' ⟶ W) [LocallyOfFiniteType z'] (hz' : z' ≫ sW = sZW')
    (θ : ZW ≅ ZW') (hθ : θ.hom ≫ z' = z) :
    c.IsRestrictionAlong m hm (θ.inv ≫ ζ)
      (Stacks.Chow.bivariantTransport C G sZW sZW' sW z hz z' hz' θ hθ p hgys y) := by
  intro T t _ k α
  obtain ⟨ψ, _, hψ, h₁, h₂, h₃⟩ := hy T t k α
  set w := (transportPullbackIso z z' θ hθ t).hom
  have hw := transportPullbackIso_hom_comp_base C sZW sZW' sW z hz z' hz' θ hθ t
  exact ⟨ψ ≫ w, inferInstance, by rw [Category.assoc, hw, hψ], by simp [w, h₁], by simp [w, h₂],
    chowPushforwardOfIso_heq_comp_of_comp_eq ψ w (ψ ≫ w) rfl hψ hw rfl rfl rfl _ _ h₃⟩

end IsRestrictionAlong

/-! ### Base change of the localized Chern class of Remark 0GUK -/

namespace LocalizedChernData

attribute [local instance 10000] HasDerivedCategory.standard

variable {D : LocalizedChernData.{u}} (hE : HasDefinedChernClasses D.E)
  (h : D.IsFiniteLocallyFreeOfRankLTOnComplement)

/-- **The two restrictions to `W₀ = Y ×_X W` agree.** Let `g : Y ⟶ X` be the envelope of the
presentation of `E` chosen by `HasDefinedChernClasses`, let `m : W ⟶ X` be locally of finite type
and `σ : W₀ = Y ×_X W ⟶ W` the base change of `g`, and suppose the data
`((Z ⟶ X, E) ×_X W) ×_W W₀` form an instance `S` of Situation 0GUJ. Then restricting
`c_p(Z ⟶ X, E)` along `m` and then along `σ` gives the class `c_p` of Stacks 0FB2 for `S`.

Both are compared with the restriction along the other projection `ρ : W₀ ⟶ Y` of the class of
Stacks 0FB2 on `Y`, which is the class of Stacks 0FB2 for `S` by Stacks 0FB3 and its invariance
under isomorphisms; all three cap as `c_p(Z ⟶ X, E)` does on `W₀ ⟶ X`. -/
theorem supportedRestriction_supportedRestriction_localizedChern {W : Scheme.{u}} (m : W ⟶ D.X)
    [LocallyOfFiniteType m] (S : LocalizedSituation.{u})
    (hS : S.toLocalizedChernData = (D.pullback m).pullback (pullback.snd hE.some.f m))
    (hS' : S.IsFiniteLocallyFreeOfRankLTOnComplement) :
    supportedRestriction D.base (pullback.snd D.i m ≫ (m ≫ D.a)) (m ≫ D.a) (pullback.snd D.i m)
        rfl (pullback.snd hE.some.f m)
        (supportedRestriction D.base (D.i ≫ D.a) D.a D.i rfl m (D.localizedChern hE h)) ≍
      S.localizedChern hS' := by
  obtain ⟨D₀, fin⟩ := S
  subst hS
  let S : LocalizedSituation.{u} := ⟨(D.pullback m).pullback (pullback.snd hE.some.f m), fin⟩
  let H₀ := hE.some
  let SY := D.envelopeSituation H₀
  let ρ := pullback.fst H₀.f m
  let σ := pullback.snd H₀.f m
  have hcond : ρ ≫ H₀.f = σ ≫ m := pullback.condition
  -- the two descriptions of `Z ×_X W₀`
  have sq₁ : IsPullback (pullback.fst (pullback.snd D.i H₀.f) ρ ≫ pullback.fst D.i H₀.f)
      (pullback.snd (pullback.snd D.i H₀.f) ρ) D.i (ρ ≫ H₀.f) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have sq₂ : IsPullback (pullback.fst (pullback.snd D.i m) σ ≫ pullback.fst D.i m)
      (pullback.snd (pullback.snd D.i m) σ) D.i (ρ ≫ H₀.f) := by
    rw [hcond]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  let θ := sq₁.isoIsPullback _ _ sq₂
  have hθ : θ.hom ≫ S.i = pullback.snd SY.i ρ := sq₁.isoIsPullback_hom_snd _ _ sq₂
  have hζ : θ.inv ≫ pullback.fst (pullback.snd D.i H₀.f) ρ ≫ pullback.fst D.i H₀.f =
      pullback.fst (pullback.snd D.i m) σ ≫ pullback.fst D.i m :=
    sq₁.isoIsPullback_inv_fst _ _ sq₂
  -- the two pullbacks of `E` to `W₀`
  have eE : (derivedPullback ρ.toLRSHom.toShHom).obj SY.E ≅ S.E :=
    derivedPullbackCompIsoOfScheme ρ H₀.f D.E ≪≫
      eqToIso (congrArg (fun F => F.obj D.E)
        (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
          (congrArg (fun m => m.toLRSHom.toShHom) hcond))) ≪≫
      (derivedPullbackCompIsoOfScheme σ m D.E).symm
  have ha' : ρ ≫ SY.a = S.a := by simpa only [Category.assoc] using hcond =≫ D.a
  -- Stacks 0FB3 and its invariance under isomorphisms, along `ρ`
  have e₁ := bivariantTransport_bivariantRestriction_graphChernClass_of_eq D.base SY.a ρ SY.E
    SY.perfect S.E S.perfect eE SY.i S.i θ hθ SY.graphSubschemeι
    SY.isFiniteLocallyFree_graphObjectRestrictHomology SY.hasDefinedChernClasses_graphObject D.p
    SY.mem_range_graphSubschemeι
    (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H₀.f) S.a ha' rfl
    S.graphSubschemeι S.isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject S.mem_range_graphSubschemeι
    (SY.finiteLocallyFreeRank_graphSubscheme_lt h.pullback)
    (S.finiteLocallyFreeRank_graphSubscheme_lt hS')
  -- the restriction along `ρ` caps as the restriction of `c_p(Z ⟶ X, E)` along `ρ ≫ g`
  have hΓ := ((BivariantClass.isRestrictionAlong_bivariantRestriction
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) (D.localizedChern hE h)
      H₀.f).bivariantRestriction (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
      ρ).bivariantTransport (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) S.i
      (by rw [ha']) θ hθ
  rw [D.bivariantRestriction_localizedChern hE h, hζ] at hΓ
  -- so does the restriction along `m` and then along `σ`
  have hy := ((((BivariantClass.isRestrictionAlong_bivariantRestriction
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) (D.localizedChern hE h)
      m).bivariantClassCongrBase
      (pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl m).symm rfl
      (hz' := rfl)).bivariantRestriction
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base) σ).bivariantClassCongrBase
      (pullbackSnd_comp_structureMorphism_eq D.base (pullback.snd D.i m ≫ (m ≫ D.a)) (m ≫ D.a)
        (pullback.snd D.i m) rfl σ).symm rfl
      (hz' := rfl)).bivariantClassCongrBase rfl ha'.symm (hz' := by rw [ha'])
  refine HEq.trans (bivariantClassCongrBase_heq (G := gysinSystemOfInvertible D.base) S.i rfl
    ha'.symm (hv := rfl) (hv' := by rw [ha']) D.p _).symm ?_
  rw [(hy.of_eq hcond.symm).eq sq₂ hΓ]
  exact (heq_of_eq e₁).trans (bivariantClassCongrBase_heq (G := gysinSystemOfInvertible D.base)
    S.i rfl ha'.symm D.p (S.localizedChern hS'))

/-- Transport of a bivariant class along equal structure morphisms is inverse to the transport
along the symmetric equality. -/
private theorem bivariantClassCongrBase_symm_eq_iff {C : ChowSituation.{u}} {G : GysinSystem C}
    {A W : Scheme.{u}} {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sW : W ⟶ C.S} [LocallyOfFiniteType sW] (v : A ⟶ W) [LocallyOfFiniteType v] (hs : sA = sA')
    {hv : v ≫ sW = sA} {hv' : v ≫ sW = sA'} {p : ℤ} {y : BivariantClass C G sA' sW v hv' p}
    {y' : BivariantClass C G sA sW v hv p} :
    bivariantClassCongrBase C G v hs.symm rfl (hv := hv') (hv' := hv) p y = y' ↔
      y = bivariantClassCongrBase C G v hs rfl (hv := hv) (hv' := hv') p y' := by
  subst hs
  rfl

/-- The restriction of `c_p(Z ⟶ X, E)` along the envelope of any presentation of `E`, in the
`Stacks.Chow.supportedRestriction` reading: the class of Stacks 0FB2 for the instance of
Situation 0GUJ over the presentation. This is
`Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedChern_envelope` with the closed
subscheme `Z ×_X Y` read over the base through `Y`. -/
theorem supportedRestriction_localizedChern_envelope (H : EnvelopePresentation D.E) :
    supportedRestriction D.base (D.i ≫ D.a) D.a D.i rfl H.f (D.localizedChern hE h) =
      (D.envelopeSituation H).localizedChern h.pullback := by
  have hs := pullbackSnd_comp_structureMorphism_eq D.base (D.i ≫ D.a) D.a D.i rfl H.f
  exact (bivariantClassCongrBase_symm_eq_iff _ hs).2
    (bivariantRestriction_localizedChern_envelope hE H h)

/-- **`i_* ∘ c_p(Z ⟶ X, E) = c_p(E)` for the localized Chern class of Remark 0GUK** (Stacks 0FB2,
equation 0FB1, with `∘` the pushforward of Stacks 0EPK): restriction to `A^p(Y)` along the envelope
`g : Y ⟶ X` of the chosen presentation of `E` is injective, it commutes with the pushforward, and
on `Y` both sides are the corresponding classes of `Lg^*E` in Situation 0GUJ, where the identity
is Stacks 0FB2. -/
theorem properPushforwardChowCohomology_localizedChern :
    properPushforwardChowCohomology D.base D.a (D.i ≫ D.a) D.i rfl (D.localizedChern hE h) =
      perfectChernClass D.base D.a hE D.p := by
  refine chowCohomologyRestriction_injective_of_isEnvelope D.base (gysinSystemOfInvertible D.base)
    D.a hE.some.f D.p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso D.base)
    hE.some.envelope ?_
  rw [chowCohomologyRestriction_properPushforwardChowCohomology,
    supportedRestriction_localizedChern_envelope hE h hE.some, ← TotalChowClass.res_rfl_apply,
    res_perfectChernClass_derivedPullback_of_comp_eq D.base D.a hE hE.some.f rfl
      (hE.derivedPullback _)]
  exact LocalizedSituation.properPushforwardChowCohomology_localizedChern
    (D.envelopeSituation hE.some) h.pullback

/-- **Stacks 0FB3 for the localized Chern class of Remark 0GUK.** Let `E ∈ D(𝒪_X)` be perfect with
defined Chern classes and `E|_{X ∖ Z}` finite locally free of rank `< p` in degree `0`, and let
`f : X' ⟶ X` be locally of finite type, with `Z' = Z ×_X X'`. Then the restriction (Remark 0F9Z)
of `c_p(Z ⟶ X, E)` along `f` is `c_p(Z' ⟶ X', Lf^*E)`.

The class `c_p(Z' ⟶ X', Lf^*E)` is characterized by its restriction along the envelope
`Y₀ ×_X X' ⟶ X'` of the base change of the chosen presentation of `E`
(`Stacks.Chow.LocalizedChernData.bivariantRestriction_localizedChern_envelope`), and the
restriction of `f^* c_p(Z ⟶ X, E)` there is computed by
`Stacks.Chow.LocalizedChernData.supportedRestriction_supportedRestriction_localizedChern`. -/
theorem supportedRestriction_localizedChern {X' : Scheme.{u}} (f : X' ⟶ D.X)
    [LocallyOfFiniteType f] :
    supportedRestriction D.base (D.i ≫ D.a) D.a D.i rfl f (D.localizedChern hE h) =
      (D.pullback f).localizedChern (hE.derivedPullback f) h.pullback := by
  let H₀' := hE.some.derivedPullback f
  have : LocallyOfFiniteType H₀'.f :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd hE.some.f f))
  let S₁ := (D.pullback f).envelopeSituation H₀'
  have h₁ : S₁.IsFiniteLocallyFreeOfRankLTOnComplement := h.pullback.pullback
  have hs := pullbackSnd_comp_structureMorphism_eq D.base (pullback.snd D.i f ≫ (f ≫ D.a))
    (f ≫ D.a) (pullback.snd D.i f) rfl H₀'.f
  refine ((D.pullback f).existsUnique_bivariantRestriction_eq_envelopeChern H₀'
    h.pullback).unique ?_
    (bivariantRestriction_localizedChern_envelope (D := D.pullback f) (hE.derivedPullback f) H₀'
      h.pullback)
  exact (bivariantClassCongrBase_symm_eq_iff _ hs).1 (eq_of_heq
    (supportedRestriction_supportedRestriction_localizedChern hE h f S₁ rfl h₁))

end LocalizedChernData

end Stacks.Chow

end
