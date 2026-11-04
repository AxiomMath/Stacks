module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.UniversalHomeomorphismLegs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InverseImageLocallyAnnihilated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FieldExtensionSmoothLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.FieldTheory.PerfectClosure
public import StacksFrontier.FieldTheory.Separable.PerfectField

/-!
# Base change of direct images along an extension of the base field

Let `L/K` be an extension of fields, let `g : T ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes over `K`, and let `g_L : T_L ⟶ S_L` be its base change to `Spec L`.
[Stacks, Tag 0F1C] asserts that for `E ∈ D⁺(T_étale)` whose cohomology sheaves have stalks which
are torsion of orders invertible in `K`, the base change map
`(S_L ⟶ S)⁻¹ Rg_* E ⟶ Rg_{L,*} E_L` is an isomorphism, `E_L` being the pullback of `E` to
`T_L`.

The source deduces this from the smooth base change theorem in the form of [Stacks, Tag 0F09].
That theorem is not available in this repository, because the smooth base change theorem
[Stacks, Tag 0EYU] is not. So the results here take it as an explicit argument
`hSB : SmoothLimitBaseChange`, and they are **not** registered. Everything else in the source's
proof is proved.

## Main results

* `Stacks.EtaleCohomology.FieldExtensionBaseChange.isIso_of_isSeparableExtension` — the
  separable case. `L` is the filtered colimit of its smooth `K`-subalgebras
  ([Stacks, Tag 07BV]), so `S_L` is a directed limit of schemes smooth over `S` with affine
  transition morphisms, and Tag 0F09 applies.
* `Stacks.EtaleCohomology.FieldExtensionBaseChange.isIso_of_isPullback` — the general case, for
  any presentation of `S_L` and `T_L` as fibre products. Let `K'` and `L'` be the perfect closures
  of `K` and `L` inside an algebraic closure of `L`. Then `Spec K' ⟶ Spec K` and
  `Spec L' ⟶ Spec L` are universal homeomorphisms ([Stacks, Tag 0BRA]), so base change along them
  is invisible to étale cohomology ([Stacks, Tag 03SI]). This reduces the lemma to `L'/K'`, which
  is separable because `K'` is perfect.
* `Stacks.EtaleCohomology.FieldExtensionBaseChange.isIso_smallEtaleDerivedBaseChangeAb_baseChange`
  — the statement of [Stacks, Tag 0F1C], with `S_L = Spec L ×_K S` and `T_L = Spec L ×_K T` the
  chosen fibre products.

## Implementation notes

*The reduction.* The square of `g_L'` over `g` is pasted from squares in two ways. Through
`g_L` it is the square of `g_L` over `g` followed by the square of `g_L'` over `g_L`. Through
`g_K'` it is the square of `g_K'` over `g` followed by the square of `g_L'` over `g_K'`. Each
pasting expresses the base change map of the outer square through those of its two squares
(`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app`). In the second
pasting both squares have invertible base change maps: the first because its horizontal legs are
universal homeomorphisms, the second by the separable case. In the first pasting the second square
again has universal homeomorphisms as legs. What remains is the inverse image along
`S_L' ⟶ S_L` of the base change map of `g_L` over `g`. That inverse image is an exact equivalence,
so it reflects isomorphisms.

*The torsion condition.* The torsion hypothesis is taken in the form
`Stacks.Torsion.IsPrimeToCharacteristicTorsion` at `ringExpChar K`: every local section is
locally killed by a positive integer prime to the exponential characteristic of `K`, that is,
invertible in `K`. For the appeal to Tag 0F09 it becomes `HasTorsionOrdersInvertibleOn S`,
since an integer invertible in `K` is invertible on every `K`-scheme.

## References

* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 07BV](https://stacks.math.columbia.edu/tag/07BV)
* [Stacks Project, Tag 0BRA](https://stacks.math.columbia.edu/tag/0BRA)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FieldExtensionBaseChange

-- `smallEtaleDerivedBaseChangeAb` (BaseChangeHigher/BaseChangeCondition.lean) is built under the
-- standard model, so its components live in the standard bounded below derived categories.
attribute [local instance] HasDerivedCategory.standard

/-! ### The torsion condition -/

/-- A positive integer prime to the exponential characteristic of a field is invertible in it. -/
theorem isUnit_natCast_of_coprime_ringExpChar (K : Type*) [Field K] {n : ℕ} (hn : 0 < n)
    (hc : n.Coprime (ringExpChar K)) : IsUnit (n : K) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · rw [ringExpChar, max_eq_left hp.one_le] at hc
    exact (CharP.isUnit_natCast_iff hp).mpr (hp.coprime_iff_not_dvd.mp hc.symm)
  · have : CharP K 0 := hp ▸ inferInstance
    have : CharZero K := CharP.charP_to_charZero _
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')

/-- For a scheme `S` over a field `K`, an abelian sheaf which is torsion prime to the exponential
characteristic of `K` has torsion of orders invertible on `S`. -/
theorem hasTorsionOrdersInvertibleOn_of_isPrimeToCharacteristicTorsion {K : Type u} [Field K]
    {S X : Scheme.{u}} (sS : S ⟶ Spec (.of K)) {F : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology X) (ringExpChar K)
      F) :
    HasTorsionOrdersInvertibleOn S F := by
  rw [isPrimeToCharacteristicTorsion_iff_locallyAnnihilated] at hF
  intro U x
  obtain ⟨R, hR, h⟩ := hF U x
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨n, ⟨hn, hc⟩, hx⟩ := h V f hf
  refine ⟨n, ⟨hn, ?_⟩, hx⟩
  simpa using (isUnit_natCast_of_coprime_ringExpChar K hn hc).map
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ sS.appTop).hom

/-- The cohomology sheaves of the derived inverse image of `E` are the inverse images of the
cohomology sheaves of `E`, so they inherit torsion prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_homology_derivedPullback {X Y : Scheme.{u}} (v : X ⟶ Y)
    {p : ℕ} (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})) (q : ℤ)
    (hE : Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology Y) p
      ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology X) p
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((smallEtalePullbackAb v).rightDerivedFunctorPlus.obj E)) := by
  rw [isPrimeToCharacteristicTorsion_iff_locallyAnnihilated] at hE ⊢
  have h := locallyAnnihilated_etaleAbelianInverseImage.{u, u + 1} v
    ⟨1, one_pos, Nat.coprime_one_left p⟩
    (fun m n ⟨hm, hm'⟩ ⟨hn, hn'⟩ ↦ ⟨Nat.mul_pos hm hn, Nat.coprime_mul_iff_left.2 ⟨hm', hn'⟩⟩)
    _ hE
  exact LocallyAnnihilated.of_epi
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb v) q).app E ≪≫
      (smallEtalePullbackAbIsoEtaleAbelianInverseImage v).app _).inv h

/-- Torsion prime to the exponential characteristic of `K` in the cohomology of `E` gives torsion
prime to that of any extension `K'` in the cohomology of a derived inverse image of `E`. -/
private theorem isPrimeToCharacteristicTorsion_homology_derivedPullback_of_algebra (K K' : Type*)
    [Field K] [Field K'] [Algebra K K'] {X Y : Scheme.{u}} (v : X ⟶ Y)
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})) (q : ℤ)
    (hE : Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology Y) (ringExpChar K)
      ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology X) (ringExpChar K')
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((smallEtalePullbackAb v).rightDerivedFunctorPlus.obj E)) := by
  have : ExpChar K' (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K K').injective (ringExpChar K)
  rw [ringExpChar.eq K' (ringExpChar K)]
  exact isPrimeToCharacteristicTorsion_homology_derivedPullback v E q hE

/-! ### Conservativity of inverse image along an equivalence -/

/-- If inverse image of abelian sheaves along `a` is an equivalence, its derived functor on
bounded below derived categories reflects isomorphisms: it commutes with cohomology, and an
equivalence reflects isomorphisms. -/
theorem isIso_of_isIso_rightDerivedFunctorPlus_map {X Y : Scheme.{u}} (a : X ⟶ Y)
    [(smallEtalePullbackAb a).IsEquivalence]
    {M N : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (φ : M ⟶ N)
    (h : IsIso ((smallEtalePullbackAb a).rightDerivedFunctorPlus.map φ)) : IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff] at h ⊢
  intro n
  have : IsIso ((smallEtalePullbackAb a).map ((DerivedCategory.Plus.homologyFunctor _ n).map φ)) :=
    (NatIso.isIso_map_iff
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb a) n) φ).1 (h n)
  exact isIso_of_reflects_iso _ (smallEtalePullbackAb a)

/-! ### Fibre products over the base -/

section FibreProducts

variable {B Z : Scheme.{u}} (φ : Z ⟶ B) {S T : Scheme.{u}} (sS : S ⟶ B) (sT : T ⟶ B)
  (g : T ⟶ S) (hg : g ≫ sS = sT)

/-- The base change `Z ×_B T ⟶ Z ×_B S` of `g` along `φ`. -/
def baseChangeMap : pullback φ sT ⟶ pullback φ sS :=
  pullback.map φ sT φ sS (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])

/-- The base change of `g` commutes with the projections to `Z`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_fst :
    baseChangeMap φ sS sT g hg ≫ pullback.fst φ sS = pullback.fst φ sT :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base change of `g` lies over `g` under the projections to `S` and `T`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_snd :
    baseChangeMap φ sS sT g hg ≫ pullback.snd φ sS = pullback.snd φ sT ≫ g :=
  pullback.lift_snd _ _ _

/-- The square of the base change of `g` over `g` is cartesian. -/
theorem isPullback_baseChangeMap :
    IsPullback (baseChangeMap φ sS sT g hg) (pullback.snd φ sT) (pullback.snd φ sS) g := by
  refine IsPullback.of_right ?_ (baseChangeMap_snd φ sS sT g hg) (IsPullback.of_hasPullback φ sS)
  rw [baseChangeMap_fst, hg]
  exact IsPullback.of_hasPullback φ sT

include hg in
/-- The square of `g_L : T_L ⟶ S_L` over `g` is cartesian, for any presentations of `S_L` and
`T_L` as fibre products over `B`. -/
theorem isPullback_of_isPullback {SL TL : Scheme.{u}} {qS : SL ⟶ Z} {pS : SL ⟶ S}
    (hS : IsPullback qS pS φ sS) {qT : TL ⟶ Z} {pT : TL ⟶ T} (hT : IsPullback qT pT φ sT)
    (gL : TL ⟶ SL) (hgq : gL ≫ qS = qT) (hgp : gL ≫ pS = pT ≫ g) :
    IsPullback gL pT pS g :=
  IsPullback.of_right (by rwa [hgq, hg]) hgp hS

variable {Z' : Scheme.{u}} (ψ : Z' ⟶ Z) (χ : Z' ⟶ B) (hχ : ψ ≫ φ = χ)
  {SL : Scheme.{u}} {qS : SL ⟶ Z} {pS : SL ⟶ S} (hS : IsPullback qS pS φ sS)

/-- The comparison `Z' ×_B S ⟶ S_L` over `Z' ⟶ Z`, for a presentation `S_L = Z ×_B S`. -/
def liftMap : pullback χ sS ⟶ SL :=
  hS.lift (pullback.fst χ sS ≫ ψ) (pullback.snd χ sS)
    (by rw [Category.assoc, hχ, pullback.condition])

/-- The comparison `liftMap` followed by `qS` is the projection to `Z'` followed by `ψ`. -/
@[reassoc (attr := simp)]
theorem liftMap_fst : liftMap φ sS ψ χ hχ hS ≫ qS = pullback.fst χ sS ≫ ψ :=
  hS.lift_fst _ _ _

/-- The comparison `liftMap` followed by `pS` is the projection to `S`. -/
@[reassoc (attr := simp)]
theorem liftMap_snd : liftMap φ sS ψ χ hχ hS ≫ pS = pullback.snd χ sS :=
  hS.lift_snd _ _ _

/-- `Z' ×_B S` is the fibre product of `S_L = Z ×_B S` with `Z'` over `Z`. -/
theorem isPullback_liftMap :
    IsPullback (pullback.fst χ sS) (liftMap φ sS ψ χ hχ hS) ψ qS := by
  refine (IsPullback.of_right ?_ (liftMap_fst φ sS ψ χ hχ hS) hS.flip).flip
  rw [liftMap_snd, hχ]
  exact (IsPullback.of_hasPullback χ sS).flip

/-- If `Z' ⟶ Z` is a universal homeomorphism, so is the comparison `Z' ×_B S ⟶ S_L`. -/
private theorem universalHomeomorphism_liftMap [UniversalHomeomorphism ψ] :
    UniversalHomeomorphism (liftMap φ sS ψ χ hχ hS) :=
  Stacks.Etale.universalHomeomorphism_of_isPullback (isPullback_liftMap φ sS ψ χ hχ hS).flip

end FibreProducts

/-! ### The separable case -/

section Separable

variable (hSB : SmoothLimitBaseChange.{u}) (K L : Type u) [Field K] [Field L] [Algebra K L]
  {S T : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (sT : T ⟶ Spec (.of K)) (g : T ⟶ S)
  [QuasiCompact g] [QuasiSeparated g] (hg : g ≫ sS = sT)

include hSB hg in
/-- **The separable case of [Stacks, Tag 0F1C]**, granted [Stacks, Tag 0F09]. For `L/K`
separable, `S_L` is the directed limit of the schemes `Spec A ×_K S`, with `A` running over the
smooth `K`-subalgebras of `L`. These are smooth over `S` and have affine transition morphisms, so
Tag 0F09 applies to the square of `g_L` over `g`. -/
theorem isIso_of_isSeparableExtension [Algebra.IsSeparableExtension K L]
    {SL TL : Scheme.{u}} {qS : SL ⟶ Spec (.of L)} {pS : SL ⟶ S}
    (hS : IsPullback qS pS (Spec.map (CommRingCat.ofHom (algebraMap K L))) sS)
    {qT : TL ⟶ Spec (.of L)} {pT : TL ⟶ T}
    (hT : IsPullback qT pT (Spec.map (CommRingCat.ofHom (algebraMap K L))) sT)
    (gL : TL ⟶ SL) (hgq : gL ≫ qS = qT) (hgp : gL ≫ pS = pT ≫ g)
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (hE : ∀ q : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology T)
      (ringExpChar K) ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    IsIso ((smallEtaleDerivedBaseChangeAb pS g gL pT hgp).app E) := by
  let e := hS.isoPullback
  let c := (FieldExtensionLimit.baseChangeCone (L := L) sS).extend e.hom
  have hc : IsLimit c := (FieldExtensionLimit.isLimitBaseChangeCone sS).ofIsoLimit
    ((FieldExtensionLimit.baseChangeCone (L := L) sS).extendIso e.symm)
  have hcg : ∀ i, c.π.app i ≫ (FieldExtensionLimit.baseChangeDiagramToBase (L := L) sS).app i =
      pS := fun i ↦ (Category.assoc e.hom _ _).trans
    ((congrArg (e.hom ≫ ·) (FieldExtensionLimit.baseChangeCone_π_app_comp sS i)).trans
      hS.isoPullback_hom_snd)
  exact hSB _ S _ _ (FieldExtensionLimit.smooth_baseChangeDiagramToBase_app sS)
    (FieldExtensionLimit.isAffineHom_baseChangeDiagram_map sS) c hc pS hcg T TL g gL pT
    (isPullback_of_isPullback _ sS sT g hg hS hT gL hgq hgp) E fun q ↦
      hasTorsionOrdersInvertibleOn_of_isPrimeToCharacteristicTorsion sS (hE q)

end Separable

/-! ### The general case -/

section General

/-- Two base change maps of squares whose horizontal legs agree are invertible together. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_congr {X' Y S T : Scheme.{u}} {a a' : X' ⟶ S}
    (g : T ⟶ S) (h : Y ⟶ X') {b b' : Y ⟶ T} (ha : a = a') (hb : b = b') (w : h ≫ a = b ≫ g)
    (w' : h ≫ a' = b' ≫ g) (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1})) :
    IsIso ((smallEtaleDerivedBaseChangeAb a g h b w).app M) ↔
      IsIso ((smallEtaleDerivedBaseChangeAb a' g h b' w').app M) := by
  subst ha hb
  rfl

section Paste

variable {S T S₁ T₁ S₂ T₂ : Scheme.{u}} (g : T ⟶ S) (g₁ : T₁ ⟶ S₁) (g₂ : T₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S₁) (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T₁) (w₁ : g₁ ≫ u₁ = v₁ ≫ g)
  (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))

/-- In a pasting of two squares whose first square has universal homeomorphisms as horizontal
legs, the outer base change map is invertible at `E` once that of the second square is. -/
private theorem isIso_app_paste_of_universalHomeomorphism [UniversalHomeomorphism u₁]
    [UniversalHomeomorphism v₁]
    (h : IsIso ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
      ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj E))) :
    IsIso ((smallEtaleDerivedBaseChangeAb (u₂ ≫ u₁) g g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).app E) := by
  have := isIso_smallEtaleDerivedBaseChangeAb_of_universalHomeomorphism u₁ g g₁ v₁ w₁
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ E]
  infer_instance

/-- In a pasting of two squares whose second square has universal homeomorphisms as horizontal
legs, the base change map of the first square is invertible at `E` once the outer one is. -/
private theorem isIso_app_of_isIso_paste_of_universalHomeomorphism [UniversalHomeomorphism u₂]
    [UniversalHomeomorphism v₂]
    (h : IsIso ((smallEtaleDerivedBaseChangeAb (u₂ ≫ u₁) g g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).app E)) :
    IsIso ((smallEtaleDerivedBaseChangeAb u₁ g g₁ v₁ w₁).app E) := by
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ E] at h
  replace h := (Stacks.Cohomology.BaseChange.isIso_comp₄_iff _ _ _ _).1 h
  have := isIso_smallEtaleDerivedBaseChangeAb_of_universalHomeomorphism u₂ g₁ g₂ v₂ w₂
  have := smallEtalePullbackAb_isEquivalence_of_universalHomeomorphism u₂
  exact isIso_of_isIso_rightDerivedFunctorPlus_map u₂ _ (IsIso.of_isIso_comp_right _
    ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app _))

end Paste

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The algebraic closure of `L` in which the perfect closures are taken. -/
local notation "Ω" => AlgebraicClosure L

/-- An element of `Ω` purely inseparable over `K` is purely inseparable over `L`. -/
theorem mem_perfectClosure_of_mem {x : Ω} (hx : x ∈ perfectClosure K Ω) :
    x ∈ perfectClosure L Ω := by
  have : ExpChar L (ringExpChar K) :=
    expChar_of_injective_algebraMap (algebraMap K L).injective (ringExpChar K)
  rw [mem_perfectClosure_iff_pow_mem (ringExpChar K)]
  obtain ⟨n, a, ha⟩ := (mem_perfectClosure_iff (F := K)).1 hx
  exact ⟨n, algebraMap K L a, by rw [← IsScalarTower.algebraMap_apply, ha]⟩

/-- The inclusion of the perfect closure of `K` in that of `L`, inside `Ω`. -/
def perfectClosureMap : perfectClosure K Ω →+* perfectClosure L Ω where
  toFun x := ⟨x.1, mem_perfectClosure_of_mem K L x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The perfect closure of `L` as an algebra over the perfect closure of `K`. -/
local instance : Algebra (perfectClosure K Ω) (perfectClosure L Ω) :=
  (perfectClosureMap K L).toAlgebra

/-- The two composites `K ⟶ L ⟶ L'` and `K ⟶ K' ⟶ L'` agree. -/
theorem algebraMap_comp_eq :
    CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom (algebraMap L (perfectClosure L Ω)) =
      CommRingCat.ofHom (algebraMap K (perfectClosure K Ω)) ≫
        CommRingCat.ofHom (algebraMap (perfectClosure K Ω) (perfectClosure L Ω)) := by
  ext a
  exact (IsScalarTower.algebraMap_apply K L Ω a).symm

/-- The two composites `Spec L' ⟶ Spec L ⟶ Spec K` and `Spec L' ⟶ Spec K' ⟶ Spec K` agree. -/
private theorem specMap_algebraMap_comp_eq :
    Spec.map (CommRingCat.ofHom (algebraMap (perfectClosure K Ω) (perfectClosure L Ω))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (perfectClosure K Ω))) =
      Spec.map (CommRingCat.ofHom (algebraMap L (perfectClosure L Ω))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (algebraMap_comp_eq K L).symm

variable {S T : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (sT : T ⟶ Spec (.of K)) (g : T ⟶ S)
  [QuasiCompact g] [QuasiSeparated g] (hg : g ≫ sS = sT)

include hg in
/-- **[Stacks, Tag 0F1C], granted [Stacks, Tag 0F09]**, for any presentations
`S_L = Spec L ×_K S` and `T_L = Spec L ×_K T` as fibre products. Let `L/K` be an extension of
fields and `g : T ⟶ S` a quasi-compact and quasi-separated morphism of schemes over `K`, with
base change `g_L : T_L ⟶ S_L`. For `E ∈ D⁺(T_étale)` whose cohomology sheaves are torsion prime
to the exponential characteristic of `K`, the base change map
`(S_L ⟶ S)⁻¹ Rg_* E ⟶ Rg_{L,*} (T_L ⟶ T)⁻¹ E` is an isomorphism. -/
theorem isIso_of_isPullback (hSB : SmoothLimitBaseChange.{u})
    {SL TL : Scheme.{u}} {qS : SL ⟶ Spec (.of L)} {pS : SL ⟶ S}
    (hS : IsPullback qS pS (Spec.map (CommRingCat.ofHom (algebraMap K L))) sS)
    {qT : TL ⟶ Spec (.of L)} {pT : TL ⟶ T}
    (hT : IsPullback qT pT (Spec.map (CommRingCat.ofHom (algebraMap K L))) sT)
    (gL : TL ⟶ SL) (hgq : gL ≫ qS = qT) (hgp : gL ≫ pS = pT ≫ g)
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (hE : ∀ q : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology T)
      (ringExpChar K) ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    IsIso ((smallEtaleDerivedBaseChangeAb pS g gL pT hgp).app E) := by
  -- the perfect closures and the morphisms between their spectra
  let K' := perfectClosure K Ω
  let L' := perfectClosure L Ω
  let φL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let φK := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  let ψL := Spec.map (CommRingCat.ofHom (algebraMap L L'))
  let ψK := Spec.map (CommRingCat.ofHom (algebraMap K' L'))
  let χ := ψL ≫ φL
  have hχ : ψK ≫ φK = χ := specMap_algebraMap_comp_eq K L
  have : UniversalHomeomorphism φK := universalHomeomorphism_specMap_algebraMap K K'
  have : UniversalHomeomorphism ψL := universalHomeomorphism_specMap_algebraMap L L'
  have : PerfectField K' := perfectClosure.perfectField K Ω
  have : Algebra.IsSeparableExtension K' L' := Algebra.isSeparableExtension_of_perfectField K' L'
  -- the schemes over `K'` and `L'`
  have hSK := IsPullback.of_hasPullback φK sS
  have hTK := IsPullback.of_hasPullback φK sT
  let gK := baseChangeMap φK sS sT g hg
  let gL' := baseChangeMap χ sS sT g hg
  let mS := liftMap φL sS ψL χ rfl hS
  let mT := liftMap φL sT ψL χ rfl hT
  let rS := liftMap φK sS ψK χ hχ hSK
  let rT := liftMap φK sT ψK χ hχ hTK
  have := universalHomeomorphism_liftMap φL sS ψL χ rfl hS
  have := universalHomeomorphism_liftMap φL sT ψL χ rfl hT
  have : UniversalHomeomorphism (pullback.snd φK sS) :=
    Stacks.Etale.universalHomeomorphism_of_isPullback hSK.flip
  have : UniversalHomeomorphism (pullback.snd φK sT) :=
    Stacks.Etale.universalHomeomorphism_of_isPullback hTK.flip
  have hgK := isPullback_baseChangeMap φK sS sT g hg
  have : QuasiCompact gK := MorphismProperty.of_isPullback hgK.flip inferInstance
  have : QuasiSeparated gK := MorphismProperty.of_isPullback hgK.flip inferInstance
  -- the commutativity of the four squares
  have w₂ : gL' ≫ mS = mT ≫ gL := hS.hom_ext (by simp [mS, mT, gL', hgq])
    (by simp [mS, mT, gL', hgp])
  have w₄ : gL' ≫ rS = rT ≫ gK := hSK.hom_ext (by simp [rS, rT, gL', gK])
    (by simp [rS, rT, gL', gK])
  -- the two presentations of the outer square
  have hm : mS ≫ pS = rS ≫ pullback.snd φK sS := by simp [mS, rS]
  have hm' : mT ≫ pT = rT ≫ pullback.snd φK sT := by simp [mT, rT]
  have h₄ := isIso_of_isSeparableExtension hSB K' L' (pullback.fst φK sS) (pullback.fst φK sT) gK
    (baseChangeMap_fst _ _ _ _ _) (isPullback_liftMap φK sS ψK χ hχ hSK)
    (isPullback_liftMap φK sT ψK χ hχ hTK) gL' (baseChangeMap_fst _ _ _ _ _) w₄ _ fun q ↦
      isPrimeToCharacteristicTorsion_homology_derivedPullback_of_algebra K K'
        (pullback.snd φK sT) E q (hE q)
  exact isIso_app_of_isIso_paste_of_universalHomeomorphism g gL gL' pS mS pT mT hgp w₂ E
    ((isIso_smallEtaleDerivedBaseChangeAb_app_congr g gL' hm hm' _ _ E).2
      (isIso_app_paste_of_universalHomeomorphism g gK gL' _ rS _ rT
        (baseChangeMap_snd φK sS sT g hg) w₄ E h₄))

end General

/-! ### The statement with the chosen fibre products -/

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {S T : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (sT : T ⟶ Spec (.of K)) (g : T ⟶ S)
  [QuasiCompact g] [QuasiSeparated g] (hg : g ≫ sS = sT)

/-- **[Stacks, Tag 0F1C], granted [Stacks, Tag 0F09].** Let `L/K` be an extension of fields, let
`g : T ⟶ S` be a quasi-compact and quasi-separated morphism of schemes over `K`, and let
`g_L : T_L ⟶ S_L` be its base change to `Spec L`, with `S_L = Spec L ×_K S` and
`T_L = Spec L ×_K T`. Let `E ∈ D⁺(T_étale)` have cohomology sheaves whose stalks are torsion of
orders invertible in `K`, and let `E_L` be its pullback to `T_L`. Then `Rg_{L,*} E_L` is the
pullback of `Rg_* E` to `S_L`: the base change map `(S_L ⟶ S)⁻¹ Rg_* E ⟶ Rg_{L,*} E_L` is an
isomorphism.

The hypothesis `hSB` is [Stacks, Tag 0F09], which is not proved in this repository; this
declaration is therefore not registered. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_baseChange (hSB : SmoothLimitBaseChange.{u})
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (hE : ∀ q : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology T)
      (ringExpChar K) ((DerivedCategory.Plus.homologyFunctor _ q).obj E)) :
    IsIso ((smallEtaleDerivedBaseChangeAb (pullback.snd _ sS) g
      (baseChangeMap (Spec.map (CommRingCat.ofHom (algebraMap K L))) sS sT g hg)
      (pullback.snd _ sT) (baseChangeMap_snd _ sS sT g hg)).app E) :=
  isIso_of_isPullback K L sS sT g hg hSB (IsPullback.of_hasPullback _ sS)
    (IsPullback.of_hasPullback _ sT) _ (baseChangeMap_fst _ _ _ _ _)
    (baseChangeMap_snd _ sS sT g hg) E hE

end Stacks.EtaleCohomology.FieldExtensionBaseChange

end
