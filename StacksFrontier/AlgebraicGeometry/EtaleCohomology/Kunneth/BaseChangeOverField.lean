module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.PullbackConservative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FieldExtensionBaseChange

/-!
# Base change over a field: the reductions of the proof of Stacks 0F1I

Let `K` be a field. [Stacks, Tag 0F1I] asserts that for every commutative diagram

```
X  ←-p-  X'  ←-h-  Y
|        |f'       |e
Spec K ←-s- S' ←-g- T
```

of schemes over `K` with `X' = X ×_K S'`, `Y = X' ×_{S'} T` and `g` quasi-compact and
quasi-separated, and every abelian sheaf `𝓕` on `T_étale` whose stalks are torsion of orders
invertible in `K`, the base change map `(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism.

After writing `𝓕 = colim 𝓕[n]`, the source's proof works with a sheaf annihilated by one integer
`n` invertible in `K`. This file names that property of `X ⟶ Spec K` and proves three steps of
the proof about it.

## Main definitions

* `Stacks.EtaleCohomology.BaseChangeOverField.DerivedBaseChangeHolds` — for a morphism
  `f : X ⟶ S` and an integer `n`: for every diagram as above over `S`, with both squares
  cartesian and `g` quasi-compact and quasi-separated, and every abelian sheaf `𝓕` on `T_étale`
  annihilated by `n`, the derived base change map `(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism.
  It is the condition `BC(f, n, q)` of [Stacks, Tag 0F02] in every degree at once, read on the
  bounded below derived category.

## Main results

* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_iff` — the derived
  condition is `BC(f, n, q)` for every `q`.
* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_universalHomeomorphism`
  — *"we may replace `X` by its reduction as we have the topological invariance of étale
  cohomology"*: the condition descends along any universal homeomorphism `Z ⟶ X`, for instance
  `X_red ⟶ X`.
* `Stacks.EtaleCohomology.BaseChangeOverField.derivedBaseChangeHolds_of_baseChange` — *"we may
  replace `K` by its algebraic closure"*: for any extension `L/K` and `n` invertible in `K`, the
  condition for `X_L ⟶ Spec L` implies the condition for `X ⟶ Spec K`. Formation of the direct
  images along `g` and along `h` commutes with base change to `L` by [Stacks, Tag 0F1C], and
  inverse image along the surjection `X'_L ⟶ X'` reflects isomorphisms.

## Implementation notes

*The input that is not proved here.* [Stacks, Tag 0F1C] is available in this repository only from
the statement of [Stacks, Tag 0F09], `Stacks.EtaleCohomology.SmoothLimitBaseChange`, which is not
proved in it. The reduction to an extension field therefore takes that statement as the explicit
argument `hSmoothLimitBaseChange`, and it is not registered.

*The derived categories.* The base change map is
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, which is constructed under the standard
model `HasDerivedCategory.standard`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BaseChangeCondition.lean`,
`smallEtaleDerivedBaseChangeAb`); that fixes the model here.

## References

* [Stacks Project, Tag 0F1I](https://stacks.math.columbia.edu/tag/0F1I)
* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.BaseChangeOverField

-- `smallEtaleDerivedBaseChangeAb` (BaseChangeHigher/BaseChangeCondition.lean) is built under the
-- standard model, so its components live in the standard bounded below derived categories.
attribute [local instance] HasDerivedCategory.standard

open FieldExtensionBaseChange

/-- **Derived base change for sheaves annihilated by `n` holds for `f : X ⟶ S`.** For every
diagram

```
X  ←-p-  X'  ←-h-  Y
|f       |f'       |e
S  ←-s-  S'  ←-g-  T
```

with `X' = X ×_S S'`, `Y = X' ×_{S'} T` and `g` quasi-compact and quasi-separated, and every
abelian sheaf `𝓕` on the small étale site of `T` annihilated by `n`, the derived base change map
`(f')⁻¹Rg_*𝓕 ⟶ Rh_*e⁻¹𝓕` is an isomorphism. By `derivedBaseChangeHolds_iff` this is the
condition `BC(f, n, q)` of [Stacks, Tag 0F02] for every `q`. -/
def DerivedBaseChangeHolds {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) : Prop :=
  ∀ ⦃S' X' T Y : Scheme.{u}⦄ (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (sq : IsPullback h e f' g) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
    (∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) →
      IsIso ((smallEtaleDerivedBaseChangeAb f' g h e sq.w).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-! ### The derived condition is the degreewise condition -/

section Degreewise

/-- Two right derived functors applied to a sheaf in degree zero have no negative cohomology. -/
private theorem isZero_homology_rightDerivedFunctorPlus_comp_single_of_neg {X₁ X₂ X₃ : Scheme.{u}}
    (G₁ : Sheaf (smallEtaleTopology X₁) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology X₂) Ab.{u + 1})
    (G₂ : Sheaf (smallEtaleTopology X₂) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology X₃) Ab.{u + 1})
    [G₁.Additive] [G₂.Additive] (F : Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) {m : ℤ}
    (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ m).obj (G₂.rightDerivedFunctorPlus.obj
      (G₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  have : (G₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).IsGE 0 :=
    Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
  have : (G₂.rightDerivedFunctorPlus.obj
      (G₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).IsGE 0 :=
    Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 m hm

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The derived base change map at a sheaf is invertible exactly when the base change maps on
all higher direct images are.** In nonnegative degree `q` the cohomology of the derived map is
the base change map on `R^q`; in negative degrees both sides vanish, the derived direct and
inverse images of a sheaf in degree zero living in degrees `≥ 0`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_single_iff
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ↔
      ∀ q : ℕ, IsIso ((higherBaseChangeMapAb f' g h e w q).app F) := by
  rw [DerivedCategory.Plus.isIso_iff]
  refine ⟨fun H q ↦ (isIso_higherBaseChangeMapAb_app_iff f' g h e w q F).2 (H q), fun H m ↦ ?_⟩
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact (isIso_higherBaseChangeMapAb_app_iff f' g h e w q F).1 (H q)
  · exact ⟨⟨0, (isZero_homology_rightDerivedFunctorPlus_comp_single_of_neg _ _ F hm).eq_of_src _ _,
      (isZero_homology_rightDerivedFunctorPlus_comp_single_of_neg _ _ F hm).eq_of_src _ _⟩⟩

end Degreewise

/-- **The derived condition is `BC(f, n, q)` for every `q`.** -/
theorem derivedBaseChangeHolds_iff {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) :
    DerivedBaseChangeHolds f n ↔ ∀ q : ℕ, BaseChangeHolds f n q := by
  constructor
  · intro H q S' X' T Y s p f' hp g h e sq _ _ F hF r _
    exact (isIso_smallEtaleDerivedBaseChangeAb_app_single_iff f' g h e sq.w F).1
      (H s p f' hp g h e sq F hF) r
  · intro H S' X' T Y s p f' hp g h e sq _ _ F hF
    exact (isIso_smallEtaleDerivedBaseChangeAb_app_single_iff f' g h e sq.w F).2
      fun r ↦ H r s p f' hp g h e sq F hF r le_rfl

/-! ### Conservativity of derived inverse image along a surjection -/

/-- **Derived inverse image along a surjection reflects isomorphisms** on bounded below derived
categories of abelian sheaves: it commutes with cohomology, and inverse image along a
surjection reflects isomorphisms of abelian sheaves. -/
theorem isIso_of_isIso_rightDerivedFunctorPlus_map_of_surjective {X Y : Scheme.{u}} (a : X ⟶ Y)
    [Surjective a] {M N : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})}
    (φ : M ⟶ N) (h : IsIso ((smallEtalePullbackAb a).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff] at h ⊢
  intro m
  have : IsIso ((smallEtalePullbackAb a).map ((DerivedCategory.Plus.homologyFunctor _ m).map φ)) :=
    (NatIso.isIso_map_iff
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb a) m) φ).1 (h m)
  exact isIso_of_isIso_smallEtalePullbackAb_map a _ this

/-! ### Replacing `X` along a universal homeomorphism -/

/-- If the base change map of a pasted square and that of its upper square are invertible, so is
the inverse image of the base change map of the lower square. -/
private theorem isIso_pullback_map_of_isIso_paste {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}} (g₀ : Y₀ ⟶ X₀)
    (g₁ : Y₁ ⟶ X₁) (g₂ : Y₂ ⟶ X₂) (u₁ : X₁ ⟶ X₀) (u₂ : X₂ ⟶ X₁) (v₁ : Y₁ ⟶ Y₀) (v₂ : Y₂ ⟶ Y₁)
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁)
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y₀) Ab.{u + 1}))
    (hout : IsIso ((smallEtaleDerivedBaseChangeAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).app M))
    (hin : IsIso ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
      ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj M))) :
    IsIso ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
      ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app M)) := by
  replace hout := (congrArg IsIso
    (smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ M)).mp hout
  have := (Stacks.Cohomology.BaseChange.isIso_comp₄_iff _ _ _ _).1 hout
  exact IsIso.of_isIso_comp_right _ ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
    ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj M))

/-- **[Stacks, Tag 0F1I], the replacement of `X` by its reduction.** If `r : Z ⟶ X` is a universal
homeomorphism, for instance the reduction `X_red ⟶ X`, then derived base change for sheaves
annihilated by `n` descends from `r ≫ f` to `f`.

Writing `Z' = Z ×_X X'` and `W = Z' ×_{X'} Y`, the base change map of the square of `Z` is that of
the square of `X`, pulled back to `Z'`, followed by the base change map of the square of `W` over
`Z'`. The legs `Z' ⟶ X'` and `W ⟶ Y` of the latter are universal homeomorphisms, so its base
change map is invertible and inverse image along `Z' ⟶ X'` is an equivalence
([Stacks, Tag 03SI]). -/
theorem derivedBaseChangeHolds_of_universalHomeomorphism {Z X S : Scheme.{u}} (r : Z ⟶ X)
    [UniversalHomeomorphism r] (f : X ⟶ S) (n : ℤ) (H : DerivedBaseChangeHolds (r ≫ f) n) :
    DerivedBaseChangeHolds f n := by
  intro S' X' T Y s p f' hp g h e sq _ _ F hF
  let a := pullback.snd r p
  let b := pullback.snd a h
  have hZ := IsPullback.of_hasPullback r p
  have hW := IsPullback.of_hasPullback a h
  have : UniversalHomeomorphism a := Stacks.Etale.universalHomeomorphism_of_isPullback hZ.flip
  have : UniversalHomeomorphism b := Stacks.Etale.universalHomeomorphism_of_isPullback hW.flip
  have hout := H s (pullback.fst r p) (a ≫ f') (hZ.paste_vert hp) g (pullback.fst a h) (b ≫ e)
    (hW.paste_vert sq) F hF
  let M := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F
  have := isIso_smallEtaleDerivedBaseChangeAb_of_universalHomeomorphism a h (pullback.fst a h)
    b pullback.condition
  have := smallEtalePullbackAb_isEquivalence_of_universalHomeomorphism a
  exact isIso_of_isIso_rightDerivedFunctorPlus_map a _
    (isIso_pullback_map_of_isIso_paste g h (pullback.fst a h) f' a e b sq.w pullback.condition M
      hout inferInstance)

/-! ### Replacing `K` by an extension field -/

section ExtensionField

/-- A positive integer invertible in a field is prime to its exponential characteristic. -/
theorem coprime_ringExpChar_of_isUnit_natCast (K : Type*) [Field K] {m : ℕ}
    (hm : IsUnit (m : K)) : m.Coprime (ringExpChar K) := by
  rcases Nat.eq_zero_or_pos (ringChar K) with h0 | hpos
  · have : ringExpChar K = 1 := by simp [ringExpChar, h0]
    simp [this]
  · have : NeZero (ringChar K) := ⟨hpos.ne'⟩
    have hp := (CharP.char_is_prime_of_pos K (ringChar K)).out
    rw [show ringExpChar K = ringChar K from max_eq_left hpos]
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd ↦
      hm.ne_zero ((CharP.cast_eq_zero_iff K (ringChar K) m).2 hd))

/-- An abelian sheaf annihilated by an integer `n` invertible in `K` is torsion prime to the
exponential characteristic of `K`. -/
theorem isPrimeToCharacteristicTorsion_of_zsmul_eq_zero (K : Type*) [Field K] {T : Scheme.{u}}
    {n : ℤ} (hn : IsUnit (n : K)) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology T) (ringExpChar K) F := by
  rw [isPrimeToCharacteristicTorsion_iff_locallyAnnihilated]
  have hm : IsUnit ((n.natAbs : ℕ) : K) := by
    rcases Int.natAbs_eq n with h | h <;> rw [h] at hn <;> simpa using hn
  have hpos : 0 < n.natAbs := Int.natAbs_pos.2 fun h0 ↦ by simp [h0] at hn
  refine fun U x ↦ ⟨⊤, (smallEtaleTopology T).top_mem U, fun V f _ ↦
    ⟨n.natAbs, ⟨hpos, coprime_ringExpChar_of_isUnit_natCast K hm⟩, ?_⟩⟩
  have hx := hF V (F.obj.map f.op x)
  rcases Int.natAbs_eq n with h | h
  · rwa [h, natCast_zsmul] at hx
  · rwa [h, neg_zsmul, neg_eq_zero, natCast_zsmul] at hx

/-- The cohomology sheaves of a sheaf placed in degree zero are torsion prime to `p` when the
sheaf is. -/
theorem isPrimeToCharacteristicTorsion_homology_single {T : Scheme.{u}} {p : ℕ}
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology T) p F) (q : ℤ) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion (smallEtaleTopology T) p
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  rw [isPrimeToCharacteristicTorsion_iff_locallyAnnihilated] at hF ⊢
  obtain rfl | hq := eq_or_ne q 0
  · let i : (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F) ≅
          F :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F
    exact LocallyAnnihilated.of_epi i.inv hF
  · have hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
          F)) := by
      rcases lt_or_gt_of_ne hq with h | h
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q h
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q h
    have : Epi (hz.from_ F) := hz.epi _
    exact LocallyAnnihilated.of_epi (hz.from_ F) hF

variable (hSmoothLimitBaseChange : SmoothLimitBaseChange.{u}) (K L : Type u) [Field K] [Field L]
  [Algebra K L]

include hSmoothLimitBaseChange in
/-- **[Stacks, Tag 0F1I], the replacement of `K` by an extension field**, granted
[Stacks, Tag 0F09]. Let `L/K` be an extension of fields, `X` a scheme over `K` with base change
`X_L = Spec L ×_K X`, and `n` an integer invertible in `K`. If derived base change for sheaves
annihilated by `n` holds for `X_L ⟶ Spec L`, it holds for `X ⟶ Spec K`.

Base change the whole diagram to `L`. The square of `X'_L` over `S'_L ⟵ T_L` is a diagram over
`X_L ⟶ Spec L` of the kind the hypothesis is about. Its base change map, pasted under the base
change map of `g_L` over `g`, is the base change map of the square of `X'_L` over `S' ⟵ T`; so is
the base change map of `h_L` over `h` pasted under the inverse image along `X'_L ⟶ X'` of the
base change map of the original square. The base change maps of `g_L` over `g` and of `h_L` over
`h` are invertible by [Stacks, Tag 0F1C]; this is where `hSmoothLimitBaseChange` is used. What is
left is the inverse image along the surjection `X'_L ⟶ X'` of the original base change map, and
that inverse image reflects isomorphisms. -/
theorem derivedBaseChangeHolds_of_baseChange {X : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (n : ℤ)
    (hn : IsUnit (n : K))
    (H : DerivedBaseChangeHolds
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L))) sX) n) :
    DerivedBaseChangeHolds sX n := by
  intro S' X' T Y s p f' hp g h e sq _ _ F hF
  let φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have he : e ≫ g ≫ s = h ≫ f' ≫ s := by rw [← Category.assoc, ← sq.w, Category.assoc]
  -- the base changes to `L`
  let gL := baseChangeMap φ s (g ≫ s) g rfl
  let hL := baseChangeMap φ (f' ≫ s) (h ≫ f' ≫ s) h rfl
  let fL := baseChangeMap φ s (f' ≫ s) f' rfl
  let eL := baseChangeMap φ (g ≫ s) (h ≫ f' ≫ s) e he
  let pL := baseChangeMap φ sX (f' ≫ s) p hp.w
  have sqB := isPullback_baseChangeMap φ s (g ≫ s) g rfl
  have sqF := isPullback_baseChangeMap φ s (f' ≫ s) f' rfl
  have sqE := isPullback_baseChangeMap φ (g ≫ s) (h ≫ f' ≫ s) e he
  have : QuasiCompact gL := MorphismProperty.of_isPullback sqB.flip inferInstance
  have : QuasiSeparated gL := MorphismProperty.of_isPullback sqB.flip inferInstance
  have : QuasiCompact h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : QuasiSeparated h := MorphismProperty.of_isPullback sq.flip inferInstance
  have : Surjective φ := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.snd φ (f' ≫ s)) := inferInstance
  -- the commutativity of the squares of the base changed diagram
  have hpS : fL ≫ pullback.snd φ s = pullback.snd φ (f' ≫ s) ≫ f' := baseChangeMap_snd _ _ _ _ _
  have hgS : gL ≫ pullback.snd φ s = pullback.snd φ (g ≫ s) ≫ g := baseChangeMap_snd _ _ _ _ _
  have hdE : eL ≫ pullback.snd φ (g ≫ s) = pullback.snd φ (h ≫ f' ≫ s) ≫ e :=
    baseChangeMap_snd _ _ _ _ _
  have hwC : hL ≫ pullback.snd φ (f' ≫ s) = pullback.snd φ (h ≫ f' ≫ s) ≫ h :=
    baseChangeMap_snd _ _ _ _ _
  have hpX : pL ≫ pullback.snd φ sX = pullback.snd φ (f' ≫ s) ≫ p := baseChangeMap_snd _ _ _ _ _
  have hw : hL ≫ fL = eL ≫ gL := pullback.hom_ext (by simp [hL, fL, eL, gL])
    (by simp [hL, fL, eL, gL, sq.w])
  -- the diagram over `X_L ⟶ Spec L`
  have hpL : IsPullback pL fL (pullback.fst φ sX) (pullback.fst φ s) := by
    refine IsPullback.of_right ?_ (by simp [pL, fL]) (IsPullback.of_hasPullback φ sX).flip
    rw [hpX, pullback.condition]
    exact sqF.flip.paste_horiz hp
  have sqL : IsPullback hL eL fL gL := by
    refine IsPullback.of_right ?_ hw sqF.flip
    rw [hwC, hgS]
    exact sqE.flip.paste_horiz sq
  let M := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F
  -- the torsion conditions for Tag 0F1C
  have hFt := isPrimeToCharacteristicTorsion_of_zsmul_eq_zero K hn F hF
  have hM : ∀ q : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion _ (ringExpChar K)
      ((DerivedCategory.Plus.homologyFunctor _ q).obj M) :=
    isPrimeToCharacteristicTorsion_homology_single F hFt
  -- the square over `L`
  have hFL : ∀ (U : (pullback φ (g ≫ s)).Etale)
      (x : ((smallEtalePullbackAb (pullback.snd φ (g ≫ s))).obj F).obj.obj (op U)), n • x = 0 :=
    fun U x ↦ zsmul_eq_zero_of_additive (smallEtalePullbackAb (pullback.snd φ (g ≫ s))) F n
      (fun V y ↦ hF V.unop y) (op U) x
  have hD := H (pullback.fst φ s) pL fL hpL gL hL eL sqL _ hFL
  have hD' : IsIso ((smallEtaleDerivedBaseChangeAb fL gL hL eL sqL.w).app
      ((smallEtalePullbackAb (pullback.snd φ (g ≫ s))).rightDerivedFunctorPlus.obj M)) :=
    (NatTrans.isIso_app_iff_of_iso (smallEtaleDerivedBaseChangeAb fL gL hL eL sqL.w)
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (smallEtalePullbackAb (pullback.snd φ (g ≫ s))) 0).app F)).1 hD
  -- the outer square through `g_L`
  have := isIso_smallEtaleDerivedBaseChangeAb_baseChange K L s (g ≫ s) g rfl
    hSmoothLimitBaseChange M hM
  have hout : IsIso ((smallEtaleDerivedBaseChangeAb (fL ≫ pullback.snd φ s) g hL
      (eL ≫ pullback.snd φ (g ≫ s))
      (smallEtaleRectangle_comm g gL hL (pullback.snd φ s) fL (pullback.snd φ (g ≫ s)) eL
        hgS hw)).app M) := by
    rw [smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g gL hL (pullback.snd φ s) fL
      (pullback.snd φ (g ≫ s)) eL hgS hw M]
    infer_instance
  -- the outer square through `h`
  have hout' : IsIso ((smallEtaleDerivedBaseChangeAb (pullback.snd φ (f' ≫ s) ≫ f') g hL
      (pullback.snd φ (h ≫ f' ≫ s) ≫ e)
      (smallEtaleRectangle_comm g h hL f' (pullback.snd φ (f' ≫ s)) e
        (pullback.snd φ (h ≫ f' ≫ s)) sq.w hwC)).app M) :=
    (isIso_smallEtaleDerivedBaseChangeAb_app_congr g hL hpS hdE _ _ M).1 hout
  have hEh : ∀ q : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion _ (ringExpChar K)
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj M)) :=
    fun q ↦ isPrimeToCharacteristicTorsion_homology_derivedPullback e M q (hM q)
  have := isIso_smallEtaleDerivedBaseChangeAb_baseChange K L (f' ≫ s) (h ≫ f' ≫ s) h rfl
    hSmoothLimitBaseChange _ hEh
  exact isIso_of_isIso_rightDerivedFunctorPlus_map_of_surjective _ _
    (isIso_pullback_map_of_isIso_paste g h hL f' (pullback.snd φ (f' ≫ s)) e
      (pullback.snd φ (h ≫ f' ≫ s)) sq.w hwC M hout' inferInstance)

end ExtensionField

end Stacks.EtaleCohomology.BaseChangeOverField

end
