module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison

/-!
# Restriction of products of classes supported on closed subschemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `g : Y ⟶ X` be a
morphism locally of finite type. Remark 0F9Z attaches to a bivariant class `c ∈ A^p(Z ⟶ X)` its
restriction `res(c) ∈ A^p(Z ×_X Y ⟶ Y)`, characterized by `res(c) ∩ α = c ∩ α`. This file proves
that restriction is compatible with the products of classes supported on closed subschemes used
in Stacks 0FE5 and Stacks 0FBF:

* the third multiplication of Stacks 0FA0, `A^p(Z ⟶ X) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`,
  `(c, c') ↦ res(c) ∘ c'` (`Stacks.Chow.supportedMul`): `res(c c') = res(c) res(c')`;
* the product `A^p(Z₁ ⟶ X) × A^q(Z₂ ⟶ X) ⟶ A^{p+q}(Z₁ ×_X Z₂ ⟶ X)`
  (`Stacks.Chow.supportedIntersectionMul`): `res(c₁ c₂) = res(c₁) res(c₂)`, the right hand side
  computed for the closed subschemes `Z₁ ×_X Y` and `Z₂ ×_X Y` of `Y`;
* the reading of a class in an equal degree (`Stacks.Chow.bivariantClassDegreeCongr`).

Both products are computed on test schemes: on `t : T ⟶ Y` each side caps with the second factor
at `t ≫ g` and then with the first one, and the two results are pushed forward along two
isomorphisms of fibre products that agree.

## Main results

* `Stacks.Chow.bivariantRestriction_supportedMul` — restriction of `res(c) ∘ c'`.
* `Stacks.Chow.bivariantRestriction_supportedIntersectionMul` — restriction of `c₁ c₂`.
* `Stacks.Chow.isPullback_pullbackMap_of_isPullback` — `W ×_X Y = (Z₁ ×_X Y) ×_Y (Z₂ ×_X Y)`.
* `Stacks.Chow.bivariantRestriction_bivariantClassDegreeCongr`,
  `Stacks.Chow.bivariantClassCongrBase_bivariantClassDegreeCongr` — restriction and the reading
  against equal structure morphisms commute with the reading in an equal degree.
* `Stacks.Chow.BivariantClass.cap_eq_of_heq_chowPushforwardOfIso` — Stacks 0B76 (1) for an
  isomorphism of test schemes, with the structure morphisms given by equalities.

## Implementation notes

The restriction of a class for `f₁ : Z₁ ⟶ X` is a class for `Z₁ ×_X Y ⟶ Y` whose source lies over
the base through `Z₁`; the product on `Y` takes classes whose source lies over the base through
`Y`, so the restrictions are read through `Stacks.Chow.bivariantClassCongrBase`, as in
Stacks 0FB3 (`Stacks.Chow.LocalizedSituation.bivariantRestriction_localizedPowerSum`). The
pullback square presenting `W ×_X Y` as `(Z₁ ×_X Y) ×_Y (Z₂ ×_X Y)` is any square whose legs lie
over those of `W = Z₁ ×_X Z₂`.

## References

* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The third multiplication of Stacks 0FA0 -/

section SupportedMul

variable (C : ChowSituation.{u}) {Z X Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hf : f ≫ sX = sZ) (g : Y ⟶ X) [LocallyOfFiniteType g] {p q : ℤ}


/-- For a monomorphism `i : A ⟶ D` and `a : B ⟶ A`, the second projection of `A ×_D B`, the base
change of `i` along `a ≫ i`, followed by `a` is the first projection. -/
@[reassoc]
theorem pullbackSnd_comp_eq_pullbackFst_of_mono {A B D : Scheme.{u}} (i : A ⟶ D) [Mono i]
    (a : B ⟶ A) : pullback.snd i (a ≫ i) ≫ a = pullback.fst i (a ≫ i) := by
  rw [← cancel_mono i]
  simp [pullback.condition]

omit [IsClosedImmersion f] in
/-- The cap operation of a class at a test scheme `g`, applied to a class pushed forward along an
isomorphism `u : T' ⟶ T`, is the pushforward of its cap operation at `u ≫ g`, the structure
morphisms of the test schemes being given by equalities. -/
theorem BivariantClass.cap_eq_of_heq_chowPushforwardOfIso {G : GysinSystem C}
    [LocallyOfFiniteType f] (c : BivariantClass C G sZ sX f hf p) {T T' : Scheme.{u}}
    (gT : T ⟶ X) [LocallyOfFiniteType gT] (u : T' ⟶ T) [IsIso u] (m : T' ⟶ X)
    [LocallyOfFiniteType m] (hm : u ≫ gT = m) {qA : T' ⟶ C.S} [LocallyOfFiniteType qA]
    {qB : T ⟶ C.S} [LocallyOfFiniteType qB] (hqA : qA = m ≫ sX) (hqB : qB = gT ≫ sX)
    (hu : u ≫ qB = qA) (k : ℤ) (x : chowGroup C qA k) (x' : chowGroup C (m ≫ sX) k)
    (hx : x' ≍ x) (y : chowGroup C (gT ≫ sX) k)
    (hy : y ≍ chowPushforwardOfIso C qA qB u hu k x) :
    c.cap gT k y = chowPushforwardOfIso C (pullback.fst f m ≫ sZ) (pullback.fst f gT ≫ sZ)
      (testBaseChangeIso f gT u m hm).hom (by simp) (k - p) (c.cap m k x') := by
  subst hqB
  obtain rfl := eq_of_heq hy
  exact BivariantClass.cap_chowPushforwardOfIso c gT u m hm qA hqA k hu x x'
    (eq_of_heq ((chowGroupCongr_heq C hqA k x).trans hx.symm))

/-- Pushforwards along two equal isomorphisms, read with equal structure morphisms and degrees, of
heterogeneously equal classes are heterogeneously equal. -/
theorem chowPushforwardOfIso_heq_of_eq {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (v v' : A ⟶ B) [IsIso v] [IsIso v']
    (hvv' : v = v') (hv : v ≫ sB = sA) (hv' : v' ≫ sB' = sA') {k l : ℤ} (hsA : sA = sA')
    (hsB : sB = sB') (hkl : k = l) {x : chowGroup C sA k} {y : chowGroup C sA' l} (hxy : x ≍ y) :
    chowPushforwardOfIso C sA sB v hv k x ≍ chowPushforwardOfIso C sA' sB' v' hv' l y := by
  subst hvv'
  exact chowPushforwardOfIso_heq v hv hv' hsA hsB hkl hxy

/-- The cap operation of `c` at the base change of a test scheme along `f'`, evaluated at a class
equal to the pushforward of `δ` along the comparison isomorphism, is the pushforward of its cap
operation at `pr₁ ≫ f'`. -/
private theorem cap_pullbackLeftPullbackSndIso_inv {G : GysinSystem C}
    (c : BivariantClass C G sZ sX f hf p) {Z' T : Scheme.{u}} (f' : Z' ⟶ X)
    [IsClosedImmersion f'] (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (hf' : f' ≫ sX = sZ')
    (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ)
    (δ : chowGroup C (pullback.fst f' (t ≫ g) ≫ sZ') k)
    (y : chowGroup C (((pullback.fst (pullback.snd f' g) t ≫ pullback.snd f' g) ≫ g) ≫ sX) k)
    (hy : y ≍ chowPushforwardOfIso C (pullback.fst f' (t ≫ g) ≫ sZ')
      (pullback.fst (pullback.snd f' g) t ≫ pullback.fst f' g ≫ sZ')
      (pullbackLeftPullbackSndIso f' g t).inv (by simp [← hf']) k δ) :
    c.cap ((pullback.fst (pullback.snd f' g) t ≫ pullback.snd f' g) ≫ g) k y =
      chowPushforwardOfIso C
        (pullback.fst f (pullback.fst f' (t ≫ g) ≫ f') ≫ sZ)
        (pullback.fst f ((pullback.fst (pullback.snd f' g) t ≫ pullback.snd f' g) ≫ g) ≫ sZ)
        (testBaseChangeIso f ((pullback.fst (pullback.snd f' g) t ≫ pullback.snd f' g) ≫ g)
          (pullbackLeftPullbackSndIso f' g t).inv (pullback.fst f' (t ≫ g) ≫ f') (by
            simp only [Category.assoc, pullback.condition]
            simp)).hom (by simp) (k - p)
        (c.cap (pullback.fst f' (t ≫ g) ≫ f') k
          (chowGroupCongr C (by simp [← hf']) k δ)) := by
  subst hf'
  exact BivariantClass.cap_eq_of_heq_chowPushforwardOfIso C sZ sX f hf c _
    (pullbackLeftPullbackSndIso f' g t).inv _ _ (by simp) (by simp [pullback.condition_assoc])
    (by simp) k δ _ (chowGroupCongr_heq C _ _ _) y hy

/-- **Restriction of the third multiplication of Stacks 0FA0** (Remark 0F9Z). For classes
`c ∈ A^p(Z ⟶ X)`, `c' ∈ A^q(Z ⟶ X)` of a closed immersion `Z ⟶ X` and `g : Y ⟶ X`, the
restriction of `res(c) ∘ c'` along `g` is the product of the restrictions of `c` and `c'`, for the
closed immersion `Z ×_X Y ⟶ Y`. -/
theorem bivariantRestriction_supportedMul
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    bivariantRestriction C (gysinSystemOfInvertible C) sZ sX f hf g (p + q)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (supportedMul C sZ sX f hf c c') =
      supportedMul C (pullback.fst f g ≫ sZ) (g ≫ sX) (pullback.snd f g)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX f hf g)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX f hf g p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX f hf g q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c') := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  apply eq_of_heq
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring : k - (p + q) = k - q - p) _ _
    (supportedLeftComp_cap C sZ sX f hf _ c' (t ≫ g) k _)).trans ?_
  refine HEq.trans ?_ (supportedLeftComp_cap C _ _ _ _ _ _ t k α).symm
  rw [BivariantClass.idRule_bivariantClassCongrBase, BivariantClass.idRule_bivariantClassCongrBase,
    closedImmersionChowCohomologyRestriction_idRule,
    closedImmersionChowCohomologyRestriction_idRule,
    bivariantRestriction_cap, bivariantRestrictionCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply]
  rw [cap_pullbackLeftPullbackSndIso_inv C sZ sX f hf g c f sZ hf t (k - q)
    (c'.cap (t ≫ g) k (chowGroupCongr C (Category.assoc t g sX).symm k α))]
  rotate_left
  · exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
      ((chowGroupCongr_heq C _ _ _).trans HEq.rfl))
  rw [chowGroupCongr_chowGroupCongr]
  simp only [chowPush, properChowPushforward_eq_chowPushforwardOfIso]
  rw [chowGroupCongr_chowPushforwardOfIso_target C _ _ _ _ ?h1,
    chowGroupCongr_chowPushforwardOfIso_target C _ _ _ _ ?h2, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  case h1 => rw [pullbackSnd_comp_eq_pullbackFst_of_mono_assoc]
  case h2 => rw [pullbackSnd_comp_eq_pullbackFst_of_mono_assoc]
  rw [chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [testBaseChangeIso]
    · simp [testBaseChangeIso, pullback.condition]
  · simp [testBaseChangeIso]

end SupportedMul

/-! ### Degrees -/

section Degree

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (h : Y' ⟶ Y) [LocallyOfFiniteType h]

/-- The restriction map as a homomorphism of groups is the restriction. -/
@[simp]
theorem bivariantRestrictionAddHom_apply (hgys : G.IsNaturalUnderBaseChangeIso) {p : ℤ}
    (c : BivariantClass C G sX sY f hf p) :
    bivariantRestrictionAddHom C G sX sY f hf h p hgys c =
      bivariantRestriction C G sX sY f hf h p hgys c :=
  rfl

/-- **Restriction commutes with reading a class in an equal degree.** -/
theorem bivariantRestriction_bivariantClassDegreeCongr (hgys : G.IsNaturalUnderBaseChangeIso)
    {p p' : ℤ} (e : p = p') (c : BivariantClass C G sX sY f hf p) :
    bivariantRestriction C G sX sY f hf h p' hgys (bivariantClassDegreeCongr C G sX sY f hf e c) =
      bivariantClassDegreeCongr C G _ _ _ _ e (bivariantRestriction C G sX sY f hf h p hgys c) := by
  subst e
  rfl

/-- Reading a class against equal structure morphisms commutes with reading it in an equal
degree. -/
theorem bivariantClassCongrBase_bivariantClassDegreeCongr {sX' : X ⟶ C.S}
    [LocallyOfFiniteType sX'] {sY' : Y ⟶ C.S} [LocallyOfFiniteType sY'] (hsX : sX = sX')
    (hsY : sY = sY') {hf' : f ≫ sY' = sX'} {p p' : ℤ} (e : p = p')
    (c : BivariantClass C G sX sY f hf p) :
    bivariantClassCongrBase C G f hsX hsY (hv := hf) (hv' := hf') p'
        (bivariantClassDegreeCongr C G sX sY f hf e c) =
      bivariantClassDegreeCongr C G sX' sY' f hf' e
        (bivariantClassCongrBase C G f hsX hsY (hv := hf) (hv' := hf') p c) := by
  subst hsX hsY e
  rfl

end Degree

section IntersectionRestriction

variable (C : ChowSituation.{u}) {X Z₁ Z₂ W Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [IsClosedImmersion f₁] (f₂ : Z₂ ⟶ X)
  [IsClosedImmersion f₂] {w₁ : W ⟶ Z₁} {w₂ : W ⟶ Z₂} (sq : IsPullback w₁ w₂ f₁ f₂)
  (iW : W ⟶ X) [IsClosedImmersion iW] (hW : w₂ ≫ f₂ = iW) (g : Y ⟶ X) [LocallyOfFiniteType g]
  {w₁' : pullback iW g ⟶ pullback f₁ g} {w₂' : pullback iW g ⟶ pullback f₂ g}
  (sq' : IsPullback w₁' w₂' (pullback.snd f₁ g) (pullback.snd f₂ g))
  (hW' : w₂' ≫ pullback.snd f₂ g = pullback.snd iW g)
  (hw₁ : w₁' ≫ pullback.fst f₁ g = pullback.fst iW g ≫ w₁)
  (hw₂ : w₂' ≫ pullback.fst f₂ g = pullback.fst iW g ≫ w₂) {p q : ℤ}

/-- The cap operation of a class read against an equal structure morphism of the source. -/
theorem bivariantClassCongrBase_cap_eq {G : GysinSystem C} {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    (v : A ⟶ B) [LocallyOfFiniteType v] (hsA : sA = sA') {hv : v ≫ sB = sA} {hv' : v ≫ sB = sA'}
    {r : ℤ} (c : BivariantClass C G sA sB v hv r) {T : Scheme.{u}} (t : T ⟶ B)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sB) k) :
    (bivariantClassCongrBase C G v hsA rfl (hv := hv) (hv' := hv') r c).cap t k α =
      chowGroupCongr C (by rw [hsA]) (k - r) (c.cap t k α) := by
  subst hsA
  rfl

omit [LocallyOfFiniteType sX] [IsClosedImmersion f₁] [IsClosedImmersion f₂] [IsClosedImmersion iW]
  [LocallyOfFiniteType g] in
include sq hW in
/-- **The base change of a pullback square is a pullback square**: for `W = Z₁ ×_X Z₂` and
`g : Y ⟶ X`, the scheme `W ×_X Y` is `(Z₁ ×_X Y) ×_Y (Z₂ ×_X Y)`, through the morphisms induced by
the legs of the square. -/
theorem isPullback_pullbackMap_of_isPullback :
    IsPullback (pullback.map iW g f₁ g w₁ (𝟙 Y) (𝟙 X) (by rw [Category.comp_id, sq.w, hW])
        (by simp))
      (pullback.map iW g f₂ g w₂ (𝟙 Y) (𝟙 X) (by rw [Category.comp_id, hW]) (by simp))
      (pullback.snd f₁ g) (pullback.snd f₂ g) := by
  have hw₁ : w₁ ≫ f₁ = iW := sq.w.trans hW
  refine IsPullback.of_isLimit' ⟨by simp⟩ (PullbackCone.IsLimit.mk _
    (fun s => pullback.lift (sq.lift (s.fst ≫ pullback.fst f₁ g) (s.snd ≫ pullback.fst f₂ g)
      (by simp only [Category.assoc, pullback.condition, PullbackCone.condition_assoc]))
      (s.fst ≫ pullback.snd f₁ g)
      (by rw [← hw₁, IsPullback.lift_fst_assoc, Category.assoc, Category.assoc,
        pullback.condition]))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.map_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · rw [Category.assoc, pullback.map_snd, Category.comp_id]
      exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.map_fst, pullback.lift_fst_assoc, IsPullback.lift_snd]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      simp [s.condition]
  · apply pullback.hom_ext
    · refine sq.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.lift_fst]
        rw [← h₁]
        simp
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.lift_snd]
        rw [← h₂]
        simp
    · simp only [pullback.lift_snd]
      rw [← h₁]
      simp

include hw₁ hw₂ in
/-- **Restriction of the product of classes supported on two closed subschemes** (Remark 0F9Z).
For `c₁ ∈ A^p(Z₁ ⟶ X)`, `c₂ ∈ A^q(Z₂ ⟶ X)` and `g : Y ⟶ X`, the restriction along `g` of
`c₁ c₂ ∈ A^{p+q}(W ⟶ X)`, `W = Z₁ ×_X Z₂`, is the product of the restrictions of `c₁` and `c₂`,
classes for `Z₁ ×_X Y ⟶ Y` and `Z₂ ×_X Y ⟶ Y`, along any pullback square presenting `W ×_X Y` whose
legs lie over those of `W`. -/
theorem bivariantRestriction_supportedIntersectionMul
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd iW g)
        (pullbackSnd_comp_structureMorphism_eq C (iW ≫ sX) sX iW rfl g).symm rfl
        (hv := pullbackSnd_comp_structureMorphism_eq C (iW ≫ sX) sX iW rfl g) (hv' := rfl) (p + q)
        (bivariantRestriction C (gysinSystemOfInvertible C) (iW ≫ sX) sX iW rfl g (p + q)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂)) =
      supportedIntersectionMul C (g ≫ sX) (pullback.snd f₁ g) (pullback.snd f₂ g) sq'
        (pullback.snd iW g) hW'
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd f₁ g)
          (pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl g).symm rfl
          (hv := pullbackSnd_comp_structureMorphism_eq C (f₁ ≫ sX) sX f₁ rfl g) (hv' := rfl) p
          (bivariantRestriction C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl g p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₁))
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd f₂ g)
          (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl g).symm rfl
          (hv := pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl g) (hv' := rfl) q
          (bivariantRestriction C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl g q
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₂)) := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  apply eq_of_heq
  rw [bivariantClassCongrBase_cap_eq, bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine (chowGroupCongr_heq C _ _ _).trans ((chowPushforwardOfIso_heq_congr C _ _ _ _
    (by ring : k - (p + q) = k - q - p) _ _
    (supportedIntersectionMul_cap C sX f₁ f₂ sq iW hW c₁ c₂ (t ≫ g) k _)).trans ?_)
  refine HEq.trans ?_ (supportedIntersectionMul_cap C _ _ _ sq' _ hW' _ _ t k α).symm
  rw [bivariantClassCongrBase_cap_eq, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    bivariantClassCongrBase_cap_eq, bivariantRestriction_cap, bivariantRestrictionCap_apply]
  rw [cap_pullbackLeftPullbackSndIso_inv C (f₁ ≫ sX) sX f₁ rfl g c₁ f₂ (f₂ ≫ sX) rfl t (k - q)
    (c₂.cap (t ≫ g) k (chowGroupCongr C (Category.assoc t g sX).symm k α))]
  rotate_left
  · exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
      ((chowGroupCongr_heq C _ _ _).trans HEq.rfl))
  simp only [chowPush, properChowPushforward_eq_chowPushforwardOfIso]
  rw [chowGroupCongr_chowPushforwardOfIso_target C _ _ _ _ ?h2, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply]
  case h2 => simp [pullback.condition_assoc]
  refine chowPushforwardOfIso_heq_of_eq C _ _ ?_ _ _ rfl ?_ rfl HEq.rfl
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · refine sq.hom_ext ?_ ?_
        · simp only [Category.assoc]
          conv_rhs => rw [← hw₁, supportedIntersectionTestIso_hom_fst_w₁_assoc]
          simp [supportedIntersectionTestIso_hom_fst_w₁]
        · simp only [Category.assoc]
          conv_rhs => rw [← hw₂, supportedIntersectionTestIso_hom_fst_w₂_assoc]
          simp [supportedIntersectionTestIso_hom_fst_w₂]
      · simp only [Category.assoc]
        simp only [pullback.condition (f := pullback.snd iW g) (g := t)]
        conv_rhs => rw [supportedIntersectionTestIso_hom_snd_assoc]
        simp [supportedIntersectionTestIso_hom_snd_assoc]
    · simp only [Category.assoc]
      simp [supportedIntersectionTestIso_hom_snd]
  · simp [← hW', pullback.condition_assoc]

end IntersectionRestriction

end Stacks.Chow
