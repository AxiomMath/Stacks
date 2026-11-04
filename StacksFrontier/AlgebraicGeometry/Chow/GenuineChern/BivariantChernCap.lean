module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist

/-!
# Bivariant classes commute with the Chern class cap products

Let `(S, δ)` be as in Situation 02QL, let `f : X' ⟶ X` be locally of finite type, let
`c ∈ A^p(X' ⟶ X)` be a bivariant class, let `g : T ⟶ X` be a test scheme and let `ℰ` be a finite
locally free `𝒪_T`-module of rank `r`. Then

  `c ∩ (c_j(ℰ) ∩ α) = c_j(ℰ') ∩ (c ∩ α)`  in  `A_{k-p-j}(T ×_X X')`,  for `α ∈ A_k(T)`,

with `ℰ'` the pullback of `ℰ` to `T ×_X X'` and `c_j ∩ -` the cap products of Stacks 02U6. This
is the cap-level content of Stacks 02UA (2).

## The argument

It is the source's. Let `π : P = 𝐏(ℰ) ⟶ T` be the projective bundle. The family
`α_j = c_j(ℰ) ∩ α` satisfies `∑ (-1)^i c₁(𝒪_P(1))^i ∩ π^*α_{r-i} = 0` (Stacks 02U6). The cap
product of `c` at the test scheme `P ⟶ X` carries each summand to the corresponding summand for
the base change `P ×_X X' ⟶ T ×_X X'`: past `π^*` by condition (2) of Stacks 0B76, past
`c₁(𝒪_P(1)) ∩ -` by Stacks 0B7B (2)
(`Stacks.Chow.BivariantChowClass.cap_capPow_heq`). The base change `P ×_X X'` is the projective
bundle of `ℰ'`, compatibly with the twists (`Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), so
pushing forward along that isomorphism the family `c ∩ α_j` satisfies the relation of Stacks
02U6 on `𝐏(ℰ')` for the class `c ∩ α`, and the uniqueness half of Stacks 02U6 identifies it with
the family `c_j(ℰ') ∩ (c ∩ α)`.

## Main results

* `Stacks.Chow.GenuineChern.bundleChernCapFamily_cap` — the rank `n + 1` case, on families.
* `Stacks.Chow.GenuineChern.chernCap_cap` — the identity above, in every rank.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {f : X' ⟶ X} {hf : f ≫ sX = sX'} {p : ℤ}

/-- **Stacks 02SU along an isomorphism.** Pushforward along an isomorphism `u : A ⟶ B` carries
`c₁(𝒩) ∩ -` to `c₁(ℳ) ∩ -` when `𝒩 ≅ u^*ℳ`. -/
theorem chowPushforwardOfIso_invCap {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA)
    (M : B.Modules) [SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property M]
    (N : A.Modules) [SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property N]
    (eN : N ≅ (Scheme.Modules.pullback u).obj M) (k : ℤ) (x : chowGroup C sA (k + 1)) :
    chowPushforwardOfIso C sA sB u hu k ((invCap C sA N).capOnChow C sA k x) =
      (invCap C sB M).capOnChow C sB k (chowPushforwardOfIso C sA sB u hu (k + 1) x) := by
  have := isInvertible_pullback u M
  rw [invCap_capOnChow_congr C sA N ((Scheme.Modules.pullback u).obj M) eN]
  exact properChowPushforward_invCap C sA sB u hu M k x

/-- **The cap product of a bivariant class carries the Chern class cap products of `ℰ` to those
of its pullback**, on families, for `ℰ` of rank `n + 1` on a test scheme `g : T ⟶ X`: the
family of `c ∩ α` for `ℰ'` is the cap product with `c` of the family of `α` for `ℰ`. -/
theorem bundleChernCapFamily_cap (c : BivariantChowClass C sX' sX f hf p) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (E : T.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.snd f g) E (n + 1)
    bundleChernCapFamily ((Scheme.Modules.pullback (pullback.snd f g)).obj E) n C
        (pullback.fst f g ≫ sX') (k - p) (c.cap g k α) =
      operationChernFamily C (g ≫ sX) (pullback.fst f g ≫ sX') (n + 1) p (c.capHom g) k
        (bundleChernCapFamily E n C (g ≫ sX) k α) := by
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.snd f g) E (n + 1)
  set E' := (Scheme.Modules.pullback (pullback.snd f g)).obj E with hE'
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E' (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  let := flat_bundleProj E' n
  let := locallyOfFiniteType_bundleProj E' n
  set π := bundleProj E with hπ
  set π' := bundleProj E' with hπ'
  have : LocallyOfFiniteType (bivariantBaseChangeMap f g π) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g π)
      (P := @LocallyOfFiniteType) inferInstance
  have : Flat (bivariantBaseChangeMap f g π) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g π) (P := @Flat)
      inferInstance
  -- the base change of `𝐏(ℰ)` is `𝐏(ℰ')`, compatibly with the twists
  obtain ⟨e, he, ⟨eT⟩⟩ := bundleBaseChangeHolds (pullback.snd f g) E E' (Iso.refl _)
  set φ : pullback f (π ≫ g) ≅ bundle E' := (pullbackLeftPullbackSndIso f g π).symm ≪≫ e.symm
  have hφh : φ.hom = (pullbackLeftPullbackSndIso f g π).inv ≫ e.inv := rfl
  have hφπ : φ.hom ≫ π' = bivariantBaseChangeMap f g π := by
    rw [hφh, Category.assoc, hπ', ← he, Iso.inv_hom_id_assoc]
    apply pullback.hom_ext
    · simp only [bivariantBaseChangeMap, pullback.lift_fst, Category.comp_id]
      exact pullbackLeftPullbackSndIso_inv_fst f g π
    · simp only [bivariantBaseChangeMap, pullback.lift_snd]
      exact pullbackLeftPullbackSndIso_inv_fst_snd f g π
  have hφs : φ.hom ≫ e.hom ≫ pullback.snd (pullback.snd f g) π = pullback.snd f (π ≫ g) := by
    rw [hφh, Category.assoc, Iso.inv_hom_id_assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
  have hφb : φ.hom ≫ π' ≫ pullback.fst f g ≫ sX' = pullback.fst f (π ≫ g) ≫ sX' := by
    rw [← Category.assoc, hφπ, bivariantBaseChangeMap_comp_structureMorphism]
  have := isInvertible_pullback (pullback.snd f (π ≫ g)) (bundleTwist E)
  have := isInvertible_pullback φ.hom (bundleTwist E')
  have eL : (Scheme.Modules.pullback (pullback.snd f (π ≫ g))).obj (bundleTwist E) ≅
      (Scheme.Modules.pullback φ.hom).obj (bundleTwist E') :=
    (Scheme.Modules.pullbackCongr hφs.symm).app (bundleTwist E) ≪≫
      ((Scheme.Modules.pullbackComp φ.hom (e.hom ≫ pullback.snd (pullback.snd f g) π)).app
        (bundleTwist E)).symm ≪≫ (Scheme.Modules.pullback φ.hom).mapIso eT
  -- the operation on the bundles: cap with `c` at `P ⟶ X`, then push forward to `𝐏(ℰ')`
  set opP : ∀ m : ℤ, chowGroup C (π ≫ g ≫ sX) m →+
      chowGroup C (π' ≫ pullback.fst f g ≫ sX') (m - p) := fun m ↦
    (chowPushforwardOfIso C _ _ φ.hom hφb (m - p)).comp (c.capHom (π ≫ g) m) with hopP
  -- Stacks 0B7B (2) and the correspondence of the twists
  have hξ : ∀ (s : ℕ) (a m : ℤ) (ham : a = m + s) (m' : ℤ) (ham' : a - p = m' + s)
      (_ : m' = m - p) (x : chowGroup C (π ≫ g ≫ sX) a),
      opP m (capPow C (π ≫ g ≫ sX) (bundleTwistCap E C (g ≫ sX)) s a m ham x) ≍
        capPow C (π' ≫ pullback.fst f g ≫ sX') (bundleTwistCap E' C (pullback.fst f g ≫ sX'))
          s (a - p) m' ham' (opP a x) := by
    intro s a m ham m' ham' hm x
    have hc := c.cap_capPow_heq (π ≫ g) (bundleTwist E) s a m ham m' ham' hm x
    refine (chowPushforwardOfIso_heq φ.hom hφb hφb rfl rfl (by omega) hc).trans (heq_of_eq ?_)
    exact capPow_comm C (π' ≫ pullback.fst f g ≫ sX') (bundleTwistCap E' C (pullback.fst f g ≫ sX'))
      (pullback.fst f (π ≫ g) ≫ sX')
      (invCap C _ ((Scheme.Modules.pullback (pullback.snd f (π ≫ g))).obj (bundleTwist E)))
      (fun d ↦ chowPushforwardOfIso C _ _ φ.hom hφb d)
      (fun d y ↦ chowPushforwardOfIso_invCap _ _ φ.hom hφb (bundleTwist E') _ eL d y) s (a - p) m'
      ham' (c.cap (π ≫ g) a x)
  -- the cap product of `c` is compatible with the summands of the two relations
  have hcompat : ChernTermsCompatibleWithOperation C (g ≫ sX) (pullback.fst f g ≫ sX')
      (π ≫ g ≫ sX) (π' ≫ pullback.fst f g ≫ sX') π rfl π' rfl (n + 1)
      (relativeDimension_bundleProj E n) (relativeDimension_bundleProj E' n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
      (bundleTwistCap E C (g ≫ sX)) (bundleTwistCap E' C (pullback.fst f g ≫ sX')) p
      (c.capHom g) opP := by
    intro k i hi
    set d : ℤ := k - ((n + 1 - i : ℕ) : ℤ) with hd
    intro x
    refine eq_of_heq ((chowGroupCast_heq C _ _ _).trans ?_)
    rw [projectiveBundleChernTerm_eq_capPow, projectiveBundleChernTerm_eq_capPow]
    refine (hξ i _ _ _ (k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) - p) (by omega) rfl
      _).trans ?_
    refine capPow_heq C _ _ _ _ rfl (by omega) (by omega) ?_
    -- condition (2) of Stacks 0B76 along `π`, and `P ×_X X' ≅ 𝐏(ℰ')`
    have hfl := c.cap_flatPullback g π (n + 1 - 1) (relativeDimension_bundleProj E n) d x
    have hsq := flatPullbackChow_chowPushforwardOfIso C (pullback.fst f g ≫ sX')
      (pullback.fst f (π ≫ g) ≫ sX') (pullback.fst f g ≫ sX') (π' ≫ pullback.fst f g ≫ sX')
      (𝟙 _) (Category.id_comp _) φ.hom hφb (bivariantBaseChangeMap f g π)
      (bivariantBaseChangeMap_comp_structureMorphism sX' f g π) π' rfl
      (by rw [Category.comp_id, hφπ]) (n + 1 - 1)
      (AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_bivariantBaseChangeMap f g π)
        (relativeDimension_bundleProj E n)) (relativeDimension_bundleProj E' n)
      (d - p)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) (c.cap g d x)
    rw [chowPushforwardOfIso_id] at hsq
    simp only [hopP, BivariantChowClass.capHom_apply, projectiveBundlePullback]
    refine (chowPushforwardOfIso_heq φ.hom hφb hφb rfl rfl (by omega) hfl).trans ?_
    refine (heq_of_eq hsq.symm).trans ?_
    exact flatPullbackChow_heq C _ _ π' rfl (n + 1 - 1) (relativeDimension_bundleProj E' n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k) (by omega)
      (chowGroupCast_heq C _ _ _).symm
  -- so the cap product of the family of `α` satisfies the relation on `𝐏(ℰ')`
  have key := operation_isChernCapFamily C (g ≫ sX) (pullback.fst f g ≫ sX') _ _ π rfl π' rfl
    (n + 1) _ _ _ _ (bundleTwistCap E C _) (bundleTwistCap E' C _) p (c.capHom g) opP hcompat k α
    _ (isChernCapFamily_bundleChernCapFamily E n C (g ≫ sX) k α)
  exact (eq_bundleChernCapFamily_of_isChernCapFamily E' n C _ (k - p) _ _ key).symm

/-- **The cap product of a bivariant class commutes with the Chern class cap products**, in every
rank. For `c ∈ A^p(X' ⟶ X)`, a test scheme `g : T ⟶ X`, `ℰ` finite locally free of rank `r` on
`T` and a module `ℰ'` on `T ×_X X'` identified with the pullback of `ℰ`,

  `c_j(ℰ') ∩ (c ∩ α) = c ∩ (c_j(ℰ) ∩ α)`  in  `A_{k-p-j}(T ×_X X')`,  for `α ∈ A_k(T)`. -/
theorem chernCap_cap (c : BivariantChowClass C sX' sX f hf p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (E : T.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (E' : (pullback f g).Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback (pullback.snd f g)).obj E) (k : ℤ) (j : Fin (r + 1))
    (α : chowGroup C (g ≫ sX) k) :
    chernCap C r (pullback.fst f g ≫ sX') E' (k - p) j (c.cap g k α) =
      chowGroupCast C (pullback.fst f g ≫ sX') (by omega)
        (c.cap g (k - (j : ℤ)) (chernCap C r (g ≫ sX) E k j α)) := by
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.snd f g) E r
  rw [chernCap_congr C _ r eE]
  cases r with
  | zero =>
    rw [chernCap_zero, chernCap_zero]
    refine eq_of_heq ((chowGroupCast_heq C _ _ _).trans (HEq.symm ?_))
    refine (chowGroupCast_heq C _ _ _).trans ?_
    exact c.heq_cap g (by rw [show (j : ℕ) = 0 from Fin.val_eq_zero j]; simp)
      (chowGroupCast_heq C _ _ _)
  | succ n =>
    rw [chernCap_succ, chernCap_succ, bundleChernCap_apply, bundleChernCap_apply,
      bundleChernCapFamily_cap c g E n k α]
    rfl

end Stacks.Chow.GenuineChern

end
