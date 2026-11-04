module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm
import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes are in the center of the bivariant ring (Stacks 02UA)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℰ` be a
locally free `𝒪_X`-module of rank `r`. Stacks 02UA asserts:

1. `c_j(ℰ) ∈ A^j(X)` is in the center of `A^*(X)`;
2. if `f : X' ⟶ X` is locally of finite type and `c ∈ A^*(X' ⟶ X)`, then
   `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c`;

and in particular, for a second locally free module `ℱ` of rank `s`,
`c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α` in `A_{k-i-j}(X)` for `α ∈ A_k(X)`.

Here `c_j(ℰ)` is the bivariant class `Stacks.Chow.GenuineChern.chernClass` of Stacks 0B7H, which
caps by the cap products `c_j(g^*ℰ) ∩ -` of Stacks 02U6 on every test scheme `g : T ⟶ X`. The
bivariant classes of clause (2) are those of Stacks 0B76, `Stacks.Chow.BivariantChowClass`, and
`A^*(X)` is the Chow cohomology ring of Stacks 0B7E, `Stacks.Chow.chowCohomologyRingOfInvertible`.

## The argument

Both clauses reduce, on each test scheme, to the identity
`c ∩ (c_j(ℰ|_T) ∩ α) = c_j(ℰ|_{T ×_X X'}) ∩ (c ∩ α)`, which is
`Stacks.Chow.GenuineChern.chernCap_cap`: the source's argument through the projective bundle
relation of Stacks 02U6 and Stacks 0B7B. The rest is bookkeeping of the canonical isomorphisms
`X ×_X T ≅ T` through which the class `c_j(ℰ)` is read on the test schemes.

## Main results

* `Stacks.Chow.GenuineChern.comp_chernClass` — **Stacks 02UA (2)**:
  `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c` in `A^{p+j}(X' ⟶ X)`.
* `Stacks.Chow.GenuineChern.chernClass_mem_center` — **Stacks 02UA (1)**: `c_j(ℰ)` lies in the
  center of `A^*(X)`.
* `Stacks.Chow.GenuineChern.chernCap_chernCap_comm` — **the "in particular" of Stacks 02UA**:
  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α` in `A_{k-i-j}(X)`.

## Implementation notes

The two composites of clause (2) are classes for `f ≫ 𝟙 X` and for `𝟙 X' ≫ f`, of degrees `p + j`
and `j + p`: the same morphism and the same integer, not the same terms. The second is read as a
class for `f ≫ 𝟙 X` of degree `p + j` through `Stacks.Chow.BivariantChowClass.degreeCongr` and the
transport along the identity of `X'`, as in Stacks 0FAS and 0FBX.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- Pushforward along an isomorphism, at heterogeneously equal classes in equal degrees. -/
private theorem pushIso_heq {A B : Scheme.{u}} {sA : A ⟶ C.S} [LocallyOfFiniteType sA]
    {sB : B ⟶ C.S} [LocallyOfFiniteType sB] (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA)
    {d₁ d₂ : ℤ} (hd : d₁ = d₂) {x : chowGroup C sA d₁} {y : chowGroup C sA d₂} (hxy : x ≍ y) :
    chowPushforwardOfIso C sA sB u hu d₁ x ≍ chowPushforwardOfIso C sA sB u hu d₂ y :=
  chowPushforwardOfIso_heq u hu hu rfl rfl hd hxy

omit [LocallyOfFiniteType sX] in
/-- The inverse of the identification `X ×_X T ≅ T` lies over the base. -/
theorem identityBaseChangeIso_inv_comp_base {T : Scheme.{u}} (g : T ⟶ X) :
    (identityBaseChangeIso g).inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX := by
  rw [fst_eq_identityBaseChangeIso_hom g, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The cap operation of `c_j(ℰ)`** on a test scheme `g : T ⟶ X` is `c_j(g^*ℰ) ∩ -`, read on
`X ×_X T` through the identification with `T`. -/
theorem chernClass_cap (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
    (chernClass C sX F r j).cap g k α =
      chowPushforwardOfIso C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) (identityBaseChangeIso g).inv
        (identityBaseChangeIso_inv_comp_base g) (k - (j : ℤ))
        (chernCap C r (g ≫ sX) ((Scheme.Modules.pullback g).obj F) k j α) := by
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
  rw [← isChernClassBivariant_chernClass C sX F r j g k α, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (by simp) _ (Category.id_comp _),
    chowPushforwardOfIso_id]

/-- The comparison of `T ×_X X'` with `(X ×_X T) ×_X X'` over the identification `T ≅ X ×_X T`. -/
private abbrev testComparison {X' T : Scheme.{u}} (f : X' ⟶ X) (t : T ⟶ X) :
    pullback f t ⟶ pullback f (pullback.fst (𝟙 X) t) :=
  pullback.map f t f (pullback.fst (𝟙 X) t) (𝟙 X') (identityBaseChangeIso t).inv (𝟙 X)
    (by simp) (by rw [Category.comp_id, fst_eq_identityBaseChangeIso_hom t, Iso.inv_hom_id_assoc])

/-- The module `(f^*ℰ)|_{T ×_X X'}` is the pullback of `ℰ|_T`. -/
private def pullbackModuleIso {X' T : Scheme.{u}} (f : X' ⟶ X) (t : T ⟶ X) (F : X.Modules) :
    (Scheme.Modules.pullback (pullback.fst f t)).obj ((Scheme.Modules.pullback f).obj F) ≅
      (Scheme.Modules.pullback (pullback.snd f t)).obj ((Scheme.Modules.pullback t).obj F) :=
  ((Scheme.Modules.pullbackComp (pullback.fst f t) f).app F) ≪≫
    (Scheme.Modules.pullbackCongr pullback.condition).app F ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f t) t).app F).symm

/-- **Stacks 02UA (2).** Let `ℰ` be a locally free `𝒪_X`-module of rank `r`, let `f : X' ⟶ X` be
locally of finite type and let `c ∈ A^p(X' ⟶ X)` be a bivariant class. Then

  `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c`   in   `A^{p+j}(X' ⟶ X)`,

with `c_j(ℰ) ∈ A^j(X)` and `c_j(f^*ℰ) ∈ A^j(X')` the bivariant Chern classes of Stacks 0B7H. The
left side is a class for `f ≫ 𝟙 X` of degree `p + j`; the right side, a class for `𝟙 X' ≫ f` of
degree `j + p`, is read as one for `f ≫ 𝟙 X` of degree `p + j` along the identity of `X'`. -/
@[stacks 02UA "(2): c ∘ c_j(E) = c_j(f^*E) ∘ c in A^{p+j}(X' → X) for every f : X' → X locally \
of finite type and every bivariant class c in A^p(X' → X) of Stacks 0B76"]
theorem comp_chernClass {X' : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']
    (F : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) (f : X' ⟶ X) (hf : f ≫ sX = sX') {p : ℤ}
    (c : BivariantChowClass C sX' sX f hf p) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f F r
    c.comp (BivariantChowClass.equivBivariantClass.symm (chernClass C sX F r j)) =
      (((BivariantChowClass.equivBivariantClass.symm
          (chernClass C sX' ((Scheme.Modules.pullback f).obj F) r j)).comp c).degreeCongr
        (add_comm (j : ℤ) p)).transport (comp_comp_structureMorphism_eq hf (Category.id_comp sX))
        (Iso.refl X') (by simp) := by
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f F r
  have := BivariantChowClass.locallyOfFiniteType_of_structure sX f hf
  refine BivariantChowClass.ext fun {T} t _ k α ↦ ?_
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback t F r
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.fst f t)
    ((Scheme.Modules.pullback f).obj F) r
  set z := chernCap C r (pullback.fst f t ≫ sX')
    ((Scheme.Modules.pullback (pullback.fst f t)).obj ((Scheme.Modules.pullback f).obj F))
    (k - p) j (c.cap t k α) with hz
  have hcore := chernCap_cap c t ((Scheme.Modules.pullback t).obj F) r
    ((Scheme.Modules.pullback (pullback.fst f t)).obj ((Scheme.Modules.pullback f).obj F))
    (pullbackModuleIso f t F) k j α
  have hw₁ : testComparison f t ≫ pullback.fst f (pullback.fst (𝟙 X) t) = pullback.fst f t := by
    simp [testComparison]
  have hw₂ : testComparison f t ≫ pullback.snd f (pullback.fst (𝟙 X) t) =
      pullback.snd f t ≫ (identityBaseChangeIso t).inv := by
    simp [testComparison]
  have hwX : testComparison f t ≫ pullback.fst f (pullback.fst (𝟙 X) t) ≫ sX' =
      pullback.fst f t ≫ sX' := by
    rw [← Category.assoc, hw₁]
  rw [BivariantChowClass.comp_cap, BivariantChowClass.equivBivariantClass_symm_cap,
    chernClass_cap, c.cap_chowPushforwardOfIso (pullback.fst (𝟙 X) t) t
      (identityBaseChangeIso t).inv (by rw [fst_eq_identityBaseChangeIso_hom t,
        Iso.inv_hom_id_assoc]) (identityBaseChangeIso_inv_comp_base t) (testComparison f t) hw₁
      hw₂ hwX, chowPushforwardOfIso_comp_apply, BivariantChowClass.transport_cap]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine (pushIso_heq _ _ (by omega)
    ((chowGroupCast_heq C _ _ _).symm.trans (heq_of_eq hcore.symm))).trans ?_
  refine HEq.symm ((pushIso_heq _ _ (by omega)
    (BivariantChowClass.degreeCongr_cap _ _ t k α)).trans ?_)
  rw [BivariantChowClass.comp_cap, BivariantChowClass.equivBivariantClass_symm_cap, chernClass_cap,
    chowPushforwardOfIso_comp_apply]
  refine (pushIso_heq _ _ (by omega) (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_
  rw [chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  apply pullback.hom_ext <;> simp [testComparison, transportPullbackIso]

/-! ### Clause (1) -/

/-- The rule `c_j(ℰ)` induces on the test schemes is `α ↦ c_j(g^*ℰ) ∩ α`. -/
theorem toIdentityCapRule_chernClass (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
    BivariantClass.toIdentityCapRule C (gysinSystemOfInvertible C) sX (j : ℤ)
        (chernClass C sX F r j) g k α =
      chernCap C r (g ≫ sX) ((Scheme.Modules.pullback g).obj F) k j α :=
  isChernClassBivariant_chernClass C sX F r j g k α

/-- **The rule of a class of `A^q(X)` commutes with the Chern class cap products** on every test
scheme `g : T ⟶ X`: `b ∩ (c_j(g^*ℰ) ∩ α) = c_j(g^*ℰ) ∩ (b ∩ α)`, both sides read on `T`. -/
theorem toIdentityCapRule_chernCap_heq {q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (E : T.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) (j : Fin (r + 1))
    (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C (gysinSystemOfInvertible C) sX q b g (k - (j : ℤ))
        (chernCap C r (g ≫ sX) E k j α) ≍
      chernCap C r (g ≫ sX) E (k - q) j
        (BivariantClass.toIdentityCapRule C (gysinSystemOfInvertible C) sX q b g k α) := by
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.snd (𝟙 X) g) E r
  have hcore := chernCap_cap (BivariantChowClass.equivBivariantClass.symm b) g E r
    ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj E) (Iso.refl _) k j α
  rw [BivariantChowClass.equivBivariantClass_symm_cap,
    BivariantChowClass.equivBivariantClass_symm_cap] at hcore
  have hpush := chernCap_properPushforward C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
    (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g) E r
    ((Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj E) (Iso.refl _) (k - q) j
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) (b.cap g k α)
  rw [BivariantClass.toIdentityCapRule_apply, BivariantClass.toIdentityCapRule_apply]
  refine (pushIso_heq _ _ (by omega)
    ((chowGroupCast_heq C _ _ _).symm.trans (heq_of_eq hcore.symm))).trans (heq_of_eq hpush.symm)

/-- **Stacks 02UA (1)**, as a commutation: `b · c_j(ℰ)` and `c_j(ℰ) · b` agree for every
`b ∈ A^q(X)`. They lie in `A^{q+j}(X)` and `A^{j+q}(X)`, the same integer and not the same term. -/
theorem chowCohomologyRingMul_chernClass_heq (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) {q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    chowCohomologyMulOfInvertible C sX q (j : ℤ) b (chernClass C sX F r j) ≍
      chowCohomologyMulOfInvertible C sX (j : ℤ) q (chernClass C sX F r j) b := by
  rw [← chowCohomologyRingMul_gysinSystemOfInvertible,
    ← chowCohomologyRingMul_gysinSystemOfInvertible]
  refine BivariantClass.heq_of_toIdentityCapRule_heq C _ sX (add_comm q (j : ℤ)) _ _
    fun {T} g _ k α ↦ ?_
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g F r
  refine (chowCohomologyMul_toIdentityCapRule_heq C _ sX _ b _ g k α).trans ?_
  refine HEq.trans ?_ (chowCohomologyMul_toIdentityCapRule_heq C _ sX _ _ b g k α).symm
  rw [toIdentityCapRule_chernClass, toIdentityCapRule_chernClass]
  exact toIdentityCapRule_chernCap_heq b g _ r k j α

/-- **Stacks 02UA (1).** The `j`-th Chern class `c_j(ℰ) ∈ A^j(X)` of a locally free `𝒪_X`-module of
rank `r` lies in the center of the Chow cohomology ring `A^*(X)` of Stacks 0B7E. -/
@[stacks 02UA "(1): c_j(E) in A^j(X) is in the center of the Chow cohomology ring A^*(X) of \
Stacks 0B7E, for the bivariant Chern class of Stacks 0B7H"]
theorem chernClass_mem_center (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) :
    letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
      chowCohomologyRingOfInvertible C sX
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) (j : ℤ)
        (chernClass C sX F r j) ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  let : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q :=
    chowCohomologyGRingOfInvertible C sX
  let : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
    chowCohomologyRingOfInvertible C sX
  rw [Subring.mem_center_iff]
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | of q b =>
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (Sigma.ext (add_comm _ _) (chowCohomologyRingMul_chernClass_heq F r j b))
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

end Stacks.Chow.GenuineChern

add_to_stacks 02UA "the 'in particular': c_i(E) ∩ c_j(F) ∩ α = c_j(F) ∩ c_i(E) ∩ α in \
CH_{k-i-j}(X) for locally free E, F of ranks r, s and every α in CH_k(X)"
  Stacks.Chow.GenuineChern.chernCap_chernCap_comm

end
