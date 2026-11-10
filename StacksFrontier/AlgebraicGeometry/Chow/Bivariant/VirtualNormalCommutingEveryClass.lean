module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteBivariantComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardPulledBackModule
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityComparison
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# The Gysin class of a closed subscheme commutes with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `Z ⊆ X` be a closed subscheme with virtual normal sheaf `𝒩`
of constant rank `r`, let `g : Y ⟶ X` be locally of finite type and let `c ∈ A^p(Y ⟶ X)` be a
bivariant class. **Stacks 0FBP** says that `c` and the Gysin class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of
Stacks 0FBK commute in the sense of Stacks 0FA2.

The class `c(Z ⟶ X, 𝒩)` is characterized by the identity

  `p^* ∘ c(Z ⟶ X, 𝒩) = ι_* ∘ j^* ∘ C   in   A⁰(N ⟶ X)`

of Stacks 0FBK, where `p : N ⟶ Z` is the vector bundle of `𝒩`, `C ∈ A⁰(W_∞ ⟶ X)` is the class of
Stacks 0F9J for the blowup `W` of `𝐏¹_X` in `∞(Z)`, `j : C_ZX ⟶ W_∞` is the open immersion of
Stacks 0FBH and `ι : C_ZX ⟶ N` the closed immersion of the normal cone.

## Main definitions

* `Stacks.Chow.BivariantClass.CommutesWithEveryClass` — a bivariant class commutes, in the sense
  of Stacks 0FA2, with every bivariant class over the same target.

## Main results

* `Stacks.Chow.gysinAtInfinityClass_bivariantCommute` — Stacks 0FAS for the class of
  Stacks 0F9J: `C` commutes with every bivariant class.
* `Stacks.Chow.commutesWithEveryClass_bivariantCompositeOfInvertible`,
  `Stacks.Chow.commutesWithEveryClass_bivariantProperPushforward`,
  `Stacks.Chow.commutesWithEveryClass_flatPullbackBivariantClass` — the property is preserved by
  composition (Stacks 0B75) and proper pushforward (Stacks 0EPK), and holds for flat pullback
  (Stacks 0B78).
* `Stacks.Chow.bivariantCommute_of_bivariantCompositeOfInvertible` — a factor `a` with injective
  cap operations commuting with `c` can be cancelled from a composite `a ∘ b` commuting with `c`.
* `Stacks.Chow.virtualNormalConeClass_commutesWithEveryClass` — the class `ι_* ∘ j^* ∘ C`
  commutes with every bivariant class.
* `Stacks.Chow.virtualNormalBundleClass_bivariantCommute` — the commutation at constant rank,
  for the class of the blowup construction.

## Implementation notes

All classes are taken at the Gysin system `Stacks.Chow.gysinSystemOfInvertible`, at which the
class `c(Z ⟶ X, 𝒩)` of `Stacks.Chow.virtualNormalBundleClass` lives. The commutation of
Stacks 0FA2 compares a class whose source lies over the base through `f ≫ sX`; the class of
Stacks 0FBK is accordingly read with `sZ = i ≫ sX`.

## References

* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The bivariance axioms of a class, read through comparison isomorphisms -/

section CapGysin

/-- Pushing forward along an isomorphism is inverted by pushing forward along its inverse. -/
theorem eq_chowPushforwardOfIso_inv_of_eq {C : ChowSituation.{u}} {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ≅ B)
    (he : e.hom ≫ sB = sA) (he' : e.inv ≫ sA = sB) (k : ℤ) {x : chowGroup C sA k}
    {y : chowGroup C sB k} (h : chowPushforwardOfIso C sA sB e.hom he k x = y) :
    x = chowPushforwardOfIso C sB sA e.inv he' k y := by
  subst h
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _)
    e.hom_inv_id _ (Category.id_comp _), chowPushforwardOfIso_id]

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y A V : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {fY : Y ⟶ X} [LocallyOfFiniteType fY] {p : ℤ}

/-- Condition (3) of Stacks 0B76 for `c`, read for a divisor identified with a test scheme by
an isomorphism `u`. -/
theorem BivariantClass.cap_chowPushforwardOfIso_gysin
    (c : BivariantClass C G (fY ≫ sX) sX fY rfl p) (g : A ⟶ X) [LocallyOfFiniteType g]
    (L : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback fY g).sheaf.obj
      (pullback fY g).ringCatSheaf.property ((Scheme.Modules.pullback (pullback.snd fY g)).obj L)]
    (s : Γ(L, ⊤)) (gV : V ⟶ X) [LocallyOfFiniteType gV]
    (u : (Stacks.Divisors.zeroScheme A L s).subscheme ⟶ V) [IsIso u]
    (hu : u ≫ gV = (Stacks.Divisors.zeroScheme A L s).subschemeι ≫ g)
    {qA : A ⟶ C.S} [LocallyOfFiniteType qA] (hqA : qA = g ≫ sX)
    {qV : V ⟶ C.S} [LocallyOfFiniteType qV] (hqV : qV = gV ≫ sX)
    (huq : u ≫ qV = (Stacks.Divisors.zeroScheme A L s).subschemeι ≫ qA) (k : ℤ)
    (γ : chowGroup C qA (k + 1)) :
    c.cap gV k (chowGroupCongr C hqV k
        (chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ qA) qV u huq k
          (G.onChow qA L s k γ))) =
      chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme (pullback fY g)
          ((Scheme.Modules.pullback (pullback.snd fY g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY g) L s)).subschemeι ≫
            (pullback.fst fY g ≫ (fY ≫ sX)))
        (pullback.fst fY gV ≫ (fY ≫ sX))
        ((bivariantDivisorBaseChangeIso fY g L s).inv ≫
          (testBaseChangeIso fY gV u ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ g) hu).hom)
        (by
          rw [Category.assoc, testBaseChangeIso_hom_fst_assoc, Iso.inv_comp_eq,
            ← Category.assoc, ← Category.assoc, bivariantDivisorBaseChangeIso_hom_subschemeι]
          simp [bivariantBaseChangeMap]) (k - p)
        (G.onChow (pullback.fst fY g ≫ (fY ≫ sX))
          ((Scheme.Modules.pullback (pullback.snd fY g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY g) L s) (k - p)
          (chowGroupDegreeEquiv C (pullback.fst fY g ≫ (fY ≫ sX))
            (by ring : k + 1 - p = k - p + 1)
            (c.cap g (k + 1) (chowGroupCongr C hqA (k + 1) γ)))) := by
  subst hqA hqV
  have hb : (bivariantDivisorBaseChangeIso fY g L s).hom ≫
      ((Stacks.Divisors.zeroScheme (pullback fY g)
        ((Scheme.Modules.pullback (pullback.snd fY g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY g) L s)).subschemeι ≫
          pullback.fst fY g ≫ (fY ≫ sX)) =
      pullback.fst fY ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ g) ≫ (fY ≫ sX) := by
    rw [← Category.assoc, bivariantDivisorBaseChangeIso_hom_subschemeι]
    simp [bivariantBaseChangeMap]
  have hgn := c.gysin_naturality g L s k (bivariantDivisorBaseChangeIso fY g L s)
    (bivariantDivisorBaseChangeIso_hom_subschemeι fY g L s) hb
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) γ
  rw [properChowPushforward_eq_chowPushforwardOfIso] at hgn
  have hinv := eq_chowPushforwardOfIso_inv_of_eq _ _ _ _ (by rw [Iso.inv_comp_eq, hb]) _ hgn
  change c.cap gV k (chowPushforwardOfIso C _ _ u huq k (G.onChow (g ≫ sX) L s k γ)) = _
  rw [BivariantClass.cap_chowPushforwardOfIso c gV u
    ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ g) hu
    ((Stacks.Divisors.zeroScheme A L s).subschemeι ≫ (g ≫ sX)) (Category.assoc _ _ _).symm k
    huq (G.onChow (g ≫ sX) L s k γ) _ rfl]
  refine (congrArg (chowPushforwardOfIso C _ _ _ _ (k - p)) hinv).trans ?_
  rw [chowPushforwardOfIso_comp_apply, eqMp_chowGroup]
  rfl


/-- **Condition (2) of Stacks 0B76 for `c`, on a lift.** Let `ι : V ⟶ U` be an open immersion
and `π : V ⟶ T` flat of relative dimension `r`, over `X`. If the restriction of `β` to `V` is
the flat pullback of `α` along `π`, then the restriction of `c ∩ β` to `Y ×_X V` is the flat
pullback of `c ∩ α` along the base change of `π`. -/
theorem BivariantClass.cap_restrict_heq_flatPullback
    (c : BivariantClass C G (fY ≫ sX) sX fY rfl p) {T U V : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (w : U ⟶ X) [LocallyOfFiniteType w] (ι : V ⟶ U) [IsOpenImmersion ι]
    [LocallyOfFiniteType (ι ≫ w)] (π : V ⟶ T) [LocallyOfFiniteType π] [Flat π] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension π r) (hπ : π ≫ t = ι ≫ w) (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) (β : chowGroup C (w ≫ sX) (k + r))
    (hβ : chowGroupRestrict C (w ≫ sX) ((ι ≫ w) ≫ sX) ι (Category.assoc _ _ _).symm (k + r) β =
      flatPullbackChow C ((ι ≫ w) ≫ sX) (t ≫ sX) π (by rw [← Category.assoc, hπ]) r hr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α) :
    haveI : IsOpenImmersion (bivariantBaseChangeMap fY w ι) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (isPullback_bivariantBaseChangeMap fY w ι) inferInstance
    haveI : LocallyOfFiniteType (baseChangeMapOfEq fY t π (ι ≫ w) hπ) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
        (isPullback_baseChangeMapOfEq fY t π (ι ≫ w) hπ) inferInstance
    haveI : Flat (baseChangeMapOfEq fY t π (ι ≫ w) hπ) :=
      MorphismProperty.of_isPullback (P := @Flat)
        (isPullback_baseChangeMapOfEq fY t π (ι ≫ w) hπ) inferInstance
    chowGroupRestrict C (pullback.fst fY w ≫ (fY ≫ sX)) (pullback.fst fY (ι ≫ w) ≫ (fY ≫ sX))
        (bivariantBaseChangeMap fY w ι) (by simp [bivariantBaseChangeMap]) (k + r - p)
        (c.cap w (k + r) β) ≍
      flatPullbackChow C (pullback.fst fY (ι ≫ w) ≫ (fY ≫ sX)) (pullback.fst fY t ≫ (fY ≫ sX))
        (baseChangeMapOfEq fY t π (ι ≫ w) hπ)
        (baseChangeMapOfEq_comp_structure (fY ≫ sX) fY t π (ι ≫ w) hπ) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_baseChangeMapOfEq fY t π (ι ≫ w) hπ) hr) (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap t k α) := by
  have := locallyOfFiniteType_baseChangeMapOfEq fY t π (ι ≫ w) hπ
  have := flat_baseChangeMapOfEq fY t π (ι ≫ w) hπ
  rw [BivariantClass.cap_chowGroupRestrict C G (fY ≫ sX) sX fY rfl p c w ι (ι ≫ w) rfl
    (bivariantBaseChangeMap fY w ι) (isPullback_bivariantBaseChangeMap fY w ι)
    (by simp [bivariantBaseChangeMap]) (k + r) (Category.assoc _ _ _).symm, hβ]
  exact BivariantClass.flat_naturality_of_eq C G (fY ≫ sX) sX fY rfl p c t π (ι ≫ w) hπ r hr
    (baseChangeMapOfEq fY t π (ι ≫ w) hπ) (isPullback_baseChangeMapOfEq fY t π (ι ≫ w) hπ)
    (baseChangeMapOfEq_fst fY t π (ι ≫ w) hπ) k (by rw [← Category.assoc, hπ])
    (AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_baseChangeMapOfEq fY t π (ι ≫ w) hπ) hr)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α

/-- **The cap product of a lift, transported along a comparison isomorphism, restricts to the
flat pullback of the cap product.** This is
    `Stacks.Chow.BivariantClass.cap_restrict_heq_flatPullback`
read through an isomorphism `cmp : Y ×_X U ⟶ U'` and an identification `ψ` of
`Y ×_X V` with an open subscheme `V'` of `U'` over `Y ×_X T`. -/
theorem BivariantClass.restrict_chowPushforwardOfIso_cap_heq
    (c : BivariantClass C G (fY ≫ sX) sX fY rfl p) {T U V U' V' : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (w : U ⟶ X) [LocallyOfFiniteType w] (ι : V ⟶ U) [IsOpenImmersion ι]
    [LocallyOfFiniteType (ι ≫ w)] (π : V ⟶ T) [LocallyOfFiniteType π] [Flat π] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension π r) (hπ : π ≫ t = ι ≫ w) (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) (β : chowGroup C (w ≫ sX) (k + r))
    (hβ : chowGroupRestrict C (w ≫ sX) ((ι ≫ w) ≫ sX) ι (Category.assoc _ _ _).symm (k + r) β =
      flatPullbackChow C ((ι ≫ w) ≫ sX) (t ≫ sX) π (by rw [← Category.assoc, hπ]) r hr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α)
    (sU' : U' ⟶ C.S) [LocallyOfFiniteType sU'] (cmp : pullback fY w ⟶ U') [IsIso cmp]
    (hcmp : cmp ≫ sU' = pullback.fst fY w ≫ (fY ≫ sX))
    (sV' : V' ⟶ C.S) [LocallyOfFiniteType sV'] (ι' : V' ⟶ U') [IsOpenImmersion ι']
    (hι' : ι' ≫ sU' = sV') (π' : V' ⟶ pullback fY t) [LocallyOfFiniteType π'] [Flat π']
    (hr' : AlgebraicGeometry.RelativeDimension π' r)
    (hπ' : π' ≫ (pullback.fst fY t ≫ (fY ≫ sX)) = sV')
    (ψ : pullback fY (ι ≫ w) ⟶ V') [IsIso ψ]
    (hψι : ψ ≫ ι' = bivariantBaseChangeMap fY w ι ≫ cmp)
    (hψπ : ψ ≫ π' = baseChangeMapOfEq fY t π (ι ≫ w) hπ) :
    chowGroupRestrict C sU' sV' ι' hι' (k + r - p)
        (chowPushforwardOfIso C (pullback.fst fY w ≫ (fY ≫ sX)) sU' cmp hcmp (k + r - p)
          (c.cap w (k + r) β)) ≍
      flatPullbackChow C sV' (pullback.fst fY t ≫ (fY ≫ sX)) π' hπ' r hr' (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap t k α) := by
  have := locallyOfFiniteType_baseChangeMapOfEq fY t π (ι ≫ w) hπ
  have := flat_baseChangeMapOfEq fY t π (ι ≫ w) hπ
  have hψS : ψ ≫ sV' = pullback.fst fY (ι ≫ w) ≫ (fY ≫ sX) := by
    rw [← hι', ← Category.assoc, hψι, Category.assoc, hcmp]
    simp [bivariantBaseChangeMap]
  rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ cmp hcmp _
      (properPushforwardDescends C _ _ _ _ _),
    chowGroupRestrict_properChowPushforward C _ _ (pullback.fst fY (ι ≫ w) ≫ (fY ≫ sX)) _ cmp
      hcmp (bivariantBaseChangeMap fY w ι) (by simp [bivariantBaseChangeMap]) ι' hι' ψ hψS
      (IsPullback.of_vert_isIso ⟨hψι.symm⟩) (k + r - p) _
      (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_eq_chowPushforwardOfIso]
  have h1 := BivariantClass.cap_restrict_heq_flatPullback c t w ι π r hr hπ k α β hβ
  have h2 := flatPullbackChow_chowPushforwardOfIso C _ _ _ _ (𝟙 (pullback fY t))
    (Category.id_comp _) ψ hψS (baseChangeMapOfEq fY t π (ι ≫ w) hπ)
    (baseChangeMapOfEq_comp_structure (fY ≫ sX) fY t π (ι ≫ w) hπ) π' hπ'
    (by rw [Category.comp_id, hψπ]) r
    (AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_baseChangeMapOfEq fY t π (ι ≫ w) hπ) hr) hr' (k - p)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) (c.cap t k α)
  rw [chowPushforwardOfIso_id] at h2
  rw [h2]
  exact chowPushforwardOfIso_heq _ _ _ rfl rfl (by ring) h1
end CapGysin

/-- The inverse of the identification of Stacks 0B6Y lies over the base change of `g`. -/
@[reassoc]
theorem bivariantDivisorBaseChangeIso_inv_fst {Y Z T : Scheme.{u}} (g : Y ⟶ Z) (t : T ⟶ Z)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (bivariantDivisorBaseChangeIso g t L s).inv ≫
        pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) =
      (Stacks.Divisors.zeroScheme (pullback g t)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫
          pullback.fst g t := by
  rw [Iso.inv_comp_eq, ← Category.assoc, bivariantDivisorBaseChangeIso_hom_subschemeι]
  simp [bivariantBaseChangeMap]

/-- The Gysin map of a section pulled back from a common base `P` commutes with pushforward along
an isomorphism compatible with the two maps to `P`. -/
theorem gysinSystemOfInvertible_onChow_chowPushforwardOfIso_pullbackModule
    (C : ChowSituation.{u}) {A B V P : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA]
    (pB : B ⟶ C.S) [LocallyOfFiniteType pB] (a : A ⟶ V) (q : V ⟶ P) (r : B ⟶ P) (u : A ⟶ B)
    [IsIso u] (hu : u ≫ pB = pA) (hur : u ≫ r = a ≫ q) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subscheme ⟶
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subscheme) [IsIso j]
    (hjsq : j ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι =
      (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ u)
    (hj : j ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) =
      (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA)
    (α : chowGroup C pA (k + 1)) :
    (gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback r).obj L)
        (AlgebraicGeometry.pullbackGlobalSections r L s) k
        (chowPushforwardOfIso C pA pB u hu (k + 1) α) =
      chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) j hj k
        ((gysinSystemOfInvertible C).onChow pA
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s)) k α) :=
  gysinSystemOfInvertible_properPushforward_pullbackModule_comp C pA pB a q r u hu hur L s k j
    hjsq hj α

/-- The Gysin map of a section pulled back from a common base `P`, after pushforward along an
isomorphism `u : A ⟶ B` compatible with the two maps to `P`, read on a third scheme `Z` through
two identifications `z` and `M` of the two zero schemes with `Z` that are compatible with `u`. -/
theorem gysinSystemOfInvertible_onChow_chowPushforwardOfIso_comparison
    (C : ChowSituation.{u}) {A B V P Z : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA]
    (pB : B ⟶ C.S) [LocallyOfFiniteType pB] (pZ : Z ⟶ C.S) [LocallyOfFiniteType pZ] (a : A ⟶ V)
    (q : V ⟶ P) (r : B ⟶ P) (u : A ⟶ B) [IsIso u] (hu : u ≫ pB = pA) (hur : u ≫ r = a ≫ q)
    (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {m l : ℤ} (hml : m = l + 1)
    (z : (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subscheme ⟶ Z) [IsIso z]
    (hz : z ≫ pZ = (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB)
    (M : (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subscheme ⟶ Z) [IsIso M]
    (hM : M ≫ pZ = (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA)
    (hMz : M ≫ inv z ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι = (Stacks.Divisors.zeroScheme
              A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ u)
    (x : chowGroup C pA m) :
    chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) pZ z hz l
        ((gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s) l
          (chowGroupDegreeEquiv C pB hml (chowPushforwardOfIso C pA pB u hu m x))) =
      chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA) pZ M hM l
        ((gysinSystemOfInvertible C).onChow pA
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s)) l
          (chowGroupDegreeEquiv C pA hml x)) := by
  have hj : (M ≫ inv z) ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback r).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r L s)).subschemeι ≫ pB) =
              (Stacks.Divisors.zeroScheme A
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback q).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a ((Scheme.Modules.pullback q).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q L s))).subschemeι ≫ pA := by
    rw [Category.assoc, ← hz, IsIso.inv_hom_id_assoc, hM]
  rw [chowGroupDegreeEquiv_chowPushforwardOfIso,
    gysinSystemOfInvertible_onChow_chowPushforwardOfIso_pullbackModule C pA pB a q r u hu hur L s
      l (M ≫ inv z) (by rw [Category.assoc, hMz]) hj, chowPushforwardOfIso_comp_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by simp) _ _ _ _

/-! ### Stacks 0FAS for the class at infinity -/

section AtInfinity

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] (p : ℤ)
  (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p)

/-- **The cap product of a lift is a lift of the cap product.** If `β ∈ A_{k+1}(W ×_X T)` lifts
`α ∈ A_k(T)` in the sense of Stacks 0F9J, then `c ∩ β`, read on `W ×_X (Y ×_X T)` through the
comparison of the two iterated fibre products, lifts `c ∩ α`. -/
theorem IsModificationLift.commuteCapTransport {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ)
    {α : chowGroup C (t ≫ f) k} {β : chowGroup C (modificationBaseChangeOver f b t) (k + 1)}
    (hβ : IsModificationLift C f b hA t k α β) :
    IsModificationLift C f b hA (pullback.fst fY t ≫ fY) (k - p)
      (chowGroupCongr C (Category.assoc (pullback.fst fY t) fY f).symm (k - p) (c.cap t k α))
      (chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
          (by ring : k + 1 - p = k - p + 1)
          (commuteCapTransport C (gysinSystemOfInvertible C) f fY (modificationProjection f b) p
            c t (k + 1) β)) := by
  have := flat_modificationAffineChartProjection f b t hA
  have := flat_modificationAffineChartProjection f b (pullback.fst fY t ≫ fY) hA
  have hur : (pullback.snd fY (pullback.fst (modificationProjection f b) t ≫ modificationProjection
      f b) ≫ modificationBaseChangeToRelativeLine f b t) ≫ 𝟙 _ =
      commuteComparisonHom fY (modificationProjection f b) t ≫
        modificationBaseChangeToRelativeLine f b (pullback.fst fY t ≫ fY) := by
    simp [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine]
  have hsq := ((isPullback_bivariantBaseChangeMap fY (pullback.fst (modificationProjection f b) t ≫
      modificationProjection f b) (modificationAffineChartι f b t)).paste_horiz
    (isPullback_modificationAffineChart_relativeLine f b t)).paste_vert
    (IsPullback.of_vert_isIso ⟨hur⟩)
  rw [Category.comp_id] at hsq
  have hψι := hsq.isoIsPullback_hom_snd _ _
    (isPullback_modificationAffineChart_relativeLine f b (pullback.fst fY t ≫ fY))
  have hπ : modificationAffineChartProjection f b t ≫ t =
      modificationAffineChartι f b t ≫ (pullback.fst (modificationProjection f b) t ≫
          modificationProjection f b) := by
    simp [modificationAffineChartProjection, pullback.condition]
  have hψπ : (hsq.isoIsPullback _ _
      (isPullback_modificationAffineChart_relativeLine f b (pullback.fst fY t ≫ fY))).hom ≫
        modificationAffineChartProjection f b (pullback.fst fY t ≫ fY) =
      baseChangeMapOfEq fY t (modificationAffineChartProjection f b t)
        (modificationAffineChartι f b t ≫ (pullback.fst (modificationProjection f b) t ≫
            modificationProjection f b)) hπ := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [modificationAffineChartProjection, Category.assoc, reassoc_of% hψι] <;>
      simp [bivariantBaseChangeMap]
  unfold IsModificationLift at hβ ⊢
  rw [chowGroupRestrict_chowGroupDegreeEquiv]
  refine (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_
  rw [commuteCapTransport_apply C _ f fY (modificationProjection f b) p c t (k + 1)]
  refine (BivariantClass.restrict_chowPushforwardOfIso_cap_heq c t (pullback.fst
      (modificationProjection f b) t ≫ modificationProjection f b)
    (modificationAffineChartι f b t) (modificationAffineChartProjection f b t) 1
    (relativeDimension_modificationAffineChartProjection f b t hA) hπ k α
    (chowGroupCongr C (Category.assoc (pullback.fst (modificationProjection f b) t)
      (modificationProjection f b) f).symm (k + 1) β) hβ _
    (commuteComparisonHom fY (modificationProjection f b) t)
    (commuteComparisonHom_comp_structureMorphism C f fY (modificationProjection f b) t) _
    (modificationAffineChartι f b (pullback.fst fY t ≫ fY)) rfl
    (modificationAffineChartProjection f b (pullback.fst fY t ≫ fY))
    (relativeDimension_modificationAffineChartProjection f b (pullback.fst fY t ≫ fY) hA)
    (by rw [← Category.assoc (pullback.fst fY t), modificationAffineChartProjection_over])
    _ hψι hψπ).trans ?_
  exact flatPullbackChow_heq_congr_base C rfl (Category.assoc _ _ _).symm rfl _ _ rfl _ _ rfl _ _ _
      _
    (chowGroupCongr_heq C _ _ _).symm

omit [LocallyOfFiniteType fY] in
/-- The Gysin map at infinity, on an element. -/
theorem modificationInfinityGysin_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1)) :
    modificationInfinityGysin C f b g k β =
      chowPushforwardOfIso C (modificationZeroSchemeOver C f b g (modificationInfinityModule f b g)
          (modificationInfinitySection f b g)) (modificationInfinityBaseChangeOver f b g)
          (modificationInfinityZeroSchemeIso f b g).hom
          (modificationInfinityZeroSchemeIso_over C f b g) k
        ((gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
          (modificationInfinityModule f b g) (modificationInfinitySection f b g) k β) :=
  rfl

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The identification of the zero scheme presenting `W_∞ ×_X T` lies over `X`. -/
theorem modificationInfinityZeroSchemeIso_hom_comp_projection {T : Scheme.{u}} (t : T ⟶ X) :
    (modificationInfinityZeroSchemeIso f b t).hom ≫
        (pullback.fst (modificationProjectionAtInfinity f b) t ≫
          modificationProjectionAtInfinity f b) =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b t) (modificationInfinityModule f b t)
          (modificationInfinitySection f b t)).subschemeι ≫ (pullback.fst (modificationProjection f
              b) t ≫ modificationProjection f b) := by
  rw [← modificationInfinityZeroSchemeIso_hom_comp, Category.assoc,
    ← Category.assoc (modificationInfinityBaseChange f b t),
    modificationInfinityBaseChange_comp_fst]
  simp

/-- The right-hand side of the Gysin step of Stacks 0FAS: `c ∩ i_∞^* β`, computed by
condition (3) of Stacks 0B76 for `c`. -/
theorem commuteCapTransport_modificationInfinityGysin {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b t) (k + 1)) :
    commuteCapTransport C (gysinSystemOfInvertible C) f fY (modificationProjectionAtInfinity f b)
        p c t k (modificationInfinityGysin C f b t k β) =
      chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme (pullback fY (pullback.fst
          (modificationProjection f b) t ≫ modificationProjection f b))
          ((Scheme.Modules.pullback (pullback.snd fY (pullback.fst (modificationProjection f b) t ≫
              modificationProjection f b))).obj (modificationInfinityModule f b t))
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY (pullback.fst
              (modificationProjection f b) t ≫ modificationProjection f b))
            (modificationInfinityModule f b t) (modificationInfinitySection f b t))).subschemeι ≫
                (pullback.fst fY (pullback.fst (modificationProjection f b) t ≫
                    modificationProjection f b) ≫ (fY ≫ f)))
        (modificationInfinityBaseChangeOver f b (pullback.fst fY t ≫ fY))
        (((bivariantDivisorBaseChangeIso fY (pullback.fst (modificationProjection f b) t ≫
            modificationProjection f b)
          (modificationInfinityModule f b t) (modificationInfinitySection f b t)).inv ≫
        (testBaseChangeIso fY
          (pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationProjectionAtInfinity
              f b)
          (modificationInfinityZeroSchemeIso f b t).hom ((Stacks.Divisors.zeroScheme
              (modificationBaseChange f b t) (modificationInfinityModule f b t)
          (modificationInfinitySection f b t)).subschemeι ≫ (pullback.fst (modificationProjection f
              b) t ≫ modificationProjection f b))
          (modificationInfinityZeroSchemeIso_hom_comp_projection C f b t)).hom) ≫
        commuteComparisonHom fY (modificationProjectionAtInfinity f b) t)
        (by
          rw [Category.assoc, commuteComparisonHom_comp_structureMorphism, Category.assoc,
            testBaseChangeIso_hom_fst_assoc, bivariantDivisorBaseChangeIso_inv_fst_assoc]) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst fY (pullback.fst (modificationProjection f
            b) t ≫ modificationProjection f b) ≫ (fY ≫ f))
          ((Scheme.Modules.pullback (pullback.snd fY (pullback.fst (modificationProjection f b) t ≫
              modificationProjection f b))).obj (modificationInfinityModule f b t))
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY (pullback.fst
              (modificationProjection f b) t ≫ modificationProjection f b))
            (modificationInfinityModule f b t) (modificationInfinitySection f b t)) (k - p)
          (chowGroupDegreeEquiv C (pullback.fst fY (pullback.fst (modificationProjection f b) t ≫
              modificationProjection f b) ≫ (fY ≫ f))
            (by ring : k + 1 - p = k - p + 1)
            (c.cap (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b) (k +
                1)
              (chowGroupCongr C (Category.assoc (pullback.fst (modificationProjection f b) t)
                (modificationProjection f b) f).symm (k + 1) β)))) := by
  conv_lhs => rw [commuteCapTransport_apply C _ f fY (modificationProjectionAtInfinity f b),
    modificationInfinityGysin_apply C f b t,
    BivariantClass.cap_chowPushforwardOfIso_gysin c (pullback.fst (modificationProjection f b) t ≫
        modificationProjection f b)
    (modificationInfinityModule f b t) (modificationInfinitySection f b t)
    (pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationProjectionAtInfinity f b)
    (modificationInfinityZeroSchemeIso f b t).hom
    (modificationInfinityZeroSchemeIso_hom_comp_projection C f b t) (Category.assoc _ _ _).symm
    (Category.assoc _ _ _).symm (modificationInfinityZeroSchemeIso_over C f b t) k β,
    chowPushforwardOfIso_comp_apply]

/-- The left-hand side of the Gysin step of Stacks 0FAS: `i_∞^* (c ∩ β)`, computed by the
compatibility of the Gysin map with pushforward along the comparison isomorphism. -/
theorem modificationInfinityGysin_commuteCapTransport_eq {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b t) (k + 1)) :
    modificationInfinityGysin C f b (pullback.fst fY t ≫ fY) (k - p)
        (chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
          (by ring : k + 1 - p = k - p + 1)
          (commuteCapTransport C (gysinSystemOfInvertible C) f fY (modificationProjection f b) p
            c t (k + 1) β)) =
      chowPushforwardOfIso C ((Stacks.Divisors.zeroScheme (pullback fY (pullback.fst
          (modificationProjection f b) t ≫ modificationProjection f b))
          ((Scheme.Modules.pullback (pullback.snd fY (pullback.fst (modificationProjection f b) t ≫
              modificationProjection f b))).obj (modificationInfinityModule f b t))
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY (pullback.fst
              (modificationProjection f b) t ≫ modificationProjection f b))
            (modificationInfinityModule f b t) (modificationInfinitySection f b t))).subschemeι ≫
                (pullback.fst fY (pullback.fst (modificationProjection f b) t ≫
                    modificationProjection f b) ≫ (fY ≫ f)))
        (modificationInfinityBaseChangeOver f b (pullback.fst fY t ≫ fY))
        (((bivariantDivisorBaseChangeIso fY (pullback.fst (modificationProjection f b) t ≫
            modificationProjection f b)
          (modificationInfinityModule f b t) (modificationInfinitySection f b t)).inv ≫
        (testBaseChangeIso fY
          (pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationProjectionAtInfinity
              f b)
          (modificationInfinityZeroSchemeIso f b t).hom ((Stacks.Divisors.zeroScheme
              (modificationBaseChange f b t) (modificationInfinityModule f b t)
          (modificationInfinitySection f b t)).subschemeι ≫ (pullback.fst (modificationProjection f
              b) t ≫ modificationProjection f b))
          (modificationInfinityZeroSchemeIso_hom_comp_projection C f b t)).hom) ≫
        commuteComparisonHom fY (modificationProjectionAtInfinity f b) t)
        (by
          rw [Category.assoc, commuteComparisonHom_comp_structureMorphism, Category.assoc,
            testBaseChangeIso_hom_fst_assoc, bivariantDivisorBaseChangeIso_inv_fst_assoc]) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst fY (pullback.fst (modificationProjection f
            b) t ≫ modificationProjection f b) ≫ (fY ≫ f))
          ((Scheme.Modules.pullback (pullback.snd fY (pullback.fst (modificationProjection f b) t ≫
              modificationProjection f b))).obj (modificationInfinityModule f b t))
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY (pullback.fst
              (modificationProjection f b) t ≫ modificationProjection f b))
            (modificationInfinityModule f b t) (modificationInfinitySection f b t)) (k - p)
          (chowGroupDegreeEquiv C (pullback.fst fY (pullback.fst (modificationProjection f b) t ≫
              modificationProjection f b) ≫ (fY ≫ f))
            (by ring : k + 1 - p = k - p + 1)
            (c.cap (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b) (k +
                1)
              (chowGroupCongr C (Category.assoc (pullback.fst (modificationProjection f b) t)
                (modificationProjection f b) f).symm (k + 1) β)))) := by
  have := lineInfinityDivisor_isEffectiveCartierDivisor C.S
  have hur : commuteComparisonHom fY (modificationProjection f b) t ≫
      modificationBaseChangeToRelativeLine f b (pullback.fst fY t ≫ fY) =
      pullback.snd fY (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b) ≫
        modificationBaseChangeToRelativeLine f b t := by
    simp [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine]
  have hZ : (modificationInfinityZeroSchemeIso f b t).hom ≫
      pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationInclusionAtInfinity f b =
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b t) (modificationInfinityModule f b t)
        (modificationInfinitySection f b t)).subschemeι ≫
          pullback.fst (modificationProjection f b) t := by
    rw [← modificationInfinityZeroSchemeIso_hom_comp_assoc, modificationInfinityBaseChange_comp_fst]
  have key : (testBaseChangeIso fY
        (pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationProjectionAtInfinity f
            b)
        (modificationInfinityZeroSchemeIso f b t).hom
        ((Stacks.Divisors.zeroScheme (modificationBaseChange f b t) (modificationInfinityModule f b
            t)
          (modificationInfinitySection f b t)).subschemeι ≫
            pullback.fst (modificationProjection f b) t ≫ modificationProjection f b)
                (modificationInfinityZeroSchemeIso_hom_comp_projection C f b t)).hom ≫
      commuteComparisonHom fY (modificationProjectionAtInfinity f b) t ≫
        modificationInfinityBaseChange f b (pullback.fst fY t ≫ fY) =
      bivariantBaseChangeMap fY
        (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b)
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b t) (modificationInfinityModule f b
            t)
          (modificationInfinitySection f b t)).subschemeι ≫
        commuteComparisonHom fY (modificationProjection f b) t := by
    have hZ' : (modificationInfinityZeroSchemeIso f b t).hom ≫
        pullback.snd (modificationProjectionAtInfinity f b) t =
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b t) (modificationInfinityModule f b
            t)
          (modificationInfinitySection f b t)).subschemeι ≫
            pullback.snd (modificationProjection f b) t := by
      rw [← modificationInfinityZeroSchemeIso_hom_comp_assoc,
        modificationInfinityBaseChange_comp_snd]
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [bivariantBaseChangeMap]
      simp only [Category.assoc, modificationInfinityBaseChange_comp_fst,
        commuteComparisonHom_fst_assoc, testBaseChangeIso_hom_snd_assoc, commuteComparisonHom_fst,
        pullback.map_snd_assoc]
      rw [hZ]
    · simp [bivariantBaseChangeMap]
    · simp only [bivariantBaseChangeMap]
      simp only [Category.assoc, modificationInfinityBaseChange_comp_snd,
        commuteComparisonHom_snd_snd, testBaseChangeIso_hom_snd_assoc, pullback.map_snd_assoc]
      rw [hZ']
  have hMz : (((bivariantDivisorBaseChangeIso fY
        (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b)
        (modificationInfinityModule f b t) (modificationInfinitySection f b t)).inv ≫
      (testBaseChangeIso fY
        (pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationProjectionAtInfinity f
            b)
        (modificationInfinityZeroSchemeIso f b t).hom
        ((Stacks.Divisors.zeroScheme (modificationBaseChange f b t) (modificationInfinityModule f b
            t)
          (modificationInfinitySection f b t)).subschemeι ≫
            pullback.fst (modificationProjection f b) t ≫ modificationProjection f b)
        (modificationInfinityZeroSchemeIso_hom_comp_projection C f b t)).hom) ≫
      commuteComparisonHom fY (modificationProjectionAtInfinity f b) t) ≫
        inv (modificationInfinityZeroSchemeIso f b (pullback.fst fY t ≫ fY)).hom ≫
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b (pullback.fst fY t ≫ fY))
        (modificationInfinityModule f b (pullback.fst fY t ≫ fY))
        (modificationInfinitySection f b (pullback.fst fY t ≫ fY))).subschemeι =
      (Stacks.Divisors.zeroScheme
        (pullback fY (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b))
        ((Scheme.Modules.pullback (pullback.snd fY
          (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b))).obj
            (modificationInfinityModule f b t))
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY
          (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b))
          (modificationInfinityModule f b t) (modificationInfinitySection f b t))).subschemeι ≫
        commuteComparisonHom fY (modificationProjection f b) t := by
    have hZinv : inv (modificationInfinityZeroSchemeIso f b (pullback.fst fY t ≫ fY)).hom ≫
        (Stacks.Divisors.zeroScheme (modificationBaseChange f b (pullback.fst fY t ≫ fY))
          (modificationInfinityModule f b (pullback.fst fY t ≫ fY))
          (modificationInfinitySection f b (pullback.fst fY t ≫ fY))).subschemeι =
        modificationInfinityBaseChange f b (pullback.fst fY t ≫ fY) := by
      rw [IsIso.inv_comp_eq, modificationInfinityZeroSchemeIso_hom_comp]
    rw [hZinv]
    simp only [Category.assoc]
    rw [key, ← bivariantDivisorBaseChangeIso_hom_subschemeι, Category.assoc, Iso.inv_hom_id_assoc]
  conv_lhs => rw [commuteCapTransport_apply C _ f fY (modificationProjection f b),
    modificationInfinityGysin_apply C f b (pullback.fst fY t ≫ fY)]
  exact gysinSystemOfInvertible_onChow_chowPushforwardOfIso_comparison C
    (pullback.fst fY (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b) ≫
      fY ≫ f)
    (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
    (modificationInfinityBaseChangeOver f b (pullback.fst fY t ≫ fY))
    (pullback.snd fY (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b))
    (modificationBaseChangeToRelativeLine f b t)
    (modificationBaseChangeToRelativeLine f b (pullback.fst fY t ≫ fY))
    (commuteComparisonHom fY (modificationProjection f b) t)
    (commuteComparisonHom_comp_structureMorphism C f fY (modificationProjection f b) t) hur
    (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) _
    (modificationInfinityZeroSchemeIso f b (pullback.fst fY t ≫ fY)).hom
    (modificationInfinityZeroSchemeIso_over C f b (pullback.fst fY t ≫ fY)) _ _ hMz _

/-- **The Gysin map at infinity commutes with `c`**: `i_∞^*(c ∩ β) = c ∩ i_∞^* β`, both sides read
on `W_∞ ×_X (Y ×_X T)`. -/
theorem modificationInfinityGysin_commuteCapTransport {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ)
    (β : chowGroup C (modificationBaseChangeOver f b t) (k + 1)) :
    modificationInfinityGysin C f b (pullback.fst fY t ≫ fY) (k - p)
        (chowGroupDegreeEquiv C (modificationBaseChangeOver f b (pullback.fst fY t ≫ fY))
          (by ring : k + 1 - p = k - p + 1)
          (commuteCapTransport C (gysinSystemOfInvertible C) f fY (modificationProjection f b) p
            c t (k + 1) β)) =
      commuteCapTransport C (gysinSystemOfInvertible C) f fY (modificationProjectionAtInfinity f b)
        p c t k (modificationInfinityGysin C f b t k β) :=
  (modificationInfinityGysin_commuteCapTransport_eq C f b fY p c t k β).trans
    (commuteCapTransport_modificationInfinityGysin C f b fY p c t k β).symm

/-- **Stacks 0FAS for the class of Stacks 0F9J.** The canonical class `C ∈ A⁰(W_∞ ⟶ X)` of
`Stacks.Chow.gysinAtInfinityClass` commutes with every bivariant class `c ∈ A^p(Y ⟶ X)`. -/
theorem gysinAtInfinityClass_bivariantCommute :
    BivariantCommute C (gysinSystemOfInvertible C) f (modificationProjectionAtInfinity f b) fY 0 p
      (gysinAtInfinityClass C f b hA) c := by
  intro T t _ k α
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA t k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply, gysinAtInfinityClass_cap,
    gysinAtInfinityClass_cap,
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA _ _ _ _
      (hβ.commuteCapTransport C f b hA fY p c t k),
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA t k α β hβ,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso,
    modificationInfinityGysin_commuteCapTransport C f b fY p c t k β,
    chowPushforwardOfIso_commuteCapTransport, chowGroupCongr_chowGroupDegreeEquiv]
  exact c.cap_transport_eq (pullback.fst (modificationProjectionAtInfinity f b) t ≫
    modificationProjectionAtInfinity f b) (sub_zero k).symm (sub_zero (k - p)).symm (by ring) _

end AtInfinity

/-! ### Classes commuting with every bivariant class -/

section Central

variable {C : ChowSituation.{u}} {G : GysinSystem C}

/-- A bivariant class `c ∈ A^p(Z ⟶ X)` *commutes with every bivariant class* when, for every
`g : Y ⟶ X` locally of finite type and every `d ∈ A^q(Y ⟶ X)`, `c` and `d` commute in the sense of
Stacks 0FA2. The class is read with its source over the base through `f ≫ sX`, the form in which
`Stacks.Chow.BivariantCommute` compares classes. -/
def BivariantClass.CommutesWithEveryClass {Z X : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X}
    [LocallyOfFiniteType f] {hf : f ≫ sX = sZ} {p : ℤ} (c : BivariantClass C G sZ sX f hf p) :
    Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X) [LocallyOfFiniteType g] (q : ℤ)
    (d : BivariantClass C G (g ≫ sX) sX g rfl q),
    BivariantCommute C G sX f g p q
      (bivariantClassCongrBase C G f hf.symm rfl (hv := hf) (hv' := rfl) p c) d

variable {Z X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X}
  [LocallyOfFiniteType f] {p : ℤ}

/-- For a class whose source lies over the base through `f ≫ sX`, commuting with every class is
literally commuting with each of them. -/
theorem BivariantClass.commutesWithEveryClass_iff (c : BivariantClass C G (f ≫ sX) sX f rfl p) :
    c.CommutesWithEveryClass ↔
      ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X) [LocallyOfFiniteType g] (q : ℤ)
        (d : BivariantClass C G (g ≫ sX) sX g rfl q), BivariantCommute C G sX f g p q c d :=
  Iff.rfl

/-- Commuting with every class does not depend on the structure morphism of the source. -/
theorem BivariantClass.commutesWithEveryClass_congrBase {sZ sZ' : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sZ'] (e : sZ = sZ') {hf : f ≫ sX = sZ}
    {hf' : f ≫ sX = sZ'} (c : BivariantClass C G sZ sX f hf p) :
    (bivariantClassCongrBase C G f e rfl (hv := hf) (hv' := hf') p c).CommutesWithEveryClass ↔
      c.CommutesWithEveryClass := by
  subst e
  rfl

/-- Commuting with every class is invariant under reading a class for an equal morphism and in an
equal degree. -/
theorem BivariantClass.commutesWithEveryClass_copy {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ]
    {f' : Z ⟶ X} [LocallyOfFiniteType f'] (hff' : f = f') (hf : f ≫ sX = sZ)
    (hf' : f' ≫ sX = sZ) {p' : ℤ} (hpp' : p = p') (c : BivariantClass C G sZ sX f hf p) :
    (BivariantClass.copy C G sZ sX hff' hf hf' hpp' c).CommutesWithEveryClass ↔
      c.CommutesWithEveryClass := by
  subst hff' hpp'
  rfl

/-- **The smooth half of Stacks 0FF6, for every class at once.** A class characterized by the
rule of Stacks 0B78 (`Stacks.Chow.IsBivariantFlatPullback`) commutes with every bivariant class. -/
theorem commutesWithEveryClass_flatPullbackBivariantClass {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] [Flat f] (hf : f ≫ sX = sZ) (r : ℕ)
    (hfr : AlgebraicGeometry.RelativeDimension f r) (hS1 : FlatPullbackDescends C)
    (c : BivariantClass C G sZ sX f hf (-(r : ℤ)))
    (hc : IsBivariantFlatPullback C G sZ sX f hf r hfr hS1 c) :
    c.CommutesWithEveryClass := by
  subst hf
  intro Y g _ q d
  exact bivariantCommute_of_isBivariantFlatPullback C G sX f g r hfr hS1 q d c hc

/-- The flat-pullback class of an open immersion commutes with every bivariant class. -/
theorem commutesWithEveryClass_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] [IsOpenImmersion f] (hf : f ≫ sX = sZ) :
    (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sZ sX f hf).CommutesWithEveryClass :=
        by
  have h : flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C sZ sX f hf =
      flatPullbackBivariantClassOfInvertible C sZ sX f hf 0
        (relativeDimension_of_isOpenImmersion f) :=
    BivariantClass.ext _ _ _ _ _ _ _ fun _ _ _ _ ↦ rfl
  rw [h]
  exact commutesWithEveryClass_flatPullbackBivariantClass hf 0 _ (flatPullbackDescends C) _
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sZ sX f hf 0
      (relativeDimension_of_isOpenImmersion f))

/-- The cap operation of the proper pushforward of Stacks 0EPK does not depend on the structure
morphism of the source of the pushed class. -/
theorem bivariantProperPushforwardCap_congrBase {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    (h : A ⟶ B) [IsProper h] (g : B ⟶ X) [LocallyOfFiniteType g] [LocallyOfFiniteType (h ≫ g)]
    (hh : h ≫ sB = sA) (hh' : h ≫ sB = sA') (hg : g ≫ sX = sB) (e : sA = sA')
    (hpp : ProperPushforwardDescends C)
    (c : BivariantClass C G sA sX (h ≫ g) (comp_comp_structureMorphism_eq hh hg) p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    bivariantProperPushforwardCap C G sA sB sX h g hh hg hpp p c t k α =
      bivariantProperPushforwardCap C G sA' sB sX h g hh' hg hpp p
        (bivariantClassCongrBase C G (h ≫ g) e rfl p c) t k α := by
  subst e
  rfl

/-- **The proper-pushforward step of Stacks 0FBX, for every class at once.** The proper
pushforward `h_* ∘ c` of Stacks 0EPK of a class commuting with every bivariant class commutes with
every bivariant class. -/
theorem commutesWithEveryClass_bivariantProperPushforward {A B : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB] (h : A ⟶ B) [IsProper h]
    (g : B ⟶ X) [LocallyOfFiniteType g] [LocallyOfFiniteType (h ≫ g)] (hh : h ≫ sB = sA)
    (hg : g ≫ sX = sB)
    (c : BivariantClass C (gysinSystemOfInvertible C) sA sX (h ≫ g)
      (comp_comp_structureMorphism_eq hh hg) p)
    (hc : c.CommutesWithEveryClass) :
    (bivariantProperPushforwardOfInvertible C sA sB sX h g hh hg p c).CommutesWithEveryClass := by
  subst hg hh
  intro Y g₂ _ q d
  refine bivariantCommute_of_isBivariantProperPushforward C (gysinSystemOfInvertible C) sX g h g₂
    (properPushforwardDescends C) p q
    (bivariantClassCongrBase C (gysinSystemOfInvertible C) (h ≫ g) (Category.assoc h g sX).symm
      rfl p c) d _ ?_ (hc g₂ q d)
  intro T t _ k α
  exact bivariantProperPushforwardCap_congrBase h g rfl _ rfl _ _ c t k α

/-- **A composite of classes commuting with every class commutes with every class.** If
`a ∈ A^{q₁}(W ⟶ U)` commutes with every bivariant class over `U` and `b ∈ A^{q₂}(U ⟶ X)` commutes
with every bivariant class over `X`, then so does `a ∘ b` (Stacks 0B75). -/
theorem commutesWithEveryClass_bivariantCompositeOfInvertible {W U : Scheme.{u}}
    {sW : W ⟶ C.S} [LocallyOfFiniteType sW] (j : W ⟶ U) [LocallyOfFiniteType j] (i : U ⟶ X)
    [LocallyOfFiniteType i] [LocallyOfFiniteType (j ≫ i)] (hj : j ≫ (i ≫ sX) = sW) (q₁ q₂ : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sW (i ≫ sX) j hj q₁)
    (b : BivariantClass C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl q₂)
    (ha : a.CommutesWithEveryClass) (hb : b.CommutesWithEveryClass) :
    (bivariantCompositeOfInvertible C sW (i ≫ sX) sX j i hj rfl q₁ q₂ a b).CommutesWithEveryClass :=
        by
  subst hj
  intro Y g _ q d
  exact bivariantCommute_bivariantCompositeOfInvertible C sX j i q₁ q₂ a b
    (fun f₂' _ p₂' c₂' ↦ ha f₂' p₂' c₂') (fun f₂ _ p₂ c₂ ↦ hb f₂ p₂ c₂) g q d rfl

end Central

/-! ### Cancelling a factor with injective cap operations -/

section Cancellation

variable {C : ChowSituation.{u}} {W U X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- Pushforward along an isomorphism is injective, up to heterogeneous equality of degrees. -/
theorem heq_of_chowPushforwardOfIso_heq {A B : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB] (v : A ⟶ B) [IsIso v]
    (hv : v ≫ sB = sA) {k l : ℤ} (hkl : k = l) {x : chowGroup C sA k} {y : chowGroup C sA l}
    (h : chowPushforwardOfIso C sA sB v hv k x ≍ chowPushforwardOfIso C sA sB v hv l y) :
    x ≍ y := by
  subst hkl
  exact heq_of_eq (chowPushforwardOfIso_injective C sA sB v hv k (eq_of_heq h))

/-- Two classes whose pushforwards along equal isomorphisms are heterogeneously equal are
heterogeneously equal. -/
theorem heq_of_chowPushforwardOfIso_heq_of_eq {A D : Scheme.{u}} {sA : A ⟶ C.S}
    [LocallyOfFiniteType sA] {sD sD' : D ⟶ C.S} [LocallyOfFiniteType sD]
    [LocallyOfFiniteType sD'] (φ φ' : A ⟶ D) [IsIso φ] [IsIso φ'] (hφφ' : φ = φ')
    (hφ : φ ≫ sD = sA) (hφ' : φ' ≫ sD' = sA) (hD : sD = sD') {k l : ℤ} (hkl : k = l)
    {x : chowGroup C sA k} {y : chowGroup C sA l}
    (h : chowPushforwardOfIso C sA sD φ hφ k x ≍ chowPushforwardOfIso C sA sD' φ' hφ' l y) :
    x ≍ y := by
  subst hφφ' hD
  exact heq_of_chowPushforwardOfIso_heq φ hφ hkl h

/-- **Cancelling a class with injective cap operations.** Let `a ∈ A^{q₁}(W ⟶ U)` have injective
cap operations and commute with the restriction of `c₂ ∈ A^{p₂}(Z₂ ⟶ X)` to `U`, and let
`b ∈ A^{q₂}(U ⟶ X)`. If the composite `a ∘ b` commutes with `c₂`, then so does `b`. -/
theorem bivariantCommute_of_bivariantCompositeOfInvertible
    (j : W ⟶ U) [LocallyOfFiniteType j] (i : U ⟶ X) [LocallyOfFiniteType i]
    [LocallyOfFiniteType (j ≫ i)] (q₁ q₂ : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) (j ≫ (i ≫ sX)) (i ≫ sX) j rfl q₁)
    (b : BivariantClass C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl q₂)
    (hinj : a.CapInjective) {Y : Scheme.{u}} (f₂ : Y ⟶ X) [LocallyOfFiniteType f₂] (p₂ : ℤ)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl p₂)
    (ha : BivariantCommute C (gysinSystemOfInvertible C) (i ≫ sX) j (pullback.snd f₂ i) q₁ p₂ a
      (bivariantClassCongrBase C _ (pullback.snd f₂ i)
        (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl i).symm rfl p₂
        (bivariantRestriction C _ (f₂ ≫ sX) sX f₂ rfl i p₂
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₂)))
    (hab : BivariantCommute C (gysinSystemOfInvertible C) sX (j ≫ i) f₂ (q₁ + q₂) p₂
      (bivariantClassCongrBase C _ (j ≫ i) (Category.assoc j i sX).symm rfl (hv' := rfl)
        (q₁ + q₂)
        (bivariantCompositeOfInvertible C (j ≫ (i ≫ sX)) (i ≫ sX) sX j i rfl rfl q₁ q₂ a b))
      c₂) :
    BivariantCommute C (gysinSystemOfInvertible C) sX i f₂ q₂ p₂ b c₂ := by
  set c₁ := bivariantClassCongrBase C (gysinSystemOfInvertible C) (j ≫ i)
    (Category.assoc j i sX).symm rfl (hv' := rfl) (q₁ + q₂)
    (bivariantCompositeOfInvertible C (j ≫ (i ≫ sX)) (i ≫ sX) sX j i rfl rfl q₁ q₂ a b) with hc₁
  set c₂' := bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd f₂ i)
    (pullbackSnd_comp_structureMorphism_eq C (f₂ ≫ sX) sX f₂ rfl i).symm rfl p₂
    (bivariantRestriction C _ (f₂ ≫ sX) sX f₂ rfl i p₂
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c₂) with hc₂'
  have h₁ : ∀ {S : Scheme.{u}} (s : S ⟶ X) [LocallyOfFiniteType s] (k' : ℤ)
      (ε : chowGroup C (s ≫ sX) k'),
      c₁.cap s k' ε ≍ chowPushforwardOfIso C (pullback.fst j (pullback.fst i s) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst (j ≫ i) s ≫ (j ≫ (i ≫ sX))) (pullbackRightPullbackFstIso i s j).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp _ j i s) ((k' - q₂) - q₁)
        (a.cap (pullback.fst i s) (k' - q₂) (b.cap s k' ε)) := by
    intro S s _ k' ε
    exact (bivariantClassCongrBase_cap C _ (j ≫ i) _ rfl (q₁ + q₂) _ s k' ε ε HEq.rfl).trans
      (chowGroupDegreeEquiv_heq C _ _ _)
  have h₂ : ∀ {V : Scheme.{u}} (v : V ⟶ U) [LocallyOfFiniteType v] (k' : ℤ)
      (δ : chowGroup C (v ≫ (i ≫ sX)) k'),
      c₂'.cap v k' δ ≍ chowPushforwardOfIso C (pullback.fst f₂ (v ≫ i) ≫ (f₂ ≫ sX))
        (pullback.fst (pullback.snd f₂ i) v ≫ (pullback.fst f₂ i ≫ (f₂ ≫ sX)))
        (pullbackLeftPullbackSndIso f₂ i v).inv (by simp) (k' - p₂)
        (c₂.cap (v ≫ i) k' (chowGroupCongr C (Category.assoc v i sX).symm k' δ)) := by
    intro V v _ k' δ
    exact bivariantClassCongrBase_cap C _ (pullback.snd f₂ i) _ rfl p₂ _ v k' δ δ HEq.rfl
  intro T t _ k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply]
  have hAB := hab t k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply] at hAB
  have hL : chowPushforwardOfIso C
        (pullback.fst (j ≫ i) (pullback.fst f₂ t ≫ f₂) ≫ ((j ≫ i) ≫ sX))
        (pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX))
        (commuteComparisonHom (j ≫ i) f₂ t)
        (commuteComparisonHom_comp_structureMorphism C sX (j ≫ i) f₂ t) ((k - p₂) - (q₁ + q₂))
        (c₁.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
          (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
            (c₂.cap t k α))) ≍
      chowPushforwardOfIso C
        (pullback.fst j (pullback.fst i (pullback.fst f₂ t ≫ f₂)) ≫ (j ≫ (i ≫ sX)))
        (pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX))
        ((pullbackRightPullbackFstIso i (pullback.fst f₂ t ≫ f₂) j).hom ≫
          commuteComparisonHom (j ≫ i) f₂ t) (by
            rw [Category.assoc, commuteComparisonHom_comp_structureMorphism]; simp)
        ((k - p₂ - q₂) - q₁)
        (a.cap (pullback.fst i (pullback.fst f₂ t ≫ f₂)) (k - p₂ - q₂)
          (b.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
            (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂)
              (c₂.cap t k α)))) := by
    refine HEq.trans (chowPushforwardOfIso_heq _ _
      (commuteComparisonHom_comp_structureMorphism C sX (j ≫ i) f₂ t) (by simp) rfl (by ring)
      (h₁ _ _ _)) (heq_of_eq ?_)
    exact chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ _
  have hR : c₂.cap (pullback.fst (j ≫ i) t ≫ (j ≫ i)) (k - (q₁ + q₂))
        (chowGroupCongr C (Category.assoc (pullback.fst (j ≫ i) t) (j ≫ i) sX).symm
          (k - (q₁ + q₂)) (c₁.cap t k α)) ≍
      chowPushforwardOfIso C
        (pullback.fst f₂ ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) ≫ (f₂ ≫ sX))
        (pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX))
        (testBaseChangeIso f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i))
          (pullbackRightPullbackFstIso i t j).hom
          ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (by simp)).hom (by simp)
        ((k - q₂ - q₁) - p₂)
        (c₂.cap ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (k - q₂ - q₁)
          (chowGroupCongr C (by simp) (k - q₂ - q₁)
            (a.cap (pullback.fst i t) (k - q₂) (b.cap t k α)))) := by
    have hmb : (pullbackRightPullbackFstIso i t j).hom ≫
        ((pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ sX) =
        pullback.fst j (pullback.fst i t) ≫ (j ≫ (i ≫ sX)) := by simp
    refine HEq.trans (BivariantClass.cap_heq c₂ _ (by ring)
      (y := chowPushforwardOfIso C _ _ (pullbackRightPullbackFstIso i t j).hom hmb (k - q₂ - q₁)
        (a.cap (pullback.fst i t) (k - q₂) (b.cap t k α))) ?_) (heq_of_eq ?_)
    · refine (chowGroupCongr_heq C _ _ _).trans ((h₁ t k α).trans ?_)
      exact chowPushforwardOfIso_heq _ _ _ rfl (by simp) rfl HEq.rfl
    · exact BivariantClass.cap_chowPushforwardOfIso c₂ _ _ _ (by simp) _ (by simp) _ hmb _ _ rfl
  have hA := ha (pullback.fst i t) (k - q₂) (b.cap t k α)
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply] at hA
  have hm : (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv ≫
      (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i) =
      commuteComparisonHom f₂ i t ≫ pullback.fst i (pullback.fst f₂ t ≫ f₂) := by
    simp
  have hqm : pullback.fst f₂ (pullback.fst i t ≫ i) ≫ (f₂ ≫ sX) =
      (commuteComparisonHom f₂ i t ≫ pullback.fst i (pullback.fst f₂ t ≫ f₂)) ≫ (i ≫ sX) := by
    rw [Category.assoc, commuteComparisonHom_comp_structureMorphism]
  have hmb : (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv ≫
      ((pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i) ≫ (i ≫ sX)) =
      pullback.fst f₂ (pullback.fst i t ≫ i) ≫ (f₂ ≫ sX) := by
    rw [← Category.assoc, hm, hqm]
  have hargL : chowGroupCongr C (Category.assoc (pullback.fst (pullback.snd f₂ i)
        (pullback.fst i t)) (pullback.snd f₂ i) (i ≫ sX)).symm (k - q₂ - p₂)
        (c₂'.cap (pullback.fst i t) (k - q₂) (b.cap t k α)) =
      chowPushforwardOfIso C (pullback.fst f₂ (pullback.fst i t ≫ i) ≫ (f₂ ≫ sX)) _
        (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv hmb (k - q₂ - p₂)
        (c₂.cap (pullback.fst i t ≫ i) (k - q₂)
          (chowGroupCongr C (Category.assoc (pullback.fst i t) i sX).symm (k - q₂)
            (b.cap t k α))) :=
    eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ((h₂ (pullback.fst i t) (k - q₂)
      (b.cap t k α)).trans (chowPushforwardOfIso_heq _ _ _ rfl
        (by simp [pullback.condition_assoc]) rfl HEq.rfl)))
  set R' := chowPushforwardOfIso C (pullback.fst f₂ (pullback.fst i t ≫ i) ≫ (f₂ ≫ sX))
    (pullback.fst i (pullback.fst f₂ t ≫ f₂) ≫ (i ≫ sX)) (commuteComparisonHom f₂ i t)
    (commuteComparisonHom_comp_structureMorphism C sX f₂ i t) (k - q₂ - p₂)
    (c₂.cap (pullback.fst i t ≫ i) (k - q₂)
      (chowGroupCongr C (Category.assoc (pullback.fst i t) i sX).symm (k - q₂)
        (b.cap t k α))) with hR'
  have hm₁ : (commuteComparisonHom i f₂ t ≫
      (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv) ≫
      (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i) =
      pullback.fst i (pullback.fst f₂ t ≫ f₂) := by
    simp
  have hmb₁ : (commuteComparisonHom i f₂ t ≫
      (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv) ≫
      ((pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i) ≫ (i ≫ sX)) =
      pullback.fst i (pullback.fst f₂ t ≫ f₂) ≫ (i ≫ sX) := by
    rw [← Category.assoc, hm₁]
  have hpushR : chowPushforwardOfIso C (pullback.fst f₂ (pullback.fst i t ≫ i) ≫ (f₂ ≫ sX)) _
        (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv hmb (k - q₂ - p₂)
        (c₂.cap (pullback.fst i t ≫ i) (k - q₂)
          (chowGroupCongr C (Category.assoc (pullback.fst i t) i sX).symm (k - q₂)
            (b.cap t k α))) =
      chowPushforwardOfIso C (pullback.fst i (pullback.fst f₂ t ≫ f₂) ≫ (i ≫ sX)) _
        (commuteComparisonHom i f₂ t ≫ (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv)
        hmb₁ (k - q₂ - p₂) R' := by
    rw [hR', chowPushforwardOfIso_comp_apply]
    exact chowPushforwardOfIso_congr_apply C _ _ _ _
      (by rw [← Category.assoc, commuteComparisonHom_comp_commuteComparisonHom,
        Category.id_comp]) _ _ _ _
  have hcapL := BivariantClass.cap_chowPushforwardOfIso a
    (pullback.fst (pullback.snd f₂ i) (pullback.fst i t) ≫ pullback.snd f₂ i)
    (commuteComparisonHom i f₂ t ≫ (pullbackLeftPullbackSndIso f₂ i (pullback.fst i t)).inv)
    (pullback.fst i (pullback.fst f₂ t ≫ f₂)) hm₁ _ rfl (k - q₂ - p₂) hmb₁ R' R' rfl
  rw [hargL, hpushR, hcapL, chowPushforwardOfIso_comp_apply] at hA
  have hB5 := h₂ (pullback.fst j (pullback.fst i t) ≫ j) (k - q₂ - q₁)
    (chowGroupCongr C (Category.assoc (pullback.fst j (pullback.fst i t)) j (i ≫ sX)).symm
      (k - q₂ - q₁) (a.cap (pullback.fst i t) (k - q₂) (b.cap t k α)))
  have hQ := chowPushforwardOfIso_comp_heq
    (sE := pullback.fst f₂ ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) ≫ (f₂ ≫ sX)) _
    (pullbackLeftPullbackSndIso f₂ i (pullback.fst j (pullback.fst i t) ≫ j)).hom _ (by simp)
    (by simp [pullback.condition_assoc]) (by ring) _ _
    (hB5.symm.trans ((chowGroupDegreeEquiv_heq C _ _ _).symm.trans (heq_of_eq hA.symm)))
  rw [chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _) (Iso.inv_hom_id _) _ (Category.id_comp _),
    chowPushforwardOfIso_id] at hQ
  have hQQ : c₂.cap ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (k - q₂ - q₁)
        (chowGroupCongr C (by simp) (k - q₂ - q₁)
          (a.cap (pullback.fst i t) (k - q₂) (b.cap t k α))) ≍
      c₂.cap ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (k - q₂ - q₁)
        (chowGroupCongr C (Category.assoc (pullback.fst j (pullback.fst i t) ≫ j) i sX).symm
          (k - q₂ - q₁)
          (chowGroupCongr C (Category.assoc (pullback.fst j (pullback.fst i t)) j (i ≫ sX)).symm
            (k - q₂ - q₁) (a.cap (pullback.fst i t) (k - q₂) (b.cap t k α)))) :=
    BivariantClass.cap_heq c₂ _ rfl ((chowGroupCongr_heq C _ _ _).trans
      ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _)).symm)
  have hQ' := chowPushforwardOfIso_comp_heq
    (sE := pullback.fst f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i)) ≫ (f₂ ≫ sX)) _
    (testBaseChangeIso f₂ (pullback.fst (j ≫ i) t ≫ (j ≫ i))
      (pullbackRightPullbackFstIso i t j).hom
      ((pullback.fst j (pullback.fst i t) ≫ j) ≫ i) (by simp)).hom _ (by simp) rfl (by ring) _ _
    (hQQ.trans hQ)
  have hmain := hL.symm.trans ((heq_of_eq hAB).trans ((chowGroupDegreeEquiv_heq C _ _ _).trans
    (hR.trans hQ')))
  have hcap := heq_of_chowPushforwardOfIso_heq_of_eq _ _
    (by refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp) _ _ rfl (by ring) hmain
  have hLR := hinj (pullback.fst i (pullback.fst f₂ t ≫ f₂)) (k - p₂ - q₂)
    (a₁ := b.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
      (chowGroupCongr C (Category.assoc (pullback.fst f₂ t) f₂ sX).symm (k - p₂) (c₂.cap t k α)))
    (a₂ := chowGroupDegreeEquiv C _ (by ring) R')
    (eq_of_heq (hcap.trans (BivariantClass.cap_heq a _ (by ring)
      (chowGroupDegreeEquiv_heq C _ _ _).symm)))
  rw [hLR, hR', chowGroupDegreeEquiv_chowPushforwardOfIso, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 _)
      (commuteComparisonHom_comp_commuteComparisonHom f₂ i t) _ (Category.id_comp _),
    chowPushforwardOfIso_id]

/-- **Cancelling a class with injective cap operations, for every class at once.** If
`a ∈ A^{q₁}(W ⟶ U)` has injective cap operations and commutes with every bivariant class over
`U`, and `a ∘ b` commutes with every bivariant class over `X`, then so does `b ∈ A^{q₂}(U ⟶ X)`. -/
theorem commutesWithEveryClass_of_bivariantCompositeOfInvertible {sW : W ⟶ C.S}
    [LocallyOfFiniteType sW] (j : W ⟶ U) [LocallyOfFiniteType j] (i : U ⟶ X)
    [LocallyOfFiniteType i] [LocallyOfFiniteType (j ≫ i)] (hj : j ≫ (i ≫ sX) = sW) (q₁ q₂ : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sW (i ≫ sX) j hj q₁)
    (b : BivariantClass C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl q₂)
    (ha : a.CommutesWithEveryClass) (hinj : a.CapInjective)
    (hab : (bivariantCompositeOfInvertible C sW (i ≫ sX) sX j i hj rfl q₁ q₂ a
      b).CommutesWithEveryClass) :
    b.CommutesWithEveryClass := by
  subst hj
  intro Y f₂ _ p₂ c₂
  exact bivariantCommute_of_bivariantCompositeOfInvertible j i q₁ q₂ a b hinj f₂ p₂ c₂
    (ha _ _ _) (hab f₂ p₂ c₂)

end Cancellation

/-! ### Stacks 0FBP -/

section VirtualNormalCone

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ)

/-- **The class `ι_* ∘ j^* ∘ C` of Stacks 0FBK commutes with every bivariant class.** -/
theorem virtualNormalConeClass_commutesWithEveryClass (𝒩 : VirtualNormalBundle i) :
    (virtualNormalConeClass C sZ sX i hi 𝒩).CommutesWithEveryClass := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  refine commutesWithEveryClass_bivariantProperPushforward _ _ _ _ _ ?_
  refine (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2 ?_
  exact commutesWithEveryClass_bivariantCompositeOfInvertible _ _ _ _ _ _ _
    (commutesWithEveryClass_flatPullbackBivariantClassOfIsOpenImmersionOfInvertible _)
    (fun _ g _ q d ↦ gysinAtInfinityClass_bivariantCommute C sX
      (blowupAtInfinityToProjectiveLineProduct i.ker sX)
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) g q d)

variable (r : ℕ)

/-- The Gysin class `c(Z ⟶ X, 𝒩)` of a virtual normal bundle of constant rank commutes with every
bivariant class. -/
theorem virtualNormalBundleClass_commutesWithEveryClass (𝒩 : VirtualNormalBundle i)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).CommutesWithEveryClass := by
  subst hi
  have := 𝒩.flat_projection_of_rank r
  refine commutesWithEveryClass_of_bivariantCompositeOfInvertible 𝒩.projection i rfl (-(r : ℤ)) r
    (𝒩.projectionPullbackClass C (i ≫ sX) i r) _
    (commutesWithEveryClass_flatPullbackBivariantClass rfl r _ (flatPullbackDescends C) _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (𝒩.projection ≫ (i ≫ sX))
        (i ≫ sX) 𝒩.projection rfl r (𝒩.relativeDimension_projection_of_rank r)))
    (BivariantClass.CapBijective.capInjective
      (𝒩.capBijective_projectionPullbackClass C (i ≫ sX) i r)) ?_
  rw [projectionPullbackClass_comp_virtualNormalBundleClass]
  exact (BivariantClass.commutesWithEveryClass_copy _ _ _ _ _).2
    (virtualNormalConeClass_commutesWithEveryClass C (i ≫ sX) sX i rfl 𝒩)

/-- **Stacks 0FBP at constant rank.** Let `X` be locally of finite type over `S`, let `Z ⊆ X` be a
closed subscheme with virtual normal sheaf `𝒩` of constant rank `r`, let `g : Y ⟶ X` be locally of
finite type and let `c ∈ A^p(Y ⟶ X)`. Then `c(Z ⟶ X, 𝒩)` and `c` commute in the sense of
Stacks 0FA2. -/
theorem virtualNormalBundleClass_bivariantCommute (𝒩 : VirtualNormalBundle i)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) sX g rfl p) :
    BivariantCommute C (gysinSystemOfInvertible C) sX i g (r : ℤ) p
      (virtualNormalBundleClass C (i ≫ sX) sX i rfl 𝒩 r) c :=
  virtualNormalBundleClass_commutesWithEveryClass C (i ≫ sX) sX i rfl r 𝒩 g p c

end VirtualNormalCone

end Stacks.Chow

end
