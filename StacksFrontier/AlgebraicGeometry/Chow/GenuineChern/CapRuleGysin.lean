module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.GysinChernTerms
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass

/-!
# The Chern class cap products commute with Gysin pullback

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℰ` be finite locally free of rank `r` on `X` and let
`(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8. Then

  `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`,  `0 ≤ j ≤ r`,  `α ∈ A_{k+1}(X)`,

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6] and the Gysin map
of [Stacks, Tag 02TO]. This is [Stacks, Tag 0B7G].

## The argument

It is the source's. Let `π : P = 𝐏(ℰ) ⟶ X` be the projective bundle. The zero scheme
`P_D = Z(π^*s)` of the pulled-back section, with the morphism `π_D : P_D ⟶ D` of Remark 0B6Y,
satisfies the projective-bundle relation for the Gysin pullback of the family `c_j(ℰ) ∩ α`
(`Stacks.Chow.gysin_isChernCapFamily`, with the compatibility of the summands
`Stacks.Chow.GenuineChern.chernTermsCompatibleWithGysin_of_invertible`, from Stacks 0B71 and
0B72). The projective bundle of `ℰ|_D` is the base change of `P` along `i`
(`Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), which is `P_D` by Remark 0B6Y
(`Stacks.Divisors.zeroScheme_pullback`); so the isomorphism `φ : 𝐏(ℰ|_D) ≅ P_D` over `D` carries
the relation over `P_D` to the relation over `𝐏(ℰ|_D)` (flat pullback along `φ`,
`Stacks.Chow.isChernCapFamily_flatPullback`), and the uniqueness half of Stacks 02TX on
`𝐏(ℰ|_D)` identifies the Gysin pullback of the family with the family of `i^*α`.

## Main results

* `Stacks.Chow.GenuineChern.bundleChernCapFamily_gysin` — the rank `n + 1` case, on families.
* `Stacks.Chow.GenuineChern.chernCap_gysin` — **Stacks 0B7G** for the cap products of every rank,
  for a module identified with the restriction of `ℰ`.
* `Stacks.Chow.GenuineChern.chernCap_gysinNaturality` — the same, as the Gysin identity
  `Stacks.Chow.IdentityCapRule.GysinNaturality` of the identity cap rule of the bivariant Chern
  class at the Gysin system `Stacks.Chow.gysinSystemOfInvertible`, which is axiom (3) of
  Stacks 0B76 read on the test schemes.

## References

* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 0B7G for the cap products of Stacks 02U6, rank `n + 1`, on families.** For `ℰ` of
rank `n + 1` on `Y`, the zero scheme `i : D ⟶ Y` of a section `s` of an invertible module and
`ℰ' ≅ i^*ℰ`, the family of `i^*α` for `ℰ'` is the Gysin pullback of the family of `α` for
`ℰ`. -/
theorem bundleChernCapFamily_gysin (E : Y.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (E' : (Stacks.Divisors.zeroScheme Y L s).subscheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    (eE : E' ≅ (Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y L s).subschemeι).obj E)
    (k : ℤ) (α : chowGroup C sY (k + 1)) :
    bundleChernCapFamily E' n C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) k
        (gysinChowOfInvertible C sY k L s α) =
      gysinChernFamily C sY L s (n + 1) (fun m ↦ gysinOfInvertibleDescends C sY L s m) k
        (bundleChernCapFamily E n C sY (k + 1) α) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
    (n + 1)
  let := Stacks.Chow.flat_bundleProj E n
  let := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  let := Stacks.Chow.flat_bundleProj E' n
  let := Stacks.Chow.locallyOfFiniteType_bundleProj E' n
  set π := bundleProj E with hπdef
  set Z := pullbackZeroScheme π L s with hZ
  set πD := zeroSchemePullbackHom π L s with hπD
  obtain ⟨e, he, ⟨eT⟩⟩ :=
    bundleBaseChangeHolds (Stacks.Divisors.zeroScheme Y L s).subschemeι E E' eE
  -- the isomorphism `φ : 𝐏(ℰ') ≅ Z(π^*s)` over `D`
  have hZc : Z = (Stacks.Divisors.zeroScheme Y L s).comap π :=
    Stacks.Divisors.zeroScheme_pullback π L s
  set φ : bundle E' ⟶ Z.subscheme :=
    e.hom ≫ (pullbackSymmetry (Stacks.Divisors.zeroScheme Y L s).subschemeι π).hom ≫
      ((Stacks.Divisors.zeroScheme Y L s).comapIso π).inv ≫
        eqToHom (congrArg Scheme.IdealSheafData.subscheme hZc.symm) with hφdef
  have hφι : φ ≫ Z.subschemeι =
      e.hom ≫ pullback.snd (Stacks.Divisors.zeroScheme Y L s).subschemeι π := by
    rw [hφdef, Category.assoc, Category.assoc, Category.assoc,
      Stacks.Chow.subschemeι_eqToHom hZc.symm, Scheme.IdealSheafData.comapIso_inv_subschemeι,
      pullbackSymmetry_hom_comp_fst]
  have hφπ : φ ≫ πD = bundleProj E' := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme Y L s).subschemeι).1 ?_
    rw [Category.assoc, hπD, zeroSchemePullbackHom_subschemeι, ← Category.assoc, hφι,
      Category.assoc, ← pullback.condition, ← Category.assoc, he]
  have : IsIso φ := by rw [hφdef]; infer_instance
  have hd' : AlgebraicGeometry.RelativeDimension φ 0 := relativeDimension_of_isIso φ
  have hf' : φ ≫ (Z.subschemeι ≫ π ≫ sY) =
      bundleProj E' ≫ (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY := by
    rw [← Category.assoc, hφι, Category.assoc, ← pullback.condition_assoc, ← Category.assoc, he]
  have hsPD : πD ≫ ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) = Z.subschemeι ≫ π ≫ sY :=
    zeroSchemePullbackHom_comp π L s C sY (π ≫ sY) rfl
  have hπD' : AlgebraicGeometry.RelativeDimension πD (n + 1 - 1) :=
    relativeDimension_zeroSchemePullbackHom π L s (n + 1 - 1)
      (Stacks.Chow.relativeDimension_bundleProj E n)
  -- the twist of `𝐏(ℰ')` is the pullback along `φ` of the restricted twist
  have eL : bundleTwist E' ≅ (Scheme.Modules.pullback φ).obj
      ((Scheme.Modules.pullback Z.subschemeι).obj (bundleTwist E)) :=
    eT.symm ≪≫ (Scheme.Modules.pullbackCongr hφι.symm).app (bundleTwist E) ≪≫
      ((Scheme.Modules.pullbackComp φ Z.subschemeι).app (bundleTwist E)).symm
  set OZ := invertibleChernCapOperator C (Z.subschemeι ≫ π ≫ sY)
    ((Scheme.Modules.pullback Z.subschemeι).obj (bundleTwist E)) (fun k ↦
      firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k _ _)
    with hOZ
  -- the Gysin pullback of the family satisfies the relation over `Z(π^*s)`
  have hfam := gysin_isChernCapFamily C sY (π ≫ sY) π rfl L s ((Scheme.Modules.pullback π).obj L)
    (AlgebraicGeometry.pullbackGlobalSections π L s) πD hsPD (n + 1)
    (Stacks.Chow.relativeDimension_bundleProj E n) hπD'
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (bundleTwistCap E C sY) OZ (fun m ↦ gysinOfInvertibleDescends C sY L s m)
    (fun m ↦ gysinOfInvertibleDescends C (π ≫ sY) _ _ m)
    (chernTermsCompatibleWithGysin_of_invertible C sY π L s n
      (Stacks.Chow.relativeDimension_bundleProj E n) (bundleTwist E)) k α
    (bundleChernCapFamily E n C sY (k + 1) α) (isChernCapFamily_bundleChernCapFamily E n C sY
      (k + 1) α)
  -- the compatibility of the summands with flat pullback along `φ`
  have hcompat := chernTermsCompatibleWithFlatPullback_of_square C
    ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
    ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
    (bundleProj E' ≫ (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) (Z.subschemeι ≫ π ≫ sY)
    (bundleProj E') rfl πD hsPD (n + 1) (Stacks.Chow.relativeDimension_bundleProj E' n) hπD'
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (bundleTwistCap E' C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)) OZ
    (𝟙 (Stacks.Divisors.zeroScheme Y L s).subscheme) (Category.id_comp _) 0
    (relativeDimension_identity (Stacks.Divisors.zeroScheme Y L s).subscheme)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _) φ hf' hd'
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (by rw [hφπ, Category.comp_id])
    (fun j y y' hy ↦ flatPullbackChow_firstChernClassCapChow_heq C
      (bundleProj E' ≫ (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) (Z.subschemeι ≫ π ≫ sY)
      φ hf' 0 hd'
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
      ((Scheme.Modules.pullback Z.subschemeι).obj (bundleTwist E)) (bundleTwist E') eL j y y' hy)
  have hinj := projectiveBundleRelationInjective_of_bundleMap C
    ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
    (bundleProj E' ≫ (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) (bundleProj E') rfl n
    (Stacks.Chow.relativeDimension_bundleProj E' n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ j)
    (bundleTwistCap E' C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY))
    fun j ↦
      (projectiveBundle_formula E' n C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) j).1
  have h1 : ∀ m : ℤ, ∀ β : chowGroup C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) m,
      flatPullbackChow C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
        ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
        (𝟙 (Stacks.Divisors.zeroScheme Y L s).subscheme) (Category.id_comp _) 0
        (relativeDimension_identity (Stacks.Divisors.zeroScheme Y L s).subscheme) m
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ m) β ≍ β :=
    fun m β ↦ (heq_of_eq (flatPullbackChow_id C
      ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) m β)).trans (chowGroupCast_heq C _ _ β)
  have hflat := isChernCapFamily_flatPullback C
    ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
    ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
    (bundleProj E' ≫ (Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) (Z.subschemeι ≫ π ≫ sY)
    (bundleProj E') rfl πD hsPD
    (n + 1) (Stacks.Chow.relativeDimension_bundleProj E' n) hπD'
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _)
    (bundleTwistCap E' C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)) OZ
    (𝟙 (Stacks.Divisors.zeroScheme Y L s).subscheme) (Category.id_comp _) 0
    (relativeDimension_identity (Stacks.Divisors.zeroScheme Y L s).subscheme)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _) φ hf' hd'
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _) hinj hcompat
    k (gysinChowOfInvertible C sY k L s α) _
    (bundleChernCapFamily E' n C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
      (k + ((0 : ℕ) : ℤ)) _) hfam
    (isChernCapFamily_bundleChernCapFamily E' n C
      ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) (k + ((0 : ℕ) : ℤ)) _)
  funext j
  have hj := congrFun hflat j
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq hj).trans ?_))
  · exact heq_apply_of_degree C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
      ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) (fun m ↦ m) (fun m ↦ m - (j : ℤ))
      (fun m ↦ bundleChernCap E' n C ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) m j)
      (by simp) (h1 k _).symm
  · exact (chowGroupCast_heq C _ _ _).trans (h1 _ _)

/-- **Stacks 0B7G for the cap products of Stacks 02U6, in every rank**, for a module `ℰ'` on the
zero scheme identified with the restriction of `ℰ`:

  `c_j(ℰ') ∩ i^*α = i^*(c_j(ℰ) ∩ α)`  in  `A_{k-j}(D)`,  for `α ∈ A_{k+1}(Y)`. -/
theorem chernCap_gysin_of_iso (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : (Stacks.Divisors.zeroScheme Y L s).subscheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y L s).subschemeι).obj E)
    (k : ℤ) (j : Fin (r + 1)) (α : chowGroup C sY (k + 1)) :
    chernCap C r ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY) E' k j
        (gysinChowOfInvertible C sY k L s α) =
      gysinChowOfInvertible C sY (k - (j : ℤ)) L s
        (chowGroupCast C sY (show k + 1 - (j : ℤ) = k - (j : ℤ) + 1 by omega)
          (chernCap C r sY E (k + 1) j α)) := by
  cases r with
  | zero =>
    rw [chernCap_zero, chernCap_zero]
    refine eq_of_heq ((chowGroupCast_heq C _ _ _).trans ?_)
    refine heq_apply_of_degree C sY ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
      (fun m ↦ m + 1) (fun m ↦ m) (fun m ↦ gysinChowOfInvertible C sY m L s)
      (by rw [show (j : ℕ) = 0 from Fin.val_eq_zero j]; simp) ?_
    exact ((chowGroupCast_heq C sY _ _).trans (chowGroupCast_heq C sY _ _)).symm
  | succ n =>
    rw [chernCap_succ, chernCap_succ, bundleChernCap_apply, bundleChernCap_apply,
      bundleChernCapFamily_gysin C sY L s E n E' eE k α]
    rfl

/-- **Stacks 0B7G.** Let `ℰ` be finite locally free of rank `r` on `Y` and let `(ℒ, s, i : D ⟶ Y)`
be a triple as in Definition 02T8. Then for every `0 ≤ j ≤ r` and every `α ∈ A_{k+1}(Y)`

  `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`  in  `A_{k-j}(D)`,

for the Chern class cap products of Stacks 02U6 and the Gysin map of Stacks 02TO. -/
@[stacks 0B7G]
theorem chernCap_gysin (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) (α : chowGroup C sY (k + 1)) :
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
      (Stacks.Divisors.zeroScheme Y L s).subschemeι E r
    chernCap C r ((Stacks.Divisors.zeroScheme Y L s).subschemeι ≫ sY)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y L s).subschemeι).obj E) k j
        (gysinChowOfInvertible C sY k L s α) =
      gysinChowOfInvertible C sY (k - (j : ℤ)) L s
        (chowGroupCast C sY (show k + 1 - (j : ℤ) = k - (j : ℤ) + 1 by omega)
          (chernCap C r sY E (k + 1) j α)) :=
  let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    (Stacks.Divisors.zeroScheme Y L s).subschemeι E r
  chernCap_gysin_of_iso C sY L s E r _ (Iso.refl _) k j α

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0B7G, as the Gysin identity of the identity cap rule of the bivariant Chern class.**
For `ℱ` finite locally free of rank `r` on `X` and every `0 ≤ j ≤ r`, the rule
`α ↦ c_j(g^*ℱ) ∩ α` on the test schemes `g : T ⟶ X` commutes with the Gysin maps of the Gysin
system `Stacks.Chow.gysinSystemOfInvertible`. -/
theorem chernCap_gysinNaturality (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) :
    IdentityCapRule.GysinNaturality C sX (j : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (chernCap C r) j) (gysinSystemOfInvertible C) := by
  intro T g _ N _ s k α
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r
    ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)
  refine (chernCap_gysin_of_iso C (g ≫ sX) N s ((Scheme.Modules.pullback g).obj F) r
    ((Scheme.Modules.pullback ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g)).obj F)
    ((Scheme.Modules.pullbackComp (Stacks.Divisors.zeroScheme T N s).subschemeι g).app F).symm
    k j α).trans ?_
  rfl

end Stacks.Chow.GenuineChern

end
