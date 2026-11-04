module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassCommute
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatPullbackChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass

/-!
# Bivariant classes commute with the Chern classes (Stacks 02UA)

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r`, let
`f : X' ⟶ X` be locally of finite type and let `c ∈ A^p(X' ⟶ X)` be a bivariant class of degree
`p`. Stacks 02UA asserts

  `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c`   in   `A^{p+j}(X' ⟶ X)`,

which is clause (2) of the tag; clause (1), that `c_j(ℰ)` lies in the center of `A^*(X)`, is the
case `f = 𝟙 X`.

`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass` carries out
the source's argument for an arbitrary degree-lowering operation on the Chow groups of the
bases and of the projective bundles, under the hypothesis that the operation carries each
summand of the relation of Stacks 02U6 to the corresponding summand. This module discharges that
hypothesis for the cap product of a bivariant class with the genuine Chern classes of
`Stacks.Chow.GenuineChern`, and assembles Stacks 02UA as an identity of bivariant classes.

The compatibility with the summands is deduced from the compatibility with `π^*` and with the
first Chern class cap of the twists (`Stacks.Chow.chernTermsCompatibleWithOperation_of`). For the
cap product of a bivariant class on the projective bundles of Stacks 02U6 both hold outright: the
first is axiom (2) of Stacks 0B76 together with the base change of the projective bundle, the
second is Stacks 0B7B (`Stacks.Chow.BivariantClass.cap_firstChernClassCapChow`).

## Main results

* `Stacks.Chow.chernTermsCompatibleWithOperation_of` — the compatibility with the summands, from
  the compatibility with `π^*` and with the twists.
* `Stacks.Chow.bundleChernCapFamily_bivariantClass` — a bivariant class carries the family of
  Chern class cap products of `α` for `ℰ` to the family of `c ∩ α` for the pullback of `ℰ`.
* `Stacks.Chow.genuineChernCap_bivariantClass_comm` — the same, member by member and in every
  rank.
* `Stacks.Chow.BivariantClass.cap_idRule_chernClass` — capping with `c` intertwines the operations
  of `c_j(ℰ)` and `c_j(f^*ℰ)` on every test scheme.
* `Stacks.Chow.BivariantClass.heq_bivariantCompositeOfInvertible_chernClass` —
  **Stacks 02UA (2)**: `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c`.
* `Stacks.Chow.BivariantClass.heq_mulId_chernClass` — **Stacks 02UA (1)**: `c_j(ℰ)` is in the
  center of `A^*(X)`.

## Implementation notes

A bivariant class of degree `p` for `f : X' ⟶ X` is a rule assigning to every `g : T ⟶ X`
locally of finite type a map `A_k(T) ⟶ A_{k-p}(T ×_X X')`, so the identity
`c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c` is, for each test scheme `g`, the identity

  `c ∩ (c_j(ℰ|_T) ∩ α) = c_j(f^*ℰ|_{T ×_X X'}) ∩ (c ∩ α)`   for `α ∈ A_k(T)`,

which is `Stacks.Chow.genuineChernCap_bivariantClass_comm`, stated for an arbitrary module on
`T ×_X X'` isomorphic to the pullback of `ℰ|_T`. The identity of bivariant classes follows by the
composition formula of Stacks 0FE0
(`Stacks.Chow.BivariantClass.heq_bivariantCompositeOfInvertible_iff`). The composites
`c ∘ c_j(ℰ)` and `c_j(f^*ℰ) ∘ c` are classes for the equal morphisms `f ≫ 𝟙 X` and `𝟙 X' ≫ f`
of the equal degrees `p + j` and `j + p`, so the two clauses are heterogeneous equalities; the
statements are for a homogeneous `c`.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.Chow

/-! ### The compatibility with the summands, from its two ingredients -/

/-- A degree-lowering operation sends heterogeneously equal classes in equal degrees to
heterogeneously equal classes. -/
private theorem heq_degreeLowering_apply (C : ChowSituation.{u}) {P P' : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sP' : P' ⟶ C.S) [LocallyOfFiniteType sP'] {q : ℤ}
    (op : ∀ m : ℤ, chowGroup C sP m →+ chowGroup C sP' (m - q)) {d₁ d₂ : ℤ} (hd : d₁ = d₂)
    {x : chowGroup C sP d₁} {y : chowGroup C sP d₂} (h : x ≍ y) : op d₁ x ≍ op d₂ y :=
  heq_apply_of_degree C sP sP' (fun d ↦ d) (fun d ↦ d - q) (fun d ↦ op d) hd h

section Operation

variable (C : ChowSituation.{u}) {X X' P P' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sP' : P' ⟶ C.S) [LocallyOfFiniteType sP']
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (π' : P' ⟶ X') [LocallyOfFiniteType π'] [Flat π'] (hsP' : π' ≫ sX' = sP')
  (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hπ' : AlgebraicGeometry.RelativeDimension π' (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (hfac' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP' sX' π' hsP' (r - 1) hπ' k)
  (twist : ChernCapOperator C sP) (twist' : ChernCapOperator C sP') (q : ℤ)
  (op : ∀ m : ℤ, chowGroup C sX m →+ chowGroup C sX' (m - q))
  (opP : ∀ m : ℤ, chowGroup C sP m →+ chowGroup C sP' (m - q))


/-- An operation on the bundles that commutes with the first Chern class cap of the twists
commutes with every iterated cap: `opP(c₁(O_P(1))^n ∩ y) = c₁(O_{P'}(1))^n ∩ opP(y)`, read
through any argument `y'` heterogeneously equal to `opP(y)`. -/
theorem operation_iteratedChernCapOnChow_heq
    (hξ : ∀ (e : ℤ) (y : chowGroup C sP (e + 1)) (y' : chowGroup C sP' (e - q + 1)),
      y' ≍ opP (e + 1) y → opP e (twist.capOnChow C sP e y) = twist'.capOnChow C sP' (e - q) y')
    (n : ℕ) (e : ℤ) (y : chowGroup C sP (e + ((List.replicate n twist).length : ℤ)))
    (y' : chowGroup C sP' (e - q + ((List.replicate n twist').length : ℤ)))
    (hy : y' ≍ opP _ y) :
    opP e (iteratedChernCapOnChow C sP (List.replicate n twist) e y) ≍
      iteratedChernCapOnChow C sP' (List.replicate n twist') (e - q) y' := by
  induction n generalizing e with
  | zero =>
    refine HEq.trans ?_ (iteratedChernCapOnChow_replicate_zero_heq C sP' twist' _ y').symm
    refine HEq.trans ?_ hy.symm
    exact heq_degreeLowering_apply C sP sP' opP (by simp)
      (iteratedChernCapOnChow_replicate_zero_heq C sP twist e y)
  | succ n ih =>
    rw [iteratedChernCapOnChow_replicate_succ_heq C sP twist n e y
      (chowGroupCast C sP (by simp; ring) y) (chowGroupCast_heq C sP _ y).symm,
      iteratedChernCapOnChow_replicate_succ_heq C sP' twist' n (e - q) y'
      (chowGroupCast C sP' (by simp; ring) y') (chowGroupCast_heq C sP' _ y').symm]
    have hy₂ : chowGroupCast C sP' (show e - q + ((List.replicate (n + 1) twist').length : ℤ) =
          e + 1 - q + ((List.replicate n twist').length : ℤ) by simp; ring) y' ≍
        opP (e + 1 + ((List.replicate n twist).length : ℤ))
          (chowGroupCast C sP (by simp; ring) y) :=
      (chowGroupCast_heq C sP' _ y').trans (hy.trans (heq_degreeLowering_apply C sP sP' opP
        (by simp; ring) (chowGroupCast_heq C sP _ y).symm))
    have h := ih (e + 1) _ _ hy₂
    rw [hξ e _ _ ((iteratedChernCapOnChow_heq C sP' _ (show e - q + 1 = e + 1 - q by ring)
      ((chowGroupCast_heq C sP' _ _).trans (chowGroupCast_heq C sP' _ _).symm)).trans h.symm)]

/-- **The compatibility of the summands, from its two ingredients.** An operation `op` on the
bases and `opP` on the bundles are compatible with the summands `c₁(O_P(1))^i ∩ π^*(-)` of the
relation as soon as `opP ∘ π^* = (π')^* ∘ op` and `opP` commutes with the first Chern class cap of
the twists. -/
theorem chernTermsCompatibleWithOperation_of
    (hpull : ∀ (m : ℤ) (x : chowGroup C sX m),
      opP (m + ((r - 1 : ℕ) : ℤ)) (projectiveBundlePullback C sX sP π hsP r hπ hfac m x) ≍
        projectiveBundlePullback C sX' sP' π' hsP' r hπ' hfac' (m - q) (op m x))
    (hξ : ∀ (e : ℤ) (y : chowGroup C sP (e + 1)) (y' : chowGroup C sP' (e - q + 1)),
      y' ≍ opP (e + 1) y → opP e (twist.capOnChow C sP e y) = twist'.capOnChow C sP' (e - q) y') :
    ChernTermsCompatibleWithOperation C sX sX' sP sP' π hsP π' hsP' r hπ hπ' hfac hfac' twist
      twist' q op opP := by
  intro k i hi x
  simp only [projectiveBundleChernTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine eq_of_heq ((chowGroupCast_heq C sP' _ _).trans ?_)
  refine (operation_iteratedChernCapOnChow_heq C sP sP' twist twist' q opP hξ i _ _
    (chowGroupCast C sP' (show k - ((r - i : ℕ) : ℤ) - q + ((r - 1 : ℕ) : ℤ) =
        k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) - q + ((List.replicate i twist').length : ℤ) by
      simp only [List.length_replicate]; omega)
      (projectiveBundlePullback C sX' sP' π' hsP' r hπ' hfac' (k - ((r - i : ℕ) : ℤ) - q)
        (op _ x))) ?_).trans ?_
  · refine (chowGroupCast_heq C sP' _ _).trans ((hpull _ x).symm.trans ?_)
    exact heq_degreeLowering_apply C sP sP' opP
      (by simp only [List.length_replicate]; omega) (chowGroupCast_heq C sP _ _).symm
  · exact iteratedChernCapOnChow_heq C sP' (List.replicate i twist')
      (show k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) - q = k - q + ((r - 1 : ℕ) : ℤ) - (r : ℤ) by omega)
      ((chowGroupCast_heq C sP' _ _).trans ((heq_apply_of_degree C sX' sP' (fun d ↦ d)
        (fun d ↦ d + ((r - 1 : ℕ) : ℤ))
        (fun d ↦ projectiveBundlePullback C sX' sP' π' hsP' r hπ' hfac' d)
        (show k - ((r - i : ℕ) : ℤ) - q = k - q - ((r - i : ℕ) : ℤ) by omega)
        (chowGroupCast_heq C sX' _ _).symm).trans (chowGroupCast_heq C sP' _ _).symm))

end Operation

/-! ### Clause (2) for the genuine Chern classes, on the test schemes -/

section Genuine

variable {C : ChowSituation.{u}} {X' X T : Scheme.{u}} {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX']
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : X' ⟶ X} [LocallyOfFiniteType f]
  {hf : f ≫ sX = sX'} {p : ℤ} (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX f hf p)
  (g : T ⟶ X) [LocallyOfFiniteType g] (r : ℕ)

/-- **Stacks 02UA (2) for the families of Stacks 02U6, on a test scheme.** Let
`c ∈ A^p(X' ⟶ X)`, let `t : T ⟶ X` be a test scheme, let `ℰ` be finite locally free of rank
`n + 1` on `T` and let `ℰ'` be a module on `T ×_X X'` isomorphic to the pullback of `ℰ`. Then the
family of Chern class cap products of `c ∩ α` for `ℰ'` is the cap product with `c` of the family
of `α` for `ℰ`:

  `c_j(ℰ') ∩ (c ∩ α) = c ∩ (c_j(ℰ) ∩ α)`.

The proof is the one of the source. The projective bundle of `ℰ'` is the base change of that of
`ℰ` (`Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), which is also the chosen base change
`𝐏(ℰ) ×_X X'` on which `c` caps for the test scheme `𝐏(ℰ) ⟶ X`. Capping with `c` commutes with
the flat pullback along the projection (axiom (2) of Stacks 0B76) and with the first Chern class
cap of the twist (Stacks 0B7B, `Stacks.Chow.BivariantClass.cap_firstChernClassCapChow`), so it
carries the relation of Stacks 02U6 for `α` to the relation for `c ∩ α`, and the uniqueness of
Stacks 02U6 on `𝐏(ℰ')` identifies the two families. -/
theorem bundleChernCapFamily_bivariantClass (E : T.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (E' : (pullback f g).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    (eE : E' ≅ (Scheme.Modules.pullback (pullback.snd f g)).obj E) (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    bundleChernCapFamily E' n C (pullback.fst f g ≫ sX') (k - p) (c.cap g k α) =
      bivariantChernFamily C (gysinSystemOfInvertible C) sX' sX f hf p c g (n + 1) k
        (bundleChernCapFamily E n C (g ≫ sX) k α) := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
    (n + 1)
  have := flat_bundleProj E n
  have := locallyOfFiniteType_bundleProj E n
  have := flat_bundleProj E' n
  have := locallyOfFiniteType_bundleProj E' n
  -- the projective bundle of `ℰ'` is the chosen base change `𝐏(ℰ) ×_X X'`
  obtain ⟨e, he, ⟨eT⟩⟩ := GenuineChern.bundleBaseChangeHolds (pullback.snd f g) E E' eE
  set π := bundleProj E with hπdef
  set π' := bundleProj E' with hπ'def
  set h' := bivariantBaseChangeMap f g π with hh'
  have sq : IsPullback (pullback.snd f (π ≫ g)) h' π (pullback.snd f g) :=
    isPullback_bivariantBaseChangeMap f g π
  have : LocallyOfFiniteType h' := MorphismProperty.of_isPullback sq inferInstance
  have : Flat h' := MorphismProperty.of_isPullback sq inferInstance
  have hr' : AlgebraicGeometry.RelativeDimension h' n :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq (relativeDimension_bundleProj E n)
  set ψ : bundle E' ≅ pullback f (π ≫ g) := e ≪≫ sq.flip.isoPullback.symm with hψ
  have hψh' : ψ.hom ≫ h' = π' := by
    rw [hψ, Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst, he]
  have hψsnd : ψ.hom ≫ pullback.snd f (π ≫ g) = e.hom ≫ pullback.snd (pullback.snd f g) π := by
    rw [hψ, Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd]
  have hψs : ψ.hom ≫ (pullback.fst f (π ≫ g) ≫ sX') = π' ≫ (pullback.fst f g ≫ sX') := by
    rw [← bivariantBaseChangeMap_fst f g π, ← hh', ← Category.assoc, ← Category.assoc, hψh',
      Category.assoc]
  have hψ0 : AlgebraicGeometry.RelativeDimension ψ.hom 0 :=
    (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero ψ.hom).mp inferInstance
  have hfacψ := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (π' ≫ (pullback.fst f g ≫ sX')) (pullback.fst f (π ≫ g) ≫ sX') ψ.hom hψs 0 hψ0 j
  -- the operation on the bundles: cap with `c` for the test scheme `𝐏(ℰ) ⟶ X`, read on `𝐏(ℰ')`
  let opP : ∀ m : ℤ, chowGroup C (π ≫ (g ≫ sX)) m →+
      chowGroup C (π' ≫ (pullback.fst f g ≫ sX')) (m - p) := fun m ↦
    (chowGroupCast C _ (show m - p + ((0 : ℕ) : ℤ) = m - p by simp)).toAddMonoidHom.comp
      ((flatPullbackChow C _ _ ψ.hom hψs 0 hψ0 (m - p) (hfacψ _)).comp (c.cap (π ≫ g) m))
  have hopP : ∀ (m : ℤ) (y : chowGroup C (π ≫ (g ≫ sX)) m), opP m y ≍
      flatPullbackChow C _ _ ψ.hom hψs 0 hψ0 (m - p) (hfacψ _) (c.cap (π ≫ g) m y) :=
    fun m y ↦ chowGroupCast_heq C _ (show m - p + ((0 : ℕ) : ℤ) = m - p by simp) _
  -- compatibility with the flat pullback along the projections
  have hpull : ∀ (m : ℤ) (x : chowGroup C (g ≫ sX) m),
      opP (m + ((n + 1 - 1 : ℕ) : ℤ)) (projectiveBundlePullback C (g ≫ sX) (π ≫ (g ≫ sX)) π rfl
        (n + 1) (relativeDimension_bundleProj E n)
        (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k) m x) ≍
      projectiveBundlePullback C (pullback.fst f g ≫ sX') (π' ≫ (pullback.fst f g ≫ sX')) π' rfl
        (n + 1) (relativeDimension_bundleProj E' n)
        (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k) (m - p)
        (c.cap g m x) := by
    intro m x
    have hflat := c.flat_naturality g π n (relativeDimension_bundleProj E n) h' sq
      (bivariantBaseChangeMap_fst f g π) m hr'
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) x
    refine (hopP _ _).trans ((flatPullbackChow_heq_of_degree C _ _ ψ.hom hψs 0 hψ0 (by omega)
      (hfacψ _) (hfacψ _) hflat).trans ?_)
    refine (flatPullbackChow_comm_of_comp_eq C _ _ (pullback.fst f g ≫ sX') _ ψ.hom h' π'
      (𝟙 _) hψs (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) rfl (Category.id_comp _)
      0 n hψ0 hr' (relativeDimension_bundleProj E' n) (relativeDimension_identity _)
      (by rw [hψh', Category.comp_id]) (m - p) (hfacψ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_id C _ _) (c.cap g m x)).trans ?_
    rw [flatPullbackChow_id]
    exact flatPullbackChow_heq_of_degree C _ _ π' rfl n (relativeDimension_bundleProj E' n)
      (by simp) _ _ (chowGroupCast_heq C _ _ _)
  -- compatibility with the first Chern class cap of the twists (Stacks 0B7B)
  have hξ : ∀ (e' : ℤ) (y : chowGroup C (π ≫ (g ≫ sX)) (e' + 1))
      (y' : chowGroup C (π' ≫ (pullback.fst f g ≫ sX')) (e' - p + 1)),
      y' ≍ opP (e' + 1) y →
      opP e' ((bundleTwistCap E C (g ≫ sX)).capOnChow C _ e' y) =
        (bundleTwistCap E' C (pullback.fst f g ≫ sX')).capOnChow C _ (e' - p) y' := by
    intro e' y y' hy
    have := GenuineChern.isInvertible_pullback (pullback.snd f (π ≫ g)) (bundleTwist E)
    have hcap := c.cap_firstChernClassCapChow (π ≫ g) (bundleTwist E)
      ((Scheme.Modules.pullback (pullback.snd f (π ≫ g))).obj (bundleTwist E)) (Iso.refl _) e' y
      (chowGroupCast C _ (show e' + 1 - p = e' - p + 1 by ring) (c.cap (π ≫ g) (e' + 1) y))
      (chowGroupCast_heq C _ _ _)
    have eL : bundleTwist E' ≅ (Scheme.Modules.pullback ψ.hom).obj
        ((Scheme.Modules.pullback (pullback.snd f (π ≫ g))).obj (bundleTwist E)) :=
      eT.symm ≪≫ (Scheme.Modules.pullbackCongr hψsnd.symm).app (bundleTwist E) ≪≫
        ((Scheme.Modules.pullbackComp ψ.hom (pullback.snd f (π ≫ g))).app (bundleTwist E)).symm
    refine eq_of_heq ((hopP _ _).trans (HEq.trans (heq_of_eq (congrArg
      (flatPullbackChow C _ _ ψ.hom hψs 0 hψ0 (e' - p) (hfacψ _)) hcap)) ?_))
    refine (flatPullbackChow_firstChernClassCapChow_heq C _ _ ψ.hom hψs 0 hψ0 hfacψ _
      (bundleTwist E') eL (e' - p) _
      (chowGroupCast C _ (show e' - p + 1 = e' - p + ((0 : ℕ) : ℤ) + 1 by simp) y') ?_).trans ?_
    · refine (chowGroupCast_heq C _ _ _).trans (hy.trans ((hopP _ _).trans ?_))
      exact flatPullbackChow_heq_of_degree C _ _ ψ.hom hψs 0 hψ0 (by ring) _ _
        (chowGroupCast_heq C _ _ _).symm
    · exact heq_apply_of_degree C _ _ (fun d ↦ d + 1) (fun d ↦ d)
        (fun d ↦ firstChernClassCapChow C d (π' ≫ (pullback.fst f g ≫ sX')) (bundleTwist E'))
        (by simp) (chowGroupCast_heq C _ _ _)
  have hcompat := chernTermsCompatibleWithOperation_of C (g ≫ sX) (pullback.fst f g ≫ sX')
    (π ≫ (g ≫ sX)) (π' ≫ (pullback.fst f g ≫ sX')) π rfl π' rfl (n + 1)
    (relativeDimension_bundleProj E n) (relativeDimension_bundleProj E' n)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k)
    (bundleTwistCap E C (g ≫ sX)) (bundleTwistCap E' C (pullback.fst f g ≫ sX')) p
    (fun m ↦ c.cap g m) opP hpull hξ
  exact (eq_bundleChernCapFamily_of_isChernCapFamily E' n C (pullback.fst f g ≫ sX') (k - p) _ _
    (operation_isChernCapFamily C (g ≫ sX) (pullback.fst f g ≫ sX') _ _ π rfl π' rfl (n + 1)
      (relativeDimension_bundleProj E n) (relativeDimension_bundleProj E' n) _ _ _ _ p _ opP
      hcompat k α _ (isChernCapFamily_bundleChernCapFamily E n C (g ≫ sX) k α))).symm

/-- **Stacks 02UA (2), on a test scheme.** Let `c ∈ A^p(X' ⟶ X)`, let `t : T ⟶ X` be a test
scheme, let `ℰ` be finite locally free of rank `r` on `T` and let `ℰ'` be a module on
`T ×_X X'` isomorphic to the pullback of `ℰ`. Then capping with `c` commutes with the Chern
classes:

  `c ∩ (c_j(ℰ) ∩ α) = c_j(ℰ') ∩ (c ∩ α)`   in   `A_{k-j-p}(T ×_X X')`,

the two sides being read in the equal degrees `k - j - p` and `k - p - j`. -/
theorem genuineChernCap_bivariantClass_comm (E : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : (pullback f g).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback (pullback.snd f g)).obj E) (k : ℤ) (j : Fin (r + 1))
    (α : chowGroup C (g ≫ sX) k) :
    c.cap g (k - (j : ℤ)) (GenuineChern.chernCap C r (g ≫ sX) E k j α) ≍
      GenuineChern.chernCap C r (pullback.fst f g ≫ sX') E' (k - p) j (c.cap g k α) := by
  cases r with
  | zero =>
    rw [GenuineChern.chernCap_zero, GenuineChern.chernCap_zero]
    refine HEq.trans ?_ (chowGroupCast_heq C _ _ _).symm
    exact heq_degreeLowering_apply C (g ≫ sX) (pullback.fst f g ≫ sX') (fun d ↦ c.cap g d)
      (by rw [show (j : ℕ) = 0 from Fin.val_eq_zero j]; simp) (chowGroupCast_heq C _ _ _)
  | succ n =>
    rw [GenuineChern.chernCap_succ, GenuineChern.chernCap_succ, bundleChernCap_apply,
      bundleChernCap_apply, bundleChernCapFamily_bivariantClass c g E n E' eE k α]
    exact (chowGroupCast_heq C _ _ _).symm

/-- **Stacks 02UA (2), on the test schemes.** For `c ∈ A^p(X' ⟶ X)`, a finite locally free `ℰ`
of rank `r` on `X` and a module `ℰ'` on `X'` isomorphic to `f^*ℰ`, capping with `c` intertwines
the operations of `c_j(ℰ) ∈ A^j(X)` and of `c_j(ℰ') ∈ A^j(X')` on every test scheme
`t : T ⟶ X`: `c ∩ (c_j(t^*ℰ) ∩ α) = c_j(t'^*ℰ') ∩ (c ∩ α)`, `t' : T ×_X X' ⟶ X'`. -/
theorem BivariantClass.cap_idRule_chernClass (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (F' : X'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (eF : F' ≅ (Scheme.Modules.pullback f).obj F) (j : Fin (r + 1)) (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    c.cap g (k - (j : ℤ))
        ((GenuineChern.chernClass C sX F r j).idRule C sX (gysinSystemOfInvertible C) g k α) ≍
      (GenuineChern.chernClass C sX' F' r j).idRule C sX' (gysinSystemOfInvertible C)
        (pullback.fst f g) (k - p) (c.cap g k α) := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F' r (pullback.fst f g)
  rw [GenuineChern.idRule_chernClass, GenuineChern.idRule_chernClass]
  exact genuineChernCap_bivariantClass_comm c g r _ _
    ((Scheme.Modules.pullback (pullback.fst f g)).mapIso eF ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f g) f).app F ≪≫
      (Scheme.Modules.pullbackCongr pullback.condition).app F ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f g) g).app F).symm) k j α

end Genuine

/-! ### Stacks 02UA as an identity of bivariant classes -/

section Composite

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {f : X' ⟶ X} [LocallyOfFiniteType f]
  {hf : f ≫ sX = sX'} {p : ℤ}

/-- **Stacks 02UA (2).** Let `f : X' ⟶ X` be locally of finite type, let `c ∈ A^p(X' ⟶ X)` and let
`ℰ` be finite locally free of rank `r` on `X`. Then for `0 ≤ j ≤ r`

  `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c`   in   `A^{p+j}(X' ⟶ X)`,

the composites being those of Stacks 0B75, classes for the equal morphisms `f ≫ 𝟙 X` and
`𝟙 X' ≫ f` of the equal degrees `p + j` and `j + p`. -/
@[stacks 02UA "(2), for a homogeneous c in A^p(X' -> X), the bivariant Chern classes of Stacks 0B7H
and the composition of Stacks 0B75 at the Gysin system of the first Chern class of an invertible
module; the two composites are classes for f ≫ 𝟙 X and 𝟙 X' ≫ f of degrees p + j and j + p,
whence the heterogeneous equality"]
theorem BivariantClass.heq_bivariantCompositeOfInvertible_chernClass
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX f hf p) (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) :
    letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r f
    bivariantCompositeOfInvertible C sX' sX sX f (𝟙 X) hf (Category.id_comp sX) p j c
        (GenuineChern.chernClass C sX F r j) ≍
      bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') f (Category.id_comp sX') hf j p
        (GenuineChern.chernClass C sX' ((Scheme.Modules.pullback f).obj F) r j) c := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r f
  exact (c.heq_bivariantCompositeOfInvertible_iff _ _).2 fun t _ k α ↦
    c.cap_idRule_chernClass t r F _ (Iso.refl _) j k α

/-- **Stacks 02UA (1).** The Chern class `c_j(ℰ) ∈ A^j(X)` of a finite locally free module of rank
`r` is in the center of `A^*(X)`: for every `c ∈ A^q(X)`,

  `c · c_j(ℰ) = c_j(ℰ) · c`,

the two products lying in `A^{q+j}(X)` and `A^{j+q}(X)`. -/
@[stacks 02UA "(1), for the product of A^*(X) given by the composition of Stacks 0B75 at the Gysin
system of the first Chern class of an invertible module, against every homogeneous c in A^q(X);
the two products have degrees q + j and j + q, whence the heterogeneous equality"]
theorem BivariantClass.heq_mulId_chernClass {q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) q)
    (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (j : Fin (r + 1)) :
    c.mulId C sX (GenuineChern.chernClass C sX F r j) ≍
      (GenuineChern.chernClass C sX F r j).mulId C sX c :=
  (c.heq_mulId_iff _).2 fun t _ k α ↦
    c.cap_idRule_chernClass t r F F ((Scheme.Modules.pullbackId X).app F).symm j k α

end Composite

end Stacks.Chow

end
