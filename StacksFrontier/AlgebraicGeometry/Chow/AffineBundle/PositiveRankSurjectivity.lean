module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback

/-!
# Surjectivity of flat pullback along an affine-space bundle of positive rank

Flat pullback along the projection `𝔸^r_T ⟶ T` is surjective on Chow groups for every `r`,
given the case `r = 1`, and hence (Stacks 02TT) flat pullback along an affine-space bundle of any
rank is surjective, given also a devissage over the trivializing opens of the bundle. The file
also builds the isomorphisms of affine spaces `𝔸^(n ⊕ m)_S ≅ 𝔸^m_(𝔸^n_S)` and the reindexing of
affine space along an equivalence of index types, each with the identification of its structure
morphism.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_affineSpaceOver` — **Stacks 02TT** for the trivial
  bundle, given the relative-dimension-one case.
* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle` — **Stacks 02TT** in
  arbitrary rank, given the relative-dimension-one case and the devissage.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! The flat pullback of Stacks 02RB takes flatness of the morphism as an instance argument, so
writing down the pullback along `𝔸(ULift (Fin r); T) ↘ T` needs `Stacks.Chow.flat_affineSpaceOver`
to be available to instance search. -/

attribute [local instance] flat_affineSpaceOver

/-! ### Affine space as an iterated affine line -/

section AffineSpaceTower

open AlgebraicGeometry.AffineSpace

/-- The morphism to affine `n`-space over `S` given by the structure morphism and the standard
coordinates is the identity: it is the reindexing of affine `n`-space along the identity of the
index type. -/
theorem affineSpace_homOfVector_coord (n : Type u) (S : Scheme.{u}) :
    homOfVector (𝔸(n; S) ↘ S) (coord S) = 𝟙 𝔸(n; S) :=
  reindex_id (n := n) (S := S)

/-- **Affine `(n ⊕ m)`-space over `S` is affine `n`-space over affine `m`-space over `S`.** The
isomorphism reads the `m`-coordinates as the coordinates of the inner affine space and the
`n`-coordinates as the coordinates of the outer one. -/
noncomputable def affineSpaceSumIso (n m : Type u) (S : Scheme.{u}) :
    𝔸(n ⊕ m; S) ≅ 𝔸(n; 𝔸(m; S)) where
  hom := homOfVector (reindex Sum.inr S) (fun i ↦ coord S (Sum.inl i))
  inv := homOfVector ((𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)) ≫ (𝔸(m; S) ↘ S))
    (Sum.elim (coord (𝔸(m; S)))
      (fun j ↦ (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)).appTop (coord S j)))
  hom_inv_id := by
    rw [comp_homOfVector, ← Category.assoc, homOfVector_over, reindex_over]
    conv_rhs => rw [← affineSpace_homOfVector_coord (n ⊕ m) S]
    congr 1
    ext (i | j)
    · simp [homOfVector_appTop_coord]
    · simp only [Function.comp_apply, Sum.elim_inr]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over,
        reindex_appTop_coord]
  inv_hom_id := by
    have hre : homOfVector ((𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)) ≫ (𝔸(m; S) ↘ S))
          (Sum.elim (coord (𝔸(m; S)))
            (fun j ↦ (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)).appTop (coord S j))) ≫
          reindex (Sum.inr : m → n ⊕ m) S =
        𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S) := by
      rw [reindex, comp_homOfVector, homOfVector_over]
      conv_rhs => rw [← Category.comp_id (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)),
        ← affineSpace_homOfVector_coord m (S := S), comp_homOfVector]
      congr 1
      ext j
      simp [homOfVector_appTop_coord]
    rw [comp_homOfVector, hre]
    conv_rhs => rw [← affineSpace_homOfVector_coord n (𝔸(m; S))]
    congr 1
    ext i
    simp [homOfVector_appTop_coord]

/-- The identification of `Stacks.Chow.affineSpaceSumIso` is compatible with the projections to
affine `m`-space over `S`: the projection of the outer affine space corresponds to forgetting the
`n`-coordinates. -/
theorem affineSpaceSumIso_hom_over (n m : Type u) (S : Scheme.{u}) :
    (affineSpaceSumIso n m S).hom ≫ (𝔸(n; 𝔸(m; S)) ↘ 𝔸(m; S)) = reindex Sum.inr S :=
  homOfVector_over _ _

/-- Reindexing affine space is contravariantly functorial in the index type. -/
theorem affineSpace_reindex_comp {n m p : Type u} (i : n → m) (j : m → p) (S : Scheme.{u}) :
    reindex j S ≫ reindex i S = reindex (j ∘ i) S :=
  (reindex_comp (TypeCat.ofHom i) (TypeCat.ofHom j) S).symm

/-- An equivalence of index types induces an isomorphism of affine spaces over a fixed base. -/
noncomputable def affineSpaceReindexIso {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    𝔸(n; S) ≅ 𝔸(m; S) where
  hom := reindex e.symm S
  inv := reindex e S
  hom_inv_id := by rw [affineSpace_reindex_comp, e.symm_comp_self, reindex_id]
  inv_hom_id := by rw [affineSpace_reindex_comp, e.self_comp_symm, reindex_id]

/-- The isomorphism induced by an equivalence of index types is one of schemes over the base. -/
theorem affineSpaceReindexIso_hom_over {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceReindexIso e S).hom ≫ (𝔸(m; S) ↘ S) = 𝔸(n; S) ↘ S :=
  reindex_over _ _

/-- Splitting off the last of `r + 1` indices, in the universe of the schemes. -/
def uliftFinSuccSumEquiv (r : ℕ) :
    ULift.{u} (Fin (r + 1)) ≃ ULift.{u} (Fin r) ⊕ ULift.{u} (Fin 1) :=
  Equiv.ulift.trans (finSumFinEquiv.symm.trans (Equiv.ulift.symm.sumCongr Equiv.ulift.symm))

/-- **Affine `(r+1)`-space over `T` is affine `r`-space over the affine line over `T`.** -/
noncomputable def affineSpaceSuccIso (T : Scheme.{u}) (r : ℕ) :
    𝔸(ULift.{u} (Fin (r + 1)); T) ≅ 𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) :=
  affineSpaceReindexIso (uliftFinSuccSumEquiv.{u} r) T ≪≫
    affineSpaceSumIso (ULift.{u} (Fin r)) (ULift.{u} (Fin 1)) T

/-- The identification of `Stacks.Chow.affineSpaceSuccIso` carries the two-step projection of the
tower to the projection of affine `(r+1)`-space. -/
theorem affineSpaceSuccIso_hom_over (T : Scheme.{u}) (r : ℕ) :
    (affineSpaceSuccIso T r).hom ≫
        ((𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T)) ≫
          (𝔸(ULift.{u} (Fin 1); T) ↘ T)) =
      𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T := by
  rw [affineSpaceSuccIso, Iso.trans_hom, Category.assoc,
    ← Category.assoc (affineSpaceSumIso (ULift.{u} (Fin r)) (ULift.{u} (Fin 1)) T).hom,
    affineSpaceSumIso_hom_over, reindex_over, affineSpaceReindexIso_hom_over]

end AffineSpaceTower

/-! ### Surjectivity of flat pullback under composition -/

/-- An isomorphism of schemes has relative dimension zero. -/
theorem relativeDimension_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    AlgebraicGeometry.RelativeDimension f 0 :=
  (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero f).mp inferInstance

/-- **Surjectivity of flat pullback on Chow groups passes to a composite.** If `p = f ≫ g` with
`f` flat of relative dimension `r` and `g` flat of relative dimension `s`, and if `f^*` is
surjective in degree `k + s` and `g^*` is surjective in degree `k`, then `p^*` is surjective in
degree `k`. Here `p` is flat of relative dimension `t`, for any `t` with `t = r + s`. -/
theorem flatPullbackChow_surjective_of_comp_eq (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [AlgebraicGeometry.Flat f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [AlgebraicGeometry.Flat g]
    (p : X ⟶ Z) [LocallyOfFiniteType p] [AlgebraicGeometry.Flat p] (hp : f ≫ g = p)
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (hpbase : p ≫ sZ = sX)
    (r s t : ℕ) (ht : t = r + s)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s)
    (hpt : AlgebraicGeometry.RelativeDimension p t) (k : ℤ)
    (hfacf : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hfbase r hf (k + (s : ℤ)))
    (hfacg : FlatPullbackFactorsThroughRationalEquivalence C sY sZ g hgbase s hg k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sZ p hpbase t hpt k)
    (hsurjf : Function.Surjective (flatPullbackChow C sX sY f hfbase r hf (k + (s : ℤ)) hfacf))
    (hsurjg : Function.Surjective (flatPullbackChow C sY sZ g hgbase s hg k hfacg)) :
    Function.Surjective (flatPullbackChow C sX sZ p hpbase t hpt k hfacp) := by
  subst hp
  subst ht
  intro γ
  have hdeg : k + (s : ℤ) + (r : ℤ) = k + ((r + s : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨β, hβ⟩ := hsurjf ((chowGroupDegreeEquiv C sX hdeg).symm γ)
  obtain ⟨α, hα⟩ := hsurjg β
  refine ⟨α, eq_of_heq ((flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k
    hfacf hfacg hfacp α).symm.trans ?_)⟩
  rw [hα, hβ]
  exact (chowGroupDegreeEquiv_eq_iff_heq C sX hdeg _ γ).mp (AddEquiv.apply_symm_apply _ γ)

/-- **Injectivity of flat pullback on Chow groups passes to a composite.** If `p = f ≫ g` with
`f` flat of relative dimension `r` and `g` flat of relative dimension `s`, and if `f^*` is
injective in degree `k + s` and `g^*` is injective in degree `k`, then `p^*` is injective in
degree `k`. Here `p` is flat of relative dimension `t`, for any `t` with `t = r + s`. -/
theorem flatPullbackChow_injective_of_comp_eq (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [AlgebraicGeometry.Flat f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [AlgebraicGeometry.Flat g]
    (p : X ⟶ Z) [LocallyOfFiniteType p] [AlgebraicGeometry.Flat p] (hp : f ≫ g = p)
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (hpbase : p ≫ sZ = sX)
    (r s t : ℕ) (ht : t = r + s)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s)
    (hpt : AlgebraicGeometry.RelativeDimension p t) (k : ℤ)
    (hfacf : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hfbase r hf (k + (s : ℤ)))
    (hfacg : FlatPullbackFactorsThroughRationalEquivalence C sY sZ g hgbase s hg k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sZ p hpbase t hpt k)
    (hinjf : Function.Injective (flatPullbackChow C sX sY f hfbase r hf (k + (s : ℤ)) hfacf))
    (hinjg : Function.Injective (flatPullbackChow C sY sZ g hgbase s hg k hfacg)) :
    Function.Injective (flatPullbackChow C sX sZ p hpbase t hpt k hfacp) := by
  subst hp
  subst ht
  intro α β hab
  refine hinjg (hinjf (eq_of_heq ?_))
  exact (flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k hfacf hfacg hfacp
      α).trans
    ((heq_of_eq hab).trans
      (flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k hfacf hfacg hfacp β).symm)


/-- **Precomposing with an isomorphism does not change surjectivity of flat pullback.** If
`p = e ≫ q` with `e` an isomorphism and `q` flat of relative dimension `r` with surjective flat
pullback in degree `k`, then `p^*` is surjective in degree `k`. -/
theorem flatPullbackChow_surjective_of_isIso_comp (C : ChowSituation.{u}) {X A Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (e : X ⟶ A) [IsIso e] (q : A ⟶ Y)
    [LocallyOfFiniteType q] [AlgebraicGeometry.Flat q] (p : X ⟶ Y) [LocallyOfFiniteType p]
    [AlgebraicGeometry.Flat p] (hp : e ≫ q = p) (hebase : e ≫ sA = sX)
    (hqbase : q ≫ sY = sA) (hpbase : p ≫ sY = sX) (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r)
    (hpr : AlgebraicGeometry.RelativeDimension p r) (k : ℤ)
    (hface : FlatPullbackFactorsThroughRationalEquivalence C sX sA e hebase 0
      (relativeDimension_of_isIso e) (k + (r : ℤ)))
    (hfacq : FlatPullbackFactorsThroughRationalEquivalence C sA sY q hqbase r hq k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sY p hpbase r hpr k)
    (hsurjq : Function.Surjective (flatPullbackChow C sA sY q hqbase r hq k hfacq)) :
    Function.Surjective (flatPullbackChow C sX sY p hpbase r hpr k hfacp) := by
  have _ : IsOpenImmersion e := IsOpenImmersion.of_isIso e
  exact flatPullbackChow_surjective_of_comp_eq C sX sA sY e q p hp hebase hqbase hpbase 0 r r
    (Nat.zero_add r).symm (relativeDimension_of_isIso e) hq hpr k hface hfacq hfacp
    (flatPullbackChow_surjective_of_isOpenImmersion C sA sX e hebase
      (relativeDimension_of_isIso e) (k + (r : ℤ)) hface) hsurjq

/-! ### Stacks 02TT: the tower reduction to relative dimension one -/

/-- **Stacks 02TT, the tower reduction for a trivial affine-space bundle.** Let `(S, δ)` be the
base situation of chapter 42 and let `T` be locally of finite type over `S`. If flat pullback
along the projection of the affine line `𝔸^1_B ⟶ B` is surjective on Chow groups for every
scheme `B` locally of finite type over `S` and in every degree, then flat pullback along the
projection `𝔸^r_T ⟶ T` is surjective on Chow groups for every `r` and every degree.

The hypothesis `hfp` is Stacks 02S1 for every flat morphism over the base and in every degree,
and `hone` is the case of the affine line. -/
theorem flatPullbackChow_surjective_affineSpaceOver (C : ChowSituation.{u})
    (hfp : ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
      [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [AlgebraicGeometry.Flat v]
      (hv : v ≫ sB = sA) (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension v d) (j : ℤ),
      FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv d hd j)
    (hone : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ),
      Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
        (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1 (relativeDimension_affineSpaceOver B 1) j
        (hfp _ _ _ _ _ _ _)))
    (r : ℕ) (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) :
    Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin r); T) ↘ T) ≫ sT) sT
      (𝔸(ULift.{u} (Fin r); T) ↘ T) rfl r (relativeDimension_affineSpaceOver T r) k
      (hfp _ _ _ _ _ _ _)) := by
  induction r generalizing T sT k with
  | zero =>
    have _ : IsOpenImmersion (𝔸(ULift.{u} (Fin 0); T) ↘ T) := IsOpenImmersion.of_isIso _
    exact flatPullbackChow_surjective_of_isOpenImmersion C sT
      ((𝔸(ULift.{u} (Fin 0); T) ↘ T) ≫ sT) (𝔸(ULift.{u} (Fin 0); T) ↘ T) rfl
      (relativeDimension_affineSpaceOver T 0) k _
  | succ r ih =>
    have hp : ((affineSpaceSuccIso T r).hom ≫
          (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T))) ≫
          (𝔸(ULift.{u} (Fin 1); T) ↘ T) =
        𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T := by
      rw [Category.assoc]
      exact affineSpaceSuccIso_hom_over T r
    have hfbase : ((affineSpaceSuccIso T r).hom ≫
          (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T))) ≫
          ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) =
        (𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) ≫ sT := by
      rw [← Category.assoc, hp]
    have hf : AlgebraicGeometry.RelativeDimension ((affineSpaceSuccIso T r).hom ≫
        (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T))) r := by
      have h := AlgebraicGeometry.RelativeDimension.comp_of_flat (affineSpaceSuccIso T r).hom
        (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T))
        (relativeDimension_of_isIso _)
        (relativeDimension_affineSpaceOver (𝔸(ULift.{u} (Fin 1); T)) r)
      rwa [Nat.zero_add] at h
    have hebase : (affineSpaceSuccIso T r).hom ≫
          ((𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T)) ≫
            ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT)) =
        (𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) ≫ sT := by
      simp only [← Category.assoc]
      rw [hp]
    exact flatPullbackChow_surjective_of_comp_eq C
      ((𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) ≫ sT) ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) sT
      ((affineSpaceSuccIso T r).hom ≫
        (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T)))
      (𝔸(ULift.{u} (Fin 1); T) ↘ T) (𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) hp hfbase rfl rfl
      r 1 (r + 1) rfl hf (relativeDimension_affineSpaceOver T 1)
      (relativeDimension_affineSpaceOver T (r + 1)) k (hfp _ _ _ _ _ _ _) (hfp _ _ _ _ _ _ _)
      (hfp _ _ _ _ _ _ _)
      (flatPullbackChow_surjective_of_isIso_comp C
        ((𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) ≫ sT)
        ((𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T)) ≫
          ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT))
        ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) (affineSpaceSuccIso T r).hom
        (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T))
        ((affineSpaceSuccIso T r).hom ≫
          (𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T)))
        rfl hebase rfl hfbase r
        (relativeDimension_affineSpaceOver (𝔸(ULift.{u} (Fin 1); T)) r) hf (k + ((1 : ℕ) : ℤ))
        (hfp _ _ _ _ _ _ _) (hfp _ _ _ _ _ _ _) (hfp _ _ _ _ _ _ _)
        (ih (𝔸(ULift.{u} (Fin 1); T)) ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT)
          (k + ((1 : ℕ) : ℤ))))
      (hone T sT k)

/-- **Stacks 02TT for an affine-space bundle of arbitrary rank, given the relative-dimension-one
case and the devissage.** Let `(S, δ)` be the base situation of chapter 42, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be flat of relative dimension `r` which is
Zariski-locally on `Y` the projection `U × 𝔸^r ⟶ U`. Then `f^* : A_k(Y) ⟶ A_{k+r}(X)` is
surjective for every `k`.

The hypotheses are:

* `hfp`, Stacks 02S1 for every flat morphism over the base and in every degree;
* `hone`, surjectivity of flat pullback along the affine line `𝔸^1_B ⟶ B` for every `B`;
* `hdevissage`, which deduces surjectivity of flat pullback along an affine-space bundle of rank
  `d` from surjectivity along the projections `𝔸^d_B ⟶ B` for every `B`. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle (C : ChowSituation.{u})
    (hfp : ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
      [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [AlgebraicGeometry.Flat v]
      (hv : v ≫ sB = sA) (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension v d) (j : ℤ),
      FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv d hd j)
    (hone : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : ℤ),
      Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB
        (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1 (relativeDimension_affineSpaceOver B 1) j
        (hfp _ _ _ _ _ _ _)))
    (hdevissage : ∀ {A B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (v : A ⟶ B)
      [LocallyOfFiniteType v] [AlgebraicGeometry.Flat v] (d : ℕ)
      (hd : AlgebraicGeometry.RelativeDimension v d) (_hv : IsAffineSpaceBundle v d) (j : ℤ),
      (∀ (B' : Scheme.{u}) (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (i : ℤ),
          Function.Surjective (flatPullbackChow C ((𝔸(ULift.{u} (Fin d); B') ↘ B') ≫ sB') sB'
            (𝔸(ULift.{u} (Fin d); B') ↘ B') rfl d (relativeDimension_affineSpaceOver B' d) i
            (hfp _ _ _ _ _ _ _))) →
        Function.Surjective (flatPullbackChow C (v ≫ sB) sB v rfl d hd j (hfp _ _ _ _ _ _ _)))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Surjective (flatPullbackChow C (f ≫ sY) sY f rfl r hf k (hfp _ _ _ _ _ _ _)) :=
  hdevissage sY f r hf hbundle k fun B' sB' _ i ↦
    flatPullbackChow_surjective_affineSpaceOver C hfp hone r B' sB' i

end Stacks.Chow

end
