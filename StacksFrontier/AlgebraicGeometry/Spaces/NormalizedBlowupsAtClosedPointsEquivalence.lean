module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizedBlowupLiftFromNeighborhood

/-!
# Sequences of normalized blowups at closed points are étale local: Stacks 0BHL

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9), and
let `f : Y ⟶ X` correspond to `gᵢ : Yᵢ ⟶ Uᵢ` under the equivalence `F` of Stacks 0BHA. Stacks 0BHL
asserts that, when `X` satisfies the equivalent conditions of Stacks 0BB1, `f` is a sequence of
normalized blowings up at closed points lying over `{x₁, …, xₙ}` if and only if every `gᵢ` is a
sequence of normalized blowings up at closed points lying over `uᵢ`.

## The statement as written is false: normality of `X` is needed

A normalized blowing up of `X` at a point over `x_k` normalizes all of `X`, so its base change to
a neighbourhood `Uᵢ`, `i ≠ k`, is the normalization of `Uᵢ` rather than an isomorphism, and the
two sides of the equivalence are no longer comparable. Concretely, let `k` be a field and let
`R = k + (x, y)² ⊂ k[x, y]`, a Noetherian ring whose normalization is `k[x, y]`, the map
`𝔸² = Spec k[x, y] ⟶ Spec R` being an isomorphism away from the maximal ideal `m = (x, y)²`.

* *"Only if" fails.* Take `X = 𝔸¹ ⊔ Spec R`, `x₁ = 0 ∈ 𝔸¹`, `x₂ = m`, `U₁ = 𝔸¹`, `U₂ = Spec R`, and
  `f = id ⊔ ν : 𝔸¹ ⊔ 𝔸² ⟶ X`. The blowing up of `X` at `x₁` is an isomorphism (`x₁` is a Cartier
  divisor on `𝔸¹` and misses `Spec R`), so the normalized blowing up of `X` at `x₁` is the
  normalization `𝔸¹ ⊔ 𝔸² ⟶ X`, which is `f`: the left side holds. But `g₂ = ν` is no sequence of
  normalized blowings up at points over `m`: it is not an isomorphism, the normalized blowing up
  of `Spec R` at `m` is `Bl₀ 𝔸²` (the Rees algebras of `m ⊂ R` and of `(x, y)² ⊂ k[x, y]` agree in
  positive degrees), whose fibre over `m` is a projective line, and further normalized blowings
  up at closed points of normal integral surfaces are surjective, whereas `ν` has a single point
  over `m`.
* *"If" fails.* Take `X = 𝔸² ⊔ Spec R` with the analogous data and `f = b ⊔ id`, `b` the blowing
  up of `𝔸²` at the origin. Then `g₁ = b` and `g₂ = id` are sequences of normalized blowings up
  at points over the `uᵢ`, but `f` is not one, since it is not an isomorphism and the source of a
  normalized blowing up is normal.

The algebraic part of these counterexamples — that `R` is a domain which is not integrally
closed and over which `k[x, y]` is integral — is formalized in
`StacksFrontier/RingTheory/PinchedPlane.lean` (`MvPolynomial.not_isIntegrallyClosed_noLinearTerms`,
`MvPolynomial.isIntegral_noLinearTerms`); the computation of the normalized blowing up of `Spec R`
and of the corresponding algebraic spaces is not.

Both uses of Stacks 0BHL in the source (Stacks 0BHM and Stacks 0BHY) apply it to a normal `X`.
The statement is therefore formalized here for normal `X`, which is the only change.

## Main results

* `ClosedPointNeighborhoods.nonempty_globalNormalizedBlowupFactorization_iff`: **Stacks 0BHL**
  for normal `X`.

## Implementation notes

The "only if" direction restricts a sequence of normalized blowings up of `X` to each
neighbourhood. The "if" direction lifts the given sequences one neighbourhood at a time and one
normalized blowing up at a time, keeping the lifted space normal, decent, satisfying the
conditions of Stacks 0BB1 and unchanged over `X ∖ {x₁, …, xₙ}`; the resulting space over `X` has
the same restrictions as `f` under `F`, so it is isomorphic to `Y` over `X` by the full
faithfulness of `F` (Stacks 0BHB).

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The points of an isomorphism of presheaves: the preimage of a point under the map of points
of an isomorphism is the image of the point under the inverse. -/
theorem preimage_pointsMap_hom_singleton {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (z : points B S hS G) :
    pointsMap B S hS F e.hom ⁻¹' {z} = {pointsMap B S hS G e.inv z} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    rw [← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id]
    rfl
  · rintro rfl
    rw [← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id]
    rfl

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The invariant of the lifting: the top of a tower of normalized blowings up of `X` at closed
points over `{x₁, …, xₙ}` is normal, decent, satisfies the conditions of Stacks 0BB1, and is
unchanged over `X ∖ {x₁, …, xₙ}`. -/
def IsGoodTower {Z : AlgebraicSpaces B S hS} (σ : NormalizedBlowupTower B S hS D.space Z) :
    Prop :=
  Space.IsNormal B S hS Z.obj ∧ IsDecentSpace B S hS Z.obj ∧
    HasLocallyFiniteIrreducibleComponents B S hS Z.obj ∧
    IsIso (pullback.snd σ.proj.hom D.openAwayFromPoints.ι) ∧ σ.CentersOver (Set.range D.point)

/-- **Lifting a sequence of normalized blowings up of the `i`th neighbourhood.** If a good tower
`σ₀` over `X` restricts to an isomorphism over `Uᵢ`, a tower `τ` of normalized blowings up of `Uᵢ`
at closed points over `uᵢ` lifts to a good tower `σ` over `X` whose restriction to `Uᵢ` is `τ` and
whose restrictions to the other neighbourhoods are those of `σ₀`. -/
theorem exists_isGoodTower_lift (i : Fin n) :
    ∀ {Zτ : AlgebraicSpaces B S hS} (τ : NormalizedBlowupTower B S hS (D.neighborhoodSpace i) Zτ),
      τ.CentersOver {D.neighborhoodPoint i} →
      ∀ {Z₀ : AlgebraicSpaces B S hS} (σ₀ : NormalizedBlowupTower B S hS D.space Z₀),
        D.IsGoodTower σ₀ → IsIso (D.restrictionHom i σ₀.proj) →
        ∃ (Z : AlgebraicSpaces B S hS) (σ : NormalizedBlowupTower B S hS D.space Z),
          D.IsGoodTower σ ∧
          (∃ e : AlgebraicSpaces.fiberProduct B S hS σ.proj (D.toSpaceHom i) ≅ Zτ,
            e.hom ≫ τ.proj = D.restrictionHom i σ.proj) ∧
          ∀ k, k ≠ i → ∃ e : AlgebraicSpaces.fiberProduct B S hS σ.proj (D.toSpaceHom k) ≅
              AlgebraicSpaces.fiberProduct B S hS σ₀.proj (D.toSpaceHom k),
            e.hom ≫ D.restrictionHom k σ₀.proj = D.restrictionHom k σ.proj
  | _, .base e, _, _, σ₀, hσ₀, hiso => by
      refine ⟨_, σ₀, hσ₀, ⟨asIso (D.restrictionHom i σ₀.proj) ≪≫ e.symm, ?_⟩,
        fun k _ => ⟨Iso.refl _, Category.id_comp _⟩⟩
      simp
  | _, .step τ₀ hZ hZfin c zc hzc hc, hcent, _, σ₀, hσ₀, hiso => by
      obtain ⟨hcent₀, hzcu⟩ := hcent
      obtain ⟨Z₁, σ₁, ⟨hn₁, hd₁, hf₁, hCX₁, hσ₁⟩, ⟨e₁, he₁⟩, hk₁⟩ :=
        exists_isGoodTower_lift i τ₀ hcent₀ σ₀ hσ₀ hiso
      have hfib : pointsMap B S hS _ e₁.hom.hom ⁻¹' {zc} = {pointsMap B S hS _ e₁.inv.hom zc} :=
        preimage_pointsMap_hom_singleton ((ObjectProperty.ι _).mapIso e₁) zc
      have ht : IsClosed ({pointsMap B S hS _ e₁.inv.hom zc} : Set (points B S hS
          (AlgebraicSpaces.fiberProduct B S hS σ₁.proj (D.toSpaceHom i)).obj)) := by
        have h := hzc.preimage (continuous_pointsMap B S hS e₁.hom.hom)
        rwa [hfib] at h
      have htu : pointsMap B S hS _ (D.restrictionHom i σ₁.proj).hom
          (pointsMap B S hS _ e₁.inv.hom zc) = D.neighborhoodPoint i := by
        have h1 : pointsMap B S hS _ (e₁.inv ≫ e₁.hom ≫ τ₀.proj).hom zc =
            pointsMap B S hS _ τ₀.proj.hom zc := by rw [Iso.inv_hom_id_assoc]
        rw [← he₁]
        simpa only [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp_apply] using
          h1.trans hzcu
      have he₁e : IsEtale B S hS e₁.hom.hom :=
        isEtale_of_iso B S hS ((ObjectProperty.ι _).mapIso e₁)
      have hq := isNormalizationOfBlowupAtClosedPoint_fiberProduct_of_isEtale he₁e ht hfib
        hc.isNormalizationOfBlowupAtClosedPoint
      obtain ⟨G', b, hb, hn, hd, hf, hCX, ⟨e', he'⟩, hk'⟩ :=
        D.exists_isNormalizedBlowupAtClosedPoint_lift i σ₁.proj ht htu hCX₁ hn₁ hd₁ hf₁ hq
      refine ⟨G', .step σ₁ hd₁ hf₁ b _ _ hb,
        ⟨hn, hd, hf, hCX, hσ₁, ⟨i, (D.pointsMap_restrictionFst_eq_point i σ₁.proj htu).symm⟩⟩,
        ?_, fun k hk => ?_⟩
      · have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS e₁.hom c
        have := sq.isIso_snd_of_isIso
        refine ⟨e' ≪≫ asIso (ObjectProperty.homMk (pullback.snd e₁.hom.hom c.hom) :
          AlgebraicSpaces.fiberProduct B S hS e₁.hom c ⟶ _), ?_⟩
        simp only [Iso.trans_hom, asIso_hom, NormalizedBlowupTower.proj_step, Category.assoc]
        rw [← reassoc_of% sq.w, he₁, ← he']
      · obtain ⟨e₂, he₂⟩ := hk' k hk
        obtain ⟨e₃, he₃⟩ := hk₁ k hk
        change ∃ e : AlgebraicSpaces.fiberProduct B S hS (b ≫ σ₁.proj) (D.toSpaceHom k) ≅ _,
          e.hom ≫ D.restrictionHom k σ₀.proj = D.restrictionHom k (b ≫ σ₁.proj)
        exact ⟨e₂ ≪≫ e₃, by rw [Iso.trans_hom, Category.assoc, he₃, he₂]⟩

/-- **Lifting the sequences of all the neighbourhoods.** Given towers `τₖ` of normalized blowings
up of the neighbourhoods at closed points over the `uₖ`, there is, for every `m`, a good tower
over `X` whose restriction to `Uₖ` is `τₖ` for `k < m` and an isomorphism for `k ≥ m`. -/
theorem exists_isGoodTower_restrictions (hXn : Space.IsNormal B S hS D.space.obj)
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj)
    (Zτ : Fin n → AlgebraicSpaces B S hS)
    (τ : ∀ k, NormalizedBlowupTower B S hS (D.neighborhoodSpace k) (Zτ k))
    (hτ : ∀ k, (τ k).CentersOver {D.neighborhoodPoint k}) :
    ∀ m : ℕ, ∃ (Z : AlgebraicSpaces B S hS) (σ : NormalizedBlowupTower B S hS D.space Z),
      D.IsGoodTower σ ∧
      (∀ k : Fin n, k.val < m →
        ∃ e : AlgebraicSpaces.fiberProduct B S hS σ.proj (D.toSpaceHom k) ≅ Zτ k,
          e.hom ≫ (τ k).proj = D.restrictionHom k σ.proj) ∧
      ∀ k : Fin n, m ≤ k.val → IsIso (D.restrictionHom k σ.proj)
  | 0 => by
      refine ⟨D.space, .base (Iso.refl _), ⟨hXn, D.decent, hXfin, ?_, trivial⟩,
        fun k hk => absurd hk (Nat.not_lt_zero _), fun k _ => ?_⟩
      · change IsIso (pullback.snd (𝟙 D.space.obj) D.openAwayFromPoints.ι)
        infer_instance
      · exact (AlgebraicSpaces.isPullback_fiberProduct B S hS (Iso.refl D.space).hom
          (D.toSpaceHom k)).isIso_snd_of_isIso
  | m + 1 => by
      obtain ⟨Z, σ, hσ, h₁, h₂⟩ := exists_isGoodTower_restrictions hXn hXfin Zτ τ hτ m
      by_cases hm : m < n
      · set i : Fin n := ⟨m, hm⟩
        obtain ⟨Z', σ', hσ', ⟨e, he⟩, hk⟩ :=
          D.exists_isGoodTower_lift i (τ i) (hτ i) σ hσ (h₂ i le_rfl)
        refine ⟨Z', σ', hσ', fun k hk' => ?_, fun k hk' => ?_⟩
        · by_cases hki : k = i
          · subst hki
            exact ⟨e, he⟩
          · have hklt : k.val < m :=
              (Nat.lt_succ_iff_lt_or_eq.1 hk').resolve_right fun h => hki (Fin.ext h)
            obtain ⟨e₀, he₀⟩ := h₁ k hklt
            obtain ⟨e₁, he₁⟩ := hk k hki
            exact ⟨e₁ ≪≫ e₀, by rw [Iso.trans_hom, Category.assoc, he₀, he₁]⟩
        · have hki : k ≠ i := fun h => by
            rw [h] at hk'
            exact absurd hk' (Nat.not_succ_le_self m)
          obtain ⟨e₁, he₁⟩ := hk k hki
          have := h₂ k (Nat.le_of_succ_le hk')
          rw [← he₁]
          infer_instance
      · exact ⟨Z, σ, hσ, fun k hk' => h₁ k (by omega), fun k hk' => absurd k.isLt (by omega)⟩

/-- An isomorphism of modifications of `T` gives an isomorphism of the underlying algebraic spaces
commuting with the structure morphisms to `T`. -/
private theorem exists_iso_homMk_of_iso {T : AlgebraicSpaces B S hS} {W₀ : Subfunctor T.obj}
    {M M' : Modification B S hS W₀} (e : M ≅ M') :
    ∃ E : (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ≅ ⟨M'.obj.left, M'.property.1⟩,
      E.hom ≫ (ObjectProperty.homMk M'.obj.hom : (⟨M'.obj.left, M'.property.1⟩ :
        AlgebraicSpaces B S hS) ⟶ T) = ObjectProperty.homMk M.obj.hom :=
  ⟨ObjectProperty.isoMk _ ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso e),
    ObjectProperty.hom_ext _ (Over.w e.hom.hom)⟩

/-- The base change to the `i`th neighbourhood of the morphism underlying a modification `M`,
identified with the morphism underlying the `i`th component of an object `N` corresponding to
`M` under the functor `F` of Stacks 0BHA. -/
theorem exists_iso_restrictionHom_of_iso {M : D.modificationsAwayFromPoints}
    {N : ∀ i, D.modificationsAt i} (e : D.restrictionFunctor.obj M ≅ N) (i : Fin n) :
    ∃ E : AlgebraicSpaces.fiberProduct B S hS
        (ObjectProperty.homMk M.obj.hom : (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶
          D.space) (D.toSpaceHom i) ≅ ⟨(N i).obj.left, (N i).property.1⟩,
      E.hom ≫ (ObjectProperty.homMk (N i).obj.hom : (⟨(N i).obj.left, (N i).property.1⟩ :
          AlgebraicSpaces B S hS) ⟶ D.neighborhoodSpace i) =
        D.restrictionHom i (ObjectProperty.homMk M.obj.hom :
          (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space) :=
  exists_iso_homMk_of_iso (Pi.isoApp e i)

/-- **Stacks 0BHL, for normal `X`.** Let `X, xᵢ, Uᵢ ⟶ X, uᵢ` be as in Stacks 0BHA and let
`f : Y ⟶ X` correspond to `gᵢ : Yᵢ ⟶ Uᵢ` under the functor `F` of Stacks 0BHA. Assume that `X`
satisfies the equivalent conditions of Stacks 0BB1 and that `X` is normal. Then `f` factors as
`Y = Zₘ ⟶ … ⟶ Z₁ ⟶ Z₀ = X` with each `Z_{j+1} ⟶ Z_j` the normalized blowing up of `Z_j` at a
closed point over `{x₁, …, xₙ}` if and only if each `gᵢ` factors as
`Yᵢ = Z_{i, mᵢ} ⟶ … ⟶ Z_{i, 0} = Uᵢ` with each step the normalized blowing up at a closed point
over `uᵢ`.

The normality of `X` is not in the source, but the statement is false without it; see the module
documentation for a counterexample to each direction. -/
@[stacks 0BHL "corrected (erratum): with X normal; false as written without it, the normalized \
blowup normalizes the whole space (counterexamples to both directions in the module \
documentation); otherwise the full statement, under the source's hypotheses"]
theorem nonempty_globalNormalizedBlowupFactorization_iff
    (hXfin : HasLocallyFiniteIrreducibleComponents B S hS D.space.obj)
    (hXn : Space.IsNormal B S hS D.space.obj) (M : D.modificationsAwayFromPoints)
    (N : ∀ i, D.modificationsAt i) (e : D.restrictionFunctor.obj M ≅ N) :
    Nonempty (D.GlobalNormalizedBlowupFactorization (ObjectProperty.homMk M.obj.hom :
        (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space)) ↔
      ∀ i, Nonempty (D.LocalNormalizedBlowupFactorization i (ObjectProperty.homMk (N i).obj.hom :
        (⟨(N i).obj.left, (N i).property.1⟩ : AlgebraicSpaces B S hS) ⟶
          D.neighborhoodSpace i)) := by
  set f : (⟨M.obj.left, M.property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.space :=
    ObjectProperty.homMk M.obj.hom
  constructor
  · rintro ⟨F⟩ i
    obtain ⟨-, hloc⟩ := D.isNormal_and_nonempty_localNormalizedBlowupFactorization hXn F.tower
      F.centersOver
    obtain ⟨E, hE⟩ := D.exists_iso_restrictionHom_of_iso e i
    refine D.nonempty_localNormalizedBlowupFactorization_of_isPullback i
      (ψ := E.inv ≫ D.restrictionFst i f ≫ F.iso.hom) ?_ (hloc i)
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS f (D.toSpaceHom i)).of_iso E F.iso
      (Iso.refl _) (Iso.refl _) (by simp) (by rw [Iso.refl_hom, Category.comp_id, hE])
      (by rw [Iso.refl_hom, Category.comp_id, F.iso_proj]) (by simp)
  · intro h
    let F := fun i => (h i).some
    obtain ⟨Z, σ, hσ, hall, -⟩ := D.exists_isGoodTower_restrictions hXn hXfin (fun i => (F i).top)
      (fun i => (F i).tower) (fun i => (F i).centersOver) n
    have hcomp : ∀ i, ∃ E : AlgebraicSpaces.fiberProduct B S hS σ.proj (D.toSpaceHom i) ≅
        ⟨(N i).obj.left, (N i).property.1⟩,
        E.hom ≫ (ObjectProperty.homMk (N i).obj.hom : (⟨(N i).obj.left, (N i).property.1⟩ :
          AlgebraicSpaces B S hS) ⟶ D.neighborhoodSpace i) = D.restrictionHom i σ.proj := by
      intro i
      obtain ⟨E, hE⟩ := hall i i.isLt
      refine ⟨E ≪≫ (F i).iso.symm, ?_⟩
      have h1 : (F i).iso.inv ≫ (ObjectProperty.homMk (N i).obj.hom :
          (⟨(N i).obj.left, (N i).property.1⟩ : AlgebraicSpaces B S hS) ⟶ D.neighborhoodSpace i) =
            (F i).tower.proj :=
        (Iso.inv_comp_eq _).2 (F i).iso_proj.symm
      rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, h1, hE]
    choose E hE using hcomp
    obtain ⟨-, -, -, hσCX, hσc⟩ := hσ
    let Mσ : D.modificationsAwayFromPoints := ⟨Over.mk σ.proj.hom, Z.property, hσCX⟩
    let Φ : D.restrictionFunctor.obj Mσ ≅ N := Pi.isoMk fun i =>
      ObjectProperty.isoMk _ (Over.isoMk ((ObjectProperty.ι _).mapIso (E i))
        (congrArg (fun m => m.hom) (hE i)))
    have : D.restrictionFunctor.IsEquivalence := D.isEquivalence_restrictionFunctor
    let Ψ : Mσ ≅ M := D.restrictionFunctor.preimageIso (Φ ≪≫ e.symm)
    obtain ⟨E', hE'⟩ := exists_iso_homMk_of_iso Ψ.symm
    exact ⟨⟨Z, σ, hσc, E', hE'⟩⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
