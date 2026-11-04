module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation

/-!
# Approximating an isomorphism of completed local rings over a second base

Let `X → S` and `Y → T` be morphisms locally of finite type with `S` locally Noetherian and
`𝒪_{S, s}` a G-ring, let `(V, v)` be an étale neighbourhood of `(S, s)` with a morphism
`τ : V ⟶ T`, and let `(y, v)` be a point of `Y ×_{T, τ} V` over `v`. Given a ring isomorphism
`Φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y ×_{T, τ} V, (y, v)}` compatible with the maps from `𝒪_{S, s}`, there is
a diagram
```
X ← X ×_S V ←—f— W —→ Y ×_{T, τ} V → Y
↓               ↓                     ↓
S ←——————————— V ———τ——————————————→ T
```
with `(W, w)` an elementary étale neighbourhood of `(Y ×_{T, τ} V, (y, v))` and `f` étale, such
that `Φ` followed by the completion map of `W` agrees modulo `𝔪_w ^ N` with the map induced by
`W → X`.

The isomorphism is taken at the completed local ring of the base change along `τ`, not along a
map `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` as in Tag 0CB1; the two completed local rings are not isomorphic
in general, so this is a variant of Tag 0CB1.

## Main results

* `StacksDraft.ArtinApproximation.exists_etale_relativeApproximation_of_adicCompletion_ringEquiv`:
  for an isomorphism `Φ` of completions over the base change along `τ`, an elementary étale
  neighbourhood `(W, w)` and a morphism `F : W ⟶ X` over `S` with `F w = x`, inducing an étale
  `W ⟶ X ×_S V`, such that `Φ` and `F` agree on completions modulo `𝔪_w ^ N`.

## References

* [Stacks Project, Tag 0CB1](https://stacks.math.columbia.edu/tag/0CB1)
* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- A local homomorphism maps the `n`-th power of the maximal ideal into that of the target. -/
private theorem map_maximalIdeal_pow_le {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (n : ℕ) :
    Ideal.map f (maximalIdeal R ^ n) ≤ maximalIdeal S ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le f) n

/-- The extension of `𝔪 ^ n` to the completion of a Noetherian local ring is the `n`-th power of
the maximal ideal of the completion. -/
private theorem map_algebraMap_maximalIdeal_pow {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R ^ n) =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
  rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map]

/-- Let `p : B → C` and `r : A → C` be local homomorphisms of Noetherian local rings and let
`Φ : A^∧ ≃ B^∧` be an isomorphism of completions whose composite with the completion `p^∧` of `p`
is bijective. If `p^∧ ∘ Φ` and `r^∧` agree modulo `𝔪_C ^ M` on the image of `A`, with `M ≥ 2`,
then `r^∧` is bijective. -/
private theorem bijective_adicCompletionMap_of_congr {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    (p : B →+* C) [IsLocalHom p] (r : A →+* C) [IsLocalHom r]
    (Φ : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B)
    (hp : Function.Bijective
      (adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p)))
    (M : ℕ) (h2M : 2 ≤ M)
    (hbase : ∀ a : A,
      adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p)
          (Φ (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) -
        algebraMap C (AdicCompletion (maximalIdeal C) C) (r a) ∈
          Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M)) :
    Function.Bijective
      (adicCompletionMap r (maximalIdeal A) (maximalIdeal C) (map_maximalIdeal_le r)) := by
  set pC := adicCompletionMap p (maximalIdeal B) (maximalIdeal C) (map_maximalIdeal_le p)
    with hpC
  set qC := adicCompletionMap r (maximalIdeal A) (maximalIdeal C) (map_maximalIdeal_le r)
    with hqC
  have hpCloc : IsLocalHom pC := AdicCompletion.isLocalHom_adicCompletionMap p
  have hrbase : (adicCompletionMap r (maximalIdeal A) (maximalIdeal C)
        (map_maximalIdeal_le r)).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap C (AdicCompletion (maximalIdeal C) C)).comp r :=
    adicCompletionMap_comp_algebraMap r (maximalIdeal A) (maximalIdeal C)
      (map_maximalIdeal_le r)
  have hqCbase : ∀ a : A, qC (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap C (AdicCompletion (maximalIdeal C) C) (r a) := by
    intro a
    rw [hqC]
    exact RingHom.congr_fun hrbase a
  have h₂ : Ideal.map qC (Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A))
      (maximalIdeal A ^ M)) ≤
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M) := by
    rw [Ideal.map_map, hqC, hrbase, ← Ideal.map_map]
    exact Ideal.map_mono (map_maximalIdeal_pow_le r M)
  have h₁ : Ideal.map (pC.comp Φ.toRingHom) (Ideal.map
      (algebraMap A (AdicCompletion (maximalIdeal A) A)) (maximalIdeal A ^ M)) ≤
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C)) (maximalIdeal C ^ M) :=
    calc Ideal.map (pC.comp Φ.toRingHom)
            (Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) (maximalIdeal A ^ M))
        = Ideal.map pC (Ideal.map Φ.toRingHom
            (Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A))
              (maximalIdeal A ^ M))) := (Ideal.map_map _ _).symm
      _ = Ideal.map pC (Ideal.map Φ.toRingHom
            (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ M)) := by
            rw [map_algebraMap_maximalIdeal_pow]
      _ = Ideal.map pC (maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ M) := by
            rw [Ideal.map_pow, map_maximalIdeal_of_surjective Φ.toRingHom Φ.surjective]
      _ ≤ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ M := map_maximalIdeal_pow_le pC M
      _ = _ := (map_algebraMap_maximalIdeal_pow M).symm
  have hcong : ∀ z : AdicCompletion (maximalIdeal A) A, pC (Φ z) - qC z ∈
      Ideal.map (algebraMap C (AdicCompletion (maximalIdeal C) C))
        (maximalIdeal C ^ M) := fun z =>
    sub_mem_of_apply_algebraMap_sub_mem (maximalIdeal A) (IsNoetherian.noetherian _) M _
      (pC.comp Φ.toRingHom) qC (fun a => by rw [RingHom.comp_apply, hqCbase a]; exact hbase a)
      h₁ h₂ z
  have hτbij : Function.Bijective (pC.comp Φ.toRingHom) := by
    rw [RingHom.coe_comp]
    exact hp.comp Φ.bijective
  set τe := RingEquiv.ofBijective (pC.comp Φ.toRingHom) hτbij with hτe
  have hτeapp : ∀ z, τe z = pC (Φ z) := fun z => rfl
  have hψ : ∀ w : AdicCompletion (maximalIdeal A) A, (τe.symm.toRingHom.comp qC) w - w ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ 2 := by
    intro w
    have hw : (τe.symm.toRingHom.comp qC) w - w = τe.symm (qC w - τe w) := by
      rw [map_sub, τe.symm_apply_apply]
      rfl
    have hmem : qC w - τe w ∈ maximalIdeal (AdicCompletion (maximalIdeal C) C) ^ 2 := by
      have hz := hcong w
      rw [map_algebraMap_maximalIdeal_pow] at hz
      have hneg : qC w - τe w = -(pC (Φ w) - qC w) := by rw [hτeapp w]; ring
      rw [hneg]
      exact Ideal.pow_le_pow_right h2M (neg_mem hz)
    rw [hw]
    have : IsLocalHom τe.symm.toRingHom :=
      isLocalHom_of_leftInverse τe.toRingHom τe.apply_symm_apply
    exact map_maximalIdeal_pow_le τe.symm.toRingHom 2 (Ideal.mem_map_of_mem _ hmem)
  have hψbij : Function.Bijective (τe.symm.toRingHom.comp qC) :=
    bijective_of_sub_id_mem_maximalIdeal_sq _ _ hψ
  have hfun : ⇑qC = ⇑(pC.comp Φ.toRingHom) ∘ ⇑(τe.symm.toRingHom.comp qC) :=
    funext fun w => (τe.apply_symm_apply (qC w)).symm
  rw [hfun]
  exact hτbij.comp hψbij

/-- If `f` is étale at `x` and `f x = y`, then the local homomorphism `f.stalkHomAt hy` is
étale. -/
private theorem isEtaleLocalHom_stalkHomAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Y} (hy : f x = y)
    (hEt : IsEtaleAt f x) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    RingHom.IsEtaleLocalHom (f.stalkHomAt hy) := by
  subst hy
  simpa [Scheme.Hom.stalkHomAt] using hEt

/-- For `f` locally of finite type and `f x = y`, the local homomorphism `f.stalkHomAt hy` is
essentially of finite type. -/
private theorem essFiniteType_stalkHomAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [LocallyOfFiniteType f] {y : Y} (hy : f x = y) :
    RingHom.EssFiniteType (f.stalkHomAt hy) := by
  subst hy
  simpa [Scheme.Hom.stalkHomAt] using LocallyOfFiniteType.stalkMap f x

/-- If `f x = y` and the local homomorphism `f.stalkHomAt hy` is étale, then `f` is étale
at `x`. -/
private theorem isEtaleAt_of_isEtaleLocalHom_stalkHomAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y : Y} (hy : f x = y)
    (h : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      RingHom.IsEtaleLocalHom (f.stalkHomAt hy)) :
    IsEtaleAt f x := by
  subst hy
  simpa [Scheme.Hom.stalkHomAt] using h

/-- The completion of the structure map of a composite étale neighbourhood factors as the
completion of the second stage after the completion of the first. -/
private theorem completionMap_comp_of_comp {X : Scheme.{u}} {x : X}
    (U : EtaleNeighborhood X x) (W : EtaleNeighborhood U.scheme U.point) :
    (U.comp W).completionMap =
      (adicCompletionMap W.stalkHom (maximalIdeal (U.scheme.presheaf.stalk U.point))
        (maximalIdeal (W.scheme.presheaf.stalk W.point)) (map_maximalIdeal_le _)).comp
        U.completionMap := by
  rw [EtaleNeighborhood.completionMap, EtaleNeighborhood.completionMap,
    Scheme.Hom.completionMapAt, Scheme.Hom.completionMapAt,
    adicCompletionMap_comp_adicCompletionMap]
  · exact adicCompletionMap_congr _ _ _ _ (EtaleNeighborhood.stalkHom_comp U W)
  · rw [← Ideal.map_map]
    exact (Ideal.map_mono (map_maximalIdeal_le U.stalkHom)).trans
      (map_maximalIdeal_le W.stalkHom)

/-- Let `W₀` be an elementary étale neighbourhood of `(Z, z)`, let `F : W₀ ⟶ X` carry the
distinguished point to `x`, and let `Φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Z, z}` be an isomorphism of
completions. If the map of completions induced by `F` agrees, on the image of `𝒪_{X, x}`, with
`Φ` followed by the completion map of `W₀` modulo `𝔪 ^ M` for some `M ≥ 2`, then `F` is étale at
the distinguished point. -/
private theorem etaleAt_of_adicCompletion_ringEquiv_congr
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {z : Z}
    (W₀ : EtaleNeighborhood Z z) (hW₀ : W₀.IsElementary) {x : X}
    (F : W₀.scheme ⟶ X) (hF : F W₀.point = x) [LocallyOfFiniteType F]
    (Φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
    (M : ℕ) (h2M : 2 ≤ M)
    (hcong : ∀ a : X.presheaf.stalk x,
      W₀.completionMap (Φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a)) -
          algebraMap (W₀.scheme.presheaf.stalk W₀.point)
            (AdicCompletion (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
              (W₀.scheme.presheaf.stalk W₀.point)) (F.stalkHomAt hF a) ∈
        Ideal.map
          (algebraMap (W₀.scheme.presheaf.stalk W₀.point)
            (AdicCompletion (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
              (W₀.scheme.presheaf.stalk W₀.point)))
          (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point) ^ M)) :
    EtaleAt F W₀.point := by
  let : IsLocallyNoetherian W₀.scheme := LocallyOfFiniteType.isLocallyNoetherian W₀.toBase
  have hpκ : Function.Bijective (ResidueField.map W₀.stalkHom) :=
    (bijective_residueField_map_stalkHomAt_iff W₀.toBase W₀.point W₀.map_point).mpr
      ((EtaleNeighborhood.isElementary_iff W₀).mp hW₀)
  have hpEt : RingHom.IsEtaleLocalHom W₀.stalkHom :=
    isEtaleLocalHom_stalkHomAt W₀.toBase W₀.point W₀.map_point
      ((etale_iff_forall_isEtaleAt W₀.toBase).mp inferInstance W₀.point)
  have hpCbij := RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom W₀.stalkHom hpEt hpκ
  have hFbij := bijective_adicCompletionMap_of_congr W₀.stalkHom (F.stalkHomAt hF) Φ hpCbij
    M h2M hcong
  exact (isEtaleAt_iff_etaleAt F W₀.point).mp
    (isEtaleAt_of_isEtaleLocalHom_stalkHomAt F W₀.point hF
      (RingHom.isEtaleLocalHom_of_bijective_adicCompletionMap _
        (essFiniteType_stalkHomAt F W₀.point hF) hFbij))

/-- A morphism `F` out of an étale neighbourhood `W₀` of `(Z, z)` which is étale at the
distinguished point becomes étale after restricting `W₀` to an affine open neighbourhood, and the
congruence modulo `𝔪 ^ M` which `F` satisfies restricts to a congruence modulo `𝔪 ^ N` for
`N ≤ M`. -/
private theorem exists_etale_elementary_restriction
    {X Z : Scheme.{u}} [IsLocallyNoetherian Z] {z : Z}
    (W₀ : EtaleNeighborhood Z z) {x : X} (F : W₀.scheme ⟶ X) (hF : F W₀.point = x)
    (hFat : EtaleAt F W₀.point)
    (Φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
    (N M : ℕ) (hNM : N ≤ M)
    (hcong : ∀ a : X.presheaf.stalk x,
      W₀.completionMap (Φ (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a)) -
          algebraMap (W₀.scheme.presheaf.stalk W₀.point)
            (AdicCompletion (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
              (W₀.scheme.presheaf.stalk W₀.point)) (F.stalkHomAt hF a) ∈
        Ideal.map
          (algebraMap (W₀.scheme.presheaf.stalk W₀.point)
            (AdicCompletion (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
              (W₀.scheme.presheaf.stalk W₀.point)))
          (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point) ^ M)) :
    ∃ (W' : EtaleNeighborhood W₀.scheme W₀.point)
        (hF' : (W'.toBase ≫ F) (W₀.comp W').point = x),
      W'.IsElementary ∧ Etale (W'.toBase ≫ F) ∧
        ∀ a : X.presheaf.stalk x,
          (W₀.comp W').completionMap (Φ (algebraMap (X.presheaf.stalk x)
                (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a)) -
              algebraMap ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point)
                (AdicCompletion
                  (maximalIdeal ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point))
                  ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point))
                ((W'.toBase ≫ F).stalkHomAt hF' a) ∈
            Ideal.map
              (algebraMap ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point)
                (AdicCompletion
                  (maximalIdeal ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point))
                  ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point)))
              (maximalIdeal ((W₀.comp W').scheme.presheaf.stalk (W₀.comp W').point) ^ N) := by
  let : IsLocallyNoetherian W₀.scheme := LocallyOfFiniteType.isLocallyNoetherian W₀.toBase
  obtain ⟨O, hOaff, hOmem, hOet⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt F W₀.point hFat
  obtain ⟨W', hW'el, hW'et⟩ : ∃ W' : EtaleNeighborhood W₀.scheme W₀.point,
      W'.IsElementary ∧ Etale (W'.toBase ≫ F) :=
    ⟨EtaleNeighborhood.ofEtale O.ι (⟨W₀.point, hOmem⟩ : O.toScheme),
      EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion O.ι _, hOet⟩
  let : IsLocallyNoetherian W'.scheme := LocallyOfFiniteType.isLocallyNoetherian W'.toBase
  have hF' : (W'.toBase ≫ F) (W₀.comp W').point = x := by
    show F (W'.toBase W'.point) = x
    rw [W'.map_point]; exact hF
  refine ⟨W', hF', hW'el, hW'et, fun a => ?_⟩
  have hstalk : (W'.toBase ≫ F).stalkHomAt hF' a = W'.stalkHom (F.stalkHomAt hF a) :=
    RingHom.congr_fun (Scheme.Hom.stalkHomAt_comp W'.toBase F W'.map_point hF) a
  have key := adicCompletionMap_mem_map_maximalIdeal_pow W'.stalkHom hNM (hcong a)
  rw [map_sub] at key
  have e1 : adicCompletionMap W'.stalkHom
        (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
        (maximalIdeal (W'.scheme.presheaf.stalk W'.point)) (map_maximalIdeal_le _)
        (W₀.completionMap (Φ (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a))) =
      (W₀.comp W').completionMap (Φ (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a)) := by
    rw [completionMap_comp_of_comp]
    rfl
  have e2 : adicCompletionMap W'.stalkHom
        (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
        (maximalIdeal (W'.scheme.presheaf.stalk W'.point)) (map_maximalIdeal_le _)
        (algebraMap (W₀.scheme.presheaf.stalk W₀.point)
          (AdicCompletion (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
            (W₀.scheme.presheaf.stalk W₀.point)) (F.stalkHomAt hF a)) =
      algebraMap (W'.scheme.presheaf.stalk W'.point)
        (AdicCompletion (maximalIdeal (W'.scheme.presheaf.stalk W'.point))
          (W'.scheme.presheaf.stalk W'.point)) ((W'.toBase ≫ F).stalkHomAt hF' a) :=
    (RingHom.congr_fun (adicCompletionMap_comp_algebraMap W'.stalkHom
        (maximalIdeal (W₀.scheme.presheaf.stalk W₀.point))
        (maximalIdeal (W'.scheme.presheaf.stalk W'.point)) (map_maximalIdeal_le _))
        (F.stalkHomAt hF a)).trans
      (congrArg (algebraMap (W'.scheme.presheaf.stalk W'.point)
        (AdicCompletion (maximalIdeal (W'.scheme.presheaf.stalk W'.point))
          (W'.scheme.presheaf.stalk W'.point))) hstalk.symm)
  rw [e1, e2] at key
  exact key

/-- Let `(V, v)` be an étale neighbourhood of `(S, s)` with a morphism `τ : V ⟶ T`, let `(y, v)` be
a point of `Y ×_{T, τ} V` over `v`, and let `Φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y ×_{T, τ} V, (y, v)}` be a ring
isomorphism compatible with the maps from `𝒪_{S, s}`, where `𝒪_{S, s}` is a G-ring. Then there are
an elementary étale neighbourhood `(W, w)` of `(Y ×_{T, τ} V, (y, v))` and a morphism `F : W ⟶ X`
over `S` with `F w = x`, together with an étale `f : W ⟶ X ×_S V` whose components are `F` and
`W → V`, such that `Φ` followed by the map `𝒪^∧_{Y ×_{T, τ} V, (y, v)} → 𝒪^∧_{W, w}` agrees modulo
`𝔪_w ^ N` with the map `𝒪_{X, x} → 𝒪_{W, w}` induced by `F`.

The isomorphism is taken over the base change along `τ`, not along `σ` as in Tag 0CB1, so this
is a variant of that tag. -/
theorem exists_etale_relativeApproximation_of_adicCompletion_ringEquiv
    {S T X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (hG : IsGRing (S.presheaf.stalk (f x)))
    (V : EtaleNeighborhood S (f x)) (τ : V.scheme ⟶ T)
    (yτ : ↥(pullback g τ)) (hyτ : pullback.snd g τ yτ = V.point)
    (N : ℕ) (hN : 1 ≤ N)
    (Φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal ((pullback g τ).presheaf.stalk yτ))
        ((pullback g τ).presheaf.stalk yτ))
    (hΦ : (Φ.toRingHom.comp (algebraMap (X.presheaf.stalk x)
          (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))).comp
          (f.stalkMap x).hom =
      (algebraMap ((pullback g τ).presheaf.stalk yτ)
          (AdicCompletion (maximalIdeal ((pullback g τ).presheaf.stalk yτ))
            ((pullback g τ).presheaf.stalk yτ))).comp
        (((pullback.snd g τ).stalkHomAt hyτ).comp V.stalkHom)) :
    ∃ W : EtaleNeighborhood (pullback g τ) yτ, W.IsElementary ∧
      ∃ (F : W.scheme ⟶ X) (hF : F W.point = x),
        F ≫ f = W.toBase ≫ pullback.snd g τ ≫ V.toBase ∧
        (∃ fW : W.scheme ⟶ pullback f V.toBase, Etale fW ∧
          fW ≫ pullback.fst f V.toBase = F ∧
            fW ≫ pullback.snd f V.toBase = W.toBase ≫ pullback.snd g τ) ∧
        ∀ a : X.presheaf.stalk x,
          W.completionMap (Φ (algebraMap (X.presheaf.stalk x)
                (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a)) -
              algebraMap (W.scheme.presheaf.stalk W.point)
                (AdicCompletion (maximalIdeal (W.scheme.presheaf.stalk W.point))
                  (W.scheme.presheaf.stalk W.point)) (F.stalkHomAt hF a) ∈
            Ideal.map
              (algebraMap (W.scheme.presheaf.stalk W.point)
                (AdicCompletion (maximalIdeal (W.scheme.presheaf.stalk W.point))
                  (W.scheme.presheaf.stalk W.point)))
              (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian V.scheme := LocallyOfFiniteType.isLocallyNoetherian V.toBase
  let : IsLocallyNoetherian ↑(pullback g τ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g τ)
  have hNM : N ≤ max N 2 := le_max_left _ _
  have h2M : 2 ≤ max N 2 := le_max_right _ _
  have hΦloc : IsLocalHom Φ.toRingHom := isLocalHom_of_leftInverse Φ.symm.toRingHom Φ.left_inv
  have hφloc : IsLocalHom (Φ.toRingHom.comp (algebraMap (X.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))) :=
    inferInstance
  obtain ⟨W₀, hW₀, F, hF, hover, -, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_relativeApproximation f g x hG V τ yτ hyτ
      (max N 2) (hN.trans hNM) _ hφloc hΦ
  let : IsLocallyNoetherian W₀.scheme := LocallyOfFiniteType.isLocallyNoetherian W₀.toBase
  have hFcomp : LocallyOfFiniteType (F ≫ f) := by rw [hover]; infer_instance
  have hFft : LocallyOfFiniteType F := locallyOfFiniteType_of_comp F f
  have hFat : EtaleAt F W₀.point :=
    etaleAt_of_adicCompletion_ringEquiv_congr W₀ hW₀ F hF Φ (max N 2) h2M hcong
  obtain ⟨W', hF', hW'el, hW'et, hcong'⟩ :=
    exists_etale_elementary_restriction W₀ F hF hFat Φ N (max N 2) hNM hcong
  have hover' : (W'.toBase ≫ F) ≫ f =
      (W₀.comp W').toBase ≫ pullback.snd g τ ≫ V.toBase := by
    show (W'.toBase ≫ F) ≫ f = (W'.toBase ≫ W₀.toBase) ≫ pullback.snd g τ ≫ V.toBase
    rw [Category.assoc, Category.assoc, hover]
  have hcomm' : (W'.toBase ≫ F) ≫ f =
      ((W₀.comp W').toBase ≫ pullback.snd g τ) ≫ V.toBase := by
    rw [hover', Category.assoc]
  exact ⟨W₀.comp W', EtaleNeighborhood.IsElementary.comp hW₀ hW'el, W'.toBase ≫ F, hF', hover',
    ⟨pullback.lift (W'.toBase ≫ F) ((W₀.comp W').toBase ≫ pullback.snd g τ) hcomm',
      @etale_of_etale_over _ _ X _ (W'.toBase ≫ F) (pullback.fst f V.toBase)
        (pullback.lift_fst _ _ hcomm') hW'et inferInstance,
      pullback.lift_fst _ _ hcomm', pullback.lift_snd _ _ hcomm'⟩, hcong'⟩

end StacksDraft.ArtinApproximation

end
