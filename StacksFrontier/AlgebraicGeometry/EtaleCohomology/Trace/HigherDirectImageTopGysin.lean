module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseBiprod
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopRealizableInput
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# The Gysin map of the top higher direct image of a family of smooth affine curves

Let `g : U ⟶ W` be smooth of relative dimension one and affine over a finite field, `W`
irreducible, and let `Z ⊆ U` be a closed subscheme finite étale over `W` meeting every connected
component of every geometric fibre. For a lisse ℓ-adic sheaf `H` on `U`, cohomological purity along
`Z` gives the Gysin map

  `γ : (g|_Z)_* (H|_Z)(-1) ⟶ R² g_! H`,

which on the fibre over a geometric point `w̄` is the sum over the points `z̄` of `Z_w̄` of the
projections `H_z̄(-1) ⟶ (H_z̄)_{π₁(U_w̄, z̄)}(-1) = H²_c(U_w̄ ⊇ C_z̄, H)` onto the coinvariants of
the component `C_z̄` through `z̄` (Tag 03VN), hence is surjective. Over a nonempty open of `W`,
where `R² g_! H` is lisse, the kernel `K` of `γ` is lisse, and at a closed point `w` with
`q_w = #κ(w)` and every `m ≥ 1`

  `Tr(π_w ^ m | R² g_! H) + Tr(π_w ^ m | K) = q_w ^ m · Tr(π_w ^ m | (g|_Z)_* (H|_Z))`
  `  = q_w ^ m · ∑_{z ∈ Z_w, d_z ∣ m} d_z · Tr(π_z ^ (m / d_z) | H)`,

with `d_z = [κ(z) : κ(w)]` (the trace formula for a finite étale direct image).

This file states that, for a family `R` in the role of `Rʳ g_!`, as one proposition,
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinInput`, and derives from it the
realizability of `R² g_!`
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopRealizableInput`, Weil II 1.5 and 3.3,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): if `G` is lisse and `ι`-realizable with
witness `G'`, then `R² g_! G' ⊞ K_G ⊞ K_{G'}` is a witness for `R² g_! G`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinInput`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageTopRealizableInput_of_gysinInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Gysin map of `R² g_!` along a divisor finite étale over the base** (cohomological
purity in codimension one and Tag 03VN in families): for `g : U ⟶ W` smooth of relative dimension
one and affine over a finite field `k` of characteristic `p ≠ ℓ`, with `W` irreducible and `U`
nonempty, there are, for each point `w` of `W`, a finite set `Z w` of closed points of `U` over
`w` (the fibre over `w` of a divisor `Z ⊆ U` finite étale over `W`) and degrees `d z` (the residue
degrees `[κ(z) : κ(w)]`), such that for every lisse `G` on `U` there is a nonempty open `V ⊆ W`
over every open `V' ⊆ V` of which, with `g' : U' ⟶ V'` the base change of `g`, the Gysin map
`(g'|_Z)_* (G|_Z)(-1) ⟶ R² g'_! (G|_{U'})` has a lisse kernel `K`: at every closed point `w` of
`V'` and for every `m ≥ 1`, `Tr(π_w ^ m | R² g'_! G) + Tr(π_w ^ m | K)` is
`#κ(w) ^ m · ∑_{z ∈ Z w, d z ∣ m} d z · Tr(π_z ^ (m / d z) | G)`. The divisor and the degrees do
not depend on `G`. -/
def LAdicSheaf.HigherDirectImageTopGysinInput (R : LAdicSheaf.HigherDirectImageFamily B ℓ) :
    Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    Fintype.card k = p ^ n → ℓ ≠ p → ∀ (U W : B.Scheme)
    [IsNoetherian U.1] [IsNoetherian W.1] [IsReduced W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)]
    [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
    [SmoothOfRelativeDimension 1 (B.inclusion.map g)] [IsAffineHom (B.inclusion.map g)]
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW],
    IrreducibleSpace W.1 → Nonempty U.1 →
    ∃ (Z : W.1 → Finset (closedPoints U.1)) (d : closedPoints U.1 → ℕ),
      (∀ (w : W.1) (z : closedPoints U.1), z ∈ Z w → (B.inclusion.map g).base z.1 = w) ∧
      ∀ G : LAdicSheaf.{u, u + 1} B U ℓ, G.IsLisse →
      ∃ (V : B.Scheme) (jV : V ⟶ W), IsOpenImmersion (B.inclusion.map jV) ∧ Nonempty V.1 ∧
        ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] (jV' : V' ⟶ V)
          (jU : U' ⟶ U) (g' : U' ⟶ V') [LocallyOfFiniteType (B.inclusion.map g')]
          [QuasiCompact (B.inclusion.map g')] [IsSeparated (B.inclusion.map g')]
          (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
          IsOpenImmersion (B.inclusion.map jV') →
          IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
            (B.inclusion.map (jV' ≫ jV)) →
          ∀ (fV' : V'.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV'],
          ∃ K : LAdicSheaf.{u, u + 1} B V' ℓ, K.IsLisse ∧
            ∀ (w : closedPoints V'.1) (m : ℕ), 1 ≤ m →
              LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ
                  (R g' jg' (LAdicSheaf.inverseImage jU G) 2) w.1
                  (finite_residueField fV' w.1 w.2) ^ m) +
                LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V' ℓ K w.1
                  (finite_residueField fV' w.1 w.2) ^ m) =
              (Nat.card (V'.1.residueField w.1) : ℚ_[ℓ]) ^ m *
                ∑ z ∈ Z ((B.inclusion.map (jV' ≫ jV)).base w.1),
                  if d z ∣ m then (d z : ℚ_[ℓ]) * LinearMap.trace ℚ_[ℓ] _
                    (LAdicSheaf.rationalStalkFrobenius B U ℓ G z.1
                      (finite_residueField (B.inclusion.map g ≫ fW) z.1 z.2) ^ (m / d z))
                  else 0

/-- If `a + b` and `a' + b'` are `q ^ m · ∑_{z ∈ Z, d z ∣ m} d z · t z (m / d z)` and the same sum
for `t'`, and every `t z e + t' z e` with `e ≥ 1` is real along `ι`, then so is
`a + (a' + (b + b'))`. -/
private theorem map_trace_add_mem_range_of_gysin (ι : ℚ_[ℓ] →+* ℂ) {a a' b b' : ℚ_[ℓ]}
    {q m : ℕ} {ι' : Type*} (Z : Finset ι') (d : ι' → ℕ) (t t' : ι' → ℕ → ℚ_[ℓ])
    (ht : ∀ z ∈ Z, ∀ e, 1 ≤ e → ι (t z e + t' z e) ∈ Set.range ((↑) : ℝ → ℂ)) (hm : 1 ≤ m)
    (h : a + b = (q : ℚ_[ℓ]) ^ m * ∑ z ∈ Z, if d z ∣ m then (d z : ℚ_[ℓ]) * t z (m / d z) else 0)
    (h' : a' + b' =
      (q : ℚ_[ℓ]) ^ m * ∑ z ∈ Z, if d z ∣ m then (d z : ℚ_[ℓ]) * t' z (m / d z) else 0) :
    ι (a + (a' + (b + b'))) ∈ Set.range ((↑) : ℝ → ℂ) := by
  have hsum : a + (a' + (b + b')) = (q : ℚ_[ℓ]) ^ m *
      ∑ z ∈ Z, if d z ∣ m then (d z : ℚ_[ℓ]) * (t z (m / d z) + t' z (m / d z)) else 0 := by
    have : a + (a' + (b + b')) = (a + b) + (a' + b') := by ring
    rw [this, h, h', ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  have hmem : ι (a + (a' + (b + b'))) ∈ Complex.ofRealHom.range := by
    rw [hsum, map_mul, map_pow, map_natCast, map_sum]
    refine mul_mem (pow_mem (RingHom.mem_range.2 ⟨(q : ℝ), by simp⟩) _)
      (Subring.sum_mem _ fun z hz => ?_)
    split_ifs with hd
    · rw [map_mul, map_natCast]
      refine mul_mem (RingHom.mem_range.2 ⟨(d z : ℝ), by simp⟩) ?_
      have hd0 : d z ≠ 0 := by
        rintro h0
        rw [h0, zero_dvd_iff] at hd
        omega
      exact ht z hz (m / d z) (Nat.div_pos (Nat.le_of_dvd hm hd) (Nat.pos_of_ne_zero hd0))
    · rw [map_zero]
      exact zero_mem _
  exact hmem

/-- **Realizability of `R² g_!` from its Gysin map** (Weil II 1.5 and 3.3): if a family `R` has
the lisse locus of `Rʳ g_!` (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageLisseLocusInput`)
and the Gysin map of `R²`
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinInput`), then `R² g_! G` is
`ι`-realizable for every lisse `ι`-realizable `G` on a family of smooth affine curves. -/
public theorem LAdicSheaf.higherDirectImageTopRealizableInput_of_gysinInput
    (R : LAdicSheaf.HigherDirectImageFamily B ℓ)
    (hL : LAdicSheaf.HigherDirectImageLisseLocusInput R)
    (hγ : LAdicSheaf.HigherDirectImageTopGysinInput R) :
    LAdicSheaf.HigherDirectImageTopRealizableInput R := by
  intro k _ _ p n _ _ hcard hℓ ι U W _ _ _ g _ _ _ _ _ fW _ _ _ G hG hGr hW hU
  obtain ⟨G', hG', hreal⟩ := hGr
  obtain ⟨Z, d, -, hZ⟩ := hγ k p n hcard hℓ U W g fW hW hU
  obtain ⟨V₁, j₁, ho₁, hn₁, h₁⟩ := hZ G hG
  obtain ⟨V₂, j₂, ho₂, hn₂, h₂⟩ := hZ G' hG'
  obtain ⟨V₃, j₃, ho₃, hn₃, h₃⟩ :=
    hL U W g G' hG' ⟨(B.inclusion.map g).base (Classical.arbitrary U.1)⟩
  let O : (B.inclusion.obj W).Opens := (B.inclusion.map j₁).opensRange ⊓
    (B.inclusion.map j₂).opensRange ⊓ (B.inclusion.map j₃).opensRange
  have hOB : B.Contains O.toScheme := (Scheme.size_le_of_isOpenImmersion O.ι).trans_lt W.2
  let V : B.Scheme := B.obj O.toScheme hOB
  let jV : V ⟶ W := ObjectProperty.homMk O.ι
  have hjV : B.inclusion.map jV = O.ι := rfl
  have hne : ∀ (X : B.Scheme) (j : X ⟶ W) [IsOpenImmersion (B.inclusion.map j)],
      Nonempty X.1 → ((B.inclusion.map j).opensRange : Set (B.inclusion.obj W)).Nonempty :=
    fun X j _ hX => ⟨_, (Classical.arbitrary X.1), rfl⟩
  have : IrreducibleSpace (B.inclusion.obj W) := hW
  have hVne : Nonempty V.1 := by
    obtain ⟨w, hw⟩ := nonempty_preirreducible_inter
      (((B.inclusion.map j₁).opensRange ⊓ (B.inclusion.map j₂).opensRange).isOpen)
      ((B.inclusion.map j₃).opensRange.isOpen)
      (nonempty_preirreducible_inter (B.inclusion.map j₁).opensRange.isOpen
        (B.inclusion.map j₂).opensRange.isOpen (hne _ _ hn₁) (hne _ _ hn₂))
      (hne _ _ hn₃)
    exact ⟨⟨w, hw⟩⟩
  refine ⟨V, jV, inferInstanceAs (IsOpenImmersion O.ι), hVne, ?_⟩
  intro V' U' _ _ jV' jU g' _ _ _ jg' hjV' hpb fV' _
  have hsub : ∀ (X : B.Scheme) (j : X ⟶ W) [IsOpenImmersion (B.inclusion.map j)],
      (O : Set (B.inclusion.obj W)) ⊆ (B.inclusion.map j).opensRange →
      ∃ j' : V' ⟶ X, IsOpenImmersion (B.inclusion.map j') ∧ j' ≫ j = jV' ≫ jV := by
    intro X j _ hO
    have hr : Set.range (B.inclusion.map (jV' ≫ jV)) ⊆ Set.range (B.inclusion.map j) := by
      rintro _ ⟨x, rfl⟩
      have : (B.inclusion.map (jV' ≫ jV)) x ∈ (O : Set (B.inclusion.obj W)) := by
        rw [Functor.map_comp, hjV, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι O]
        exact ⟨_, rfl⟩
      exact hO this
    have : IsOpenImmersion (B.inclusion.map (jV' ≫ jV)) := by
      rw [Functor.map_comp, hjV]; infer_instance
    have hfac := IsOpenImmersion.lift_fac (B.inclusion.map j) (B.inclusion.map (jV' ≫ jV)) hr
    refine ⟨ObjectProperty.homMk (IsOpenImmersion.lift (B.inclusion.map j)
      (B.inclusion.map (jV' ≫ jV)) hr), ?_, B.inclusion.map_injective ?_⟩
    · have : IsOpenImmersion (IsOpenImmersion.lift (B.inclusion.map j)
          (B.inclusion.map (jV' ≫ jV)) hr ≫ B.inclusion.map j) := by
        rw [hfac]; infer_instance
      exact IsOpenImmersion.of_comp (IsOpenImmersion.lift (B.inclusion.map j)
        (B.inclusion.map (jV' ≫ jV)) hr) (B.inclusion.map j)
    · rwa [Functor.map_comp]
  obtain ⟨i₁, hi₁, hf₁⟩ := hsub V₁ j₁ fun w hw => hw.1.1
  obtain ⟨i₂, hi₂, hf₂⟩ := hsub V₂ j₂ fun w hw => hw.1.2
  obtain ⟨i₃, hi₃, hf₃⟩ := hsub V₃ j₃ fun w hw => hw.2
  obtain ⟨K₁, hK₁, e₁⟩ := h₁ V' U' i₁ jU g' jg' hi₁ (hf₁ ▸ hpb) fV'
  obtain ⟨K₂, hK₂, e₂⟩ := h₂ V' U' i₂ jU g' jg' hi₂ (hf₂ ▸ hpb) fV'
  have hR' := h₃ V' U' i₃ jU g' jg' hi₃ (hf₃ ▸ hpb) 2
  refine ⟨R g' jg' (LAdicSheaf.inverseImage jU G') 2 ⊞ (K₁ ⊞ K₂),
    hR'.biprod (hK₁.biprod hK₂), fun w m hm => ?_⟩
  have e₁' := e₁ w m hm
  have e₂' := e₂ w m hm
  rw [hf₁] at e₁'
  rw [hf₂] at e₂'
  rw [LAdicSheaf.trace_rationalStalkFrobenius_biprod_pow,
    LAdicSheaf.trace_rationalStalkFrobenius_biprod_pow]
  exact map_trace_add_mem_range_of_gysin ι _ d _ _
    (fun z _ e he => hreal z e he) hm e₁' e₂'

end Stacks.EtaleCohomology

end
