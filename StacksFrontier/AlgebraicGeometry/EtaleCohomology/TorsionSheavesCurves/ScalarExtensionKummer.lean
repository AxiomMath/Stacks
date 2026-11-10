module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# Restriction of `μ_ℓ`-cohomology through the Kummer sequence

Restriction along a morphism `π : X' ⟶ X` is compared with the Kummer sequences
`0 → μ_ℓ → 𝐆_m → 𝐆_m → 0` of `X` and `X'`: restriction on `H^q(μ_ℓ)` is bijective as soon as
restriction on `H^{q-1}(𝐆_m)` is bijective modulo `ℓ` and restriction on `H^q(𝐆_m)` is bijective on
`ℓ`-torsion.

## Main results

* `AddMonoidHom.bijective_of_nsmul_ladder`: the diagram chase.
* `Stacks.EtaleCohomology.bijective_rootsOfUnityRestriction`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

/-- **The diagram chase of the Kummer sequence.** Given exact rows
`A →δ M →i B` (the kernel of `δ` being `ℓ A`, the image of `i` the `ℓ`-torsion of `B`) and
`A' →δ' M' →i' B'`, and commuting vertical maps `rA, rM, rB` (each a composite of two maps), the
middle map is bijective as soon as `rA` is bijective modulo `ℓ` and `rB` is bijective on
`ℓ`-torsion. -/
theorem AddMonoidHom.bijective_of_nsmul_ladder {A M B A' M' B' : Type*} [AddCommGroup A]
    [AddCommGroup M] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup M'] [AddCommGroup B']
    (ℓ : ℕ) (δ : A →+ M) (i : M →+ B) (δ' : A' →+ M') (i' : M' →+ B')
    (rA : A →+ A') (rM : M →+ M') (rB : B →+ B')
    (hδ : ∀ a, rM (δ a) = δ' (rA a)) (hi : ∀ m, rB (i m) = i' (rM m))
    (exδ : ∀ z, δ (ℓ • z) = 0) (exδ' : ∀ a', δ' a' = 0 → ∃ z', ℓ • z' = a')
    (exδ'₀ : ∀ z', δ' (ℓ • z') = 0)
    (exi : ∀ m, i m = 0 → ∃ a, δ a = m) (exi' : ∀ m', i' m' = 0 → ∃ a', δ' a' = m')
    (tor : ∀ m, ℓ • i m = 0) (tor' : ∀ m', ℓ • i' m' = 0)
    (lift : ∀ b, ℓ • b = 0 → ∃ m, i m = b)
    (hU₁ : ∀ a z', ℓ • z' = rA a → ∃ z, ℓ • z = a)
    (hU₂ : ∀ a', ∃ a z', a' = rA a + ℓ • z')
    (hT₁ : ∀ b, ℓ • b = 0 → rB b = 0 → b = 0)
    (hT₂ : ∀ b', ℓ • b' = 0 → ∃ b, ℓ • b = 0 ∧ rB b = b') :
    Function.Bijective rM := by
  refine ⟨(injective_iff_map_eq_zero rM).2 fun m hm => ?_, fun m' => ?_⟩
  · have hb : i m = 0 := hT₁ _ (tor m) (by rw [hi, hm, map_zero])
    obtain ⟨a, rfl⟩ := exi m hb
    obtain ⟨z', hz'⟩ := exδ' (rA a) (by rw [← hδ, hm])
    obtain ⟨z, rfl⟩ := hU₁ a z' hz'
    exact exδ z
  · obtain ⟨b, hb, hbb⟩ := hT₂ (i' m') (tor' m')
    obtain ⟨m, rfl⟩ := lift b hb
    obtain ⟨a', ha'⟩ := exi' (m' - rM m) (by rw [map_sub, ← hi, hbb, sub_self])
    obtain ⟨a, z', rfl⟩ := hU₂ a'
    refine ⟨m + δ a, ?_⟩
    rw [map_add, hδ]
    rw [map_add, exδ'₀, add_zero] at ha'
    rw [ha', add_sub_cancel]

namespace Stacks.EtaleCohomology

open Stacks.Kummer

/-- Composition with `n • 𝟙` is multiplication by `n` on `Ext`. -/
theorem Abelian.Ext.comp_mk₀_nsmul_id {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {A B : C} {q : ℕ} (d : Abelian.Ext A B q) (n : ℕ) :
    d.comp (Abelian.Ext.mk₀ (n • 𝟙 B)) (add_zero q) = n • d := by
  induction n with
  | zero => rw [zero_smul, zero_smul, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ n ih => rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih,
      Abelian.Ext.comp_mk₀_id, succ_nsmul]

/-- **The Kummer connecting map** `H^r(𝐆_m) → H^{r+1}(μ_n)`. -/
def kummerConnecting (Z : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit ((n : ℕ) : Γ(Z, ⊤)))
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (r : ℕ) :
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) r →+
      Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Z n) (r + 1) :=
  (kummerSequence_shortExact.{u, v} Z hn0 hn).extClass.postcomp _ rfl

/-- The map `H^q(μ_n) → H^q(𝐆_m)` induced by the inclusion. -/
def rootsOfUnityInclusion (Z : Scheme.{u}) (n : ℕ)
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (q : ℕ) :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Z n) q →+ Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) q :=
  Sheaf.H.map (rootsOfUnityι.{u, v} Z n) q

/-- `rootsOfUnityInclusion` is composition with the inclusion `μ_n ⟶ 𝐆_m`. -/
theorem rootsOfUnityInclusion_apply (Z : Scheme.{u}) (n : ℕ)
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (q : ℕ)
    (m : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Z n) q) :
    rootsOfUnityInclusion.{u, v, w} Z n q m =
      m.comp (Abelian.Ext.mk₀ (rootsOfUnityι.{u, v} Z n)) (add_zero q) :=
  rfl

/-- `kummerConnecting` is composition with the extension class of the Kummer sequence. -/
theorem kummerConnecting_apply (Z : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0)
    (hn : IsUnit ((n : ℕ) : Γ(Z, ⊤)))
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (r : ℕ)
    (a : Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) r) :
    kummerConnecting.{u, v, w} Z hn0 hn r a =
      a.comp (kummerSequence_shortExact.{u, v} Z hn0 hn).extClass rfl :=
  rfl

section KummerRow

variable (Z : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit ((n : ℕ) : Γ(Z, ⊤)))
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The connecting map kills `n`-th multiples. -/
theorem kummerConnecting_nsmul (r : ℕ) (z : Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) r) :
    kummerConnecting.{u, v, w} Z hn0 hn r (n • z) = 0 := by
  rw [kummerConnecting_apply]
  have h1 : n • z = z.comp (Abelian.Ext.mk₀ (kummerSequence.{u, v} Z n).g) (add_zero r) :=
    (Abelian.Ext.comp_mk₀_nsmul_id z n).symm
  rw [h1]
  exact (Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans
    ((congrArg (fun t => z.comp t _)
      (kummerSequence_shortExact.{u, v} Z hn0 hn).comp_extClass).trans
      (Abelian.Ext.comp_zero _ _ _ _ _))

/-- The kernel of the connecting map consists of `n`-th multiples. -/
theorem exists_nsmul_eq_of_kummerConnecting_eq_zero (r : ℕ)
    (a : Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) r)
    (ha : kummerConnecting.{u, v, w} Z hn0 hn r a = 0) : ∃ z, n • z = a := by
  obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₃ _
    (kummerSequence_shortExact.{u, v} Z hn0 hn) a rfl ha
  exact ⟨z, (Abelian.Ext.comp_mk₀_nsmul_id z n).symm.trans hz⟩

/-- The kernel of `H^{r+1}(μ_n) → H^{r+1}(𝐆_m)` is the image of the connecting map. -/
theorem exists_kummerConnecting_eq_of_rootsOfUnityInclusion_eq_zero (r : ℕ)
    (m : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Z n) (r + 1))
    (hm : rootsOfUnityInclusion.{u, v, w} Z n (r + 1) m = 0) :
    ∃ a, kummerConnecting.{u, v, w} Z hn0 hn r a = m :=
  Abelian.Ext.covariant_sequence_exact₁ _ (kummerSequence_shortExact.{u, v} Z hn0 hn) m hm rfl

/-- The image of `H^q(μ_n) → H^q(𝐆_m)` is killed by `n`. -/
theorem nsmul_rootsOfUnityInclusion (q : ℕ) (m : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Z n) q) :
    n • rootsOfUnityInclusion.{u, v, w} Z n q m = 0 := by
  rw [rootsOfUnityInclusion_apply]
  refine (Abelian.Ext.comp_mk₀_nsmul_id _ n).symm.trans ?_
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  have h0 : rootsOfUnityι.{u, v} Z n ≫ (n • 𝟙 (multiplicativeSheaf.{u, v} Z)) = 0 :=
    (kummerSequence.{u, v} Z n).zero
  rw [h0, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

include hn0 hn in
/-- The `n`-torsion of `H^q(𝐆_m)` comes from `H^q(μ_n)`. -/
theorem exists_rootsOfUnityInclusion_eq_of_nsmul_eq_zero (q : ℕ)
    (b : Sheaf.H.{w} (multiplicativeSheaf.{u, v} Z) q) (hb : n • b = 0) :
    ∃ m, rootsOfUnityInclusion.{u, v, w} Z n q m = b :=
  Abelian.Ext.covariant_sequence_exact₂ _ (kummerSequence_shortExact.{u, v} Z hn0 hn) b
    ((Abelian.Ext.comp_mk₀_nsmul_id b n).trans hb)

end KummerRow

variable {X Y : Scheme.{u}} (π : Y ⟶ X) {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit ((n : ℕ) : Γ(X, ⊤)))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction on `H^q(𝐆_m)`**, moved to the cohomology of `𝐆_{m,Y}` along
`π⁻¹ 𝐆_{m,X} ⟶ 𝐆_{m,Y}`. -/
def multiplicativeRestriction (q : ℕ) :
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q →+ Sheaf.H.{w} (multiplicativeSheaf.{u, v} Y) q :=
  (Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) q).comp
    (etaleCohomologyRestrictionMap.{u, v, w} π (multiplicativeSheaf.{u, v} X) q)

/-- `multiplicativeRestriction` is restriction followed by the comparison on `𝐆_m`. -/
theorem multiplicativeRestriction_apply (q : ℕ) (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q) :
    multiplicativeRestriction.{u, v, w} π q x =
      Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) q
        (etaleCohomologyRestrictionMap.{u, v, w} π (multiplicativeSheaf.{u, v} X) q x) :=
  rfl

/-- **Restriction on `H^q(μ_n)`**, moved to the cohomology of `μ_{n,Y}` along
`π⁻¹ μ_{n,X} ⟶ μ_{n,Y}`. -/
def rootsOfUnityRestriction (n q : ℕ) :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) q →+ Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q :=
  (Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) q).comp
    (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} X n) q)

/-- `rootsOfUnityRestriction` is restriction followed by the comparison on `μ_n`. -/
theorem rootsOfUnityRestriction_apply (n q : ℕ) (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) q) :
    rootsOfUnityRestriction.{u, v, w} π n q x =
      Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) q
        (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} X n) q x) :=
  rfl

set_option maxHeartbeats 1000000 in
-- long `rw` chain through `Sheaf.H.map` and `Ext` composition over the étale site
/-- **Restriction commutes with `μ_n ⟶ 𝐆_m`**, read in the cohomology of `μ_{n,Y}` and
`𝐆_{m,Y}`. -/
theorem multiplicativeRestriction_rootsOfUnityInclusion (q : ℕ)
    (m : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) q) :
    multiplicativeRestriction.{u, v, w} π q (rootsOfUnityInclusion.{u, v, w} X n q m) =
      rootsOfUnityInclusion.{u, v, w} Y n q (rootsOfUnityRestriction.{u, v, w} π n q m) := by
  rw [multiplicativeRestriction_apply, rootsOfUnityRestriction_apply, rootsOfUnityInclusion_apply,
    rootsOfUnityInclusion_apply, etaleCohomologyRestrictionMap_comp_mk₀,
    Sheaf.H.map_apply, Sheaf.H.map_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀,
    rootsOfUnityInverseImageComparison_comp_rootsOfUnityι]

include hn0 hn in
/-- **Restriction on `H^{r+1}(μ_n)` is bijective** once restriction on `H^r(𝐆_m)` is bijective
modulo `n` and restriction on `H^{r+1}(𝐆_m)` is bijective on `n`-torsion: the Kummer sequences
of `X` and `Y` and `AddMonoidHom.bijective_of_nsmul_ladder`. -/
theorem bijective_rootsOfUnityRestriction (r : ℕ)
    (hU₁ : ∀ a z', n • z' = multiplicativeRestriction.{u, v, w} π r a → ∃ z, n • z = a)
    (hU₂ : ∀ a', ∃ a z', a' = multiplicativeRestriction.{u, v, w} π r a + n • z')
    (hT₁ : ∀ b, n • b = 0 → multiplicativeRestriction.{u, v, w} π (r + 1) b = 0 → b = 0)
    (hT₂ : ∀ b', n • b' = 0 →
      ∃ b, n • b = 0 ∧ multiplicativeRestriction.{u, v, w} π (r + 1) b = b') :
    Function.Bijective (rootsOfUnityRestriction.{u, v, w} π n (r + 1)) := by
  refine AddMonoidHom.bijective_of_nsmul_ladder n
    (kummerConnecting.{u, v, w} X hn0 hn r) (rootsOfUnityInclusion.{u, v, w} X n (r + 1))
    (kummerConnecting.{u, v, w} Y hn0 (isUnit_natCast_of_hom π hn) r)
    (rootsOfUnityInclusion.{u, v, w} Y n (r + 1))
    (multiplicativeRestriction.{u, v, w} π r) (rootsOfUnityRestriction.{u, v, w} π n (r + 1))
    (multiplicativeRestriction.{u, v, w} π (r + 1))
    (fun a => ?_) (fun m => ?_)
    (kummerConnecting_nsmul X hn0 hn r)
    (exists_nsmul_eq_of_kummerConnecting_eq_zero Y hn0 (isUnit_natCast_of_hom π hn) r)
    (kummerConnecting_nsmul Y hn0 (isUnit_natCast_of_hom π hn) r)
    (exists_kummerConnecting_eq_of_rootsOfUnityInclusion_eq_zero X hn0 hn r)
    (exists_kummerConnecting_eq_of_rootsOfUnityInclusion_eq_zero Y hn0
      (isUnit_natCast_of_hom π hn) r)
    (nsmul_rootsOfUnityInclusion X (r + 1)) (nsmul_rootsOfUnityInclusion Y (r + 1))
    (exists_rootsOfUnityInclusion_eq_of_nsmul_eq_zero X hn0 hn (r + 1)) hU₁ hU₂ hT₁ hT₂
  · rw [rootsOfUnityRestriction_apply, kummerConnecting_apply, kummerConnecting_apply,
      multiplicativeRestriction_apply]
    exact etaleCohomologyRestrictionMap_kummerExtClass.{u, v, w} π hn0 hn r (r + 1) rfl a
  · exact multiplicativeRestriction_rootsOfUnityInclusion.{u, v, w} π (r + 1) m

end Stacks.EtaleCohomology

end
