module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedBaseField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIISheafDevissage
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective

/-!
# The induction step of Weil II

The step `S(n) → S(n + 1)` (`n ≥ 1`) of the induction on the dimension in the weight bound of
Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3), modulo the
inputs of `Mathlib`-external results stated in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs`.

Let `g : U ⟶ W` have fibres of dimension `≤ 1` and `G` be lisse, pointwise `ι`-mixed of weights
`≤ w` and `ι`-realizable on `U`. At a closed point `y` of `W`, with residue field `κ(y)` of
degree `d` over `k`, the restriction of `G` to the fibre `U_y` is lisse, pointwise mixed of
weights `≤ w` over `κ(y)` (with `q ^ d` elements) and realizable; the weight bound in dimension
one over `κ(y)` bounds the weights of `Hʳ_c(U_y, G)` by `w + r`, and through the stalks of
`Rʳ g_! G` at `y` this is the pointwise mixedness of weights `≤ w + r` of `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.isPointwiseMixedOfWeightLE_higherDirectImage`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- The point `Spec κ(x) ⟶ X` of a scheme over `k` lies over `Spec k` through the `k`-algebra
structure of `κ(x)`. -/
theorem fromSpecResidueField_comp_eq_specMap_algebraMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
    X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x))) := by
  let : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have h := (fromSpecResidueField_comp_eq_iff f (X.residueField x) x
    (𝟙 (X.residueField x))).2 (by rw [Category.comp_id]; rfl)
  rw [Spec.map_id] at h
  refine Eq.trans ?_ h
  exact congrArg (· ≫ f) (Category.id_comp _).symm

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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

/-- Pointwise mixedness only depends on the structure morphism. -/
theorem LAdicSheaf.IsPointwiseMixedOfWeightLE.congr {X : B.Scheme} [IsNoetherian X.1]
    {k : Type u} [Field k] [Finite k] {f f' : X.1 ⟶ Spec (.of k)} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (h : f = f') {F : LAdicSheaf B X ℓ} {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ}
    {w : ℤ} (hF : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F q ι w) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f' F q ι w := by
  subst h
  exact hF

/-- **The higher direct images with compact support are pointwise mixed** (Weil II 3.3, the
fibrewise step): for `g : U ⟶ W` over a finite field `k` with fibres of dimension `≤ 1` and `G`
lisse, pointwise `ι`-mixed of weights `≤ w` and `ι`-realizable on `U`, every `Rʳ g_! G` is
pointwise `ι`-mixed of weights `≤ w + r`: at a closed point `y` of `W` the Frobenius on the stalk
has the characteristic polynomial of the Frobenius of `κ(y)` on `Hʳ_c` of the fibre `U_y`, whose
weights are `≤ w + r` by the weight bound in dimension one over `κ(y)`. -/
theorem LAdicSheaf.isPointwiseMixedOfWeightLE_higherDirectImage
    {R : LAdicSheaf.HigherDirectImageFamily B ℓ} (hstalk : LAdicSheaf.HigherDirectImageStalkInput R)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hS1 : LAdicSheaf.WeightBoundInDimension B ℓ 1)
    {k : Type u} [Field k] [Fintype k] {p q : ℕ} [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ)
    {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
    (hdim : ∀ y : W.1, topologicalKrullDim ↥((B.inclusion.map g).base ⁻¹' ({y} : Set W.1)) ≤
      (1 : WithBot ℕ∞))
    {G : LAdicSheaf.{u, u + 1} B U ℓ} {w : ℤ} (hl : G.IsLisse)
    (hm : LAdicSheaf.IsPointwiseMixedOfWeightLE B U ℓ (B.inclusion.map g ≫ fW) G (p ^ q) ι w)
    (hr : LAdicSheaf.IsIotaRealizable B U ℓ (B.inclusion.map g ≫ fW) G ι) (r : ℕ) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B W ℓ fW (R g jg G r) (p ^ q) ι (w + r) := by
  intro y z hz
  -- the residue field at `y`, a finite extension of degree `d` of `k`
  have : Finite (W.1.residueField y.1) := finite_residueField fW y.1 y.2
  let : Fintype (W.1.residueField y.1) := Fintype.ofFinite _
  let : Algebra k (W.1.residueField y.1) := (fieldToResidue fW y.1).hom.toAlgebra
  have : CharP (W.1.residueField y.1) p :=
    charP_of_injective_algebraMap (algebraMap k (W.1.residueField y.1)).injective p
  have hcardκ : Fintype.card (W.1.residueField y.1) =
      p ^ (q * Module.finrank k (W.1.residueField y.1)) := by
    rw [Module.card_eq_pow_finrank (K := k), hcard, pow_mul]
  -- the fibre `U_y` over `κ(y)`
  have hSpec : B.Contains (Spec (W.1.residueField y.1)) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      (W.1.fromSpecResidueField y.1) W.property
  have hB : B.Contains ((B.inclusion.map g).fiber y.1) :=
    Scheme.size_pullback_lt _ _ U.property hSpec
  have : IsClosedImmersion ((B.inclusion.obj W).fromSpecResidueField y.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp y.2
  have : IsClosedImmersion ((B.inclusion.map g).fiberι y.1) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have : LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField y.1) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField y.1) :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : IsSeparated ((B.inclusion.map g).fiberToSpecResidueField y.1) :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsNoetherian ((B.inclusion.map g).fiber y.1) :=
    isNoetherian_of_locallyOfFiniteType_over_field (k := W.1.residueField y.1)
      ((B.inclusion.map g).fiberToSpecResidueField y.1)
  let Fb : B.Scheme := B.obj ((B.inclusion.map g).fiber y.1) hB
  have : IsNoetherian Fb.1 := ‹IsNoetherian ((B.inclusion.map g).fiber y.1)›
  let ιF : Fb ⟶ U := ObjectProperty.homMk ((B.inclusion.map g).fiberι y.1)
  have : IsClosedImmersion (B.inclusion.map ιF) :=
    ‹IsClosedImmersion ((B.inclusion.map g).fiberι y.1)›
  have hcl : ∀ x : closedPoints Fb.1, (B.inclusion.map ιF).base x.1 ∈ closedPoints U.1 :=
    mem_closedPoints_of_isClosedImmersion (B.inclusion.map ιF)
  -- the restriction of `G` to the fibre is lisse, mixed over `κ(y)` and realizable
  have heq : B.inclusion.map ιF ≫ B.inclusion.map g ≫ fW =
      (B.inclusion.map g).fiberToSpecResidueField y.1 ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (W.1.residueField y.1))) := by
    show (B.inclusion.map g).fiberι y.1 ≫ B.inclusion.map g ≫ fW = _
    rw [Scheme.Hom.fiber_fac_assoc, fromSpecResidueField_comp_eq_specMap_algebraMap]
    rfl
  have : LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField y.1 ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (W.1.residueField y.1)))) := by
    rw [← heq]
    infer_instance
  have hmF := (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage U ℓ ιF (B.inclusion.map g ≫ fW)
    hm hcl).congr
    heq
  have hmκ := LAdicSheaf.IsPointwiseMixedOfWeightLE.of_comp_specMap B Fb ℓ
    (k' := W.1.residueField y.1)
    ((B.inclusion.map g).fiberToSpecResidueField y.1) hmF
  rw [← pow_mul] at hmκ
  have hrF : LAdicSheaf.IsIotaRealizable (k := W.1.residueField y.1) B Fb ℓ
      ((B.inclusion.map g).fiberToSpecResidueField y.1)
      (LAdicSheaf.inverseImage ιF G) ι :=
    LAdicSheaf.IsIotaRealizable.inverseImage ℓ (B.inclusion.map g ≫ fW) ιF hr hcl
  -- the fibre has dimension at most one
  have hdF : topologicalKrullDim Fb.1 ≤ 1 :=
    ((B.inclusion.map g).fiberHomeo y.1).isInducing.topologicalKrullDim_le.trans (hdim y.1)
  -- the weight bound in dimension one over `κ(y)`, and the stalk of `Rʳ g_! G` at `y`
  have hSF := hS1 (W.1.residueField y.1) (AlgebraicClosure (W.1.residueField y.1)) p
    (q * Module.finrank k (W.1.residueField y.1)) hcardκ hℓ ι Fb
    ((B.inclusion.map g).fiberToSpecResidueField y.1) hdF
  obtain ⟨jw, hjw⟩ := hstalk k U W g jg fW y hB (AlgebraicClosure (W.1.residueField y.1)) p
    (q * Module.finrank k (W.1.residueField y.1)) hcardκ
  have := (hfin (W.1.residueField y.1) (AlgebraicClosure (W.1.residueField y.1)) p
    (q * Module.finrank k (W.1.residueField y.1)) hcardκ hℓ Fb
    ((B.inclusion.map g).fiberToSpecResidueField y.1)
    jw (LAdicSheaf.inverseImage ιF G) r).1
  have hbound := hSF jw (LAdicSheaf.inverseImage ιF G) w (hl.inverseImage ιF) hmκ hrF r
  obtain ⟨w', hw', hz'⟩ := hbound z (by rw [← hjw G r]; exact hz)
  refine ⟨w', hw', ?_⟩
  rw [hz']
  show ((p ^ (q * Module.finrank k (W.1.residueField y.1)) : ℕ) : ℝ) ^ ((w' : ℝ) / 2) =
    ((p ^ q : ℕ) : ℝ) ^ (((Module.finrank k (W.1.residueField y.1) : ℤ) * w' : ℝ) / 2)
  rw [pow_mul]
  push_cast
  rw [← Real.rpow_natCast ((p : ℝ) ^ q), ← Real.rpow_mul (by positivity)]
  ring_nf

/-- The weight bound for one sheaf only depends on the structure morphism. -/
theorem LAdicSheaf.CompactSupportWeightLE.congr {X : B.Scheme} [IsNoetherian X.1]
    {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
    {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q} {ι : ℚ_[ℓ] →+* ℂ}
    {f f' : X.1 ⟶ Spec (.of k)} [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f'] [QuasiCompact f'] [IsSeparated f'] (h : f = f')
    {F : LAdicSheaf.{u, u + 1} B X ℓ} {w : ℤ}
    (hF : LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f F w) :
    LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι X f' F w := by
  subst h
  exact hF

/-- **The Leray step** (Weil II 3.3): for `g : U ⟶ W` over a finite field with fibres of
dimension `≤ 1` and `W` of dimension `≤ n`, and `G` lisse, pointwise `ι`-mixed of weights `≤ w`
and `ι`-realizable on `U` with all `Rʳ g_! G` lisse and `ι`-realizable on `W`, the weight bound in
dimension `n` on `W` applies to the `Rʳ g_! G`, pointwise mixed of weights `≤ w + r` by the
weight bound in dimension one on the fibres, and the Leray spectral sequence gives the weight
bound for `G`; the compactification of `U` does not matter. -/
theorem LAdicSheaf.compactSupportWeightLE_of_higherDirectImage
    {R : LAdicSheaf.HigherDirectImageFamily B ℓ} (hleray : LAdicSheaf.LerayWeightInput R)
    (hstalk : LAdicSheaf.HigherDirectImageStalkInput R)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hind : LAdicSheaf.CompactSupportCompactificationIndependenceInput B ℓ) {n : ℕ}
    (hS : LAdicSheaf.WeightBoundInDimension B ℓ n) (hS1 : LAdicSheaf.WeightBoundInDimension B ℓ 1)
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ)
    {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
    (hdimW : topologicalKrullDim W.1 ≤ n)
    (hdim : ∀ y : W.1, topologicalKrullDim ↥((B.inclusion.map g).base ⁻¹' ({y} : Set W.1)) ≤
      (1 : WithBot ℕ∞))
    {G : LAdicSheaf.{u, u + 1} B U ℓ} {w : ℤ} (hl : G.IsLisse)
    (hm : LAdicSheaf.IsPointwiseMixedOfWeightLE B U ℓ (B.inclusion.map g ≫ fW) G (p ^ q) ι w)
    (hr : LAdicSheaf.IsIotaRealizable B U ℓ (B.inclusion.map g ≫ fW) G ι)
    (hRl : ∀ r : ℕ, (R g jg G r).IsLisse)
    (hRr : ∀ r : ℕ, LAdicSheaf.IsIotaRealizable B W ℓ fW (R g jg G r) ι) :
    LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι U (B.inclusion.map g ≫ fW) G w := by
  have hSW := hS k kbar p q hcard hℓ ι W fW hdimW
  obtain ⟨jU₀, hjU₀⟩ := hleray k kbar p q hcard hℓ ι U W g jg fW G w fun r jW i _ =>
    hSW jW (R g jg G r) (w + r) (hRl r)
      (LAdicSheaf.isPointwiseMixedOfWeightLE_higherDirectImage hstalk hfin hS1 hcard hℓ ι g jg fW
        hdim hl hm hr r) (hRr r) i
  intro j i _
  have := (hfin k kbar p q hcard hℓ U (B.inclusion.map g ≫ fW) jU₀ G i).1
  have h₀ := hjU₀ i
  have hc := hind k kbar p q hcard hℓ U (B.inclusion.map g ≫ fW) j jU₀ G i
  unfold IsCharpolyNormMixedOfWeightLE at h₀ ⊢
  rw [hc]
  exact h₀

/-- An element of `WithBot ℕ∞` which is at most `n + 1` is at most `n` or equal to `n + 1`. -/
theorem le_or_eq_add_one_of_le_add_one {d : WithBot ℕ∞} {n : ℕ} (hd : d ≤ n + 1) :
    d ≤ n ∨ d = n + 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact Or.inl bot_le
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      have h : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast hd
      exact (ENat.coe_lt_top (n + 1)).not_ge (WithBot.coe_le_coe.1 h)
    | coe m =>
      have hm : m ≤ n + 1 := by exact_mod_cast hd
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact Or.inl (by exact_mod_cast Nat.lt_succ_iff.1 h)
      · exact Or.inr (by exact_mod_cast le_antisymm hm h)

end Stacks.EtaleCohomology
