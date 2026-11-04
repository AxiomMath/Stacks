module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveFirstCohomologyOrder
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveFirstCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.KummerClassGroup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointClassGroupRestriction
public import StacksFrontier.AlgebraicGeometry.MeromorphicConstant.OrderUnit
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClassGroupPicardBridge
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeOneCocycles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafModuleDictionaryEtaleSite

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### Counting in abelian groups -/

section Counting

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- `#G = #ker f · #im f` for a homomorphism out of a finite group. -/
theorem natCard_eq_natCard_ker_mul_natCard_range_of_finite [Finite G] (f : G →+ H) :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker

/-- A group is finite when the kernel and the image of a homomorphism out of it are. -/
theorem finite_of_finite_ker_of_finite_range (f : G →+ H) [Finite f.ker] [Finite f.range] :
    Finite G := by
  have : Finite (G ⧸ f.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange f).symm.toEquiv
  exact (AddSubgroup.finite_iff_finite_and_finiteIndex (H := f.ker)).2
    ⟨inferInstance, AddSubgroup.finiteIndex_of_finite_quotient⟩

/-- The kernel of `g` is the range of `f` when `f` and `g` are exact, elementwise. -/
private theorem ker_eq_range_of_forall_apply_eq_zero_iff {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
    (hfg : ∀ b, g b = 0 ↔ ∃ a, f a = b) : g.ker = f.range :=
  AddSubgroup.ext hfg

/-- For `C₀ → A₁ → B₁` exact at `A₁` with `C₀` and `B₁` finite, `A₁` is finite and
`#A₁ ≤ #C₀ · #B₁`. -/
theorem finite_and_natCard_le_of_exact {C₀ A₁ B₁ : Type*} [AddCommGroup C₀] [AddCommGroup A₁]
    [AddCommGroup B₁] [Finite C₀] [Finite B₁] (δ : C₀ →+ A₁) (h : A₁ →+ B₁)
    (hδh : ∀ a, h a = 0 ↔ ∃ c, δ c = a) :
    Finite A₁ ∧ Nat.card A₁ ≤ Nat.card C₀ * Nat.card B₁ := by
  have hk := ker_eq_range_of_forall_apply_eq_zero_iff δ h hδh
  have : Finite δ.range := Finite.of_surjective _ δ.rangeRestrict_surjective
  have : Finite h.ker := hk ▸ inferInstance
  have := finite_of_finite_ker_of_finite_range h
  refine ⟨inferInstance, ?_⟩
  rw [natCard_eq_natCard_ker_mul_natCard_range_of_finite h, hk]
  exact Nat.mul_le_mul (Nat.card_le_card_of_surjective _ δ.rangeRestrict_surjective)
    (Nat.card_le_card_of_injective _ Subtype.val_injective)

/-- For `A₀ → B₀ → C₀ → A₁ → B₁` exact at `B₀`, `C₀`, `A₁` with `A₀`, `B₀`, `C₀`, `B₁` finite,
`A₁` is finite and `#A₁ · #B₀ ≤ #A₀ · #C₀ · #B₁`. -/
theorem finite_and_natCard_mul_le_of_exact {A₀ B₀ C₀ A₁ B₁ : Type*} [AddCommGroup A₀]
    [AddCommGroup B₀] [AddCommGroup C₀] [AddCommGroup A₁] [AddCommGroup B₁] [Finite A₀]
    [Finite B₀] [Finite C₀] [Finite B₁] (f : A₀ →+ B₀) (g : B₀ →+ C₀) (δ : C₀ →+ A₁)
    (h : A₁ →+ B₁) (hfg : ∀ b, g b = 0 ↔ ∃ a, f a = b) (hgδ : ∀ c, δ c = 0 ↔ ∃ b, g b = c)
    (hδh : ∀ a, h a = 0 ↔ ∃ c, δ c = a) :
    Finite A₁ ∧ Nat.card A₁ * Nat.card B₀ ≤ Nat.card A₀ * Nat.card C₀ * Nat.card B₁ := by
  obtain ⟨hfin, -⟩ := finite_and_natCard_le_of_exact δ h hδh
  have := hfin
  refine ⟨hfin, ?_⟩
  have kh := ker_eq_range_of_forall_apply_eq_zero_iff δ h hδh
  have kδ := ker_eq_range_of_forall_apply_eq_zero_iff g δ hgδ
  have kg := ker_eq_range_of_forall_apply_eq_zero_iff f g hfg
  rw [natCard_eq_natCard_ker_mul_natCard_range_of_finite h,
    natCard_eq_natCard_ker_mul_natCard_range_of_finite δ,
    natCard_eq_natCard_ker_mul_natCard_range_of_finite g, kh, kδ, kg]
  calc Nat.card δ.range * Nat.card h.range * (Nat.card f.range * Nat.card g.range)
      = Nat.card f.range * (Nat.card g.range * Nat.card δ.range) * Nat.card h.range := by ring
    _ ≤ Nat.card A₀ * (Nat.card g.range * Nat.card δ.range) * Nat.card B₁ :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _
          (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective))
          (Nat.card_le_card_of_injective _ Subtype.val_injective)

/-- Exactness of a short complex of modules, elementwise. -/
theorem moduleCat_g_eq_zero_iff_of_exact {R : Type*} [Ring R] {S : ShortComplex (ModuleCat.{w} R)}
    (hS : S.Exact) (y : S.X₂) : S.g.hom y = 0 ↔ ∃ x, S.f.hom x = y := by
  rw [← LinearMap.mem_ker, ← hS.moduleCat_range_eq_ker, LinearMap.mem_range]

end Counting

/-! ### The `n`-torsion of the cone of a homomorphism

For `ψ : Q → A` and `n : ℕ` the group `T = {(q, a) | ψ q = n a} / {(n q, ψ q)}` sits between
`(A/ψ(Q))[n]` (through `[(q, a)] ↦ [a]`, with kernel the classes of `(ker ψ, 0)`) and `Q/n`
(through `[(q, a)] ↦ [q]`, with kernel `A[n]` when `Q` has no `n`-torsion). Counting `T` both ways
bounds `#(A/ψ(Q))[n]` from below. -/

section Cone

variable {Q A : Type*} [AddCommGroup Q] [AddCommGroup A] (n : ℕ) (ψ : Q →+ A)

/-- The pairs `(q, a)` with `ψ q = n a`. -/
def coneCycles : AddSubgroup (Q × A) :=
  (ψ.comp (AddMonoidHom.fst Q A) - (nsmulAddMonoidHom n).comp (AddMonoidHom.snd Q A)).ker

/-- A pair `(q, a)` is a cone cycle if and only if `ψ q = n • a`. -/
theorem mem_coneCycles {p : Q × A} : p ∈ coneCycles n ψ ↔ ψ p.1 = n • p.2 := by
  simp [coneCycles, sub_eq_zero]

/-- The boundaries `q ↦ (n q, ψ q)`. -/
def coneBoundary : Q →+ coneCycles n ψ :=
  ((nsmulAddMonoidHom n).prod ψ).codRestrict _ fun q => by
    rw [mem_coneCycles]
    simp

/-- The boundary of `q` is the pair `(n • q, ψ q)`. -/
@[simp]
theorem coe_coneBoundary (q : Q) :
    ((coneBoundary n ψ q : coneCycles n ψ) : Q × A) = (n • q, ψ q) :=
  rfl

/-- The `n`-torsion of the cone of `ψ`: cycles modulo boundaries. -/
abbrev coneTorsion : Type _ :=
  coneCycles n ψ ⧸ (coneBoundary n ψ).range

/-- `[(q, a)] ↦ [a]`, to `A/ψ(Q)`. -/
def coneTorsionToQuotient : coneTorsion n ψ →+ A ⧸ ψ.range :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' ψ.range).comp
    ((AddMonoidHom.snd Q A).comp (coneCycles n ψ).subtype)) (by
      rintro _ ⟨q, rfl⟩
      rw [AddMonoidHom.mem_ker]
      simp)

variable {V : Type*} [AddCommGroup V] (red : Q →+ V)

/-- `[(q, a)] ↦ red q`, for a homomorphism `red` killing `n Q`. -/
def coneTorsionReduction (hred : ∀ q, red (n • q) = 0) : coneTorsion n ψ →+ V :=
  QuotientAddGroup.lift _ (red.comp ((AddMonoidHom.fst Q A).comp (coneCycles n ψ).subtype)) (by
    rintro _ ⟨q, rfl⟩
    rw [AddMonoidHom.mem_ker]
    simpa using hred q)

/-- `a ↦ [(0, a)]` on the `n`-torsion of `A`. -/
def torsionToConeTorsion : AddSubgroup.torsionBy A (n : ℤ) →+ coneTorsion n ψ :=
  (QuotientAddGroup.mk' _).comp
    (((AddMonoidHom.inr Q A).comp (AddSubgroup.torsionBy A (n : ℤ)).subtype).codRestrict _
      fun a => by
        rw [mem_coneCycles]
        change ψ 0 = n • (a : A)
        rw [map_zero, AddSubgroup.torsionBy.nsmul_iff.1 a.2])

variable {U : Type*} [AddCommGroup U] (θ : U →+ Q)

/-- `u ↦ [(θ u, 0)]`, for `θ` with values in the kernel of `ψ`. -/
def unitsToConeTorsion (hθ : ∀ u, ψ (θ u) = 0) : U →+ coneTorsion n ψ :=
  (QuotientAddGroup.mk' _).comp (((AddMonoidHom.inl Q A).comp θ).codRestrict _ fun u => by
    rw [mem_coneCycles]
    simp [hθ])

/-- **A lower bound for the `n`-torsion of a cokernel.** Let `ψ : Q → A`, let `θ : U → Q` have
image the kernel of `ψ`, and let `red : Q → V` be surjective onto a finite group with kernel
`n Q`, where `Q` has no `n`-torsion. Then
`#A[n] · #V ≤ #(U/n) · #(A/ψ(Q))[n] · [Q : ψ⁻¹(n A)]`, and `(A/ψ(Q))[n]` is finite. -/
theorem finite_and_natCard_mul_le_of_cone [Finite V]
    [Finite (AddSubgroup.torsionBy A (n : ℤ))]
    [Finite (U ⧸ (nsmulAddMonoidHom n : U →+ U).range)]
    (hθ : ∀ x, ψ x = 0 ↔ x ∈ θ.range) (hred : Function.Surjective red)
    (hker : ∀ x, red x = 0 ↔ ∃ y, x = n • y) (htf : ∀ x : Q, n • x = 0 → x = 0)
    (hS : ((nsmulAddMonoidHom n : A →+ A).range.comap ψ).index ≠ 0) :
    Finite (AddSubgroup.torsionBy (A ⧸ ψ.range) (n : ℤ)) ∧
      Nat.card (AddSubgroup.torsionBy A (n : ℤ)) * Nat.card V ≤
        Nat.card (U ⧸ (nsmulAddMonoidHom n : U →+ U).range) *
          Nat.card (AddSubgroup.torsionBy (A ⧸ ψ.range) (n : ℤ)) *
            ((nsmulAddMonoidHom n : A →+ A).range.comap ψ).index := by
  classical
  have hθ0 : ∀ u, ψ (θ u) = 0 := fun u => (hθ _).2 ⟨u, rfl⟩
  have hred0 : ∀ q, red (n • q) = 0 := fun q => (hker _).2 ⟨q, rfl⟩
  set π := coneTorsionToQuotient n ψ
  set ρ := coneTorsionReduction n ψ red hred0
  set α := torsionToConeTorsion (Q := Q) n ψ
  set β := unitsToConeTorsion n ψ θ hθ0
  set S := (nsmulAddMonoidHom n : A →+ A).range.comap ψ
  have hβn : (nsmulAddMonoidHom n : U →+ U).range ≤ β.ker := by
    rintro _ ⟨u, rfl⟩
    rw [AddMonoidHom.mem_ker]
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨θ u, Subtype.ext ?_⟩
    simp [hθ0]
  set β' := QuotientAddGroup.lift _ β hβn
  have hkerρ : ∀ x, ρ x = 0 ↔ x ∈ α.range := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H p =>
      constructor
      · intro hx
        obtain ⟨y, hy⟩ := (hker p.1.1).1 hx
        have hp := (mem_coneCycles n ψ).1 p.2
        have ht : (p.1.2 - ψ y) ∈ AddSubgroup.torsionBy A (n : ℤ) := by
          rw [AddSubgroup.torsionBy.nsmul_iff, smul_sub, ← hp, hy, map_nsmul]
          exact sub_self _
        refine ⟨⟨_, ht⟩, ?_⟩
        refine (QuotientAddGroup.eq_iff_sub_mem).2 ⟨-y, Subtype.ext ?_⟩
        ext <;> simp [hy]
      · rintro ⟨a, ha⟩
        rw [← ha]
        simp [ρ, α, coneTorsionReduction, torsionToConeTorsion]
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨q, hq⟩ := (QuotientAddGroup.eq_zero_iff _).1 ha
    have h1 := congrArg (fun p : coneCycles n ψ => (p : Q × A).1) hq
    have h2 := congrArg (fun p : coneCycles n ψ => (p : Q × A).2) hq
    simp only [coe_coneBoundary] at h1 h2
    have hq0 : q = 0 := htf q h1
    exact Subtype.ext (by simpa [hq0] using h2.symm)
  have hrangeπ : ∀ y, y ∈ π.range ↔ y ∈ AddSubgroup.torsionBy (A ⧸ ψ.range) (n : ℤ) := by
    intro y
    rw [AddSubgroup.torsionBy.nsmul_iff]
    constructor
    · rintro ⟨x, rfl⟩
      induction x using QuotientAddGroup.induction_on with
      | H p =>
        have hp := (mem_coneCycles n ψ).1 p.2
        show n • (QuotientAddGroup.mk (p : Q × A).2 : A ⧸ ψ.range) = 0
        rw [← QuotientAddGroup.mk_nsmul, ← hp, QuotientAddGroup.eq_zero_iff]
        exact ⟨_, rfl⟩
    · induction y using QuotientAddGroup.induction_on with
      | H a =>
        intro ha
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at ha
        obtain ⟨q, hq⟩ := ha
        exact ⟨QuotientAddGroup.mk ⟨(q, a), (mem_coneCycles n ψ).2 hq⟩, rfl⟩
  have hkerπ : ∀ x, π x = 0 → x ∈ β'.range := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H p =>
      intro hx
      obtain ⟨q', hq'⟩ := (QuotientAddGroup.eq_zero_iff _).1 hx
      have hp := (mem_coneCycles n ψ).1 p.2
      have hk : ψ ((p : Q × A).1 - n • q') = 0 := by
        rw [map_sub, map_nsmul, hp, hq']
        exact sub_self _
      obtain ⟨u, hu⟩ := (hθ _).1 hk
      refine ⟨QuotientAddGroup.mk u, ?_⟩
      show β u = _
      refine (QuotientAddGroup.eq_iff_sub_mem).2 ⟨-q', Subtype.ext ?_⟩
      ext <;> simp [hu, hq']
  have hSρ : S.map red ≤ ρ.range := by
    rintro _ ⟨q, ⟨a, ha⟩, rfl⟩
    exact ⟨QuotientAddGroup.mk ⟨(q, a), (mem_coneCycles n ψ).2 ha.symm⟩, rfl⟩
  have : Finite α.range := Set.finite_range α |>.to_subtype
  have hkρ : ρ.ker = α.range := AddSubgroup.ext hkerρ
  have : Finite ρ.ker := hkρ ▸ inferInstance
  have : Finite (coneTorsion n ψ) := finite_of_finite_ker_of_finite_range ρ
  have htors : π.range = AddSubgroup.torsionBy (A ⧸ ψ.range) (n : ℤ) :=
    AddSubgroup.ext hrangeπ
  have : Finite π.range := Set.finite_range π |>.to_subtype
  refine ⟨htors ▸ inferInstance, ?_⟩
  have hT1 : Nat.card (coneTorsion n ψ) =
      Nat.card (AddSubgroup.torsionBy A (n : ℤ)) * Nat.card ρ.range := by
    rw [natCard_eq_natCard_ker_mul_natCard_range_of_finite ρ, hkρ,
      ← Nat.card_congr (AddMonoidHom.ofInjective hαinj).toEquiv]
  have hT2 : Nat.card (coneTorsion n ψ) ≤
      Nat.card (U ⧸ (nsmulAddMonoidHom n : U →+ U).range) *
        Nat.card (AddSubgroup.torsionBy (A ⧸ ψ.range) (n : ℤ)) := by
    rw [natCard_eq_natCard_ker_mul_natCard_range_of_finite π, htors]
    refine Nat.mul_le_mul_right _ ((Nat.card_mono (Set.toFinite _) fun x hx => hkerπ x hx).trans ?_)
    exact Nat.card_le_card_of_surjective _ (β'.rangeRestrict_surjective)
  have hV : Nat.card V ≤ Nat.card ρ.range * S.index := by
    rw [← AddSubgroup.card_mul_index (S.map red)]
    refine Nat.mul_le_mul (AddSubgroup.card_le_of_le hSρ) ?_
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hS) (AddSubgroup.index_map_dvd _ hred)
  calc Nat.card (AddSubgroup.torsionBy A (n : ℤ)) * Nat.card V
      ≤ Nat.card (AddSubgroup.torsionBy A (n : ℤ)) * (Nat.card ρ.range * S.index) :=
        Nat.mul_le_mul_left _ hV
    _ = Nat.card (coneTorsion n ψ) * S.index := by rw [hT1, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hT2

end Cone

/-! ### Cohomology of constant sheaves on finite products of groups -/

section ConstantProducts

variable (X : Scheme.{u})

/-- `(Π i, M_i)_X ≅ ⨁ i, (M_i)_X`: the constant sheaf functor is additive. -/
def etaleConstantSheafPiIso {ι : Type} [Finite ι] (M : ι → Type) [∀ i, AddCommGroup (M i)] :
    etaleConstantSheaf.{u, 0} X (Π i, M i) ≅ ⨁ fun i => etaleConstantSheaf.{u, 0} X (M i) :=
  haveI := Fintype.ofFinite ι
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (((AddEquiv.ulift.{0, u + 1} (α := Π i, M i)).trans
        ((AddEquiv.piCongrRight fun i =>
          (AddEquiv.ulift.{0, u + 1} (α := M i)).symm))).toAddCommGrpIso ≪≫
        (AddCommGrpCat.biproductIsoPi fun i => AddCommGrpCat.of (ULift.{u + 1} (M i))).symm) ≪≫
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapBiproduct _

/-- **`Hᵠ(X, (Π i, M_i)_X) ≃+ Π i, Hᵠ(X, (M_i)_X)`** for a finite family of groups. -/
def sheafHEtaleConstantPiAddEquiv {ι : Type} [Finite ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] (q : ℕ) :
    Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (Π i, M i)) q ≃+
      Π i, Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (M i)) q :=
  haveI := Fintype.ofFinite ι
  (sheafHAddEquivOfIso (etaleConstantSheafPiIso X M) q).trans
    (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit _) q)

/-- `Hᵠ(X, M_X) ≃+ Hᵠ(X, N_X)` for `M ≃+ N`. -/
def sheafHEtaleConstantAddEquivOfAddEquiv {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (q : ℕ) :
    Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X M) q ≃+
      Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X N) q :=
  sheafHAddEquivOfIso ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    (((AddEquiv.ulift.{0, u + 1} (α := M)).trans
      (e.trans (AddEquiv.ulift.{0, u + 1} (α := N)).symm)).toAddCommGrpIso)) q

/-- **The cardinality of `Hᵠ(X, A_X)` is multiplicative in a finite group `A`**: for
`A ≃+ ⨁ i, ℤ/(p_i^{e_i})` it is the product of the cardinalities for the cyclic summands. Any
statement of the form `#Hᵠ(X, (ℤ/m)_X) ~ m^k` for the orders `m ∣ N` therefore passes to all
finite groups killed by `N`, and is recorded here for `≤`, `≥` and `=`. -/
theorem natCard_sheafH_etaleConstantSheaf_eq_prod {A : Type} [AddCommGroup A] {ι : Type}
    [Fintype ι] (m : ι → ℕ) (e : A ≃+ Π i, ZMod (m i)) (q : ℕ) :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X A) q) =
      ∏ i, Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod (m i))) q) := by
  rw [Nat.card_congr (sheafHEtaleConstantAddEquivOfAddEquiv X e q).toEquiv,
    Nat.card_congr (sheafHEtaleConstantPiAddEquiv X _ q).toEquiv, Nat.card_pi]

end ConstantProducts

/-- **Structure theorem, in product form**: a finite abelian group killed by `N` is a finite
product of cyclic groups `ℤ/m_i` with `m_i ∣ N`. -/
theorem exists_addEquiv_pi_zmod_of_finite (A : Type) [AddCommGroup A] [Finite A] (N : ℕ)
    (hN : ∀ a : A, N • a = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (_ : ∀ i, m i ∣ N),
      Nonempty (A ≃+ Π i, ZMod (m i)) := by
  classical
  obtain ⟨ι, hι, p, -, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let g : A ≃+ Π i, ZMod (p i ^ e i) :=
    f.trans (DirectSum.linearEquivFunOnFintype ℤ ι fun i => ZMod (p i ^ e i)).toAddEquiv
  refine ⟨ι, hι, fun i => p i ^ e i, fun i => ?_, ⟨g⟩⟩
  have h0 : g (N • g.symm (Pi.single i 1)) = 0 := by rw [hN, map_zero]
  rw [map_nsmul, AddEquiv.apply_symm_apply] at h0
  have h1 := congrArg (fun x => x i) h0
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Pi.zero_apply] at h1
  exact (ZMod.natCast_eq_zero_iff _ _).1 h1

/-! ### From cyclic coefficients to finite coefficients -/

section Transfer

variable (X : Scheme.{u}) (q k N : ℕ)

/-- A finite group `A` killed by `N` is a product of cyclic groups `ℤ/m_i` with `m_i ∣ N`, so that
`#Hᵠ(X, A_X)` and `#A^k` are the products of the corresponding cyclic quantities. -/
private theorem exists_prod_natCard_sheafH_etaleConstantSheaf_of_nsmul_eq_zero
    (A : Type) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ), (∀ i, m i ∣ N) ∧
      Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X A) q) =
        ∏ i, Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod (m i))) q) ∧
      Nat.card A ^ k = ∏ i, m i ^ k := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ := exists_addEquiv_pi_zmod_of_finite A N hN
  refine ⟨ι, hι, m, hm, ?_, ?_⟩
  · rw [natCard_sheafH_etaleConstantSheaf_eq_prod X m e q]
  · rw [Nat.card_congr e.toEquiv, Nat.card_pi, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [Nat.card_zmod]

/-- `#Hᵠ(X, A_X) = #A^k` for every finite group `A` killed by `N`, from the cyclic case. -/
theorem natCard_sheafH_etaleConstantSheaf_eq_pow_of_zmod
    (h : ∀ m, m ∣ N → Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod m)) q) = m ^ k)
    (A : Type) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X A) q) = Nat.card A ^ k := by
  obtain ⟨ι, hι, m, hm, h1, h2⟩ :=
    exists_prod_natCard_sheafH_etaleConstantSheaf_of_nsmul_eq_zero X q k N A hN
  rw [h1, h2]
  exact Finset.prod_congr rfl fun i _ => h _ (hm i)

/-- `#Hᵠ(X, A_X) ≤ #A^k` for every finite group `A` killed by `N`, from the cyclic case. -/
theorem natCard_sheafH_etaleConstantSheaf_le_pow_of_zmod
    (h : ∀ m, m ∣ N → Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod m)) q) ≤ m ^ k)
    (A : Type) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X A) q) ≤ Nat.card A ^ k := by
  obtain ⟨ι, hι, m, hm, h1, h2⟩ :=
    exists_prod_natCard_sheafH_etaleConstantSheaf_of_nsmul_eq_zero X q k N A hN
  rw [h1, h2]
  exact Finset.prod_le_prod' fun i _ => h _ (hm i)

/-- `#A^k ≤ #Hᵠ(X, A_X)` for every finite group `A` killed by `N`, from the cyclic case. -/
theorem pow_le_natCard_sheafH_etaleConstantSheaf_of_zmod
    (h : ∀ m, m ∣ N → m ^ k ≤ Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod m)) q))
    (A : Type) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    Nat.card A ^ k ≤ Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X A) q) := by
  obtain ⟨ι, hι, m, hm, h1, h2⟩ :=
    exists_prod_natCard_sheafH_etaleConstantSheaf_of_nsmul_eq_zero X q k N A hN
  rw [h1, h2]
  exact Finset.prod_le_prod' fun i _ => h _ (hm i)

/-- `Hᵠ(X, A_X)` is finite for every finite group `A` killed by `N`, from the cyclic case. -/
theorem finite_sheafH_etaleConstantSheaf_of_zmod
    (h : ∀ m, m ∣ N → Finite (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod m)) q))
    (A : Type) [AddCommGroup A] [Finite A] (hN : ∀ a : A, N • a = 0) :
    Finite (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X A) q) := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ := exists_addEquiv_pi_zmod_of_finite A N hN
  have := fun i => h _ (hm i)
  exact Finite.of_equiv _
    ((sheafHEtaleConstantAddEquivOfAddEquiv X e q).trans
      (sheafHEtaleConstantPiAddEquiv X _ q)).symm.toEquiv

end Transfer

/-! ### Cyclic coefficients -/

section Cyclic

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **`#H⁰(X, ℤ/m) = m`** on an integral scheme over an algebraically closed field in which `m`
is invertible: every class is a constant class. -/
theorem natCard_sheafH_zero_etaleConstantSheaf_zmod {X : Scheme.{u}} (gX : X ⟶ Spec (.of K))
    [IsIntegral X] {m : ℕ} (hm : IsUnit (m : K)) :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod m)) 0) = m := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hm
  have hm0 := ne_zero_of_isUnit_natCast gX hm
  rw [← Nat.card_congr (Equiv.ofBijective _ (etaleConstantClass_bijective gX hζ hm0)),
    Nat.card_zmod]

/-- **`#H¹(X, ℤ/m) = m^{2g}`** for a smooth proper curve of genus `g` over an algebraically
closed field in which `m` is invertible: `ℤ/m ≅ μ_m` and `H¹(X, μ_m) = Pic(X)[m]`. -/
theorem natCard_sheafH_one_etaleConstantSheaf_zmod_of_isProper {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f] {m : ℕ} (hm : IsUnit (m : K)) :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} X (ZMod m)) 1) = m ^ (2 * genus f) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hm
  have hm0 := ne_zero_of_isUnit_natCast f hm
  have : IsProjectiveVariety K f := (isProjectiveVariety_iff_isProjectiveMorphism K f).2
    (isProjectiveMorphism_of_isProper_of_isCurve K f)
  rw [Nat.card_congr (sheafHRootsOfUnityConstantAddEquiv f hζ hm0 1).toEquiv,
    Nat.card_congr (Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion_of_isCurve.{u + 1, 0, u}
      X m hm0 (Stacks.Kummer.isUnit_natCast_globalSections X m f hm) f hm).toEquiv]
  exact Stacks.Picard.natCard_torsionBy_eq_pow_genus f m hm

/-- On a finite reduced scheme the `m`-th roots of unity of the global functions are finite and
number at most `m^{#Z}`: a global function is determined by its values in the residue fields. -/
theorem finite_rootsOfUnity_and_natCard_le_pow_natCard (Z : Scheme.{u}) [IsReduced Z] [Finite Z]
    (m : ℕ) [NeZero m] :
    Finite (rootsOfUnity m Γ(Z, ⊤)) ∧ Nat.card (rootsOfUnity m Γ(Z, ⊤)) ≤ m ^ Nat.card Z := by
  classical
  have := Fintype.ofFinite Z
  let φ : rootsOfUnity m Γ(Z, ⊤) → Π z : Z, rootsOfUnity m (Z.residueField z) := fun x z =>
    ⟨Units.map (Z.Γevaluation z).hom.toMonoidHom x, by
      rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity _ _).1 x.2, map_one]⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    refine Subtype.ext (Units.ext ?_)
    rw [← sub_eq_zero]
    refine eq_zero_of_basicOpen_eq_bot _ ?_
    rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
    intro z
    have h := congrArg (fun f => ((f z.1 : (Z.residueField z.1)ˣ) : Z.residueField z.1)) hxy
    simp only [φ, Units.coe_map] at h
    rw [map_sub, sub_eq_zero]
    exact h
  have : Finite (rootsOfUnity m Γ(Z, ⊤)) := Finite.of_injective φ hφ
  refine ⟨inferInstance, ?_⟩
  calc Nat.card (rootsOfUnity m Γ(Z, ⊤))
      ≤ Nat.card (Π z : Z, rootsOfUnity m (Z.residueField z)) := Nat.card_le_card_of_injective φ hφ
    _ = ∏ z, Nat.card (rootsOfUnity m (Z.residueField z)) := Nat.card_pi
    _ ≤ ∏ _z : Z, m := Finset.prod_le_prod' fun z _ => card_rootsOfUnity _ _
    _ = m ^ Nat.card Z := by rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **`#H⁰(Z, ℤ/m) ≤ m^{#Z}`** on a finite reduced scheme over an algebraically closed field in
which `m` is invertible: through `ℤ/m ≅ μ_m`, a class is an `m`-th root of unity in `Γ(Z, 𝒪_Z)`. -/
theorem natCard_sheafH_zero_etaleConstantSheaf_zmod_le_of_finite {Z : Scheme.{u}}
    (gZ : Z ⟶ Spec (.of K)) [IsReduced Z] [Finite Z] {m : ℕ} (hm : IsUnit (m : K)) :
    Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Z (ZMod m)) 0) ≤ m ^ Nat.card Z := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hm
  have hm0 := ne_zero_of_isUnit_natCast gZ hm
  have : NeZero m := ⟨hm0⟩
  obtain ⟨hfin, hcard⟩ := finite_rootsOfUnity_and_natCard_le_pow_natCard Z m
  exact (Nat.card_le_card_of_injective _ (h0EtaleConstantToRootsOfUnity_injective gZ hζ hm0)).trans
    hcard

/-- `H⁰(Z, ℤ/m)` is finite on a finite reduced scheme over an algebraically closed field in which
`m` is invertible. -/
theorem finite_sheafH_zero_etaleConstantSheaf_zmod_of_finite {Z : Scheme.{u}}
    (gZ : Z ⟶ Spec (.of K)) [IsReduced Z] [Finite Z] {m : ℕ} (hm : IsUnit (m : K)) :
    Finite (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Z (ZMod m)) 0) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hm
  have hm0 := ne_zero_of_isUnit_natCast gZ hm
  have : NeZero m := ⟨hm0⟩
  obtain ⟨hfin, -⟩ := finite_rootsOfUnity_and_natCard_le_pow_natCard Z m
  exact Finite.of_injective _ (h0EtaleConstantToRootsOfUnity_injective gZ hζ hm0)

end Cyclic

/-! ### The Kummer count -/

section KummerCount

open Stacks.Kummer

/-- A group covered by finitely many translates of `n G` has finite quotient `G/n G`. -/
theorem finite_quotient_nsmul_of_exists_finset {G : Type*} [AddCommGroup G] (n : ℕ) (T : Finset G)
    (hT : ∀ x, ∃ t ∈ T, ∃ y, x = t + n • y) :
    Finite (G ⧸ (nsmulAddMonoidHom n : G →+ G).range) := by
  refine Finite.of_surjective (fun t : T => (QuotientAddGroup.mk (t : G) : G ⧸ _)) ?_
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨t, ht, y, rfl⟩ := hT x
    refine ⟨⟨t, ht⟩, (QuotientAddGroup.eq_iff_sub_mem).2 ⟨-y, ?_⟩⟩
    simp

variable {K : Type u} [Field K] {X : Scheme.{u}} (gX : X ⟶ Spec (.of K)) {n : ℕ}
  (hn : IsUnit (n : K))

include gX hn in
/-- **`#H¹(X, μ_n) = #(H⁰(X, 𝐆_m)/n) · #H¹(X, 𝐆_m)[n]`**, from the Kummer sequence, when the two
right-hand groups are finite (and then `H¹(X, μ_n)` is finite). -/
theorem finite_and_natCard_sheafH_one_rootsOfUnitySheaf
    [Finite (Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 ⧸
      (nsmulAddMonoidHom n : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 →+ _).range)]
    [Finite (AddSubgroup.torsionBy (Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 1) (n : ℤ))] :
    Finite (Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) 1) ∧
      Nat.card (Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} X n) 1) =
        Nat.card (Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 ⧸
          (nsmulAddMonoidHom n : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 →+ _).range) *
        Nat.card (AddSubgroup.torsionBy (Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 1)
          (n : ℤ)) := by
  have hn0 := ne_zero_of_isUnit_natCast gX hn
  have hX := isUnit_natCast_globalSections X n gX hn
  set δ := kummerδ.{u + 1, u, 0} X hn0 hX 0
  set ι := Sheaf.H.map.{u + 1} (rootsOfUnityι.{u, 0} X n) 1
  have hkerδ : δ.ker = (nsmulAddMonoidHom n : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 →+
      _).range := by
    ext y
    rw [AddMonoidHom.mem_ker, ← mem_range_sheafH_map_powMap_iff X hn0 hX 0 y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, (sheafH_map_powMap X n 0 z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, sheafH_map_powMap X n 0 z⟩
  have hkerι : ι.ker = δ.range := by
    ext x
    rw [AddMonoidHom.mem_ker]
    exact (mem_range_kummerδ_iff X hn0 hX 0 x).symm
  have hrangeι : ι.range = AddSubgroup.torsionBy (Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 1)
      (n : ℤ) := by
    ext x
    rw [AddSubgroup.torsionBy.nsmul_iff, ← sheafH_map_powMap X n 1 x]
    exact mem_range_sheafH_map_rootsOfUnityι_iff X hn0 hX 1 x
  have eδ : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 ⧸
      (nsmulAddMonoidHom n : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, 0} X) 0 →+ _).range ≃+
        δ.range :=
    (QuotientAddGroup.quotientAddEquivOfEq hkerδ).symm.trans
      (QuotientAddGroup.quotientKerEquivRange δ)
  have : Finite δ.range := Finite.of_equiv _ eδ.toEquiv
  have : Finite ι.ker := hkerι ▸ inferInstance
  have : Finite ι.range := hrangeι ▸ inferInstance
  have := finite_of_finite_ker_of_finite_range ι
  refine ⟨inferInstance, ?_⟩
  rw [natCard_eq_natCard_ker_mul_natCard_range_of_finite ι, hkerι, hrangeι,
    Nat.card_congr eδ.toEquiv]

end KummerCount

/-! ### Divisors at the boundary of an open subcurve -/

section Boundary

variable {K : Type u} [Field K] {D Db : Scheme.{u}}
  (q : D ⟶ Spec (.of K)) [IsCurve K q] (qb : Db ⟶ Spec (.of K)) [IsCurve K qb]
  (jD : D ⟶ Db) [IsOpenImmersion jD] [IsIntegral D] [IsIntegral Db]

/-- The divisors on `Db` supported on the closed points outside `D`. -/
abbrev boundaryDivisors : AddSubgroup (closedPoints Db →₀ ℤ) :=
  (closedPointDivisorRestriction q qb jD).ker

/-- A divisor on `Db` is a boundary divisor if and only if it vanishes at every closed point in
the image of `D`. -/
theorem mem_boundaryDivisors_iff (d : closedPoints Db →₀ ℤ) :
    d ∈ boundaryDivisors q qb jD ↔ ∀ y : closedPoints Db, y.1 ∈ Set.range jD.base → d y = 0 := by
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro hd y hy
    obtain ⟨x, rfl⟩ := exists_closedPointsMapOfOpenImmersion_eq q qb jD y hy
    rw [← closedPointDivisorRestriction_apply, hd, Finsupp.zero_apply]
  · intro hd
    refine Finsupp.ext fun x => ?_
    rw [closedPointDivisorRestriction_apply, Finsupp.zero_apply]
    exact hd _ ⟨x.1, rfl⟩

/-- The closed points of `Db` outside `D`. -/
abbrev BoundaryPoints : Type u :=
  {y : closedPoints Db // y.1 ∉ Set.range jD.base}

/-- `d ↦ (d(z) mod n)_z` on boundary divisors. -/
def boundaryReduction (n : ℕ) : boundaryDivisors q qb jD →+ (BoundaryPoints jD → ZMod n) where
  toFun d := fun z => (((d : closedPoints Db →₀ ℤ) z.1 : ℤ) : ZMod n)
  map_zero' := by
    ext z
    simp
  map_add' d e := by
    ext z
    simp

/-- When there are finitely many boundary points and `n ≠ 0`, the reduction modulo `n` of boundary
divisors is surjective. -/
theorem surjective_boundaryReduction [Finite (BoundaryPoints jD)] (n : ℕ) [NeZero n] :
    Function.Surjective (boundaryReduction q qb jD n) := by
  classical
  intro v
  let d : closedPoints Db →₀ ℤ := Finsupp.mapDomain Subtype.val
    (Finsupp.equivFunOnFinite.symm fun z : BoundaryPoints jD => ((v z).val : ℤ))
  have hd : d ∈ boundaryDivisors q qb jD := by
    rw [mem_boundaryDivisors_iff]
    intro y hy
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨z, rfl⟩
    exact z.2 hy
  refine ⟨⟨d, hd⟩, funext fun z => ?_⟩
  show (((d z.1 : ℤ)) : ZMod n) = v z
  rw [Finsupp.mapDomain_apply Subtype.val_injective, Finsupp.coe_equivFunOnFinite_symm]
  simp

/-- A boundary divisor reduces to zero modulo `n` if and only if it is `n` times a boundary
divisor. -/
theorem boundaryReduction_eq_zero_iff (n : ℕ) (x : boundaryDivisors q qb jD) :
    boundaryReduction q qb jD n x = 0 ↔ ∃ y, x = n • y := by
  constructor
  · intro hx
    have hdvd : ∀ y : closedPoints Db, (n : ℤ) ∣ (x : closedPoints Db →₀ ℤ) y := by
      intro y
      by_cases hy : y.1 ∈ Set.range jD.base
      · rw [(mem_boundaryDivisors_iff q qb jD _).1 x.2 y hy]
        exact dvd_zero _
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hx ⟨y, hy⟩)
    let e : closedPoints Db →₀ ℤ :=
      Finsupp.mapRange (fun a : ℤ => a / (n : ℤ)) (by simp) (x : closedPoints Db →₀ ℤ)
    have he : e ∈ boundaryDivisors q qb jD := by
      rw [mem_boundaryDivisors_iff]
      intro y hy
      simp [e, (mem_boundaryDivisors_iff q qb jD _).1 x.2 y hy]
    refine ⟨⟨e, he⟩, Subtype.ext (Finsupp.ext fun y => ?_)⟩
    simp only [AddSubgroup.coe_nsmul, Finsupp.coe_smul, Pi.smul_apply, e,
      Finsupp.mapRange_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd y)).symm
  · rintro ⟨y, rfl⟩
    ext z
    simp [boundaryReduction]

/-- The group of boundary divisors is torsion-free: `n • x = 0` with `n ≠ 0` implies `x = 0`. -/
theorem eq_zero_of_nsmul_eq_zero_boundaryDivisors {n : ℕ} (hn : n ≠ 0)
    (x : boundaryDivisors q qb jD) (hx : n • x = 0) : x = 0 := by
  refine Subtype.ext (Finsupp.ext fun y => ?_)
  have h := congrArg (fun d : boundaryDivisors q qb jD => (d : closedPoints Db →₀ ℤ) y) hx
  simp only [AddSubgroup.coe_nsmul, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul,
    ZeroMemClass.coe_zero, Finsupp.coe_zero, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at h
  simpa [hn] using h

/-- With no points at infinity there are no nonzero boundary divisors. -/
theorem eq_zero_of_isEmpty_boundaryPoints [IsEmpty (BoundaryPoints jD)]
    (x : boundaryDivisors q qb jD) : x = 0 :=
  Subtype.ext (Finsupp.ext fun y => by
    by_cases hy : y.1 ∈ Set.range jD.base
    · exact (mem_boundaryDivisors_iff q qb jD _).1 x.2 y hy
    · exact isEmptyElim (⟨y, hy⟩ : BoundaryPoints jD))

variable [IsLocallyNoetherian D] [IsLocallyNoetherian Db] [TopologicalSpace.NoetherianSpace D]
  [TopologicalSpace.NoetherianSpace Db]

/-- A boundary divisor and its class on `Db`. -/
def boundaryClassMap : boundaryDivisors q qb jD →+ closedPointClassGroup Db :=
  (QuotientAddGroup.mk' _).comp (boundaryDivisors q qb jD).subtype

/-- **The classes of the boundary divisors are the kernel of restriction of classes to `D`.** -/
theorem range_boundaryClassMap :
    (boundaryClassMap q qb jD).range = (closedPointClassGroupRestriction q qb jD).ker := by
  classical
  rw [ker_closedPointClassGroupRestriction]
  apply le_antisymm
  · rintro _ ⟨d, rfl⟩
    have h := mem_closure_of_closedPointDivisorRestriction_eq_zero q qb jD d.1 d.2
    have h' :=
      AddSubgroup.mem_map_of_mem (QuotientAddGroup.mk' (closedPointDivisorOfUnit Db).range) h
    rwa [AddMonoidHom.map_closure, Set.image_image] at h'
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨Finsupp.single y 1, ?_⟩, rfl⟩
    rw [mem_boundaryDivisors_iff]
    intro y' hy'
    rw [Finsupp.single_apply, ite_eq_right]
    rintro rfl
    exact hy hy'

/-- **`Cl(D) ≅ Cl(Db)/⟨boundary⟩`.** -/
def closedPointClassGroupAddEquivQuotient :
    closedPointClassGroup D ≃+ closedPointClassGroup Db ⧸ (boundaryClassMap q qb jD).range :=
  ((QuotientAddGroup.quotientAddEquivOfEq (range_boundaryClassMap q qb jD)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_closedPointClassGroupRestriction q qb jD))).symm

include q in
/-- The germ at the generic point of a global unit has trivial divisor on a curve. -/
theorem closedPointDivisorOfUnit_germ_eq_zero (a : (Γ(D, ⊤))ˣ) :
    closedPointDivisorOfUnit D (Additive.ofMul
      (Units.map (D.presheaf.germ ⊤ (genericPoint D) trivial).hom.toMonoidHom a)) = 0 := by
  refine Finsupp.ext fun x => ?_
  rw [closedPointDivisorOfUnit_apply, Finsupp.zero_apply]
  have hx := ne_genericPoint_of_mem_closedPoints_of_isCurve q x
  have h := Stacks.AlgebraicGeometry.MeromorphicConstant.ord_algebraMap_of_isUnit D
    (IsCurve.coheight_eq_one q hx) (u := D.presheaf.germ ⊤ x.1 trivial (a : Γ(D, ⊤)))
    ((Units.isUnit a).map _)
  have hg : algebraMap (D.presheaf.stalk x.1) D.functionField
      (D.presheaf.germ ⊤ x.1 trivial (a : Γ(D, ⊤))) =
        D.presheaf.germ ⊤ (genericPoint D) trivial (a : Γ(D, ⊤)) := by
    show (D.presheaf.stalkSpecializes _).hom (D.presheaf.germ ⊤ x.1 trivial (a : Γ(D, ⊤))) = _
    rw [← CommRingCat.comp_apply]
    exact congrArg (fun f => (ConcreteCategory.hom f) (a : Γ(D, ⊤)))
      (TopCat.Presheaf.germ_stalkSpecializes D.presheaf (U := ⊤) (y := x.1) trivial
        ((genericPoint_spec D).specializes trivial))
  rwa [hg] at h

variable [IsDominant jD]

/-- **The divisor of a unit on `D`, as a boundary divisor on `Db`.** -/
def unitBoundaryDivisor : Additive (Γ(D, ⊤))ˣ →+ boundaryDivisors q qb jD :=
  ((closedPointDivisorOfUnit Db).comp (MonoidHom.toAdditive
    ((Units.map (Stacks.Chow.functionFieldEquiv_openImmersion jD).symm.toMonoidHom).comp
      (Units.map (D.presheaf.germ ⊤ (genericPoint D) trivial).hom.toMonoidHom)))).codRestrict _
    fun a => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
        closedPointDivisorRestriction_closedPointDivisorOfUnit q qb jD]
      convert closedPointDivisorOfUnit_germ_eq_zero q (Additive.toMul a) using 3
      ext
      simp

/-- The underlying divisor of `unitBoundaryDivisor q qb jD a` is the divisor on `Db` of the unit
`a`, viewed in the function field of `Db`. -/
theorem coe_unitBoundaryDivisor (a : Additive (Γ(D, ⊤))ˣ) :
    (unitBoundaryDivisor q qb jD a : closedPoints Db →₀ ℤ) = closedPointDivisorOfUnit Db
      (Additive.ofMul (Units.map (Stacks.Chow.functionFieldEquiv_openImmersion jD).symm.toMonoidHom
        (Units.map (D.presheaf.germ ⊤ (genericPoint D) trivial).hom.toMonoidHom
          (Additive.toMul a)))) :=
  rfl

/-- **The principal boundary divisors are the divisors of the units on `D`** (algebraic
Hartogs on the normal curve `D`). -/
theorem boundaryClassMap_eq_zero_iff [IsNormal D] (x : boundaryDivisors q qb jD) :
    boundaryClassMap q qb jD x = 0 ↔ x ∈ (unitBoundaryDivisor q qb jD).range := by
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := (QuotientAddGroup.eq_zero_iff _).1 hx
    set g : D.functionFieldˣ :=
      Units.map (Stacks.Chow.functionFieldEquiv_openImmersion jD).toMonoidHom (Additive.toMul f)
    have hres := closedPointDivisorRestriction_closedPointDivisorOfUnit q qb jD f
    have hx0 : closedPointDivisorRestriction q qb jD ((boundaryDivisors q qb jD).subtype x) = 0 :=
      x.2
    rw [hf, hx0] at hres
    have hord : ∀ y : D, Order.coheight y = 1 → Scheme.ord (g : D.functionField) y = 0 := by
      intro y hy
      have hcl := isClosed_singleton_of_coheight_eq_one q hy
      have h := congrArg (fun d : closedPoints D →₀ ℤ => d ⟨y, hcl⟩) hres
      simpa [closedPointDivisorOfUnit_apply, g] using h.symm
    obtain ⟨s, hs⟩ :=
      Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero g hord
    refine ⟨Additive.ofMul s, Subtype.ext ?_⟩
    rw [coe_unitBoundaryDivisor]
    refine Eq.trans ?_ hf
    congr 1
    ext
    simp [hs, g]
  · rintro ⟨a, rfl⟩
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, (coe_unitBoundaryDivisor q qb jD a).symm⟩

end Boundary

/-! ### The lower bound on an open subcurve -/

section Transport

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The `n`-torsion subgroups of isomorphic groups correspond. -/
def torsionByEquivOfAddEquiv (e : G ≃+ H) (n : ℕ) :
    AddSubgroup.torsionBy G (n : ℤ) ≃ AddSubgroup.torsionBy H (n : ℤ) :=
  e.toEquiv.subtypeEquiv fun x => by
    rw [AddSubgroup.torsionBy.nsmul_iff, AddSubgroup.torsionBy.nsmul_iff]
    change _ ↔ n • e x = 0
    rw [← map_nsmul, e.map_eq_zero_iff]

/-- Additively isomorphic groups have `n`-torsion subgroups of the same cardinality. -/
theorem natCard_torsionBy_congr (e : G ≃+ H) (n : ℕ) :
    Nat.card (AddSubgroup.torsionBy G (n : ℤ)) = Nat.card (AddSubgroup.torsionBy H (n : ℤ)) :=
  Nat.card_congr (torsionByEquivOfAddEquiv e n)

/-- `G/nG ≃+ H/nH` for `G ≃+ H`. -/
def quotientNsmulAddEquiv (e : G ≃+ H) (n : ℕ) :
    G ⧸ (nsmulAddMonoidHom n : G →+ G).range ≃+ H ⧸ (nsmulAddMonoidHom n : H →+ H).range :=
  QuotientAddGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨n • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩)

end Transport

/-- **`H⁰(X, 𝐆_m) ≃+ Γ(X, 𝒪_X)^*`**: the sections of `𝐆_m` over the terminal étale `X`-scheme. -/
def sheafHZeroMultiplicativeAddEquivUnits (X : Scheme.{u}) :
    Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} X) 0 ≃+ Additive (Γ(X, ⊤))ˣ :=
  (Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, 0} X) (isTerminalEtaleMkId X)).trans
    (AddEquiv.ulift (α := Additive (Γ(X, ⊤))ˣ))

section LowerBound

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable {K : Type u} [Field K] [IsAlgClosed K] {D Db : Scheme.{u}}
  (q : D ⟶ Spec (.of K)) [IsCurve K q] [Smooth q]
  (qb : Db ⟶ Spec (.of K)) [IsCurve K qb] [Smooth qb]
  (jD : D ⟶ Db) [IsOpenImmersion jD]

include q qb in
omit [Smooth q] in
/-- **A curve open in a curve has finite complement.** -/
theorem finite_compl_range_of_isCurve : ((Set.range jD.base)ᶜ).Finite := by
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve qb
  refine Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := qb)).le
    jD.isOpenEmbedding.isOpen_range.isClosed_compl fun h => ?_
  obtain ⟨x⟩ : Nonempty D := inferInstance
  exact Set.eq_univ_iff_forall.1 h (jD.base x) ⟨x, rfl⟩

include q qb in
omit [Smooth q] in
/-- A curve `Db` has only finitely many closed points outside the open subscheme `D`. -/
theorem finite_boundaryPoints : Finite (BoundaryPoints jD) := by
  have := (finite_compl_range_of_isCurve q qb jD).to_subtype
  exact Finite.of_injective
    (fun z : BoundaryPoints jD => (⟨z.1.1, z.2⟩ : ((Set.range jD.base)ᶜ : Set Db)))
    fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)

variable [IsProper qb]

/-- **A divisor class of degree divisible by `n ∈ K^*` is divisible by `n`** on a smooth proper
curve over an algebraically closed field: `Pic⁰` is `n`-divisible (through the Jacobian) and the
class of a closed point has degree one. -/
theorem exists_nsmul_eq_of_dvd_curveClassGroupDegree {n : ℕ} (hn : IsUnit (n : K))
    (p : closedPoints Db) (c : curveClassGroup qb) (hc : (n : ℤ) ∣ curveClassGroupDegree qb c) :
    ∃ b : curveClassGroup qb, c = n • b := by
  have hdim : topologicalKrullDim Db ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := qb)).le
  obtain ⟨k, hk⟩ := hc
  set P : curveClassGroup qb :=
    (QuotientAddGroup.mk (Finsupp.single p (1 : ℤ)) : curveClassGroup qb)
  have hP : curveClassGroupDegree qb P = 1 := by
    simp [P]
  have h0 : c - ((n : ℤ) * k) • P ∈ (curveClassGroupDegree qb).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, map_zsmul, hP, hk, smul_eq_mul, mul_one, sub_self]
  set e := curveClassGroupDegreeZeroAddEquiv qb hdim
  obtain ⟨y, hy⟩ := exists_nsmul_eq_of_mem_picardDegreeZero qb hdim hn (e ⟨_, h0⟩)
  have hy' : n • e.symm y = ⟨_, h0⟩ := by
    rw [← map_nsmul, hy, AddEquiv.symm_apply_apply]
  have hx : n • (e.symm y : curveClassGroup qb) = c - ((n : ℤ) * k) • P := by
    rw [← AddSubgroup.coe_nsmul, hy']
  refine ⟨(e.symm y : curveClassGroup qb) + k • P, ?_⟩
  rw [smul_add, hx, mul_smul, natCast_zsmul, sub_add_cancel]

variable {jD} in
include q in
/-- **`n^{2g + r - 1} ≤ #H¹(D, ℤ/n)`** for a smooth curve `D` open in a smooth proper curve `Db`
of genus `g` with `r ≥ 1` points at infinity, and `n^{2g} ≤ #H¹(D, ℤ/n)` when `r = 0`, over an
algebraically closed field in which `n` is invertible. Through `ℤ/n ≅ μ_n` and the Kummer
sequence, `#H¹(D, ℤ/n) = #(𝒪^*(D)/n) · #Cl(D)[n]`; with `Cl(D) = Cl(Db)/⟨boundary⟩`, the units
of `D` being the principal boundary divisors, and `#Cl(Db)[n] = n^{2g}`, the cone count
`Stacks.EtaleCohomology.finite_and_natCard_mul_le_of_cone` bounds this from below, the index
`[Q : ψ⁻¹(n Cl(Db))]` being at most `n` (degrees modulo `n`, `Pic⁰(Db)` being `n`-divisible). -/
theorem pow_le_natCard_sheafH_one_etaleConstantSheaf_zmod_of_isOpenImmersion {n : ℕ}
    (hn : IsUnit (n : K)) :
    n ^ (2 * genus qb + (Nat.card (BoundaryPoints jD) - 1)) ≤
      Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} D (ZMod n)) 1) := by
  classical
  have hn0 := ne_zero_of_isUnit_natCast q hn
  have : NeZero n := ⟨hn0⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isUnit hn
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve q
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve qb
  have : IsDominant jD := isDominant_of_isOpenImmersion_of_isCurve q qb jD
  have := finite_boundaryPoints q qb jD
  set ψ := boundaryClassMap q qb jD
  set S := (nsmulAddMonoidHom n : closedPointClassGroup Db →+ _).range.comap ψ
  have hA : Nat.card (AddSubgroup.torsionBy (closedPointClassGroup Db) (n : ℤ)) =
      n ^ (2 * genus qb) := by
    refine (natCard_torsionBy_congr (curveClassGroupAddEquivSchemePicard qb) n).trans ?_
    refine (natCard_torsionBy_congr
      (Stacks.GluePicard.picardModelAddEquiv Db.toRingedSpace) n).symm.trans ?_
    exact Stacks.Picard.natCard_torsionBy_eq_pow_genus qb n hn
  have : Finite (AddSubgroup.torsionBy (closedPointClassGroup Db) (n : ℤ)) :=
    Nat.finite_of_card_ne_zero (hA ▸ pow_ne_zero _ hn0)
  have hH0 : Finite (Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} D) 0 ⧸
      (nsmulAddMonoidHom n :
        Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} D) 0 →+ _).range) := by
    obtain ⟨T, hT⟩ := exists_finset_sheafH_zero_multiplicativeSheaf.{u, 0, u + 1} q hn0
    exact finite_quotient_nsmul_of_exists_finset n T hT
  have : Finite (Additive (Γ(D, ⊤))ˣ ⧸
      (nsmulAddMonoidHom n : Additive (Γ(D, ⊤))ˣ →+ _).range) :=
    Finite.of_equiv _ (quotientNsmulAddEquiv (sheafHZeroMultiplicativeAddEquivUnits D) n).toEquiv
  let σ : boundaryDivisors q qb jD →+ ZMod n :=
    (Int.castAddHom (ZMod n)).comp ((curveClassGroupDegree qb).comp ψ)
  have hσ : σ.ker.index ≠ 0 ∧ σ.ker.index ≤ n := by
    rw [AddSubgroup.index_ker]
    have h := Nat.card_le_card_of_injective (Subtype.val : σ.range → ZMod n)
      Subtype.val_injective
    rw [Nat.card_zmod] at h
    exact ⟨Nat.card_pos.ne', h⟩
  have hidx : S.index ≠ 0 ∧ S.index ≤ n ∧ (IsEmpty (BoundaryPoints jD) → S.index = 1) := by
    refine ⟨?_, ?_, fun he => ?_⟩
    rotate_right
    · rw [AddSubgroup.index_eq_one, eq_top_iff]
      intro x _
      rw [eq_zero_of_isEmpty_boundaryPoints q qb jD x]
      exact S.zero_mem
    all_goals
      have hle : σ.ker ≤ S := by
        intro x hx
        rcases isEmpty_or_nonempty (BoundaryPoints jD) with he | hne
        · rw [eq_zero_of_isEmpty_boundaryPoints q qb jD x]
          exact S.zero_mem
        obtain ⟨z⟩ := hne
        have hdvd : (n : ℤ) ∣ curveClassGroupDegree qb (ψ x) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx
        obtain ⟨b, hb⟩ := exists_nsmul_eq_of_dvd_curveClassGroupDegree qb hn z.1 (ψ x) hdvd
        exact ⟨b, hb.symm⟩
      have hdvd := AddSubgroup.index_dvd_of_le hle
    · exact fun h => hσ.1 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
    · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hσ.1) hdvd).trans hσ.2
  obtain ⟨hfin, hcone⟩ := finite_and_natCard_mul_le_of_cone n ψ (boundaryReduction q qb jD n)
    (unitBoundaryDivisor q qb jD) (boundaryClassMap_eq_zero_iff q qb jD)
    (surjective_boundaryReduction q qb jD n) (boundaryReduction_eq_zero_iff q qb jD n)
    (fun x hx => eq_zero_of_nsmul_eq_zero_boundaryDivisors q qb jD hn0 x hx) hidx.1
  let eCl : Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} D) 1 ≃+
      closedPointClassGroup Db ⧸ ψ.range :=
    (sheafHOneMultiplicativeAddEquivClosedPointClassGroup q).trans
      (closedPointClassGroupAddEquivQuotient q qb jD)
  have : Finite (AddSubgroup.torsionBy
      (Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} D) 1) (n : ℤ)) :=
    Finite.of_equiv _ (torsionByEquivOfAddEquiv eCl n).symm
  obtain ⟨-, hK⟩ := finite_and_natCard_sheafH_one_rootsOfUnitySheaf q hn
  have hH1 : Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} D (ZMod n)) 1) =
      Nat.card (Additive (Γ(D, ⊤))ˣ ⧸ (nsmulAddMonoidHom n : Additive (Γ(D, ⊤))ˣ →+ _).range) *
        Nat.card (AddSubgroup.torsionBy (closedPointClassGroup Db ⧸ ψ.range) (n : ℤ)) := by
    rw [Nat.card_congr (sheafHRootsOfUnityConstantAddEquiv q hζ hn0 1).toEquiv, hK,
      Nat.card_congr (quotientNsmulAddEquiv (sheafHZeroMultiplicativeAddEquivUnits D) n).toEquiv,
      natCard_torsionBy_congr eCl n]
  rw [hA, Nat.card_fun, Nat.card_zmod, ← hH1] at hcone
  rcases Nat.eq_zero_or_pos (Nat.card (BoundaryPoints jD)) with hr | hr
  · have : IsEmpty (BoundaryPoints jD) := Finite.card_eq_zero_iff.1 hr
    rw [hidx.2.2 inferInstance, hr, pow_zero, mul_one, mul_one] at hcone
    rwa [hr, Nat.zero_sub, add_zero]
  · refine Nat.le_of_mul_le_mul_right ?_ (Nat.pos_of_ne_zero hn0)
    calc n ^ (2 * genus qb + (Nat.card (BoundaryPoints jD) - 1)) * n
        = n ^ (2 * genus qb) * n ^ Nat.card (BoundaryPoints jD) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
      _ ≤ _ * S.index := hcone
      _ ≤ _ := Nat.mul_le_mul_left _ hidx.2.1

end LowerBound

/-! ### Constant coefficients in sheaves of `Λ`-modules -/

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at the
module universe `u + 1`: instance search cannot solve `max (u + 1) ?r = u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_firstCount (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section ConstantModule

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] (E : ModuleCat.{u + 1} Λ) [Finite E]

/-- **`Hⁱ(Y, E_Y)` computed in sheaves of `Λ`-modules is `Hⁱ(Y, E_Y)` of abelian sheaves**, `E`
being replaced by a small copy. -/
def constantModuleCohomologyAddEquivSheafH (Y : Scheme.{u}) (i : ℕ) :
    ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≃+
      Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (Shrink.{0} E)) i :=
  (etaleModuleCohomologyAddEquivSheafH Y _ i).trans
    (sheafHAddEquivOfIso (underlyingConstantSheafIso Y E Shrink.addEquiv.symm) i)

variable [Finite Λ] {K : Type*} [Field K] (hΛ : IsUnit (Nat.card Λ : K))

include hΛ in
omit [Ring Λ] [Finite Λ] in
/-- Every divisor `m` of the cardinality of `Λ` is a unit in `K`. -/
theorem isUnit_natCast_of_dvd_card [Fintype Λ] {m : ℕ} (hm : m ∣ Fintype.card Λ) :
    IsUnit (m : K) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast hm) (by rwa [Nat.card_eq_fintype_card] at hΛ)

include hΛ in
/-- `#Hⁱ(Y, E_Y) = #E^k` from `#Hⁱ(Y, ℤ/m) = m^k` for the `m` invertible in `K`. -/
theorem natCard_rightDerivedPlus_constantSheaf_eq_pow (Y : Scheme.{u}) (i k : ℕ)
    (h : ∀ m : ℕ, IsUnit (m : K) →
      Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (ZMod m)) i) = m ^ k) :
    Nat.card (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) = Nat.card E ^ k := by
  have := Fintype.ofFinite Λ
  rw [Nat.card_congr (constantModuleCohomologyAddEquivSheafH Λ E Y i).toEquiv,
    natCard_sheafH_etaleConstantSheaf_eq_pow_of_zmod Y i k (Fintype.card Λ)
      (fun m hm => h m (isUnit_natCast_of_dvd_card Λ hΛ hm)) (Shrink.{0} E)
      (shrink_card_nsmul_eq_zero Λ E), Nat.card_congr (equivShrink.{0} E).symm]

include hΛ in
/-- `#Hⁱ(Y, E_Y) ≤ #E^k` from `#Hⁱ(Y, ℤ/m) ≤ m^k` for the `m` invertible in `K`. -/
theorem natCard_rightDerivedPlus_constantSheaf_le_pow (Y : Scheme.{u}) (i k : ℕ)
    (h : ∀ m : ℕ, IsUnit (m : K) →
      Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (ZMod m)) i) ≤ m ^ k) :
    Nat.card (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ≤ Nat.card E ^ k := by
  have := Fintype.ofFinite Λ
  rw [Nat.card_congr (constantModuleCohomologyAddEquivSheafH Λ E Y i).toEquiv,
    Nat.card_congr (equivShrink.{0} E)]
  exact natCard_sheafH_etaleConstantSheaf_le_pow_of_zmod Y i k (Fintype.card Λ)
    (fun m hm => h m (isUnit_natCast_of_dvd_card Λ hΛ hm)) (Shrink.{0} E)
    (shrink_card_nsmul_eq_zero Λ E)

include hΛ in
/-- `#E^k ≤ #Hⁱ(Y, E_Y)` from `m^k ≤ #Hⁱ(Y, ℤ/m)` for the `m` invertible in `K`. -/
theorem pow_le_natCard_rightDerivedPlus_constantSheaf (Y : Scheme.{u}) (i k : ℕ)
    (h : ∀ m : ℕ, IsUnit (m : K) →
      m ^ k ≤ Nat.card (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (ZMod m)) i)) :
    Nat.card E ^ k ≤ Nat.card (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) := by
  have := Fintype.ofFinite Λ
  rw [Nat.card_congr (constantModuleCohomologyAddEquivSheafH Λ E Y i).toEquiv,
    Nat.card_congr (equivShrink.{0} E)]
  exact pow_le_natCard_sheafH_etaleConstantSheaf_of_zmod Y i k (Fintype.card Λ)
    (fun m hm => h m (isUnit_natCast_of_dvd_card Λ hΛ hm)) (Shrink.{0} E)
    (shrink_card_nsmul_eq_zero Λ E)

include hΛ in
/-- `Hⁱ(Y, E_Y)` is finite when the `Hⁱ(Y, ℤ/m)` are, for the `m` invertible in `K`. -/
theorem finite_rightDerivedPlus_constantSheaf (Y : Scheme.{u}) (i : ℕ)
    (h : ∀ m : ℕ, IsUnit (m : K) →
      Finite (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} Y (ZMod m)) i)) :
    Finite (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) := by
  have := Fintype.ofFinite Λ
  have := finite_sheafH_etaleConstantSheaf_of_zmod Y i (Fintype.card Λ)
    (fun m hm => h m (isUnit_natCast_of_dvd_card Λ hΛ hm)) (Shrink.{0} E)
    (shrink_card_nsmul_eq_zero Λ E)
  exact Finite.of_equiv _ (constantModuleCohomologyAddEquivSheafH Λ E Y i).toEquiv.symm

end ConstantModule

/-! ### The upper bound on the compactification -/

section UpperBound

attribute [local instance] HasDerivedCategory.standard

/-- Lifting modules from the universe `u + 1` along `ULift.{0}` is the identity. -/
def moduleCatUliftFunctorZeroIso (Λ : Type) [Ring Λ] :
    ModuleCat.uliftFunctor.{0, u + 1} Λ ≅ 𝟭 (ModuleCat.{u + 1} Λ) :=
  NatIso.ofComponents (fun M => LinearEquiv.toModuleIso (ULift.moduleEquiv (R := Λ) (M := M)))
    (fun _ => by ext; rfl)

variable {K : Type u} [Field K] [IsAlgClosed K] {D Db : Scheme.{u}}
  (q : D ⟶ Spec (.of K)) [IsCurve K q] [Smooth q]
  (qb : Db ⟶ Spec (.of K)) [IsCurve K qb] [Smooth qb] [IsProper qb]
  (jD : D ⟶ Db) [IsOpenImmersion jD]
  (Λ : Type) [Ring Λ] [Finite Λ] (E : ModuleCat.{u + 1} Λ) [Finite E]

include q in
omit [IsAlgClosed K] [Smooth q] [Smooth qb] [IsProper qb] in
/-- With a point at infinity, the open subcurve is not proper over `K`. -/
theorem not_isProper_comp_of_nonempty_boundaryPoints [Nonempty (BoundaryPoints jD)] :
    ¬ IsProper (jD ≫ qb) := by
  intro hp
  have := hp
  have : IsProper jD := IsProper.of_comp jD qb
  have hcl : IsClosed (Set.range jD.base) := jD.isClosedMap.isClosed_range
  have : PreconnectedSpace Db :=
    ⟨IsPreirreducible.isPreconnected (IrreducibleSpace.isIrreducible_univ Db).2⟩
  have huniv : Set.range jD.base = Set.univ :=
    IsClopen.eq_univ ⟨hcl, jD.isOpenEmbedding.isOpen_range⟩ (Set.range_nonempty _)
  obtain ⟨z⟩ := ‹Nonempty (BoundaryPoints jD)›
  exact z.2 (Set.eq_univ_iff_forall.1 huniv _)

include q qb in
omit [IsAlgClosed K] [Smooth q] [Smooth qb] in
/-- **`H⁰(Db, j_!(E_D)) = 0`** when `D` misses a point of `Db`. -/
theorem subsingleton_rightDerivedPlus_zero_extensionByZero [Nonempty (BoundaryPoints jD)] :
    Subsingleton (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerivedPlus ((0 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jD).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) := by
  set H := (constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E
  have := small_pair.{u} D Db
  let B := BigEtaleSite.ofSet {D, Db}
  have hD : B.Contains D := BigEtaleSite.contains_ofSet _ (by simp)
  have : ConnectedSpace D :=
    { toPreconnectedSpace :=
        ⟨IsPreirreducible.isPreconnected (IrreducibleSpace.isIrreducible_univ D).2⟩
      toNonempty := inferInstance }
  have : ConnectedSpace (⟨D, hD⟩ : B.Scheme).obj := inferInstanceAs (ConnectedSpace D)
  have hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ D.smallEtaleTopology H :=
    AlgebraicGeometry.isFiniteTypeLocallyConstant_constantSheafModule_etaleSite B ⟨D, hD⟩ Λ E
  have h := subsingleton_globalSections_extensionByZero_uliftFunctor.{u, 0} Λ jD K qb
    (not_isProper_comp_of_nonempty_boundaryPoints q qb jD) H hH
  let eU : (sheafCompose D.smallEtaleTopology (ModuleCat.uliftFunctor.{0, u + 1} Λ)).obj H ≅ H :=
    ObjectProperty.isoMk _
      (Functor.isoWhiskerLeft H.obj (moduleCatUliftFunctorZeroIso Λ) ≪≫ Functor.rightUnitor H.obj)
  exact subsingleton_of_moduleIso Λ
    ((etaleModuleGlobalSections.{u, 0} Λ Db).mapIso
        ((etaleModuleExtensionByZero.{u, 0} Λ jD).mapIso eU) ≪≫
      (Stacks.GroupCohomology.rightDerivedPlusZeroIso
        (etaleModuleGlobalSections.{u, 0} Λ Db)).app _) h

variable {Λ} in
include q in
omit [Smooth q] in
/-- **`#H¹(Db, j_!(E_D)) ≤ #E^{2g + r - 1}`** (`≤ #E^{2g}` when `r = 0`) for a smooth curve `D`
open in a smooth proper curve `Db` of genus `g` with `r` points at infinity, and a finite
`Λ`-module `E` of order invertible in `K`, from the long exact sequence of
`0 → j_!(E_D) → E_{Db} → i_*(E_Z) → 0`: `H⁰(Db, E) = E`, `#H⁰(Z, E) ≤ #E^r`,
`#H¹(Db, E) = #E^{2g}`, and `H⁰(Db, j_!(E_D)) = 0` when `r ≥ 1`. -/
theorem finite_and_natCard_rightDerivedPlus_one_extensionByZero_le
    (hΛ : IsUnit (Nat.card Λ : K)) :
    Finite (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jD).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) ∧
      Nat.card (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jD).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) ≤
        Nat.card E ^ (2 * genus qb + (Nat.card (BoundaryPoints jD) - 1)) := by
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve qb
  have := finite_boundaryPoints q qb jD
  have : Nonempty E := ⟨0⟩
  have hE : 0 < Nat.card E := Nat.card_pos
  set F := (constantSheaf Db.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E
  obtain ⟨h0, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ
    (openImmersionReducedComplementι jD) jD
    (by rw [range_openImmersionReducedComplementι, compl_compl]) F
  set S := ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jD).counit.app F)
    ((etaleModuleInverseImageAdj.{u, 0} Λ (openImmersionReducedComplementι jD)).unit.app F) h0
  let Dl := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor
    (etaleModuleGlobalSections.{u, 0} Λ Db)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
    (Stacks.DerivedIndexing.canonicalδ _) (fun _ _ => rfl)
  let eX : (etaleModuleExtensionByZero.{u, 0} Λ jD).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≅ S.X₁ :=
    (etaleModuleExtensionByZero.{u, 0} Λ jD).mapIso
      (((etaleModuleInverseImageConstantIso.{u, 0} Λ jD).app E).symm ≪≫
        (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jD).app F)
  have hdim1 := IsCurve.topologicalKrullDim_eq_one (k := K) (f := qb)
  have hmem : ∀ z, (openImmersionReducedComplementι jD).base z ∈ (Set.range jD.base)ᶜ := fun z => by
    rw [← range_openImmersionReducedComplementι]
    exact Set.mem_range_self z
  have hgen : genericPoint Db ∈ Set.range jD.base := by
    obtain ⟨x⟩ : Nonempty D := inferInstance
    exact ((genericPoint_spec Db).mem_open_set_iff jD.isOpenEmbedding.isOpen_range).2
      ⟨jD.base x, trivial, x, rfl⟩
  let φ :
      (Scheme.IdealSheafData.vanishingIdeal (openImmersionReducedComplementCloseds jD)).subscheme →
      BoundaryPoints jD := fun z =>
    ⟨⟨(openImmersionReducedComplementι jD).base z,
      Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Db hdim1
        fun hg => hmem z (hg ▸ hgen)⟩, hmem z⟩
  have hφ : Function.Injective φ := fun a b h =>
    (openImmersionReducedComplementι jD).isClosedEmbedding.injective
      (congrArg (fun z : BoundaryPoints jD => z.1.1) h)
  have : Finite (Scheme.IdealSheafData.vanishingIdeal
      (openImmersionReducedComplementCloseds jD)).subscheme := Finite.of_injective φ hφ
  have hZ : Nat.card (Scheme.IdealSheafData.vanishingIdeal
      (openImmersionReducedComplementCloseds jD)).subscheme ≤ Nat.card (BoundaryPoints jD) :=
    Nat.card_le_card_of_injective φ hφ
  have hB0 : Nat.card ((Dl.functor 0).obj S.X₂) = Nat.card E :=
    (natCard_rightDerivedPlus_constantSheaf_eq_pow Λ E hΛ Db 0 1 fun m hm =>
      (natCard_sheafH_zero_etaleConstantSheaf_zmod qb hm).trans (pow_one m).symm).trans (pow_one _)
  have hB1 : Nat.card ((Dl.functor 1).obj S.X₂) = Nat.card E ^ (2 * genus qb) :=
    natCard_rightDerivedPlus_constantSheaf_eq_pow Λ E hΛ Db 1 _
      (fun m hm => natCard_sheafH_one_etaleConstantSheaf_zmod_of_isProper qb hm)
  let eC := integralDirectImageCohomologyIso Λ (openImmersionReducedComplementι jD)
      ((etaleModuleInverseImage.{u, 0} Λ (openImmersionReducedComplementι jD)).obj F)
      ((0 : ℕ) : ℤ) ≪≫
    ((etaleModuleGlobalSections.{u, 0} Λ
      (Scheme.IdealSheafData.vanishingIdeal
        (openImmersionReducedComplementCloseds jD)).subscheme).rightDerivedPlus
        ((0 : ℕ) : ℤ)).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} Λ (openImmersionReducedComplementι jD)).app E)
  have hC0 : Nat.card ((Dl.functor 0).obj S.X₃) ≤ Nat.card E ^ Nat.card (BoundaryPoints jD) := by
    refine (Nat.card_congr eC.toLinearEquiv.toEquiv).trans_le
      ((natCard_rightDerivedPlus_constantSheaf_le_pow Λ E hΛ _ 0 _ (fun m hm =>
        natCard_sheafH_zero_etaleConstantSheaf_zmod_le_of_finite
          (openImmersionReducedComplementι jD ≫ qb) hm)).trans ?_)
    exact Nat.pow_le_pow_right hE hZ
  have : Finite ((Dl.functor 0).obj S.X₃) := by
    have := finite_rightDerivedPlus_constantSheaf Λ E hΛ
      (Scheme.IdealSheafData.vanishingIdeal (openImmersionReducedComplementCloseds jD)).subscheme 0
      (fun m hm => finite_sheafH_zero_etaleConstantSheaf_zmod_of_finite
        (openImmersionReducedComplementι jD ≫ qb) hm)
    exact Finite.of_equiv _ eC.toLinearEquiv.toEquiv.symm
  have : Finite ((Dl.functor 0).obj S.X₂) := Nat.finite_of_card_ne_zero (hB0 ▸ hE.ne')
  have : Finite ((Dl.functor 1).obj S.X₂) := Nat.finite_of_card_ne_zero (hB1 ▸ (pow_pos hE _).ne')
  have hδh := moduleCat_g_eq_zero_iff_of_exact (Dl.exact_δ₂ hS 0)
  have hgδ := moduleCat_g_eq_zero_iff_of_exact (Dl.exact_δ₁ hS 0)
  have hfg := moduleCat_g_eq_zero_iff_of_exact (Dl.exact_map hS 0)
  have key : Finite ((Dl.functor 1).obj S.X₁) ∧ Nat.card ((Dl.functor 1).obj S.X₁) ≤
      Nat.card E ^ (2 * genus qb + (Nat.card (BoundaryPoints jD) - 1)) := by
    rcases isEmpty_or_nonempty (BoundaryPoints jD) with he | hne
    · have hr : Nat.card (BoundaryPoints jD) = 0 := Nat.card_of_isEmpty
      obtain ⟨hfin, hle⟩ := finite_and_natCard_le_of_exact (Dl.δ hS 0).hom.toAddMonoidHom
        ((Dl.functor (0 + 1)).map S.f).hom.toAddMonoidHom hδh
      refine ⟨hfin, hle.trans ?_⟩
      rw [hr, Nat.zero_sub, add_zero]
      calc Nat.card ((Dl.functor 0).obj S.X₃) * Nat.card ((Dl.functor (0 + 1)).obj S.X₂)
          ≤ Nat.card E ^ 0 * Nat.card E ^ (2 * genus qb) :=
            Nat.mul_le_mul (hr ▸ hC0) hB1.le
        _ = Nat.card E ^ (2 * genus qb) := by rw [pow_zero, one_mul]
    · have : Subsingleton ((Dl.functor 0).obj S.X₁) :=
        subsingleton_of_moduleIso Λ
          (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerivedPlus ((0 : ℕ) : ℤ)).mapIso eX)
          (subsingleton_rightDerivedPlus_zero_extensionByZero q qb jD Λ E)
      have : Finite ((Dl.functor 0).obj S.X₁) := Finite.of_subsingleton
      obtain ⟨hfin, hle⟩ := finite_and_natCard_mul_le_of_exact
        ((Dl.functor 0).map S.f).hom.toAddMonoidHom ((Dl.functor 0).map S.g).hom.toAddMonoidHom
        (Dl.δ hS 0).hom.toAddMonoidHom ((Dl.functor (0 + 1)).map S.f).hom.toAddMonoidHom
        hfg hgδ hδh
      refine ⟨hfin, ?_⟩
      have hr : 1 ≤ Nat.card (BoundaryPoints jD) := Nat.card_pos
      rw [hB0] at hle
      refine Nat.le_of_mul_le_mul_right ?_ hE
      calc Nat.card ((Dl.functor 1).obj S.X₁) * Nat.card E
          ≤ Nat.card ((Dl.functor 0).obj S.X₁) * Nat.card ((Dl.functor 0).obj S.X₃) *
              Nat.card ((Dl.functor (0 + 1)).obj S.X₂) := hle
        _ ≤ 1 * Nat.card E ^ Nat.card (BoundaryPoints jD) * Nat.card E ^ (2 * genus qb) :=
            Nat.mul_le_mul
              (Nat.mul_le_mul (Finite.card_le_one_iff_subsingleton.2 inferInstance) hC0) hB1.le
        _ = Nat.card E ^ (2 * genus qb + (Nat.card (BoundaryPoints jD) - 1)) * Nat.card E := by
            rw [one_mul, ← pow_succ, ← pow_add, mul_comm]
            congr 1
            omega
  let e1 := ((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerivedPlus ((1 : ℕ) : ℤ)).mapIso eX
  have : Finite (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
    S.X₁) := key.1
  refine ⟨Finite.of_equiv _ e1.toLinearEquiv.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e1.toLinearEquiv.toEquiv]
  exact key.2

include q qb in
/-- **The counting lemma `#H¹(Db, j_!E) ≤ #H¹(D, E)`.** Let `K` be an algebraically closed field,
`D` a smooth curve over `K` and `j : D ⟶ Db` an open immersion into a smooth proper curve `Db`
over `K`, `Λ` a finite ring whose order is invertible in `K`, and `E` a finite `Λ`-module. Then
`H¹(Db, j_!(E_D))` and `H¹(D, E_D)`, computed in sheaves of `Λ`-modules, are finite and
`#H¹(Db, j_!(E_D)) ≤ #H¹(D, E_D)`. Both are `#E^{2g + r - 1}` when `Db ∖ D` has `r ≥ 1` points
and `#E^{2g}` when `D = Db`, `g` being the genus of `Db`: the upper bound comes from the long
exact sequence of `0 → j_!(E_D) → E_{Db} → i_*(E_{Db ∖ D}) → 0`, the lower bound from the Kummer
sequence on `D` and the class groups of `D` and `Db` (with `Pic⁰(Db)` divisible, through the
Jacobian). -/
theorem finite_and_finite_and_natCard_rightDerived_one_extensionByZero_le
    (hΛ : IsUnit (Nat.card Λ : K)) :
    Finite (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerived 1).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jD).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) ∧
      Finite (((etaleModuleGlobalSections.{u, 0} Λ D).rightDerived 1).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ∧
      Nat.card (((etaleModuleGlobalSections.{u, 0} Λ Db).rightDerived 1).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ jD).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) ≤
        Nat.card (((etaleModuleGlobalSections.{u, 0} Λ D).rightDerived 1).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) := by
  have : Nonempty E := ⟨0⟩
  have hE : 0 < Nat.card E := Nat.card_pos
  obtain ⟨hfin, hup⟩ := finite_and_natCard_rightDerivedPlus_one_extensionByZero_le q qb jD E hΛ
  have hlow := pow_le_natCard_rightDerivedPlus_constantSheaf Λ E hΛ D 1
    (2 * genus qb + (Nat.card (BoundaryPoints jD) - 1))
    (fun m hm => pow_le_natCard_sheafH_one_etaleConstantSheaf_zmod_of_isOpenImmersion q qb hm)
  let eb := (Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, 0} Λ Db) 1).app
    ((etaleModuleExtensionByZero.{u, 0} Λ jD).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))
  let ed := (Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, 0} Λ D) 1).app
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
  have := Nat.finite_of_card_ne_zero (lt_of_lt_of_le (pow_pos hE _) hlow).ne'
  refine ⟨Finite.of_equiv _ eb.toLinearEquiv.toEquiv.symm,
    Finite.of_equiv _ ed.toLinearEquiv.toEquiv.symm, ?_⟩
  rw [Nat.card_congr eb.toLinearEquiv.toEquiv, Nat.card_congr ed.toLinearEquiv.toEquiv]
  exact hup.trans hlow

end UpperBound

end Stacks.EtaleCohomology


