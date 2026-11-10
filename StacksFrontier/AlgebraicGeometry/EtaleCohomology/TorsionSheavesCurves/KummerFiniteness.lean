module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantPrimeToCharacteristicCurveStatements
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ConnectedReduced

/-!
# Case I of Stacks 0A5B: finiteness of `H¹` and `H²` of `𝐙/ℓ𝐙` from `H¹(X, 𝐆_m)`

Let `X` be a smooth curve over an algebraically closed field `k` and `ℓ` invertible in `k`. The
Kummer sequence `0 → μ_ℓ → 𝐆_m →ℓ 𝐆_m → 0` places

* `H¹(X, μ_ℓ)` between `Γ(X, 𝒪_X)^*/(Γ(X, 𝒪_X)^*)^ℓ` and the `ℓ`-torsion of `H¹(X, 𝐆_m)`;
* `H²(X, μ_ℓ)` after `H¹(X, 𝐆_m)/ℓ H¹(X, 𝐆_m)`, followed by `H²(X, 𝐆_m) = 0` (Tag 03RM).

The first end of the first sequence is finite unconditionally: `Γ(X, 𝒪_X)^*/k^*` is finitely
generated (Tag 04L6) and `k^*` is `ℓ`-divisible, `k` being algebraically closed. So finiteness of
`H¹` and `H²` of `𝐙/ℓ𝐙 ≅ μ_ℓ` reduces to two statements about `H¹(X, 𝐆_m)` alone: its
`ℓ`-torsion is finite, and so is its quotient by `ℓ`. With them, statements (4) and (5) of
Situation 0A52 for `𝐙/ℓ𝐙` are reduced to `H¹(X, 𝐆_m)`, and
`Stacks.EtaleCohomology.curveStatements_constantSheaf_of_smoothCurve_of_multiplicative` records
the sharpened reduction of the bundle.

## Main results

* `Stacks.EtaleCohomology.finite_ext_succ_X₁_of_shortExact`: in the long exact `Ext` sequence of
  a short exact sequence `0 → A → B → C → 0`, `Ext^{n+1}(X, A)` is finite as soon as the image of
  `Ext^{n+1}(X, A) → Ext^{n+1}(X, B)` and the cokernel of `Ext^n(X, B) → Ext^n(X, C)` are.
* `Stacks.EtaleCohomology.finite_units_quotient_powMonoidHom_range`: `Γ(X, 𝒪_X)^*` modulo
  `ℓ`-th powers is finite for an integral scheme locally of finite type over an algebraically
  closed field.
* `Stacks.EtaleCohomology.finite_sheafH_one_rootsOfUnitySheaf_of_finite` and
  `Stacks.EtaleCohomology.finite_sheafH_two_rootsOfUnitySheaf_of_finite`: the two Kummer
  reductions.

## References

* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 04L6](https://stacks.math.columbia.edu/tag/04L6)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-! ### Finiteness from the long exact sequence -/

/-- **Finiteness in the long exact `Ext` sequence.** For a short exact sequence `0 → A → B → C →
0` and `n : ℕ`, `Ext^{n+1}(X, A)` is finite if the image of `Ext^{n+1}(X, A) → Ext^{n+1}(X, B)` is
finite and `Ext^n(X, C)` is covered by finitely many translates of the image of
`Ext^n(X, B) → Ext^n(X, C)`: the kernel of the first map is the image of the connecting map, which
kills that image. -/
theorem finite_ext_succ_X₁_of_shortExact {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (X : C) (n : ℕ)
    (T : Finset (Abelian.Ext X S.X₃ n))
    (hT : ∀ x : Abelian.Ext X S.X₃ n, ∃ t ∈ T, ∃ y : Abelian.Ext X S.X₂ n,
      x = t + y.comp (Abelian.Ext.mk₀ S.g) (add_zero n))
    (hf : (Set.range fun x : Abelian.Ext X S.X₁ (n + 1) =>
      x.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 1))).Finite) :
    Finite (Abelian.Ext X S.X₁ (n + 1)) := by
  classical
  let φ := fun x : Abelian.Ext X S.X₁ (n + 1) => x.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 1))
  have : Finite (Set.range φ) := hf.to_subtype
  choose r hr using fun z : Set.range φ => z.2
  let F : Set.range φ × T → Abelian.Ext X S.X₁ (n + 1) :=
    fun p => r p.1 + (p.2 : Abelian.Ext X S.X₃ n).comp hS.extClass rfl
  refine Finite.of_surjective F fun x => ?_
  have hφ : (x - r ⟨φ x, x, rfl⟩).comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := by
    rw [sub_eq_add_neg, Abelian.Ext.add_comp, Abelian.Ext.neg_comp]
    exact add_neg_eq_zero.mpr (hr ⟨φ x, x, rfl⟩).symm
  obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS _ hφ (rfl : n + 1 = n + 1)
  obtain ⟨t, ht, y, rfl⟩ := hT z
  refine ⟨(⟨φ x, x, rfl⟩, ⟨t, ht⟩), ?_⟩
  have h0 : (y.comp (Abelian.Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0 :=
    (Abelian.Ext.comp_assoc_of_second_deg_zero y (Abelian.Ext.mk₀ S.g) hS.extClass rfl).trans
      (by rw [hS.comp_extClass, Abelian.Ext.comp_zero])
  rw [Abelian.Ext.add_comp, h0, add_zero] at hz
  change r _ + t.comp hS.extClass rfl = x
  rw [hz]
  abel

/-- Composing an `Ext` class with `n • 𝟙` is multiplication by `n`. -/
theorem ext_comp_mk₀_nsmul_id {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {X Y : C} {q : ℕ} (d : Abelian.Ext X Y q) (n : ℕ) :
    d.comp (Abelian.Ext.mk₀ (n • 𝟙 Y)) (add_zero q) = n • d := by
  induction n with
  | zero => rw [zero_smul, zero_smul, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ n ih =>
    rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih, Abelian.Ext.comp_mk₀_id,
      succ_nsmul]

/-- An abelian group whose quotient by its `ℓ`-multiples is finite is covered by finitely many
translates of its `ℓ`-multiples. -/
theorem exists_finset_add_nsmul_of_finite_quotient {A : Type*} [AddCommGroup A] (ℓ : ℕ)
    (h : Finite (A ⧸ (nsmulAddMonoidHom ℓ : A →+ A).range)) :
    ∃ T : Finset A, ∀ x : A, ∃ t ∈ T, ∃ y : A, x = t + ℓ • y := by
  classical
  have := Fintype.ofFinite (A ⧸ (nsmulAddMonoidHom ℓ : A →+ A).range)
  let r := Function.surjInv (QuotientAddGroup.mk_surjective
    (s := (nsmulAddMonoidHom ℓ : A →+ A).range))
  refine ⟨Finset.univ.image r, fun x => ⟨r (x : A ⧸ _), by simp, ?_⟩⟩
  have hx : ((r x : A) : A ⧸ (nsmulAddMonoidHom ℓ : A →+ A).range) = x :=
    Function.surjInv_eq _ _
  obtain ⟨y, hy⟩ := QuotientAddGroup.eq.mp hx
  exact ⟨y, by rw [← nsmulAddMonoidHom_apply, hy]; abel⟩

/-! ### Invertible functions modulo `ℓ`-th powers -/

/-- **Invertible global functions modulo `ℓ`-th powers form a finite group** on an integral scheme
locally of finite type over an algebraically closed field `k`, for `ℓ ≠ 0`: modulo the constants
they are finitely generated (Tag 04L6), and the constants are `ℓ`-th powers. -/
theorem finite_units_quotient_powMonoidHom_range (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType f]
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Finite (Γ(X, ⊤)ˣ ⧸ (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range) := by
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hfg := fg_units_quotient_of_connectedSpace_of_isReduced k f
    (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _)
  have hC : (Units.map φ.toMonoidHom).range ≤ (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : k) (Nat.pos_of_ne_zero hℓ)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [← ha, zero_pow hℓ])
    refine ⟨Units.map φ.toMonoidHom (Units.mk0 a ha0), ?_⟩
    rw [powMonoidHom_apply, ← map_pow]
    congr 1
    exact Units.ext (by simp [ha])
  let π := QuotientGroup.map (Units.map φ.toMonoidHom).range
    (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range (MonoidHom.id _)
    (fun x hx => show x ∈ Subgroup.comap (MonoidHom.id _) _ from hC hx)
  have hπ : Function.Surjective π := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, rfl⟩
  have : Group.FG (Γ(X, ⊤)ˣ ⧸ (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range) :=
    Group.fg_of_surjective hπ
  refine CommGroup.finite_of_fg_isMulTorsion _ fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ, Nat.pos_of_ne_zero hℓ, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩

/-! ### The Kummer reductions -/

/-- The Kummer sequence reduces finiteness of `H^{n+1}(X, μ_ℓ)` to the multiplication-by-`ℓ`
cokernel of `H^n(X, 𝐆_m)` and the image of `H^{n+1}(X, μ_ℓ) → H^{n+1}(X, 𝐆_m)`. -/
private theorem finite_sheafH_succ_rootsOfUnitySheaf_of_finite {X : Scheme.{u}} {ℓ : ℕ}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (hSE : (Stacks.Kummer.kummerSequence.{u, v} X ℓ).ShortExact) (n : ℕ)
    (T : Finset (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) n))
    (hT : ∀ x, ∃ t ∈ T, ∃ y, x = t + ℓ • y)
    (hf : (Set.range fun x : Sheaf.H.{w} (Stacks.Kummer.kummerSequence.{u, v} X ℓ).X₁ (n + 1) =>
      x.comp (Abelian.Ext.mk₀ (Stacks.Kummer.kummerSequence.{u, v} X ℓ).f)
        (add_zero (n + 1))).Finite) :
    Finite (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) (n + 1)) := by
  refine finite_ext_succ_X₁_of_shortExact hSE _ n T (fun x => ?_) hf
  obtain ⟨t, ht, y, rfl⟩ := hT x
  exact ⟨t, ht, y, congrArg (fun z => t + z) (ext_comp_mk₀_nsmul_id y ℓ).symm⟩

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include g

omit [Smooth g] in
/-- `H⁰(X, 𝐆_m)` is covered by finitely many translates of its `ℓ`-multiples, on an integral
scheme locally of finite type over an algebraically closed field: through
`H⁰(X, 𝐆_m) = Γ(X, 𝒪_X)^*` this is `finite_units_quotient_powMonoidHom_range`. -/
theorem exists_finset_sheafH_zero_multiplicativeSheaf {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    ∃ T : Finset (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 0),
      ∀ x, ∃ t ∈ T, ∃ y, x = t + ℓ • y := by
  classical
  have := finite_units_quotient_powMonoidHom_range k g hℓ
  have := Fintype.ofFinite (Γ(X, ⊤)ˣ ⧸ (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range)
  let e := Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, v} X) (isTerminalEtaleMkId X)
  let ι : Γ(X, ⊤)ˣ → Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 0 :=
    fun a => e.symm (Stacks.Kummer.ofUnit.{u, v} (U := Scheme.Etale.mk (𝟙 X)) a)
  have hι : ∀ a b : Γ(X, ⊤)ˣ, ι (a * b ^ ℓ) = ι a + ℓ • ι b := by
    intro a b
    simp only [ι, ← map_nsmul, ← map_add]
    rfl
  let r := Function.surjInv (QuotientGroup.mk_surjective
    (s := (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range))
  refine ⟨Finset.univ.image fun q => ι (r q), fun x => ?_⟩
  obtain ⟨a, ha⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} (e x)
  let a' : Γ(X, ⊤)ˣ := a
  have hq : ((r a' : Γ(X, ⊤)ˣ) : Γ(X, ⊤)ˣ ⧸ (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range) =
      a' := Function.surjInv_eq _ _
  obtain ⟨b, hb⟩ : (r a')⁻¹ * a' ∈ (powMonoidHom ℓ : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range :=
    QuotientGroup.eq.mp hq
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (a' : _ ⧸ _)), ι b, ?_⟩
  have hab : r a' * b ^ ℓ = a' := by
    rw [← powMonoidHom_apply, hb, mul_inv_cancel_left]
  rw [← hι, hab]
  exact (e.symm_apply_apply x).symm.trans (congrArg e.symm ha.symm)

omit [Smooth g] in
/-- **`H¹(X, μ_ℓ)` is finite once the `ℓ`-torsion of `H¹(X, 𝐆_m)` is**, on a smooth curve over an
algebraically closed field, `ℓ` invertible in `k`. The Kummer sequence gives
`H⁰(X, 𝐆_m) →ℓ H⁰(X, 𝐆_m) → H¹(X, μ_ℓ) → H¹(X, 𝐆_m)[ℓ]`, and the cokernel of the first map is
finite (`exists_finset_sheafH_zero_multiplicativeSheaf`). -/
theorem finite_sheafH_one_rootsOfUnitySheaf_of_finite {ℓ : ℕ} (hℓk : IsUnit (ℓ : k))
    (hfin : Finite {c : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 //
      ℓ • c = 0}) :
    Finite (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) 1) := by
  let S := Stacks.Kummer.kummerSequence.{u, v} X ℓ
  obtain ⟨T, hT⟩ := exists_finset_sheafH_zero_multiplicativeSheaf.{u, v, w} g
    (ne_zero_of_isUnit_natCast hℓk)
  have hSE := Stacks.Kummer.kummerSequence_shortExact.{u, v} X
    (ne_zero_of_isUnit_natCast hℓk) (isUnit_natCast_globalSections_of_isUnit g hℓk)
  refine finite_sheafH_succ_rootsOfUnitySheaf_of_finite hSE 0 T hT ?_
  refine Set.Finite.subset (Set.finite_range fun c : {c : Sheaf.H.{w}
      (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 // ℓ • c = 0} =>
      (show Abelian.Ext _ S.X₂ 1 from c.1)) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1), ?_⟩, rfl⟩
  change ℓ • x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0
  rw [← ext_comp_mk₀_nsmul_id (x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1)) ℓ,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  change x.comp (Abelian.Ext.mk₀ (S.f ≫ S.g)) _ = 0
  rw [S.zero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

/-- **`H²(X, μ_ℓ)` is finite once `H¹(X, 𝐆_m)/ℓ` is**, on a smooth curve over an algebraically
closed field, `ℓ` invertible in `k`: the Kummer sequence gives
`H¹(X, 𝐆_m) →ℓ H¹(X, 𝐆_m) → H²(X, μ_ℓ) → H²(X, 𝐆_m) = 0` (Tag 03RM). -/
theorem finite_sheafH_two_rootsOfUnitySheaf_of_finite {ℓ : ℕ} (hℓk : IsUnit (ℓ : k))
    (hfin : Finite (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 ⧸
      (nsmulAddMonoidHom ℓ : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 →+
        Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1).range)) :
    Finite (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) 2) := by
  obtain ⟨T, hT⟩ := exists_finset_add_nsmul_of_finite_quotient ℓ hfin
  have hSE := Stacks.Kummer.kummerSequence_shortExact.{u, v} X
    (ne_zero_of_isUnit_natCast hℓk) (isUnit_natCast_globalSections_of_isUnit g hℓk)
  refine finite_sheafH_succ_rootsOfUnitySheaf_of_finite hSE 1 T hT ?_
  refine Set.Finite.subset (Set.finite_singleton 0) ?_
  rintro _ ⟨x, rfl⟩
  exact (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ.{u, v, w} g 2
    le_rfl).elim _ _

/-- **The bundle of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth curve, `ℓ ∈ k^*`, with statements (4)
and (5) reduced to `H¹(X, 𝐆_m)`.** This sharpens
`Stacks.EtaleCohomology.curveStatements_constantSheaf_of_smoothCurve_of`: its finiteness input is
replaced by finiteness of the `ℓ`-torsion of `H¹(X, 𝐆_m)` and of `H¹(X, 𝐆_m)/ℓ`, through the
Kummer reductions `finite_sheafH_one_rootsOfUnitySheaf_of_finite` and
`finite_sheafH_two_rootsOfUnitySheaf_of_finite`. It is a reduction; nothing is registered. -/
theorem curveStatements_constantSheaf_of_smoothCurve_of_multiplicative
    {ℓ : ℕ} (hℓk : IsUnit (ℓ : k)) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    (hdiv : IsAffine X → ∀ c : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1,
      ∃ d, ℓ • d = c)
    (hfin1 : Finite {c : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 //
      ℓ • c = 0})
    (hfin2 : Finite (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 ⧸
      (nsmulAddMonoidHom ℓ : Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1 →+
        Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) 1).range))
    (h6 : ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']
        [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
        [HasExt.{w} (Sheaf (scalarExtension k k' g).smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v})] (q : ℕ), 1 ≤ q →
        Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' g)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) q)) :
    CurveStatements.{u, v, w} g
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  refine curveStatements_constantSheaf_of_smoothCurve_of g hℓk E hE hdiv (fun q hq1 hq2 => ?_) h6
  obtain ⟨e⟩ := Stacks.Kummer.nonempty_constantSheaf_iso_rootsOfUnitySheaf.{u, v} k g ℓ
    (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast hℓk)) hℓk E hE
  have hμ : Finite (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X ℓ) q) := by
    obtain rfl | rfl : q = 1 ∨ q = 2 := by omega
    · exact finite_sheafH_one_rootsOfUnitySheaf_of_finite g hℓk hfin1
    · exact finite_sheafH_two_rootsOfUnitySheaf_of_finite g hℓk hfin2
  exact Finite.of_equiv _
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr e q).toEquiv.symm

end Curve

end Stacks.EtaleCohomology

end
