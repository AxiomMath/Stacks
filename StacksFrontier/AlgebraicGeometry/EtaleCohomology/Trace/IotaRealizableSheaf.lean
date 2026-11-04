module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRealTraces
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBound

/-!
# `ι`-realizable ℓ-adic sheaves

A lisse ℓ-adic sheaf `F` is `ι`-realizable (Weil II 1.5) when it is a direct summand, up to
traces, of a sheaf with real Frobenius traces, i.e. there is a lisse `F'` with
`ι(Tr(π_y ^ n | F) + Tr(π_y ^ n | F'))` real at every closed point `y` and every `n ≥ 1`. This
condition passes to inverse images through the comparison of Frobenius traces at a point above a
point (`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow`), and it
is equivalent to the reality of the characteristic polynomial of `π_y` on `F ⊕ F'` by Newton's
identities (`Stacks.EtaleCohomology.coeff_charpoly_mul_mem_range_ofReal_iff`).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable`: `ι`-realizability in trace form.

## Main results

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.IsLisse.inverseImage`: the inverse image of a lisse
  ℓ-adic sheaf is lisse.
* `Stacks.EtaleCohomology.LAdicSheaf.IsIotaRealizable.inverseImage`: realizability passes to
  inverse images along morphisms sending closed points to closed points.
* `Stacks.EtaleCohomology.LAdicSheaf.isIotaRealizable_representationSheaf`: the sheaf `ℱ_ρ` of an
  `ι`-realizable representation is `ι`-realizable.

## References

* P. Deligne, *La conjecture de Weil II*, 1.5.
* K. Kedlaya, *Fourier transforms and p-adic Weil II*, §6.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace AlgebraicGeometry.SmallEtale.LAdicSheaf

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- **The inverse image of a lisse ℓ-adic sheaf is lisse**: at every level, the inverse image of a
locally constant sheaf along a morphism of small étale sites is locally constant (Tag 093R). -/
theorem IsLisse.inverseImage {F : LAdicSheaf.{u, u + 1} B Y ℓ} (hF : F.IsLisse) :
    (LAdicSheaf.inverseImage f F).IsLisse := fun n => by
  refine ⟨fun U => ?_⟩
  have hH : ∀ V : SmallEtale B Y.obj Y.property,
      ∃ (I : Type (u + 1)) (W : I → SmallEtale B Y.obj Y.property) (g : ∀ i, W i ⟶ V),
        Sieve.ofArrows W g ∈ SmallEtale.topology B Y.obj Y.property V ∧ ∀ i,
          ∃ E : ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))), True ∧ Nonempty
            ((constantSheaf ((SmallEtale.topology B Y.obj Y.property).over (W i)) _).obj E ≅
              ((SmallEtale.topology B Y.obj Y.property).overPullback _ (W i)).obj
                (F.level n)) := fun V => by
    obtain ⟨I, W, g, hg, hc⟩ := (hF n).exists_cover V
    refine ⟨I, W, g, hg, fun i => ?_⟩
    have := hc i
    obtain ⟨E, ⟨c⟩⟩ := Sheaf.mem_essImage_of_isConstant
      ((SmallEtale.topology B Y.obj Y.property).over (W i))
      (((SmallEtale.topology B Y.obj Y.property).overPullback _ (W i)).obj (F.level n))
    exact ⟨E, trivial, ⟨c⟩⟩
  obtain ⟨I, W, g, hg, hc⟩ :=
    exists_trivializing_cover_smallEtaleSheafPullback B _ f (F.level n) (fun _ => True) hH U
  refine ⟨I, W, g, hg, fun i => ?_⟩
  obtain ⟨E, -, ⟨c⟩⟩ := hc i
  exact Sheaf.isConstant_of_iso _ c.symm

end AlgebraicGeometry.SmallEtale.LAdicSheaf

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- **`ι`-realizability of an ℓ-adic sheaf** (Weil II 1.5, Kedlaya §6), in trace form: there is a
lisse ℓ-adic sheaf `F'` such that at every closed point `y` and for every `n ≥ 1` the sum
`Tr(π_y ^ n | F_ȳ ⊗ ℚ_ℓ) + Tr(π_y ^ n | F'_ȳ ⊗ ℚ_ℓ)` of the traces of the powers of the geometric
Frobenius is mapped by `ι` into `ℝ`; equivalently (Newton's identities) the characteristic
polynomial of `π_y` on `(F ⊕ F')_ȳ` is real along `ι`. -/
def LAdicSheaf.IsIotaRealizable (F : LAdicSheaf B X ℓ) (ι : ℚ_[ℓ] →+* ℂ) : Prop :=
  ∃ F' : LAdicSheaf B X ℓ, F'.IsLisse ∧ ∀ (y : closedPoints X.1) (n : ℕ), 1 ≤ n →
    ι (LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F y.1 (finite_residueField f y.1 y.2) ^ n) +
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F' y.1 (finite_residueField f y.1 y.2) ^ n)) ∈
      Set.range ((↑) : ℝ → ℂ)

/-- Realizability in the form of characteristic polynomials: `F` is `ι`-realizable exactly when
there is a lisse `F'` with the product of the Frobenius characteristic polynomials on `F_ȳ` and
`F'_ȳ` real along `ι` at every closed point. -/
theorem LAdicSheaf.isIotaRealizable_iff_charpoly (F : LAdicSheaf B X ℓ) (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.IsIotaRealizable B X ℓ f F ι ↔
      ∃ F' : LAdicSheaf B X ℓ, F'.IsLisse ∧ ∀ (y : closedPoints X.1) (j : ℕ),
        ι (((LAdicSheaf.rationalStalkFrobenius B X ℓ F y.1
            (finite_residueField f y.1 y.2)).charpoly *
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F' y.1
            (finite_residueField f y.1 y.2)).charpoly).coeff j) ∈ Set.range ((↑) : ℝ → ℂ) := by
  refine exists_congr fun F' => and_congr_right fun _ => forall_congr' fun y => ?_
  exact (coeff_charpoly_mul_mem_range_ofReal_iff ι _ _).symm

/-- **The sheaf of an `ι`-realizable representation is `ι`-realizable**: for a continuous
`ι`-realizable representation `ρ` of the étale fundamental group, the sheaf `ℱ_ρ` is
`ι`-realizable. -/
theorem LAdicSheaf.isIotaRealizable_representationSheaf [ConnectedSpace X.1]
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) {ι : ℚ_[ℓ] →+* ℂ} (h : Stacks.EtaleCohomology.IsIotaRealizable f x ι ρ) :
    LAdicSheaf.IsIotaRealizable B X ℓ f (LAdicSheaf.representationSheaf B X x ρ hρ) ι := by
  obtain ⟨r', ρ', hρ', hreal⟩ := h
  refine (LAdicSheaf.isIotaRealizable_iff_charpoly B X ℓ f _ ι).2
    ⟨LAdicSheaf.representationSheaf B X x ρ' hρ',
      LAdicSheaf.representationSheaf_isLisse B X x ρ' hρ', fun y j => ?_⟩
  rw [charpoly_rationalStalkFrobenius_representationSheaf_eq B X x f ρ hρ y,
    charpoly_rationalStalkFrobenius_representationSheaf_eq B X x f ρ' hρ' y]
  exact hreal y j

section InverseImage

variable {B X} {X' : B.Scheme} (g : X' ⟶ X)
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [IsNoetherian X'.1]
  [LocallyOfFiniteType (B.inclusion.map g)]

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **Realizability passes to inverse images** along a morphism `g : X' ⟶ X` of schemes of finite
type over a finite field sending closed points to closed points. -/
theorem LAdicSheaf.IsIotaRealizable.inverseImage {F : LAdicSheaf B X ℓ} {ι : ℚ_[ℓ] →+* ℂ}
    (hF : LAdicSheaf.IsIotaRealizable B X ℓ f F ι)
    (hg : ∀ y : closedPoints X'.1, (B.inclusion.map g).base y.1 ∈ closedPoints X.1) :
    LAdicSheaf.IsIotaRealizable B X' ℓ (B.inclusion.map g ≫ f)
      (LAdicSheaf.inverseImage g F) ι := by
  obtain ⟨F', hF', hreal⟩ := hF
  refine ⟨LAdicSheaf.inverseImage g F', hF'.inverseImage g, fun y n hn => ?_⟩
  set x : closedPoints X.1 := ⟨(B.inclusion.map g).base y.1, hg y⟩
  have hx : Finite (X.1.residueField x.1) := finite_residueField f x.1 x.2
  have : Finite (X'.1.residueField y.1) :=
    finite_residueField ((B.inclusion.map g) ≫ f) y.1 y.2
  let : Algebra (X.1.residueField x.1) (X'.1.residueField y.1) :=
    ((B.inclusion.map g).residueFieldMap y.1).hom.toAlgebra
  have : Module.Finite (X.1.residueField x.1) (X'.1.residueField y.1) := Module.Finite.of_finite
  set m := Module.finrank (X.1.residueField x.1) (X'.1.residueField y.1)
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (X'.1.residueField y.1) =
      Nat.card (X.1.residueField x.1) ^ (m - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)]
    exact Module.natCard_eq_pow_finrank
  rw [LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow X ℓ g F y.1 _ hx (m - 1) hcard hn,
    LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow X ℓ g F' y.1 _ hx (m - 1) hcard hn]
  exact hreal x _ (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero _)
    (Nat.one_le_iff_ne_zero.1 hn)))

end InverseImage

end Stacks.EtaleCohomology
