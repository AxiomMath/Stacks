module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.CoinductionRetraction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Subquotients
public import StacksFrontier.Topology.Algebra.Group.ProPGroup
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Cohomology of a pro-`ℓ` group with `ℓ`-power torsion coefficients

Let `ℓ` be a prime and `P` a profinite pro-`ℓ` group. If `Hⁿ(P, ℤ/ℓℤ) = 0` for the trivial module
`ℤ/ℓℤ`, then `Hⁿ(P, M) = 0` for every discrete `P`-module `M` which is `ℓ`-power torsion.

The proof has two steps.

* A finite `ℓ`-power torsion module `M ≠ 0` contains a copy of `ℤ/ℓℤ` with trivial action: `P`
  acts on `M` through a finite `ℓ`-group, and the number of fixed points of an `ℓ`-group acting on
  a set of cardinality a power of `ℓ` is divisible by `ℓ`. Induction on the cardinality of `M` and
  the long exact sequence of cohomology then give `Hⁿ(P, M) = 0`.
* Every cohomology class of an `ℓ`-power torsion module comes from a finite submodule. This is
  proved by induction on the degree: in degree `0` a class is an invariant element, and in
  positive degree one embeds `M` into the module coinduced from the trivial subgroup, which has no
  higher cohomology, and lifts finitely many elements of the quotient.

This is the part of the argument of the source after the reduction to a pro-`ℓ` Galois group;
there the second step is phrased as the compatibility of étale cohomology with filtered colimits.

## Main results

* `Stacks.GroupCohomology.exists_fixedPoint_ne_zero`: a nonzero finite `ℓ`-power torsion module
  over a pro-`ℓ` group has a nonzero invariant element killed by `ℓ`.
* `Stacks.GroupCohomology.subsingleton_ext_of_finite`: the case of finite modules.
* `Stacks.GroupCohomology.exists_finite_ext_comp`: every class comes from a finite submodule.
* `Stacks.GroupCohomology.subsingleton_ext_of_isProPGroup`: the general case.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [J.-P. Serre, *Galois cohomology*, I.4.1][serre1997galois]
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v w

namespace Stacks.GroupCohomology

variable {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

section Ext

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} P)]

omit [IsTopologicalGroup P] in
/-- `Ext` into a module with trivial underlying group vanishes. -/
lemma subsingleton_ext_of_subsingleton (X N : ContinuousGModule.{v, max v w} P)
    [Subsingleton N.obj.obj.V] (n : ℕ) : Subsingleton (Abelian.Ext X N n) := by
  have hN : IsZero N := (IsZero.iff_id_eq_zero N).mpr (hom_ext fun _ ↦ Subsingleton.elim _ _)
  refine subsingleton_of_forall_eq 0 fun e ↦ ?_
  rw [← Abelian.Ext.comp_mk₀_id e, hN.eq_of_src (𝟙 N) 0, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero]

end Ext

variable [CompactSpace P] [TotallyDisconnectedSpace P] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

section FixedPoints

variable (N : ContinuousGModule.{v, w} P)

/-- The kernel of the action on a finite discrete module is an open normal subgroup. -/
def actionKernel [Finite N.obj.obj.V] : OpenNormalSubgroup P where
  toSubgroup := (representation N).ker
  isOpen' := by
    have : ((representation N).ker : Set P) =
        ⋂ y : N.obj.obj.V, {g | (N.obj.obj.ρ g).asHom.hom y = y} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      exact ⟨fun h y ↦ congrArg (fun f : Module.End ℤ N.obj.obj.V ↦ f y) h,
        fun h ↦ LinearMap.ext h⟩
    change IsOpen ((representation N).ker : Set P)
    rw [this]
    exact isOpen_iInter_of_finite fun y ↦ isOpen_stabilizer ℤ P N y
  isNormal' := inferInstance

omit [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] in
/-- **A nonzero finite `ℓ`-power torsion module over a pro-`ℓ` group has a nonzero invariant
element killed by `ℓ`.** -/
theorem exists_fixedPoint_ne_zero (hP : IsProPGroup ℓ P) [Finite N.obj.obj.V]
    [Nontrivial N.obj.obj.V] (hN : ∀ x : N.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    ∃ x : N.obj.obj.V, x ≠ 0 ∧ ℓ • x = 0 ∧ ∀ g, (N.obj.obj.ρ g).asHom.hom x = x := by
  classical
  let K := actionKernel N
  have hK : IsPGroup ℓ (P ⧸ K.toSubgroup) := hP K
  let φ : P ⧸ K.toSubgroup →* Module.End ℤ N.obj.obj.V :=
    QuotientGroup.lift _ (representation N) le_rfl
  let : MulAction (P ⧸ K.toSubgroup) N.obj.obj.V := MulAction.compHom _ φ
  -- the cardinality of `N` is a positive power of `ℓ`
  have hpow : IsPGroup ℓ (Multiplicative N.obj.obj.V) := fun g ↦ by
    obtain ⟨k, hk⟩ := hN (Multiplicative.toAdd g)
    exact ⟨k, by rw [← ofAdd_toAdd g, ← ofAdd_nsmul, hk, ofAdd_zero]⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hpow
  have hm' : Nat.card N.obj.obj.V = ℓ ^ m := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simpa [hm'] using Finite.one_lt_card (α := N.obj.obj.V)
  have hdvd : ℓ ∣ Nat.card (MulAction.fixedPoints (P ⧸ K.toSubgroup) N.obj.obj.V) :=
    ((hK.card_modEq_card_fixedPoints N.obj.obj.V).dvd_iff dvd_rfl).mp (hm' ▸ dvd_pow_self ℓ hm0)
  -- a nonzero fixed point
  have h0 : (0 : N.obj.obj.V) ∈ MulAction.fixedPoints (P ⧸ K.toSubgroup) N.obj.obj.V :=
    fun q ↦ map_zero (φ q)
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ MulAction.fixedPoints (P ⧸ K.toSubgroup) N.obj.obj.V, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Set.eq_singleton_iff_unique_mem.mpr ⟨h0, hcon⟩, Nat.card_unique] at hdvd
    exact hℓ.out.ne_one (Nat.dvd_one.mp hdvd)
  have hyfix : ∀ g, (N.obj.obj.ρ g).asHom.hom y = y := fun g ↦ hy (g : P ⧸ K.toSubgroup)
  -- multiply by a power of `ℓ` to get an element killed by `ℓ`
  have hex : ∃ k, ℓ ^ k • y = 0 := hN y
  let k := Nat.find hex
  have hk : ℓ ^ k • y = 0 := Nat.find_spec hex
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h ↦ hy0 (by simpa [h] using hk)
  refine ⟨ℓ ^ (k - 1) • y, Nat.find_min hex (Nat.sub_lt hk0 one_pos), ?_, fun g ↦ ?_⟩
  · rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hk0, hk]
  · rw [map_nsmul, hyfix]

end FixedPoints

section FiniteCase

/-- The cyclic subgroup generated by an invariant element is stable under the action. -/
private theorem zmultiples_stable {G : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {N : ContinuousGModule.{v, w} G} {x : N.obj.obj.V}
    (hfix : ∀ g, (N.obj.obj.ρ g).asHom.hom x = x) :
    ∀ g, ∀ a ∈ AddSubgroup.zmultiples x,
      (N.obj.obj.ρ g).asHom.hom a ∈ AddSubgroup.zmultiples x := by
  intro g a ha
  obtain ⟨c, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨c, by rw [map_zsmul, hfix]⟩

/-- A stable subgroup of an `ℓ`-power torsion module is `ℓ`-power torsion. -/
private theorem exists_pow_smul_subObj_eq_zero {G : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {N : ContinuousGModule.{v, w} G} {ℓ : ℕ}
    (A : AddSubgroup N.obj.obj.V) (hA : ∀ g, ∀ a ∈ A, (N.obj.obj.ρ g).asHom.hom a ∈ A)
    (hN : ∀ x : N.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) (y : (subObj N A hA).obj.obj.V) :
    ∃ k : ℕ, ℓ ^ k • y = 0 :=
  (hN ((subObjι N A hA).hom.hom.hom.hom y)).imp
    fun k hk ↦ subObjι_injective N A hA (by rw [map_nsmul, hk, map_zero])

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} P)]

/-- The additive map `ℤ/ℓℤ → N` sending `1` to an element killed by `ℓ`. -/
def zmodHom {A : Type*} [AddCommGroup A] (x : A) (hx : ℓ • x = 0) : ZMod ℓ →+ A :=
  ZMod.lift ℓ ⟨zmultiplesHom A x, by simpa using hx⟩

/-- The map `zmodHom x hx` sends the class of an integer `c` to `c • x`. -/
@[simp]
lemma zmodHom_intCast {A : Type*} [AddCommGroup A] (x : A) (hx : ℓ • x = 0) (c : ℤ) :
    zmodHom x hx (c : ZMod ℓ) = c • x := by
  simp [zmodHom]

/-- The trivial module `ℤ/ℓℤ` included in a module along an invariant element killed by `ℓ`. -/
def zmodIncl (N : ContinuousGModule.{v, max v w} P) (x : N.obj.obj.V) (hx : ℓ • x = 0)
    (hfix : ∀ g, (N.obj.obj.ρ g).asHom.hom x = x) :
    trivialGModule.{v, max v w} P (ULift.{max v w} (ZMod ℓ)) ⟶ N :=
  (gModuleHomEquiv P _ _).symm
    ⟨(zmodHom x hx).comp AddEquiv.ulift.toAddMonoidHom, fun g a ↦ by
        obtain ⟨a⟩ := a
        obtain ⟨c, rfl⟩ := ZMod.intCast_surjective a
        change zmodHom x hx (c : ZMod ℓ) = (N.obj.obj.ρ g).asHom.hom (zmodHom x hx (c : ZMod ℓ))
        rw [zmodHom_intCast, map_zsmul, hfix]⟩

omit [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P]
  [HasExt (ContinuousGModule P)] in
/-- The morphism `zmodIncl N x hx hfix` sends the class of an integer `c` to `c • x`. -/
lemma zmodIncl_apply (N : ContinuousGModule.{v, max v w} P) (x : N.obj.obj.V) (hx : ℓ • x = 0)
    (hfix : ∀ g, (N.obj.obj.ρ g).asHom.hom x = x) (c : ℤ) :
    (zmodIncl N x hx hfix).hom.hom.hom.hom (ULift.up (c : ZMod ℓ)) = c • x :=
  zmodHom_intCast x hx c

omit [CompactSpace P] [TotallyDisconnectedSpace P] in
/-- **Finite case.** If `Hⁿ(P, ℤ/ℓℤ) = 0` for a profinite pro-`ℓ` group `P`, then `Hⁿ(P, M) = 0`
for every finite `ℓ`-power torsion discrete `P`-module `M`. -/
theorem subsingleton_ext_of_finite (hP : IsProPGroup ℓ P) (n : ℕ)
    [h : Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ))
      (trivialGModule.{v, max v w} P (ULift.{max v w} (ZMod ℓ))) n)]
    (N : ContinuousGModule.{v, max v w} P) [Finite N.obj.obj.V]
    (hN : ∀ x : N.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ)) N n) := by
  induction hc : Nat.card N.obj.obj.V using Nat.strong_induction_on generalizing N with
  | _ c ih =>
  rcases subsingleton_or_nontrivial N.obj.obj.V with hs | hnt
  · exact subsingleton_ext_of_subsingleton _ _ n
  obtain ⟨x, hx0, hx, hfix⟩ := exists_fixedPoint_ne_zero N hP hN
  let A : AddSubgroup N.obj.obj.V := AddSubgroup.zmultiples x
  have hmemA : ∀ y, y ∈ A ↔ ∃ c : ℤ, c • x = y := fun y ↦ AddSubgroup.mem_zmultiples_iff
  have hA := zmultiples_stable hfix
  let f := zmodIncl N x hx hfix
  let S : ShortComplex (ContinuousGModule.{v, max v w} P) :=
    ShortComplex.mk f (quotObjπ N A hA) (hom_ext fun a ↦ by
      obtain ⟨a⟩ := a
      obtain ⟨c, rfl⟩ := ZMod.intCast_surjective a
      show (QuotientAddGroup.mk (f.hom.hom.hom.hom (ULift.up (c : ZMod ℓ))) :
        N.obj.obj.V ⧸ A) = 0
      rw [zmodIncl_apply]
      exact (QuotientAddGroup.eq_zero_iff (N := A) _).mpr ((hmemA _).mpr ⟨c, rfl⟩))
  have horder : addOrderOf x = ℓ := addOrderOf_eq_prime hx hx0
  have hS : S.ShortExact := by
    refine shortExact_of_function_exact S ?_ (quotObjπ_surjective N A hA) ?_
    · intro a b hab
      obtain ⟨a⟩ := a
      obtain ⟨b⟩ := b
      obtain ⟨c, rfl⟩ := ZMod.intCast_surjective a
      obtain ⟨d, rfl⟩ := ZMod.intCast_surjective b
      have hab' : c • x = d • x := by
        change f.hom.hom.hom.hom (ULift.up (c : ZMod ℓ)) =
          f.hom.hom.hom.hom (ULift.up (d : ZMod ℓ)) at hab
        rwa [zmodIncl_apply, zmodIncl_apply] at hab
      have : ((c - d : ℤ) : ZMod ℓ) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← horder, ← addOrderOf_dvd_iff_zsmul_eq_zero.symm,
          sub_zsmul, hab']
        exact add_neg_cancel (d • x)
      congr 1
      rwa [Int.cast_sub, sub_eq_zero] at this
    · intro m
      show (QuotientAddGroup.mk m : N.obj.obj.V ⧸ A) = 0 ↔ m ∈ Set.range f.hom.hom.hom.hom
      refine (QuotientAddGroup.eq_zero_iff (N := A) m).trans ⟨fun hm ↦ ?_, ?_⟩
      · obtain ⟨c, rfl⟩ := (hmemA m).mp hm
        exact ⟨ULift.up (c : ZMod ℓ), zmodIncl_apply N x hx hfix c⟩
      · rintro ⟨⟨a⟩, rfl⟩
        obtain ⟨c, rfl⟩ := ZMod.intCast_surjective a
        rw [zmodIncl_apply]
        exact (hmemA _).mpr ⟨c, rfl⟩
  -- the quotient is finite, `ℓ`-power torsion and smaller
  have hQfin : Finite (quotObj N A hA).obj.obj.V :=
    Finite.of_surjective _ (quotObjπ_surjective N A hA)
  have hQcard : Nat.card (quotObj N A hA).obj.obj.V < c := by
    have h2 : Nat.card A = ℓ := by rw [← horder, ← Nat.card_zmultiples x]
    rw [← hc, ← card_quotObj_mul N A hA, h2]
    exact lt_mul_of_one_lt_right Nat.card_pos hℓ.out.one_lt
  have := ih _ hQcard (quotObj N A hA) (quotObj_exists_pow_smul_eq_zero N A hA hN) rfl
  refine subsingleton_of_forall_eq 0 fun e ↦ ?_
  obtain ⟨e₁, he₁⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS e (Subsingleton.elim _ _)
  rw [← he₁, Subsingleton.elim e₁ 0, Abelian.Ext.zero_comp]

end FiniteCase

section TrivialSubgroup

/-- Over the trivial subgroup, the trivial module `ℤ` is projective: every discrete module of
the trivial group has the trivial action. -/
instance projective_trivialGModule_bot :
    Projective (trivialGModule.{v, max v w} (⊥ : Subgroup P) (ULift.{max v w} ℤ)) where
  factors {E X} f e he := by
    rw [epi_iff_surjective] at he
    obtain ⟨x, hx⟩ := he (f.hom.hom.hom.hom (ULift.up 1))
    have htriv : ∀ (g : (⊥ : Subgroup P)) (y : E.obj.obj.V), (E.obj.obj.ρ g).asHom.hom y = y := by
      intro g y
      obtain rfl : g = 1 := Subsingleton.elim _ _
      exact ρ_one_apply E y
    refine ⟨(gModuleHomEquiv _ _ _).symm
      ⟨(zmultiplesHom E.obj.obj.V x).comp AddEquiv.ulift.toAddMonoidHom,
        fun g a ↦ (htriv g _).symm⟩, hom_ext fun a ↦ ?_⟩
    obtain ⟨a⟩ := a
    have h1 : (ULift.up a : ULift.{max v w} ℤ) = a • ULift.up 1 := by
      ext
      simp
    change e.hom.hom.hom.hom (a • x) = f.hom.hom.hom.hom (ULift.up a)
    rw [h1]
    exact (map_zsmul e.hom.hom.hom.hom.toAddMonoidHom a x).trans ((congrArg (a • ·) hx).trans
      (map_zsmul f.hom.hom.hom.hom.toAddMonoidHom a _).symm)

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} P)]
  [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup P))]

/-- **A module coinduced from the trivial subgroup has no higher cohomology.** -/
theorem ext_coinduction_bot_eq_zero (N : ContinuousGModule.{v, max v w} (⊥ : Subgroup P))
    (n : ℕ) (e : Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ))
      ((coinduction.{v, w} (⊥ : Subgroup P)).obj N) (n + 1)) : e = 0 :=
  (shapiroAddEquiv.{v, w} (⊥ : Subgroup P) N (n + 1)).symm.map_eq_zero_iff.mp
    (Abelian.Ext.eq_zero_of_projective _)

end TrivialSubgroup

section Reduction

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} P)]
  [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup P))]

omit hℓ in
/-- A module all of whose elements are killed by a power of `ℓ` has torsion elements, for
`ℓ ≠ 0`. -/
lemma exists_nsmul_eq_zero_of_pow (hℓ0 : ℓ ≠ 0) {A : Type*} [AddCommGroup A] {a : A}
    (ha : ∃ k : ℕ, ℓ ^ k • a = 0) : ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨ℓ ^ k, pow_pos (Nat.pos_of_ne_zero hℓ0) k, hk⟩

/-- **Every cohomology class of an `ℓ`-power torsion module comes from a finite submodule.**
More precisely, it is the image of a class of a finite `ℓ`-power torsion module mapping to it. -/
theorem exists_finite_ext_comp (n : ℕ) : ∀ (N : ContinuousGModule.{v, max v w} P)
    (_hN : ∀ x : N.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0)
    (c : Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ)) N n),
    ∃ (N' : ContinuousGModule.{v, max v w} P) (_ : Finite N'.obj.obj.V)
      (_ : ∀ x : N'.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) (ι : N' ⟶ N)
      (c' : Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ)) N' n),
      c = c'.comp (Abelian.Ext.mk₀ ι) (add_zero n) := by
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  induction n with
  | zero =>
    intro N hN c
    obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 c
    set x := φ.hom.hom.hom.hom (ULift.up 1)
    have hfix : ∀ g, (N.obj.obj.ρ g).asHom.hom x = x := fun g ↦ (hom_comm φ g _).symm
    let A : AddSubgroup N.obj.obj.V := AddSubgroup.zmultiples x
    have hA := zmultiples_stable hfix
    have hφ : ∀ a : ℤ, φ.hom.hom.hom.hom (ULift.up a) = a • x := by
      intro a
      have h1 : (ULift.up a : ULift.{max v w} ℤ) = a • ULift.up 1 := by
        ext
        simp
      rw [h1]
      exact map_zsmul φ.hom.hom.hom.hom.toAddMonoidHom a _
    let φ' : trivialGModule.{v, max v w} P (ULift.{max v w} ℤ) ⟶ subObj N A hA :=
      (gModuleHomEquiv P _ _).symm
        ⟨(zmultiplesHom (subObj N A hA).obj.obj.V ⟨x, AddSubgroup.mem_zmultiples x⟩).comp
          AddEquiv.ulift.toAddMonoidHom, fun g a ↦ by
            obtain ⟨a⟩ := a
            refine Subtype.ext ?_
            show a • x = (N.obj.obj.ρ g).asHom.hom (a • x)
            rw [map_zsmul, hfix]⟩
    refine ⟨subObj N A hA, ?_, exists_pow_smul_subObj_eq_zero A hA hN,
      subObjι N A hA, Abelian.Ext.mk₀ φ', ?_⟩
    · exact Set.finite_coe_iff.mpr (finite_zmultiples.mpr
        (isOfFinAddOrder_iff_nsmul_eq_zero.mpr (exists_nsmul_eq_zero_of_pow hℓ0 (hN x))))
    · rw [Abelian.Ext.mk₀_comp_mk₀]
      congr 1
      exact hom_ext fun ⟨a⟩ ↦ hφ a
  | succ n ih =>
    intro N hN c
    -- the embedding into the module coinduced from the trivial subgroup
    let RN := (restriction.{v, v, max v w} (⊥ : Subgroup P).subtype continuous_subtype_val).obj N
    let C := (coinduction.{v, w} (⊥ : Subgroup P)).obj RN
    let η : N ⟶ C := (restrictionCoinductionAdjunction.{v, w} (⊥ : Subgroup P)).unit.app N
    have hη1 : ∀ m, (η.hom.hom.hom.hom m : coinductionCarrier (⊥ : Subgroup P) RN).1 1 = m :=
      fun m ↦ (restrictionCoinductionAdjunction_unit_app_apply N m 1).trans (ρ_one_apply N m)
    have hηinj : Function.Injective η.hom.hom.hom.hom := fun m m' h ↦ by
      rw [← hη1 m, ← hη1 m', h]
    let B : AddSubgroup C.obj.obj.V := η.hom.hom.hom.hom.toAddMonoidHom.range
    have hB : ∀ g, ∀ a ∈ B, (C.obj.obj.ρ g).asHom.hom a ∈ B := by
      rintro g _ ⟨m, rfl⟩
      exact ⟨(N.obj.obj.ρ g).asHom.hom m, hom_comm η g m⟩
    let S : ShortComplex (ContinuousGModule.{v, max v w} P) :=
      ShortComplex.mk η (quotObjπ C B hB)
        (hom_ext fun m ↦ (QuotientAddGroup.eq_zero_iff (N := B) _).mpr ⟨m, rfl⟩)
    have hS : S.ShortExact :=
      shortExact_of_function_exact S hηinj (quotObjπ_surjective C B hB) fun y ↦ by
        show (QuotientAddGroup.mk y : C.obj.obj.V ⧸ B) = 0 ↔ y ∈ Set.range _
        exact (QuotientAddGroup.eq_zero_iff (N := B) y)
    have hCtors : ∀ y : C.obj.obj.V, ∃ k : ℕ, ℓ ^ k • y = 0 :=
      exists_pow_smul_coinduction_eq_zero (N := RN) hN
    -- the class comes from the quotient
    obtain ⟨d, hd⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS c
      (ext_coinduction_bot_eq_zero.{v, w} RN n _) rfl
    obtain ⟨Q', hQ'fin, hQ'tors, ι₃, d', rfl⟩ :=
      ih (quotObj C B hB) (quotObj_exists_pow_smul_eq_zero C B hB hCtors) d
    -- lifts of the elements of `Q'`
    let L : Q'.obj.obj.V → C.obj.obj.V :=
      Function.surjInv (quotObjπ_surjective C B hB) ∘ ι₃.hom.hom.hom.hom
    have hL : ∀ q, (quotObjπ C B hB).hom.hom.hom.hom (L q) = ι₃.hom.hom.hom.hom q :=
      fun q ↦ Function.surjInv_eq (quotObjπ_surjective C B hB) _
    let PP := prodObj Q' C
    let T : Set PP.obj.obj.V := Set.range fun q ↦ (q, L q)
    let BB : AddSubgroup PP.obj.obj.V :=
      { carrier := {p | ι₃.hom.hom.hom.hom p.1 = (quotObjπ C B hB).hom.hom.hom.hom p.2}
        zero_mem' := by
          show ι₃.hom.hom.hom.hom 0 = (quotObjπ C B hB).hom.hom.hom.hom 0
          rw [map_zero, map_zero]
        add_mem' := fun {a b} ha hb ↦ by
          show ι₃.hom.hom.hom.hom (a.1 + b.1) = (quotObjπ C B hB).hom.hom.hom.hom (a.2 + b.2)
          rw [map_add, map_add, ha, hb]
        neg_mem' := fun {a} ha ↦ by
          show ι₃.hom.hom.hom.hom (-a.1) = (quotObjπ C B hB).hom.hom.hom.hom (-a.2)
          rw [map_neg, map_neg, ha] }
    have hBB : ∀ g, ∀ a ∈ BB, (PP.obj.obj.ρ g).asHom.hom a ∈ BB := by
      intro g a ha
      show ι₃.hom.hom.hom.hom ((Q'.obj.obj.ρ g).asHom.hom a.1) =
        (quotObjπ C B hB).hom.hom.hom.hom ((C.obj.obj.ρ g).asHom.hom a.2)
      rw [hom_comm, hom_comm]
      exact congrArg _ ha
    let F := generatedSubmodule PP T
    have hF := generatedSubmodule_stable PP T
    have hFB : F ≤ BB := generatedSubmodule_le PP hBB (by
      rintro _ ⟨q, rfl⟩
      exact (hL q).symm)
    have hTF : ∀ q, ((q, L q) : PP.obj.obj.V) ∈ F := fun q ↦
      subset_generatedSubmodule PP T ⟨q, rfl⟩
    have hFfin : Finite F := by
      refine finite_generatedSubmodule PP (Set.finite_range _) ?_
      rintro _ ⟨q, rfl⟩
      obtain ⟨k₁, hk₁⟩ := hQ'tors q
      obtain ⟨k₂, hk₂⟩ := hCtors (L q)
      refine ⟨ℓ ^ (k₁ + k₂), pow_pos (Nat.pos_of_ne_zero hℓ0) _, Prod.ext ?_ ?_⟩
      · show ℓ ^ (k₁ + k₂) • q = 0
        rw [pow_add, mul_comm, mul_smul, hk₁, smul_zero]
      · show ℓ ^ (k₁ + k₂) • L q = 0
        rw [pow_add, mul_smul, hk₂, smul_zero]
    -- the finite short exact sequence `N' → P' → Q'`
    let incl : N.obj.obj.V →+ PP.obj.obj.V :=
      (AddMonoidHom.inr _ _).comp η.hom.hom.hom.hom.toAddMonoidHom
    let Nsub : AddSubgroup N.obj.obj.V := F.comap incl
    have hNsub : ∀ g, ∀ a ∈ Nsub, (N.obj.obj.ρ g).asHom.hom a ∈ Nsub := by
      intro g a ha
      have := hF g _ ha
      change ((Q'.obj.obj.ρ g).asHom.hom 0,
        (C.obj.obj.ρ g).asHom.hom (η.hom.hom.hom.hom a)) ∈ F at this
      show ((0 : Q'.obj.obj.V), η.hom.hom.hom.hom ((N.obj.obj.ρ g).asHom.hom a)) ∈ F
      rwa [map_zero, ← hom_comm] at this
    let N' := subObj N Nsub hNsub
    let P' := subObj PP F hF
    let f'₀ : Nsub →+ F :=
      { toFun a := ⟨incl a, a.2⟩
        map_zero' := Subtype.ext (map_zero incl)
        map_add' a b := Subtype.ext (map_add incl (a : N.obj.obj.V) b) }
    let f' : N' ⟶ P' := (gModuleHomEquiv P _ _).symm
      ⟨f'₀, fun g a ↦ Subtype.ext (by
        show ((0 : Q'.obj.obj.V), η.hom.hom.hom.hom ((N.obj.obj.ρ g).asHom.hom a.1)) =
          ((Q'.obj.obj.ρ g).asHom.hom 0, (C.obj.obj.ρ g).asHom.hom (η.hom.hom.hom.hom a.1))
        rw [map_zero, hom_comm])⟩
    let g' : P' ⟶ Q' := subObjι PP F hF ≫ prodObjFst Q' C
    let S' : ShortComplex (ContinuousGModule.{v, max v w} P) :=
      ShortComplex.mk f' g' (hom_ext fun _ ↦ rfl)
    have hf' : Function.Injective f'.hom.hom.hom.hom := fun a b hab ↦
      subObjι_injective N Nsub hNsub (hηinj (congrArg (fun p ↦
        ((prodObjSnd Q' C).hom.hom.hom.hom ((subObjι PP F hF).hom.hom.hom.hom p))) hab))
    have hS' : S'.ShortExact := by
      refine shortExact_of_function_exact S' hf' (fun q ↦ ?_) (fun p ↦ ?_)
      · exact ⟨subObjMk PP F hF (q, L q) (hTF q), rfl⟩
      · set pp := (subObjι PP F hF).hom.hom.hom.hom p
        have hpF : pp ∈ F := subObjι_mem PP F hF p
        show pp.1 = 0 ↔ p ∈ Set.range f'.hom.hom.hom.hom
        refine ⟨fun hp ↦ ?_, ?_⟩
        · have hpB : ι₃.hom.hom.hom.hom pp.1 = (quotObjπ C B hB).hom.hom.hom.hom pp.2 := hFB hpF
          rw [hp, map_zero] at hpB
          obtain ⟨m, hm⟩ := (QuotientAddGroup.eq_zero_iff (N := B) _).mp hpB.symm
          have hpm : pp = incl m := Prod.ext hp hm.symm
          exact ⟨subObjMk N Nsub hNsub m ((congrArg (· ∈ F) hpm).mp hpF),
            subObjι_injective PP F hF hpm.symm⟩
        · rintro ⟨a, rfl⟩
          rfl
    let τ : S' ⟶ S :=
      { τ₁ := subObjι N Nsub hNsub
        τ₂ := subObjι PP F hF ≫ prodObjSnd Q' C
        τ₃ := ι₃
        comm₁₂ := hom_ext fun _ ↦ rfl
        comm₂₃ := hom_ext fun p ↦ (hFB (subObjι_mem PP F hF p)).symm }
    have hfinN' : Finite N'.obj.obj.V := by
      have : Finite P'.obj.obj.V := hFfin
      exact Finite.of_injective _ hf'
    refine ⟨N', hfinN', exists_pow_smul_subObj_eq_zero Nsub hNsub hN, τ.τ₁,
      d'.comp hS'.extClass (by omega), ?_⟩
    rw [← hd, Abelian.Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega),
      ← hS'.extClass_naturality hS τ,
      Abelian.Ext.comp_assoc _ _ _ (by omega) (add_zero 1) (by omega)]

end Reduction

/-- **Cohomology of a pro-`ℓ` group with `ℓ`-power torsion coefficients.** Let `P` be a profinite
pro-`ℓ` group with `Hⁿ(P, ℤ/ℓℤ) = 0`. Then `Hⁿ(P, M) = 0` for every discrete `P`-module `M`
which is `ℓ`-power torsion. -/
theorem subsingleton_ext_of_isProPGroup
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} P)]
    [HasExt.{max v w} (ContinuousGModule.{v, max v w} (⊥ : Subgroup P))]
    (hP : IsProPGroup ℓ P) (n : ℕ)
    [Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ))
      (trivialGModule.{v, max v w} P (ULift.{max v w} (ZMod ℓ))) n)]
    (N : ContinuousGModule.{v, max v w} P) (hN : ∀ x : N.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} P (ULift.{max v w} ℤ)) N n) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨N', hN'fin, hN'tors, ι, c', rfl⟩ := exists_finite_ext_comp.{v, w} n N hN c
  have := subsingleton_ext_of_finite.{v, w} hP n N' hN'tors
  rw [Subsingleton.elim c' 0, Abelian.Ext.zero_comp]

end Stacks.GroupCohomology

end
