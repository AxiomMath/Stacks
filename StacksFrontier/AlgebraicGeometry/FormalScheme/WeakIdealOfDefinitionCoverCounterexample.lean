module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionNotCutOut

/-!
# The weak ideal of definition condition cannot be checked on an affine open covering

**Stacks 0AIV** asserts that an ideal sheaf `ℐ` on a formal scheme `𝔛` in the sense of McQuillan
is a weak ideal of definition, meaning that `ℐ(𝔘)` is a weak ideal of definition of `𝒪_𝔛(𝔘)` for
every affine formal open `𝔘`, as soon as this holds for the members of one covering of `𝔛` by
affine formal opens. As printed this is false, already for a single affine scheme covered by
itself. This file gives a witness.

Let `R = ℤ₂[ε]` be the dual numbers over the `2`-adic integers, a local ring, and `X = Spec R`,
pseudo-discretised. Let `ℐ` be the ideal sheaf of the sections whose germ at the closed point `𝔪`
vanishes; over an open missing `𝔪` it is the unit ideal. Every open neighbourhood of the closed
point of a local spectrum is everything, so a global section of `ℐ` vanishes on all of `X`:
`ℐ(X) = 0`, which is a weak ideal of definition of the discrete ring `R`. The covering of `X` by
itself thus satisfies the condition on its member. But over the affine open `D(2)`, which misses
`𝔪`, the ideal `ℐ(D(2))` is the unit ideal of the discrete ring `R_2`, which is non-zero since the
image of `ε` in it is; and `1` is not topologically nilpotent in a non-zero discrete ring.

## Main definitions

* `AlgebraicGeometry.Scheme.germVanishingAtIdeal`: the ideal of sections of `𝒪_X` over an open
  whose germ at a point vanishes, the unit ideal when the open misses the point.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.germVanishingAt`: these ideals, as
  an ideal sheaf on the pseudo-discretisation of `X`.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.germVanishingAt_closedPoint_ideal_top`: on a local spectrum the ideal sheaf of sections
  vanishing at the closed point has no non-zero global section.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.exists_not_isWeakIdealOfDefinitionOn_of_cover`: a McQuillan formal scheme `X` whose whole
  space is a weak affine formal open, with an ideal sheaf whose global sections form a weak ideal
  of definition but which is not a weak ideal of definition over all weak affine formal opens.

## Implementation notes

The condition does pass from a covering to all affine formal opens when it is imposed on every
affine formal open contained in a member of the covering (see
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isWeakIdealOfDefinitionOn_of_cover`);
the witness here shows that this refinement cannot be dropped.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Filter

universe u

namespace AlgebraicGeometry

/-! ### The ideal of sections at the level of the scheme -/

namespace Scheme

variable (X : Scheme.{u}) (x : X)

/-- The ideal of the sections of `𝒪_X` over `U` whose germ at the point `x` vanishes; it is the
unit ideal when `U` does not contain `x`. -/
noncomputable def germVanishingAtIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  ⨅ hx : x ∈ U, RingHom.ker (X.presheaf.germ U x hx).hom

variable {X x}

/-- A section lies in `X.germVanishingAtIdeal x U` exactly when its germ at `x` vanishes. -/
theorem mem_germVanishingAtIdeal {U : X.Opens} {s : Γ(X, U)} :
    s ∈ X.germVanishingAtIdeal x U ↔ ∀ hx : x ∈ U, X.presheaf.germ U x hx s = 0 := by
  simp only [germVanishingAtIdeal, Ideal.mem_iInf, RingHom.mem_ker]

/-- Over an open missing `x`, `X.germVanishingAtIdeal x U` is the unit ideal. -/
theorem germVanishingAtIdeal_eq_top {U : X.Opens} (hx : x ∉ U) :
    X.germVanishingAtIdeal x U = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_germVanishingAtIdeal.mpr fun h => absurd h hx

/-- Restriction carries `X.germVanishingAtIdeal x U` into the ideal over a smaller open, the
germ of a restriction being a germ of the section. -/
theorem map_mem_germVanishingAtIdeal {U V : X.Opens} (h : V ≤ U) {s : Γ(X, U)}
    (hs : s ∈ X.germVanishingAtIdeal x U) :
    X.presheaf.map (homOfLE h).op s ∈ X.germVanishingAtIdeal x V := by
  rw [mem_germVanishingAtIdeal] at hs ⊢
  intro hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs (h hx)

/-- Membership in `X.germVanishingAtIdeal x U` is local, the condition being on a germ. -/
theorem mem_germVanishingAtIdeal_of_locally {U : X.Opens} {s : Γ(X, U)}
    (hlocal : ∀ y ∈ U, ∃ (V : X.Opens) (h : V ≤ U),
      y ∈ V ∧ X.presheaf.map (homOfLE h).op s ∈ X.germVanishingAtIdeal x V) :
    s ∈ X.germVanishingAtIdeal x U := by
  rw [mem_germVanishingAtIdeal]
  intro hx
  obtain ⟨V, hVU, hxV, hV⟩ := hlocal x hx
  have := mem_germVanishingAtIdeal.mp hV hxV
  rwa [TopCat.Presheaf.germ_res_apply] at this

end Scheme

namespace LocallyTopologicallyRingedSpace.IdealSheaf

/-! ### The ideal sheaf -/

variable (X : Scheme.{u}) (x : X)

/-- The ideal sheaf on the pseudo-discretisation of a scheme `X` of the sections whose germ at a
given point `x` vanishes. -/
noncomputable def germVanishingAt : IdealSheaf (schemeToLTRSObj X) where
  ideal U := X.germVanishingAtIdeal x U
  map_mem h _ hs := Scheme.map_mem_germVanishingAtIdeal h hs
  mem_of_locally_mem hlocal := Scheme.mem_germVanishingAtIdeal_of_locally hlocal

variable {X x} in
/-- A section lies in `germVanishingAt X x` exactly when its germ at `x` vanishes. -/
theorem mem_germVanishingAt {U : X.Opens} {s : Γ(X, U)} :
    s ∈ (germVanishingAt X x).ideal U ↔ ∀ hx : x ∈ U, X.presheaf.germ U x hx s = 0 :=
  Scheme.mem_germVanishingAtIdeal

variable (R : CommRingCat.{u}) [IsLocalRing R]

/-- On the spectrum of a local ring the ideal sheaf of sections vanishing at the closed point has
zero ideal of global sections: a global section with vanishing germ at the closed point vanishes
on an open neighbourhood of it, and every open neighbourhood of the closed point of a local
spectrum is everything. -/
theorem germVanishingAt_closedPoint_ideal_top :
    (germVanishingAt (Spec R) (IsLocalRing.closedPoint R)).ideal ⊤ = ⊥ := by
  refine eq_bot_iff.mpr fun s hs => ?_
  have h0 := (mem_germVanishingAt (U := ⊤)).mp hs trivial
  obtain ⟨W, hxW, iU, iV, h⟩ := (Spec R).presheaf.germ_eq (U := ⊤) (V := ⊤)
    (IsLocalRing.closedPoint R) trivial trivial s 0 (h0.trans (map_zero _).symm)
  obtain rfl : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hxW
  rw [show iU = 𝟙 _ from Subsingleton.elim _ _, op_id, (Spec R).presheaf.map_id, map_zero] at h
  exact h

/-- On the spectrum of a local ring, the ideal sheaf of sections vanishing at the closed point is
a weak ideal of definition over the whole space: its global sections are zero, and the global
sections of the pseudo-discretised structure sheaf are discrete. -/
theorem isWeakIdealOfDefinition_germVanishingAt_closedPoint_ideal_top :
    TopologicalRing.IsWeakIdealOfDefinition
      ((germVanishingAt (Spec R) (IsLocalRing.closedPoint R)).ideal ⊤) := by
  have : DiscreteTopology ((schemeToLTRSObj (Spec R)).presheaf.obj (op ⊤)).α :=
    isPseudoDiscrete_pseudoDiscrete (Spec R).presheaf ⊤
      (isWeakAffineFormalOpen_top_Spec R).isCompact
  refine ⟨isOpen_discrete _, fun s hs => ?_⟩
  rw [germVanishingAt_closedPoint_ideal_top, Ideal.mem_bot] at hs
  rw [hs]
  exact IsNilpotent.zero.isTopologicallyNilpotent

variable {R}

/-- On the spectrum of a local ring, if no power of an element `t` of the maximal ideal kills some
`ε`, the ideal sheaf of sections vanishing at the closed point is not a weak ideal of definition
over the weak affine formal opens. Over the affine open `D(t)`, which misses the closed point, it
is the unit ideal of `R_t`, which is discrete and non-zero, so that `1` is not topologically
nilpotent there. -/
theorem not_isWeakIdealOfDefinitionOn_germVanishingAt_closedPoint {t ε : R}
    (ht : t ∈ IsLocalRing.maximalIdeal R) (htε : ∀ n : ℕ, t ^ n * ε ≠ 0) :
    ¬ (germVanishingAt (Spec R) (IsLocalRing.closedPoint R)).IsWeakIdealOfDefinitionOn
      (IsWeakAffineFormalOpen (schemeToLTRSObj (Spec R))) := by
  intro hI
  have hcx : IsLocalRing.closedPoint R ∉ (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv t) :=
    fun hx => by
      rw [basicOpen_eq_of_affine] at hx
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hx ht
  set D := (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv t)
  have hD : IsWeakAffineFormalOpen (schemeToLTRSObj (Spec R)) D :=
    ((isAffineOpen_top (Spec R)).basicOpen _).isWeakAffineFormalOpen
  have : DiscreteTopology ((schemeToLTRSObj (Spec R)).presheaf.obj (op D)).α :=
    isPseudoDiscrete_pseudoDiscrete (Spec R).presheaf D hD.isCompact
  have h1 := (hI D hD).2 1 (by
    change (1 : Γ(Spec R, D)) ∈ (Spec R).germVanishingAtIdeal _ D
    rw [Scheme.germVanishingAtIdeal_eq_top hcx]
    exact Submodule.mem_top)
  have h10 : (1 : ((schemeToLTRSObj (Spec R)).presheaf.obj (op D)).α) = 0 := by
    simpa only [IsTopologicallyNilpotent, one_pow, tendsto_const_nhds_iff] using h1
  have h01 : (0 : Γ(Spec R, D)) = 1 := h10.symm
  have := subsingleton_of_zero_eq_one h01
  exact map_basicOpen_ne_zero htε (Subsingleton.elim _ _)

/-- **Stacks 0AIV is false as printed: the weak ideal of definition condition cannot be checked on
the members of an affine open covering.** There is a McQuillan formal scheme `X` whose whole space
is a weak affine formal open, with an ideal sheaf `ℐ` such that `ℐ(X)` is a weak ideal of
definition, while `ℐ` is not a weak ideal of definition over every weak affine formal open. The
witness is the spectrum of the dual numbers `ℤ₂[ε]` over the `2`-adic integers, pseudo-discretised,
with the ideal sheaf of sections vanishing at the closed point; here `t = 2` lies in the maximal
ideal and `2ⁿ ε ≠ 0` for every `n`. -/
@[stacks 0AIV "the statement as printed is false: checking the weak ideal-of-definition \
condition on the members of an affine open covering does not suffice, already for Spec of the \
dual numbers over the 2-adic integers covered by itself, with the ideal sheaf of sections \
vanishing at the closed point; the corrected form is \
IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme"]
theorem exists_not_isWeakIdealOfDefinitionOn_of_cover :
    ∃ (X : LTRS.{0}) (_ : IsMcQuillanFormalScheme X) (I : IdealSheaf X),
      IsWeakAffineFormalOpen X ⊤ ∧ TopologicalRing.IsWeakIdealOfDefinition (I.ideal ⊤) ∧
        ¬ I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X) := by
  let R : CommRingCat.{0} := CommRingCat.of (DualNumber ℤ_[2])
  have : IsLocalRing R := DualNumber.isLocalRing ℤ_[2]
  let t : R := TrivSqZeroExt.inl ((2 : ℕ) : ℤ_[2])
  let ε : R := DualNumber.eps
  have ht : t ∈ IsLocalRing.maximalIdeal R := fun hu =>
    PadicInt.p_nonunit (p := 2) (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hu)
  have htε (n : ℕ) : t ^ n * ε ≠ 0 := by
    intro h
    have h' := congrArg TrivSqZeroExt.snd h
    change ((TrivSqZeroExt.inl ((2 : ℕ) : ℤ_[2]) : DualNumber ℤ_[2]) ^ n *
      DualNumber.eps).snd = (0 : DualNumber ℤ_[2]).snd at h'
    rw [TrivSqZeroExt.inl_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, DualNumber.snd_eps,
      DualNumber.fst_eps, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, mul_one,
      TrivSqZeroExt.snd_zero] at h'
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr two_ne_zero) h'
  exact ⟨schemeToLTRSObj (Spec R), isMcQuillanFormalScheme_schemeToLTRSObj _,
    germVanishingAt (Spec R) (IsLocalRing.closedPoint R), isWeakAffineFormalOpen_top_Spec R,
    isWeakIdealOfDefinition_germVanishingAt_closedPoint_ideal_top R,
    not_isWeakIdealOfDefinitionOn_germVanishingAt_closedPoint ht htε⟩

end LocallyTopologicallyRingedSpace.IdealSheaf

namespace LocallyTopologicallyRingedSpace

open IdealSheaf

/-- **Stacks 0AIV, the locality of the fundamental-system condition, is false as printed.** It is
not true that a family of ideal sheaves on a formal scheme in the sense of McQuillan is a
fundamental system of weak ideals of definition as soon as, over the members of an affine open
covering, its members are weak ideals of definition whose ideals of sections form a
neighbourhood basis of zero, even for a nonempty family directed by inclusion. The witness is
the one-member family `{ℐ}` of `IdealSheaf.exists_not_isWeakIdealOfDefinitionOn_of_cover`, on
the pseudo-discretised spectrum of the dual numbers `ℤ₂[ε]` covered by itself: `ℐ(X) = 0` is a
weak ideal of definition and a neighbourhood of zero of the discrete ring `𝒪_X(X)`, but `ℐ` is
not a weak ideal of definition over the affine open `D(2)`.

The corrected statement checks the condition on the affine formal opens contained in the members
of the covering:
`isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`. -/
@[stacks 0AIV "the statement as printed is false: checking the fundamental-system condition on \
the members of an affine open covering does not suffice, already for a one-member family on Spec \
of the dual numbers over the 2-adic integers covered by itself, with the ideal sheaf of sections \
vanishing at the closed point; the corrected form is \
isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme"]
theorem not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover :
    ¬ ∀ (X : LTRS.{0}), IsMcQuillanFormalScheme X → ∀ (𝒮 : Set (IdealSheaf X))
      (𝒰 : Set (Opens X)), 𝒮.Nonempty →
      (∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
        K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W) →
      (∀ V ∈ 𝒰, IsWeakAffineFormalOpen X V) → sSup 𝒰 = ⊤ →
      (∀ I ∈ 𝒮, ∀ V ∈ 𝒰, TopologicalRing.IsWeakIdealOfDefinition (I.ideal V)) →
      (∀ V ∈ 𝒰, (nhds (0 : (X.presheaf.obj (op V)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal V : Set (X.presheaf.obj (op V)).α)) →
      IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen X) := by
  intro h
  let R : CommRingCat.{0} := CommRingCat.of (DualNumber ℤ_[2])
  have : IsLocalRing R := DualNumber.isLocalRing ℤ_[2]
  let t : R := TrivSqZeroExt.inl ((2 : ℕ) : ℤ_[2])
  let ε : R := DualNumber.eps
  have ht : t ∈ IsLocalRing.maximalIdeal R := fun hu =>
    PadicInt.p_nonunit (p := 2) (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hu)
  have htε (n : ℕ) : t ^ n * ε ≠ 0 := by
    intro h
    have h' := congrArg TrivSqZeroExt.snd h
    change ((TrivSqZeroExt.inl ((2 : ℕ) : ℤ_[2]) : DualNumber ℤ_[2]) ^ n *
      DualNumber.eps).snd = (0 : DualNumber ℤ_[2]).snd at h'
    rw [TrivSqZeroExt.inl_pow, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, DualNumber.snd_eps,
      DualNumber.fst_eps, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, mul_one,
      TrivSqZeroExt.snd_zero] at h'
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr two_ne_zero) h'
  let 𝒥 := germVanishingAt (Spec R) (IsLocalRing.closedPoint R)
  have : DiscreteTopology ((schemeToLTRSObj (Spec R)).presheaf.obj (op ⊤)).α :=
    isPseudoDiscrete_pseudoDiscrete (Spec R).presheaf ⊤
      (isWeakAffineFormalOpen_top_Spec R).isCompact
  have hbot : 𝒥.ideal ⊤ = ⊥ := germVanishingAt_closedPoint_ideal_top R
  have hfund := h (schemeToLTRSObj (Spec R)) (isMcQuillanFormalScheme_schemeToLTRSObj _) {𝒥} {⊤}
    ⟨𝒥, rfl⟩ (by rintro _ rfl _ rfl; exact ⟨𝒥, rfl, fun _ => ⟨le_rfl, le_rfl⟩⟩)
    (by rintro V rfl; exact isWeakAffineFormalOpen_top_Spec R) sSup_singleton
    (by
      rintro _ rfl V rfl
      exact isWeakIdealOfDefinition_germVanishingAt_closedPoint_ideal_top R)
    (by
      rintro V rfl
      refine ⟨fun s => ⟨fun hs => ⟨𝒥, rfl, ?_⟩, fun ⟨J, _, hJs⟩ => ?_⟩⟩
      · rw [hbot, Submodule.bot_coe, Set.singleton_subset_iff]
        exact mem_of_mem_nhds hs
      · exact Filter.mem_of_superset ((isOpen_discrete _).mem_nhds (Submodule.zero_mem _)) hJs)
  exact not_isWeakIdealOfDefinitionOn_germVanishingAt_closedPoint ht htε (hfund.1 𝒥 rfl)

open TruncatedPolynomialCounterexample in
/-- **Stacks 0AIV, the locality of the fundamental-system condition, is false as printed, also when
only the neighbourhood-basis half is checked on the covering.** It is not true that a family of
weak ideals of definition (over every affine formal open) on a formal scheme in the sense of
McQuillan is a fundamental system as soon as its ideals of sections form a neighbourhood basis of
zero over the members of an affine open covering, even for a nonempty family directed by
inclusion. The witness is that of
`not_forall_isFundamentalSystemOfIdealsOfDefinitionOn_of_hasBasis_cover` for Stacks 0AIW: on the
pseudo-discretisation of `Spec (ℤ[X₀, X₁, …] / (X_k ^ (k + 1)))`, a McQuillan formal scheme, the
sections whose germs are multiples of the germ of `X₁`, vanishing outside `D(n!)`, form an ideal
of definition, hence a weak one, over every quasi-compact open; it is zero over the whole space,
which is affine and has discrete sections, but its sections over `D(n!)`, which are discrete,
contain `X₁ ≠ 0`.

The corrected statement checks the condition on the affine formal opens contained in the members
of the covering:
`isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`. -/
@[stacks 0AIV "the statement as printed is false, also on the reading where the members are \
weak ideals of definition everywhere and the neighbourhood-basis property alone is checked on \
the members of an affine open covering: already for one weak ideal of definition on the \
pseudo-discretised Spec(Z[X_0, X_1, ...]/(X_k^(k+1))) covered by itself; the corrected form is \
isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme"]
theorem not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_hasBasis_cover :
    ¬ ∀ (X : LTRS.{0}), IsMcQuillanFormalScheme X → ∀ (𝒮 : Set (IdealSheaf X))
      (𝒰 : Set (Opens X)), 𝒮.Nonempty →
      (∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
        K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W) →
      (∀ V ∈ 𝒰, IsWeakAffineFormalOpen X V) → sSup 𝒰 = ⊤ →
      (∀ I ∈ 𝒮, I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X)) →
      (∀ V ∈ 𝒰, (nhds (0 : (X.presheaf.obj (op V)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal V : Set (X.presheaf.obj (op V)).α)) →
      IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen X) := by
  intro h
  obtain ⟨n, z, hz⟩ := exists_not_mem_basicOpen_factorial
  have hreg := fun (a : Γ(scheme, ⊤)) (ha : ¬ IsNilpotent a) =>
    mem_nonZeroDivisors_of_not_isNilpotent_global ha
  let P : ∀ z : scheme, Ideal (scheme.presheaf.stalk z) :=
    fun z => Ideal.span {scheme.presheaf.Γgerm z squareZeroSection}
  let 𝒥 := IdealSheaf.germsVanishingOff scheme P (n.factorial : Γ(scheme, ⊤))
  have hfund := h (schemeToLTRSObj scheme) (isMcQuillanFormalScheme_schemeToLTRSObj scheme) {𝒥}
    {⊤} ⟨𝒥, rfl⟩ (by rintro _ rfl _ rfl; exact ⟨𝒥, rfl, fun _ => ⟨le_rfl, le_rfl⟩⟩)
    (by rintro V rfl; exact (isAffineOpen_top scheme).isWeakAffineFormalOpen)
    sSup_singleton
    (by
      rintro _ rfl W hW
      exact TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition
        (isIdealOfDefinition_germsVanishingOff_span scheme squareZeroSection_sq _ hW.isCompact))
    (by
      rintro V rfl
      have : DiscreteTopology ((schemeToLTRSObj scheme).presheaf.obj (op ⊤)).α :=
        discreteTopology_schemeToLTRSObj scheme (W := ⊤) isCompact_univ
      have hI : 𝒥.ideal ⊤ = ⊥ :=
        germsVanishingOffIdeal_eq_bot scheme hreg P (n.factorial : Γ(scheme, ⊤)) (W := ⊤) trivial hz
      refine ⟨fun t => ⟨fun ht => ⟨𝒥, rfl, ?_⟩, fun ⟨J, _, hJt⟩ => ?_⟩⟩
      · rw [hI, Submodule.bot_coe, Set.singleton_subset_iff]
        exact mem_of_mem_nhds ht
      · exact Filter.mem_of_superset ((isOpen_discrete _).mem_nhds (Submodule.zero_mem _)) hJt)
  exact not_hasBasis_germsVanishingOff_span scheme squareZeroSection_ne_zero
    (hreg _ (not_isNilpotent_factorial_global n))
    (hfund.2 _ ((isAffineOpen_top _).basicOpen _).isWeakAffineFormalOpen)

end LocallyTopologicallyRingedSpace

end AlgebraicGeometry

end
