module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmoothLifting
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism

/-!
# The divided power relations vanish when the divided power ideal comes from the base

Let `(T, J, δ)` be a divided power scheme over a scheme `Y` whose divided power ideal is, over
every affine open `U ⊆ T`, the image of a single ideal `I ⊆ Γ(Y, ⊤)` of the base under the map on
sections `Γ(Y, ⊤) ⟶ Γ(T, U)`, and suppose that map carries a divided power structure `γ` on `I`
to `δ`.  Then every divided power relation `d (δ_{n+1} x) - δ_n x · d x` of
`Crystalline.dpRelationSection` vanishes in `Ω_{T/Y}`: it suffices to check this at the
generators `x = φ(a)` with `a ∈ I`, and there both `d (φ a)` and `d (δ_{n+1} (φ a)) = d (φ (γ_{n+1}
a))` are zero, because the universal relative derivation kills every section pulled back from the
base.  The passage from the generators to the whole of `J` is
`Crystalline.dpRelation_mem_of_mem_span`, and the passage from affine opens to arbitrary opens is
separatedness of `Ω_{T/Y}`.

Consequently the subsheaf of divided power relations is the zero subsheaf, so the comparison map
`Crystalline.toDpDifferentials : Ω_{T/Y} ⟶ Ω_{T/Y,δ}` of [Stacks, Tag 07IY] is an isomorphism:
it factors as the quotient map by the relations followed by the isomorphism
`Crystalline.dpDifferentialsIsoQuotient`, and the quotient map by a zero subsheaf is an
isomorphism.

The hypotheses are met by the smooth lifting of [Stacks, Tag 07MW] part (1): there `I` is the
divided power ideal of the affine base `S`, `φ` is `toBase.appLE ⊤ U`, the ideal identification is
`Crystalline.GlobalCrystallineSituation.ideal_map_appTop_restrict` and the divided power
compatibility is `Crystalline.GlobalCrystallineSituation.isDPMorphism_appLE`.  So on a smooth
lifting the two spellings of `Ω` agree.

## Main results

* `Crystalline.dpRelation_eq_zero_of_isDPMorphism` — the ring-theoretic statement: the divided
  power relations of a Leibniz map vanish when the divided power ideal is the image of a divided
  power morphism whose image the map kills.
* `Crystalline.universalRelativeDerivation_d_appLE_top` — the universal relative derivation kills
  the restriction to any open of a global section pulled back from the base.
* `Crystalline.dpRelationSection_eq_zero` — every divided power relation vanishes.
* `Crystalline.dpRelationSpan_eq_bot` and `Crystalline.dpRelationSubmodule_obj_eq_bot` — the
  relations span nothing, and the subsheaf of relations has no nonzero section.
* `Crystalline.dpRelationSubmodule_eq_bot` — the subsheaf of divided power relations is zero.
* `Crystalline.isIso_toDpDifferentials` — the comparison map `Ω_{T/Y} ⟶ Ω_{T/Y,δ}` is an
  isomorphism.
* `Crystalline.GlobalCrystallineSituation.smoothLifting_dpRelationSubmodule_eq_bot` and
  `Crystalline.GlobalCrystallineSituation.isIso_smoothLifting_toDpDifferentials` — the two
  statements for the smooth lifting of a closed fibre.

## Scope

Nothing here carries the tag of [Stacks, Tag 07MW] part (2).  That assertion is about the
canonical integrable connection on the restriction of a crystal to the smooth lifting; the
identification of the two sheaves of differentials proved here is one of its inputs, not the
statement itself.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### Sections pulled back from the base -/

/-- Sections over an open, pulled back from global sections of the target, factor as the map on
global sections followed by restriction. -/
private theorem appLE_top_hom' {X Z : Scheme.{u}} (g : X ⟶ Z) (U : X.Opens) :
    (g.appLE ⊤ U (le_preimage_top g U)).hom =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp g.appTop.hom :=
  rfl

/-- **The projection onto the quotient by a subsheaf with no nonzero sections is an
isomorphism.**  The inclusion of such a subsheaf is the zero morphism, so this is
`CategoryTheory.Limits.cokernel.π_of_zero`.  The statement is at the `SheafOfModules` spelling
rather than at `AlgebraicGeometry.Scheme.Modules`, which is a definition and so hides the zero
morphisms of the category from instance search. -/
private lemma isIso_cokernelπ_ι_of_obj_eq_bot {X : Scheme.{u}}
    {M : _root_.SheafOfModules.{u} X.ringCatSheaf} (N : M.Submodule)
    (h : ∀ W, N.obj W = ⊥) : IsIso (cokernel.π N.ι) := by
  refine cokernel.π_of_zero ?_
  ext W s
  have hs : s.1 ∈ N.obj W := s.2
  show s.1 = 0
  exact (Submodule.mem_bot _).mp ((h W).le hs)

/-- **The universal relative derivation kills every global section of the base**, restricted to
any open of the source: such a section lies in the image of the structural map, and the
derivation is natural. -/
theorem universalRelativeDerivation_d_appLE_top (W : T.scheme.Opens) (a : Γ(Y, ⊤)) :
    (Scheme.Hom.universalRelativeDerivation f).d
        ((f.appLE ⊤ W (le_preimage_top f W)).hom a) = 0 := by
  have h0 : (Scheme.Hom.universalRelativeDerivation f).d ((f.app ⊤).hom a) = 0 :=
    SheafOfModules.d_comorphism_eq_zero f (Scheme.Hom.universalRelativeDerivation f) ⊤ a
  have hmap := (Scheme.Hom.universalRelativeDerivation f).d_map
    (homOfLE (le_preimage_top f W)).op ((f.app ⊤).hom a)
  rw [h0, map_zero] at hmap
  exact hmap

/-! ### Vanishing of the relations, as a statement about rings -/

/-- **The divided power relations of a Leibniz map vanish when the divided power ideal is the
image of a divided power morphism whose image the map kills.**  At a generator `ψ a` of `J` the
relation is `D (δ_{n+1} (ψ a)) - δ_n (ψ a) · D (ψ a) = D (ψ (γ_{n+1} a)) - δ_n (ψ a) · 0`, and
both terms vanish; the passage from the generators to the whole of `J` is
`Crystalline.dpRelation_mem_of_mem_span`. -/
theorem dpRelation_eq_zero_of_isDPMorphism {A B M : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module B M] {I : Ideal A} {J : Ideal B} {γ : DividedPowers I}
    {hJ : DividedPowers J} {ψ : A →+* B} (hψ : DividedPowers.IsDPMorphism γ hJ ψ)
    (hgen : Ideal.map ψ I = J) {D : B →+ M}
    (hmul : ∀ a b : B, D (a * b) = a • D b + b • D a) (hker : ∀ a : A, D (ψ a) = 0)
    {x : B} (hx : x ∈ J) (n : ℕ) : dpRelation hJ D x n = 0 := by
  have hbase : ∀ s ∈ ψ '' (I : Set A), ∀ m : ℕ,
      dpRelation hJ D s m ∈ (⊥ : Submodule B M) := by
    rintro _ ⟨a, ha, rfl⟩ m
    rw [Submodule.mem_bot, dpRelation_eq, hψ.dpow_comp a ha, hker, hker, smul_zero, sub_zero]
  have hSJ : ψ '' (I : Set A) ⊆ (J : Set B) := by
    rw [← hgen]
    rintro _ ⟨a, ha, rfl⟩
    exact Ideal.mem_map_of_mem _ ha
  have hxspan : x ∈ Submodule.span B (ψ '' (I : Set A)) := by
    rw [show Submodule.span B (ψ '' (I : Set A)) = J from hgen]
    exact hx
  exact (Submodule.mem_bot _).mp (dpRelation_mem_of_mem_span hmul ⊥ hSJ hbase hxspan n)

/-! ### Vanishing of the relations -/

/-- A section of `Ω_{T/Y}` over `W` that restricts to zero on an open neighbourhood of every point
of `W` is zero. -/
private theorem eq_zero_of_locally_eq_zero (W : T.scheme.Opens)
    (s : (Scheme.Hom.relativeDifferentials f).val.obj (op W))
    (h : ∀ p ∈ W, ∃ (V : T.scheme.Opens) (hle : V ≤ W), p ∈ V ∧
      (Scheme.Hom.relativeDifferentials f).val.map (homOfLE hle).op s = 0) : s = 0 := by
  refine (Scheme.Hom.relativeDifferentials f).isSheaf.section_ext (U := op W) fun p hp ↦ ?_
  obtain ⟨V, hle, hpV, hs⟩ := h p hp
  exact ⟨V, hle, hpV, hs.trans (map_zero _).symm⟩

section Generated

variable {I : Ideal Γ(Y, ⊤)} (γ : DividedPowers I)
  (hgen : ∀ U : T.scheme.affineOpens,
    Ideal.map (f.appLE ⊤ U.1 (le_preimage_top f U.1)).hom I =
      sectionIdeal T.scheme.sheaf T.ideal (op U.1))
  (hdp : ∀ U : T.scheme.affineOpens,
    DividedPowers.IsDPMorphism γ (T.dividedPowers.dividedPowers (op U.1))
      (f.appLE ⊤ U.1 (le_preimage_top f U.1)).hom)

include hgen hdp

/-- **Over an affine open the divided power relations vanish.**  The ideal of sections there is
generated by the image of `I`, and at a generator `φ a` both the derivative of `φ a` and the
derivative of `δ_{n+1} (φ a) = φ (γ_{n+1} a)` vanish, because they are pulled back from the base;
the passage from the generators to the whole ideal is
`Crystalline.dpRelation_mem_of_mem_span`. -/
theorem dpRelationSection_eq_zero_of_isAffineOpen (U : T.scheme.affineOpens)
    (x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op U.1))) (n : ℕ) :
    dpRelationSection T Y f U.1 x n = 0 :=
  dpRelation_eq_zero_of_isDPMorphism (hdp U) (hgen U)
    (fun a b ↦ (Scheme.Hom.universalRelativeDerivation f).d_mul a b)
    (universalRelativeDerivation_d_appLE_top T Y f U.1) x.2 n

/-- **The divided power relations vanish over every open.**  Each affine open of the source is
covered by the affine case, the relations are stable under restriction, and `Ω_{T/Y}` is a
sheaf. -/
theorem dpRelationSection_eq_zero (W : T.scheme.Opens)
    (x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W))) (n : ℕ) :
    dpRelationSection T Y f W x n = 0 := by
  refine eq_zero_of_locally_eq_zero T Y f W _ fun p hp ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, hUW⟩ :=
    T.scheme.isBasis_affineOpens.exists_subset_of_mem_open hp W.2
  have hUW' : U ≤ W := hUW
  refine ⟨U, hUW', hpU, ?_⟩
  rw [map_dpRelationSection T Y f (homOfLE hUW').op x n]
  exact dpRelationSection_eq_zero_of_isAffineOpen T Y f γ hgen hdp ⟨U, hU⟩ _ n

/-- **The span of the divided power relations over an open is zero**, every relation being
zero. -/
theorem dpRelationSpan_eq_bot (W : T.scheme.Opens) : dpRelationSpan T Y f W = ⊥ :=
  Submodule.span_eq_bot.mpr <| by
    rintro _ ⟨⟨x, m⟩, rfl⟩
    exact dpRelationSection_eq_zero T Y f γ hgen hdp W x m

/-- **The sections of the subsheaf of divided power relations over an open are zero**: such a
section is locally a combination of relations, every combination of relations is zero, and
`Ω_{T/Y}` is a sheaf. -/
theorem dpRelationSubmodule_obj_eq_bot (W : T.scheme.Opens) :
    (dpRelationSubmodule T Y f).obj (op W) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun s hs ↦ ?_
  refine eq_zero_of_locally_eq_zero T Y f W _ fun p hp ↦ ?_
  obtain ⟨V, hle, hpV, hmem⟩ := hs p hp
  rw [dpRelationSpan_eq_bot T Y f γ hgen hdp V] at hmem
  exact ⟨V, hle, hpV, (Submodule.mem_bot _).mp hmem⟩

/-- **The subsheaf of divided power relations is the zero subsheaf.** -/
theorem dpRelationSubmodule_eq_bot : dpRelationSubmodule T Y f = ⊥ :=
  le_bot_iff.mp <| SheafOfModules.Submodule.le_iff.mpr <|
    PresheafOfModules.Submodule.le_iff.mpr fun X ↦ by
      rw [dpRelationSubmodule_obj_eq_bot T Y f γ hgen hdp X.unop]
      exact bot_le

/-- **The comparison map `Ω_{T/Y} ⟶ Ω_{T/Y,δ}` is an isomorphism.**  It factors as the quotient
map by the subsheaf of divided power relations followed by the isomorphism of
`Crystalline.dpDifferentialsIsoQuotient`, and the quotient map is an isomorphism because the
subsheaf is zero. -/
theorem isIso_toDpDifferentials : IsIso (toDpDifferentials T Y f) := by
  have hmk : IsIso (dpQuotientMk T Y f) :=
    isIso_cokernelπ_ι_of_obj_eq_bot (dpRelationSubmodule T Y f)
      fun W ↦ dpRelationSubmodule_obj_eq_bot T Y f γ hgen hdp W.unop
  have hto : IsIso (dpQuotientToDifferentials T Y f) :=
    (dpDifferentialsIsoQuotient T Y f).isIso_inv
  rw [← dpQuotientMk_comp_dpQuotientToDifferentials T Y f]
  infer_instance

end Generated

/-! ### The smooth lifting of a closed fibre -/

namespace GlobalCrystallineSituation

variable (base : GlobalCrystallineSituation.{u}) [IsAffine base.S.scheme]
  (prime_nilpotent : IsNilpotent (base.p : Γ(base.S.scheme, ⊤)))
  (Y : Scheme.{u}) (toBase : Y ⟶ base.S.scheme) [Smooth toBase] (toY : base.X ⟶ Y)
  (cartesian : IsPullback toY base.toClosedFiber toBase
    (DividedPowerScheme.closedFiberι base.S))

include prime_nilpotent cartesian

/-- **On a smooth lifting the divided power ideal is generated, over every affine open, by the
divided power ideal of the base**, at the spelling `Scheme.Hom.appLE` of the map on sections.
This is `Crystalline.GlobalCrystallineSituation.ideal_map_appTop_restrict`. -/
theorem smoothLifting_ideal_map_appLE_top (U : Y.affineOpens) :
    Ideal.map (toBase.appLE ⊤ U.1 (le_preimage_top toBase U.1)).hom
        (base.S.ideal.obj (op (⊤ : base.S.scheme.Opens))) =
      sectionIdeal
        (smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian).scheme.sheaf
        (smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian).ideal
        (op U.1) := by
  rw [appLE_top_hom' toBase U.1]
  exact ideal_map_appTop_restrict base prime_nilpotent Y toBase toY cartesian U

/-- **On a smooth lifting the map on sections from the global sections of the base is a divided
power morphism**, at the spelling `Scheme.Hom.appLE`.  This is
`Crystalline.GlobalCrystallineSituation.isDPMorphism_appLE` at the affine open `⊤` of the base. -/
theorem smoothLifting_isDPMorphism_appLE_top (U : Y.affineOpens) :
    DividedPowers.IsDPMorphism (base.S.dividedPowers.dividedPowers (op ⊤))
      ((smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY
        cartesian).dividedPowers.dividedPowers (op U.1))
      (toBase.appLE ⊤ U.1 (le_preimage_top toBase U.1)).hom :=
  isDPMorphism_appLE base prime_nilpotent Y toBase toY cartesian
    ⟨⊤, isAffineOpen_top base.S.scheme⟩ U (le_preimage_top toBase U.1)

/-- **On a smooth lifting the subsheaf of divided power relations is zero.**  The divided power
ideal is generated over every affine open by the divided power ideal of the affine base, and the
map on sections carries `γ` to its extension. -/
theorem smoothLifting_dpRelationSubmodule_eq_bot :
    dpRelationSubmodule
        (smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian)
        base.S.scheme toBase = ⊥ :=
  dpRelationSubmodule_eq_bot _ _ _ (base.S.dividedPowers.dividedPowers (op ⊤))
    (smoothLifting_ideal_map_appLE_top base prime_nilpotent Y toBase toY cartesian)
    (smoothLifting_isDPMorphism_appLE_top base prime_nilpotent Y toBase toY cartesian)

/-- **On a smooth lifting the two spellings of `Ω` agree**: the comparison map
`Ω_{Y/S} ⟶ Ω_{Y/S,δ}` of [Stacks, Tag 07IY] is an isomorphism, the divided power relations
all vanishing. -/
theorem isIso_smoothLifting_toDpDifferentials :
    IsIso (toDpDifferentials
      (smoothLiftingDividedPowerScheme base prime_nilpotent Y toBase toY cartesian)
      base.S.scheme toBase) :=
  isIso_toDpDifferentials _ _ _ (base.S.dividedPowers.dividedPowers (op ⊤))
    (smoothLifting_ideal_map_appLE_top base prime_nilpotent Y toBase toY cartesian)
    (smoothLifting_isDPMorphism_appLE_top base prime_nilpotent Y toBase toY cartesian)

end GlobalCrystallineSituation

end Crystalline

end
