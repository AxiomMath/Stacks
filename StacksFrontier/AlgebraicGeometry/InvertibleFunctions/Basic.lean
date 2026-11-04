module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.NormalExtension.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Invertible functions on an open subscheme of a normal scheme

Stacks section 04L3 studies, for a variety `X` over a field `k`, the group `𝒪^*(X)/k^*` of
invertible functions modulo the constants, and proves it finitely generated when `X` is a normal
open subscheme of a proper variety over an algebraically closed field.  This file collects the
three steps of that argument which do not depend on the base field.

The first is group-theoretic and is the last step of the source's proof: a group whose quotient by
a subgroup embeds in a finitely generated commutative group has that quotient finitely generated.
The second says the index set of the source's family of valuations is finite: on a Noetherian
irreducible sober space there are only finitely many points of codimension one outside a given
nonempty open, because such a point must be a generic point of an irreducible component of the
complement.  The third is the computation of the kernel of that family: an invertible function on a
nonempty open `U` of a normal integral locally Noetherian scheme whose order of vanishing is zero
at every codimension-one point outside `U` is the restriction of an invertible global function.
This is the source's claim, and it uses the extension result of
`StacksFrontier.AlgebraicGeometry.NormalExtension.Basic`.  The three are then assembled into
Tag 04L4 for a normal scheme whose invertible global functions are constants.

What is *not* here is the identification of the invertible global functions with `k^*`, which for a
proper variety over an algebraically closed field is Tag 04L2, and the reduction of a proper
variety to a normal one, which is Tag 0BXR.

## Main results

* `Group.fg_of_injective`: a commutative group embedding in a finitely generated commutative group
  is finitely generated.
* `Group.fg_quotient_of_ker_eq`: the quotient by the kernel of a homomorphism into a finitely
  generated commutative group is finitely generated.
* `AlgebraicGeometry.finite_coheight_eq_one_of_notMem`: finiteness of the set of codimension-one
  points outside a nonempty open.
* `AlgebraicGeometry.exists_units_germ_top_eq_of_forall_ord_eq_zero`: an invertible function with
  no zero or pole outside its domain of definition extends to an invertible global function.
* `AlgebraicGeometry.fg_units_quotient_of_constant_globalUnits`: the three steps assembled.  On a
  normal integral Noetherian scheme whose invertible global functions are all constants, the
  invertible functions on a nonempty open modulo the constants form a finitely generated group.
  This is Tag 04L4 with its two geometric inputs, Tags 0BXR and 04L2, taken as hypotheses.

## References

* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite Order

universe u

/-- A commutative group which embeds in a finitely generated commutative group is itself finitely
generated: a finitely generated commutative group is a Noetherian `ℤ`-module. -/
theorem Group.fg_of_injective {G A : Type*} [CommGroup G] [CommGroup A] [Group.FG A]
    {ψ : G →* A} (hψ : Function.Injective ψ) : Group.FG G := by
  have hA : Module.Finite ℤ (Additive A) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive A))
  have hN : IsNoetherian ℤ (Additive A) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hlin : Function.Injective (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive ψ)) := hψ
  exact (GroupFG.iff_add_fg (G := G)).mpr
    (Module.Finite.iff_addGroup_fg.mp (Module.Finite.of_injective _ hlin))

/-- If a homomorphism from a commutative group to a finitely generated commutative group has kernel
`H`, then the quotient by `H` is finitely generated. -/
theorem Group.fg_quotient_of_ker_eq {G A : Type*} [CommGroup G] [CommGroup A] [Group.FG A]
    (ψ : G →* A) {H : Subgroup G} (hH : ψ.ker = H) : Group.FG (G ⧸ H) := by
  subst hH
  exact Group.fg_of_injective (ψ := QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ)

namespace AlgebraicGeometry

/-- On a Noetherian irreducible scheme only finitely many points outside a given nonempty open have
codimension one.  Such a point has no proper generalization inside the complement, since a proper
one would sit strictly between it and the generic point of the whole space. -/
theorem finite_coheight_eq_one_of_notMem {X : Scheme.{u}} [IrreducibleSpace X]
    [NoetherianSpace X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    {z : X | z ∉ U ∧ coheight z = 1}.Finite := by
  classical
  set Z : Set X := (U : Set X)ᶜ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  have : QuasiSober ↥Z := hZc.isClosedEmbedding_subtypeVal.quasiSober
  have hfinZ : (genericPoints ↥Z).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  refine Set.Finite.subset (hfinZ.image Subtype.val) ?_
  rintro z ⟨hzU, hzc⟩
  refine ⟨⟨z, hzU⟩, ?_, rfl⟩
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun y hy => ?_
  by_contra hne
  have hspec : (y : X) ⤳ z := hy.map continuous_subtype_val
  have hzy : z < (y : X) := by
    refine lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hspec, fun hge => ?_⟩
    exact hne (Subtype.ext (hspec.antisymm (Scheme.le_iff_specializes.mp hge)).eq)
  have hylt : (y : X) < genericPoint X := by
    refine lt_iff_le_not_ge.mpr
      ⟨Scheme.le_iff_specializes.mpr (genericPoint_specializes _), fun hge => ?_⟩
    exact y.2 (((genericPoint_specializes (y : X)).antisymm
      (Scheme.le_iff_specializes.mp hge)).eq ▸ hgen)
  have h₁ : 1 ≤ coheight (y : X) := le_add_self.trans (Order.coheight_add_one_le hylt)
  have h₂ : coheight (y : X) + 1 ≤ 1 := hzc ▸ Order.coheight_add_one_le hzy
  have h₃ : (1 + 1 : ℕ∞) ≤ 1 := le_trans (by gcongr) h₂
  exact absurd h₃ (by decide)

/-- The germ at the generic point of a unit section over a nonempty open is nonzero. -/
private theorem germ_genericPoint_unit_ne_zero {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hgen : genericPoint X ∈ U) (a : Γ(X, U)ˣ) :
    X.presheaf.germ U (genericPoint X) hgen (a : Γ(X, U)) ≠ 0 := by
  have : Nonempty U := ⟨⟨_, hgen⟩⟩
  simp [map_ne_zero_iff, germ_injective_of_isIntegral X (U := U) (genericPoint X) hgen]

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The claim of Stacks Tag 04L4.** Let `X` be a normal integral locally Noetherian scheme and
let `U` be a nonempty open.  An invertible section over `U` whose order of vanishing is zero at
every point of codimension one outside `U` is the restriction of an invertible global section.

Normality is the hypothesis that the ring of sections on every affine open is integrally closed,
and the nonemptiness of `U` is spelled as containing the generic point, which for an irreducible
space is the same thing. -/
theorem exists_units_germ_top_eq_of_forall_ord_eq_zero
    (hnorm : ∀ U : X.affineOpens, IsIntegrallyClosed Γ(X, U.1))
    {U : X.Opens} (hgen : genericPoint X ∈ U) (u : Γ(X, U)ˣ)
    (h : ∀ z : X, z ∉ U → coheight z = 1 →
      X.ord (X.presheaf.germ U (genericPoint X) hgen (u : Γ(X, U))) z = 0) :
    ∃ s : Γ(X, ⊤)ˣ, X.presheaf.germ ⊤ (genericPoint X) trivial (s : Γ(X, ⊤))
      = X.presheaf.germ U (genericPoint X) hgen (u : Γ(X, U)) := by
  have hne : Nonempty U := ⟨⟨_, hgen⟩⟩
  set gu : X.functionField := X.presheaf.germ U (genericPoint X) hgen (u : Γ(X, U)) with hgu
  set gv : X.functionField :=
    X.presheaf.germ U (genericPoint X) hgen ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) with hgv
  have hprod : gu * gv = 1 := by rw [hgu, hgv, ← map_mul, u.mul_inv, map_one]
  have hone : ∀ z : X, X.ord (1 : X.functionField) z = 0 := by
    intro z
    by_cases hz : coheight z = 1
    · rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz, map_one]
      simp
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  have hu0 : gu ≠ 0 := germ_genericPoint_unit_ne_zero hgen u
  have hv0 : gv ≠ 0 := germ_genericPoint_unit_ne_zero hgen u⁻¹
  have hordu : ∀ z : X, coheight z = 1 → X.ord gu z = 0 := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Scheme.ord_of_isUnit u.isUnit hzU
    · exact h z hzU hz
  have hordv : ∀ z : X, coheight z = 1 → X.ord gv z = 0 := by
    intro z hz
    have hmul := Scheme.ord_mul (x := z) hu0 hv0
    rw [hprod, hone z, hordu z hz] at hmul
    omega
  obtain ⟨s, hs⟩ := exists_germ_top_eq_of_forall_zero_le_ord hnorm hu0
    fun z hz => (hordu z hz).ge
  obtain ⟨t, ht⟩ := exists_germ_top_eq_of_forall_zero_le_ord hnorm hv0
    fun z hz => (hordv z hz).ge
  have hst : s * t = 1 := by
    refine germ_injective_of_isIntegral X (U := (⊤ : X.Opens)) (genericPoint X) trivial ?_
    rw [map_mul, map_one, hs, ht, hprod]
  exact ⟨⟨s, t, hst, by rwa [mul_comm]⟩, hs⟩

/-- **Stacks Tag 04L4 for a normal scheme whose global units are constants.**  Let `X` be a normal
integral locally Noetherian scheme with Noetherian underlying space, let `k` be a field and let
`φ : k →+* Γ(X, ⊤)` be a ring map under which every invertible global function on `X` is the image
of a unit of `k`.  Then for every nonempty open `U` of `X` the group of invertible functions on `U`
modulo the constants is finitely generated.

This is the whole of Tag 04L4 except for its two geometric inputs: that a proper variety may be
replaced by a normal one (Tag 0BXR), and that the global functions on a proper variety over an
algebraically closed field are the constants (Tag 04L2).  With `X` the normalized proper variety
and `U` the given open subscheme, the hypothesis `hφ` is the latter and the conclusion is the
assertion of the tag.

The proof is the source's: the finitely many codimension-one points outside `U` carry a family of
valuations, the resulting homomorphism to a finite product of copies of `ℤ` has kernel exactly the
constants by `exists_units_germ_top_eq_of_forall_ord_eq_zero`, and a quotient embedding in a
finitely generated commutative group is finitely generated. -/
theorem fg_units_quotient_of_constant_globalUnits [NoetherianSpace X]
    (hnorm : ∀ V : X.affineOpens, IsIntegrallyClosed Γ(X, V.1))
    {k : Type u} [Field k] (φ : k →+* Γ(X, ⊤))
    (hφ : ∀ s : Γ(X, ⊤)ˣ, s ∈ (Units.map φ.toMonoidHom).range)
    {U : X.Opens} (hgen : genericPoint X ∈ U) :
    Group.FG (Γ(X, U)ˣ ⧸ (Units.map
      (((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)).toMonoidHom).range) := by
  classical
  have hne : Nonempty U := ⟨⟨_, hgen⟩⟩
  have hnt : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  set J : Set X := {z : X | z ∉ U ∧ coheight z = 1}
  have : Finite ↥J := finite_coheight_eq_one_of_notMem U ⟨genericPoint X, hgen⟩
  set γ : Γ(X, U) →+* X.functionField := (X.presheaf.germ U (genericPoint X) hgen).hom with hγ
  have hγ0 : ∀ a : Γ(X, U)ˣ, γ (a : Γ(X, U)) ≠ 0 := germ_genericPoint_unit_ne_zero hgen
  set v : Γ(X, U)ˣ →* (↥J → Multiplicative ℤ) :=
    MonoidHom.mk' (fun a j => Multiplicative.ofAdd (X.ord (γ (a : Γ(X, U))) j.1)) (by
      intro a b
      funext j
      have : γ ((a * b : Γ(X, U)ˣ) : Γ(X, U)) = γ (a : Γ(X, U)) * γ (b : Γ(X, U)) := by
        rw [Units.val_mul, map_mul]
      simp only [this, Pi.mul_apply]
      rw [Scheme.ord_mul (hγ0 a) (hγ0 b)]
      rfl) with hv
  refine Group.fg_quotient_of_ker_eq v ?_
  ext a
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro ha
    have hord : ∀ z : X, z ∉ U → coheight z = 1 → X.ord (γ (a : Γ(X, U))) z = 0 := by
      intro z hzU hzc
      have hj := congrFun ha ⟨z, hzU, hzc⟩
      simp only [hv, MonoidHom.mk'_apply, Pi.one_apply] at hj
      simpa using congrArg Multiplicative.toAdd hj
    obtain ⟨s, hs⟩ := exists_units_germ_top_eq_of_forall_ord_eq_zero hnorm hgen a hord
    obtain ⟨c, hc⟩ := hφ s
    refine ⟨c, Units.ext ?_⟩
    calc ((Units.map (((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)).toMonoidHom) c :
          Γ(X, U))
        = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ (c : k)) := rfl
      _ = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s : Γ(X, ⊤)) := by
            rw [show φ (c : k) = (s : Γ(X, ⊤)) from congrArg Units.val hc]
      _ = (a : Γ(X, U)) := germ_injective_of_isIntegral X (U := U) (genericPoint X) hgen
            (by rwa [X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) (genericPoint X) hgen])
  · rintro ⟨c, rfl⟩
    funext j
    obtain ⟨hjU, hjc⟩ := j.2
    have h2 : γ ((Units.map (((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp φ)
        ).toMonoidHom) c : Γ(X, U)) = X.presheaf.germ ⊤ (genericPoint X) trivial (φ (c : k)) := by
      show X.presheaf.germ U (genericPoint X) hgen
          (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ (c : k))) = _
      rw [X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) (genericPoint X) hgen]
    have h3 := Scheme.ord_of_isUnit (U := (⊤ : X.Opens))
      (⟨Units.map φ.toMonoidHom c, rfl⟩ : IsUnit (φ (c : k))) (x := j.1) trivial
    simp only [hv, MonoidHom.mk'_apply, h2]
    rw [show X.presheaf.germ ⊤ (genericPoint X) trivial (φ (c : k))
        = X.germToFunctionField ⊤ (φ (c : k)) from rfl, h3]
    rfl

end AlgebraicGeometry
