module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationStalk
public import StacksFrontier.RingTheory.Derivation.LeibnizHom

/-!
# The derivation a vector field induces on the stalks of its own scheme

Let `X` be a scheme over a field `k` and let `D` be a vector field on `X`, that is, a
`k`-derivation of `𝒪_X` in the sense of Tag 0E66. For a point `x` of `X` the local ring
`𝒪_{X, x}` carries a `k`-derivation induced by `D`: the germ at `x` of a local section `s` is
sent to the germ of `D s`. The `k`-algebra structure on the stalk is the germ at `x` of the
structure morphism, `AlgebraicGeometry.fieldToStalk`.

This is the construction of `Stacks.Curves.stalkDerivation` — which produces a derivation of the
stalk `(ν_* 𝒪_Y)_x` of a direct image along a morphism `ν : Y ⟶ X` — carried out for the
structure sheaf of `X` itself. It is *not* obtained from that one by taking `ν = 𝟙 X`: the
pushforward `(𝟙 X).base _* X.presheaf` is isomorphic to `X.presheaf`, but not equal to it, so the
derivation of its stalk is a derivation of a different ring and every statement about germs of
sections of `𝒪_X` would have to be transported across the isomorphism. The construction is short
enough that repeating it directly is cheaper than the transport.

## Main definitions

* `Stacks.Curves.ownStalkFun` — the underlying map of the induced derivation of `𝒪_{X, x}`.
* `Stacks.Curves.ownStalkDerivation` — the induced `k`-derivation of `𝒪_{X, x}`.
* `Stacks.Curves.ownStalkAddHom` — the same map as a bare additive map, the shape in which the
  uniqueness theory of Leibniz maps on a localization consumes it.

## Main results

* `Stacks.Curves.ownStalkDerivation_germ` — the induced derivation sends the germ of `s` to the
  germ of `D s`; this is the defining property, and the only one its consumers use.
* `Stacks.Curves.ownStalkFun_add`, `Stacks.Curves.ownStalkFun_mul`,
  `Stacks.Curves.ownStalkFun_structureMap` — additivity, the Leibniz rule and the vanishing on
  the image of the base, the three facts the derivation is assembled from.
* `Stacks.Curves.eq_ownStalkDerivation_of_leibniz_of_germ` — **the induced derivation is the only
  Leibniz map of `𝒪_{X, x}` extending `D` through the germ map of one affine open containing
  `x`.** The ring of sections over an affine open `U` localizes to the stalk at a point of `U`
  (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and a Leibniz additive map of a
  localization is determined by its values on the image of the base
  (`Stacks.DerivationExtension.eq_of_leibniz_of_localization`). So a vector field controls the
  derivations of all the stalks over an affine open through its values on that one ring of
  sections.

## Implementation notes

As for the direct image, this is not a descent of ring maps along the colimit computing the stalk:
`D` is only additive over each open, so there is no morphism of presheaves of rings to apply
`CategoryTheory.Limits.colimit.desc` to. The map is defined by choosing a representative of the
germ (`TopCat.Presheaf.exists_germ_eq`), and is well defined because two representatives agree on
a smaller open (`TopCat.Presheaf.germ_eq`) on which `D` commutes with restriction
(`Stacks.Curves.SheafDerivationOf.onSections_map`).

The uniqueness statement is phrased for a bare `AddMonoidHom` rather than for a bundled
`Derivation`, because the competing map in its intended use is built from the sheaf data and is
not linear over anything before the comparison is made; the `k`-linearity of the induced
derivation plays no part in the argument, only the Leibniz rule does.

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

section OwnStalk

variable {X : Scheme.{u}} {hX : X ⟶ Spec (.of k)}

/-- The germ of the value of `D` on a representative does not depend on the representative: two
representatives agree on a smaller open, and `D` commutes with restriction. -/
public theorem exists_germ_ownSections (D : SheafDerivationOf hX) {x : X}
    (z : X.presheaf.stalk x) :
    ∃ w : X.presheaf.stalk x, ∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      X.presheaf.germ U x hx s = z → X.presheaf.germ U x hx (D.onSections s) = w := by
  obtain ⟨U₀, hx₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf z
  refine ⟨X.presheaf.germ U₀ x hx₀ (D.onSections s₀), fun U hx s hs => ?_⟩
  obtain ⟨W, hxW, iU, iU₀, heq⟩ := X.presheaf.germ_eq x hx hx₀ s s₀ (hs.trans hs₀.symm)
  refine TopCat.Presheaf.germ_ext _ W hxW iU iU₀ ?_
  exact ((D.onSections_map iU.op s).symm.trans (congrArg _ heq)).trans
    (D.onSections_map iU₀.op s₀)

/-- The endomorphism of the local ring `𝒪_{X, x}` induced by a vector field `D` on `X`: the germ
of a section is sent to the germ of the value of `D` on it. -/
public def ownStalkFun {hX : X ⟶ Spec (.of k)} (D : SheafDerivationOf hX) {x : X}
    (z : X.presheaf.stalk x) : X.presheaf.stalk x :=
  (exists_germ_ownSections D z).choose

/-- `Stacks.Curves.ownStalkFun` sends the germ of `s` to the germ of `D s`. -/
public theorem ownStalkFun_germ (D : SheafDerivationOf hX) {x : X} (U : X.Opens) (hx : x ∈ U)
    (s : Γ(X, U)) :
    ownStalkFun D (X.presheaf.germ U x hx s) = X.presheaf.germ U x hx (D.onSections s) :=
  ((exists_germ_ownSections D _).choose_spec U hx s rfl).symm

/-- `Stacks.Curves.ownStalkFun` is additive. -/
public theorem ownStalkFun_add (D : SheafDerivationOf hX) {x : X} (z w : X.presheaf.stalk x) :
    ownStalkFun D (z + w) = ownStalkFun D z + ownStalkFun D w := by
  obtain ⟨U, hx, s, t, hs, ht⟩ := exists_germ_eq_pair X.presheaf x z w
  subst hs ht
  rw [← map_add, ownStalkFun_germ, SheafDerivationOf.onSections_add, map_add,
    ownStalkFun_germ, ownStalkFun_germ]

/-- `Stacks.Curves.ownStalkFun` obeys the Leibniz rule. -/
public theorem ownStalkFun_mul (D : SheafDerivationOf hX) {x : X} (z w : X.presheaf.stalk x) :
    ownStalkFun D (z * w) = z * ownStalkFun D w + w * ownStalkFun D z := by
  obtain ⟨U, hx, s, t, hs, ht⟩ := exists_germ_eq_pair X.presheaf x z w
  subst hs ht
  rw [← map_mul, ownStalkFun_germ, SheafDerivationOf.onSections_mul, map_add, map_mul, map_mul,
    ownStalkFun_germ, ownStalkFun_germ]

/-- `Stacks.Curves.ownStalkFun` annihilates `1`, by the Leibniz rule at `1 * 1`. -/
public theorem ownStalkFun_one (D : SheafDerivationOf hX) (x : X) :
    ownStalkFun D (1 : X.presheaf.stalk x) = 0 := by
  have h := ownStalkFun_mul D (1 : X.presheaf.stalk x) 1
  rw [mul_one, one_mul] at h
  have h2 : ownStalkFun D (1 : X.presheaf.stalk x) + 0 =
      ownStalkFun D (1 : X.presheaf.stalk x) + ownStalkFun D (1 : X.presheaf.stalk x) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- A vector field annihilates the germ of a section pulled back from the base. -/
public theorem ownStalkFun_structureMap (D : SheafDerivationOf hX) (x : X)
    (hx : x ∈ hX ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)) (b : Γ(Spec (.of k), ⊤)) :
    ownStalkFun D (X.presheaf.germ (hX ⁻¹ᵁ ⊤) x hx ((hX.app ⊤).hom b)) = 0 := by
  have h2 : D.onSections ((hX.app ⊤).hom b) = 0 := D.onSections_app ⊤ b
  rw [ownStalkFun_germ, h2, map_zero]

/-- **The derivation induced on a stalk of the structure sheaf.** A vector field `D` on `X` — a
`k`-derivation of `𝒪_X` in the sense of Tag 0E66 — induces a `k`-derivation of the local ring
`𝒪_{X, x}`, sending the germ at `x` of a local section `s` to the germ of `D s`. The `k`-algebra
structure is the germ at `x` of the structure morphism, `AlgebraicGeometry.fieldToStalk`.

This is not the descent of a morphism of rings along a colimit: `D` is only additive over each
open, so the construction is by choice of a representative of the germ, well defined because two
representatives agree on a smaller open and `D` commutes with restriction. -/
public def ownStalkDerivation {hX : X ⟶ Spec (.of k)} (D : SheafDerivationOf hX) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
    Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
  { toFun := ownStalkFun D
    map_add' := ownStalkFun_add D
    map_smul' := fun c z => by
      change ownStalkFun D (c • z) = c • ownStalkFun D z
      have h0 : ownStalkFun D (algebraMap k (X.presheaf.stalk x) c) = 0 :=
        ownStalkFun_structureMap D x trivial (((Scheme.ΓSpecIso (.of k)).inv).hom c)
      rw [Algebra.smul_def, ownStalkFun_mul, h0, mul_zero, add_zero, Algebra.smul_def]
    map_one_eq_zero' := ownStalkFun_one D x
    leibniz' := fun z w => by
      change ownStalkFun D (z * w) = z • ownStalkFun D w + w • ownStalkFun D z
      rw [ownStalkFun_mul, smul_eq_mul, smul_eq_mul] }

/-- **The germ computation rule.** The induced derivation on the stalk sends the germ of `s` to
the germ of `D s`. -/
@[simp] public theorem ownStalkDerivation_germ {hX : X ⟶ Spec (.of k)}
    (D : SheafDerivationOf hX) {x : X} (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
    ownStalkDerivation D x (X.presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (D.onSections s) :=
  ownStalkFun_germ D U hx s

/-- The map induced on `𝒪_{X, x}` by a vector field, as a bare additive map. This is the shape in
which the uniqueness of a Leibniz map on a localization is stated, and it mentions no algebra
structure on the stalk. -/
public def ownStalkAddHom (D : SheafDerivationOf hX) (x : X) :
    X.presheaf.stalk x →+ X.presheaf.stalk x :=
  AddMonoidHom.mk' (ownStalkFun D) (ownStalkFun_add D)

/-- `Stacks.Curves.ownStalkAddHom` is `Stacks.Curves.ownStalkFun`. -/
@[simp] public theorem ownStalkAddHom_apply (D : SheafDerivationOf hX) (x : X)
    (z : X.presheaf.stalk x) : ownStalkAddHom D x z = ownStalkFun D z := rfl

/-- **A vector field's map on a stalk is determined by its values over any affine open containing
the point.** If `U` is an affine open containing `x` and `g` is an additive map of `𝒪_{X, x}`
obeying the Leibniz rule which sends the germ of `s` to the germ of `D s` for every section `s`
over `U`, then `g` is `Stacks.Curves.ownStalkFun D`.

The ring of sections `Γ(X, U)` localizes to `𝒪_{X, x}` at the prime of `x`, and a Leibniz
additive map of a localization is determined by its values on the image of the base. -/
public theorem eq_ownStalkFun_of_leibniz_of_germ (D : SheafDerivationOf hX) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U)
    (g : X.presheaf.stalk x →+ X.presheaf.stalk x)
    (hg : ∀ z w : X.presheaf.stalk x, g (z * w) = z * g w + w * g z)
    (h : ∀ s : Γ(X, U), g (X.presheaf.germ U x hx s) = X.presheaf.germ U x hx (D.onSections s)) :
    ∀ z, g z = ownStalkFun D z := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have key : g = ownStalkAddHom D x :=
    Stacks.DerivationExtension.eq_of_leibniz_of_localization
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl g (ownStalkAddHom D x) hg
      (fun z w => ownStalkFun_mul D z w) fun a => by
        rw [TopCat.Presheaf.stalk_open_algebraMap X.presheaf ⟨x, hx⟩]
        rw [ownStalkAddHom_apply, ownStalkFun_germ]
        exact h a
  exact fun z => congrArg (fun f => f z) key

/-- **The induced derivation of the stalk is the only Leibniz map extending the vector field
through the germ map of an affine open.** This is
`Stacks.Curves.eq_ownStalkFun_of_leibniz_of_germ` read for
`Stacks.Curves.ownStalkDerivation`. -/
public theorem eq_ownStalkDerivation_of_leibniz_of_germ {hX : X ⟶ Spec (.of k)}
    (D : SheafDerivationOf hX) {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U)
    (g : X.presheaf.stalk x →+ X.presheaf.stalk x)
    (hg : ∀ z w : X.presheaf.stalk x, g (z * w) = z * g w + w * g z)
    (h : ∀ s : Γ(X, U), g (X.presheaf.germ U x hx s) = X.presheaf.germ U x hx (D.onSections s)) :
    letI : Algebra k (X.presheaf.stalk x) := (fieldToStalk hX x).hom.toAlgebra
    ∀ z, g z = ownStalkDerivation D x z :=
  eq_ownStalkFun_of_leibniz_of_germ D hU hx g hg h

end OwnStalk

end Stacks.Curves

end
