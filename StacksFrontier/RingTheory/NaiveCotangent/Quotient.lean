module

public import StacksFrontier.RingTheory.NaiveCotangent.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quotients of a two-term complex, and reduction modulo an ideal

Let `X : X₁ --d--> X₀` be a two-term complex of `S`-modules.  Given a pair of submodules
`U ⊆ X₁` and `V ⊆ X₀` with `d U ⊆ V`, the quotients `X₁ / U` and `X₀ / V` again form a
two-term complex, and a pair of inclusions `U ⊆ U'`, `V ⊆ V'` induces a chain map between
two such quotients.  The special case `U = 𝔞 X₁`, `V = 𝔞 X₀` for an ideal `𝔞 ⊆ S` is the
base change `X ⊗_S S / 𝔞`, realised on the nose rather than through a tensor product, and
the inclusions `𝔞 ⊆ 𝔟` give the transition maps of the inverse system `{X ⊗_S S / 𝔞ⁿ}`.

This is the shape in which **Stacks 0AJS (1)** compares the two inverse systems
`{NL^∧_{B/A} ⊗_B B/IⁿB}` and `{NL_{Bₙ/Aₙ}}` of two-term complexes.  Both systems have the
*same* degree-`0` terms — `(⨁ᵢ B dxᵢ) ⊗_B Bₙ = ⨁ᵢ Bₙ dxᵢ` with no shift at all — and differ
in degree `-1` only by which submodule of `J / J²` is divided out: `IⁿJ` for the first
system and `J ∩ Iⁿ A⟨x⟩` for the second.  The whole content of the comparison is therefore
a sandwich of submodules of `X₁`, and `quotByMap` turns such a sandwich into the chain maps.

## Main definitions

* `NaiveCotangent.TwoTerm.quotBy`: the quotient complex `X₁ / U --> X₀ / V`.
* `NaiveCotangent.TwoTerm.quotByMap`: the chain map induced by `U ⊆ U'` and `V ⊆ V'`.
* `NaiveCotangent.TwoTerm.modIdeal`: the reduction `X ⊗_S S / 𝔞 = (X₁ / 𝔞 X₁ --> X₀ / 𝔞 X₀)`.
* `NaiveCotangent.TwoTerm.modIdealMap`: the transition chain map for `𝔞 ⊆ 𝔟`.

## Main results

* `NaiveCotangent.TwoTerm.quotByMap_comp`: the comparison chain maps compose, so a chain of
  nested sandwiches gives a commuting diagram of quotient complexes.
* `NaiveCotangent.TwoTerm.quotByMap_self`: the comparison map of a sandwich with itself is
  the identity.
* `NaiveCotangent.TwoTerm.modIdealMap_comp`, `NaiveCotangent.TwoTerm.modIdealMap_self`: the
  same two statements for the transition maps of `{X ⊗_S S / 𝔞}`.
* `NaiveCotangent.TwoTerm.surjective_quotByMap_f₁`,
  `NaiveCotangent.TwoTerm.surjective_quotByMap_f₀`: every comparison chain map is
  degreewise surjective, which is what makes the maps of Stacks 0AJS (1) *canonical
  surjections*.

## Implementation notes

The compatibility hypothesis is stated as `U ≤ V.comap X.d` rather than
`U.map X.d ≤ V`, because that is the form `Submodule.mapQ` consumes;
`quotBy_of_map_le` builds the complex from the other form.

The comparison chain map is `Submodule.factor` in each degree, so `quotByMap_comp` is
`Submodule.factor_comp` degreewise and the whole file is free of diagram chases.

## References

* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 00S0](https://stacks.math.columbia.edu/tag/00S0)
-/

@[expose] public section

namespace NaiveCotangent

namespace TwoTerm

universe u v w

variable {S : Type u} [CommRing S] (X : TwoTerm.{u, v, w} S)

/-! ## Quotient by a compatible pair of submodules -/

/-- The quotient of a two-term complex `X₁ --d--> X₀` by a pair of submodules `U ⊆ X₁`,
`V ⊆ X₀` with `d U ⊆ V`: the complex `X₁ / U --> X₀ / V` with the induced differential. -/
public def quotBy (U : Submodule S X.X₁) (V : Submodule S X.X₀) (h : U ≤ V.comap X.d) :
    TwoTerm S where
  X₁ := X.X₁ ⧸ U
  X₀ := X.X₀ ⧸ V
  d := U.mapQ V X.d h

/-- The differential of a quotient complex is the one induced by the differential of `X`. -/
@[simp] public theorem quotBy_d (U : Submodule S X.X₁) (V : Submodule S X.X₀)
    (h : U ≤ V.comap X.d) : (X.quotBy U V h).d = U.mapQ V X.d h := rfl

/-- The quotient complex, built from the compatibility hypothesis in the form `d U ⊆ V`. -/
public def quotByOfMapLe (U : Submodule S X.X₁) (V : Submodule S X.X₀)
    (h : U.map X.d ≤ V) : TwoTerm S :=
  X.quotBy U V (Submodule.map_le_iff_le_comap.mp h)

/-- The differential of a quotient complex sends the class of `x` to the class of `d x`. -/
@[simp] public theorem quotBy_d_mkQ {U : Submodule S X.X₁} {V : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (x : X.X₁) :
    (X.quotBy U V h).d (Submodule.mkQ U x) = Submodule.mkQ V (X.d x) := rfl

/-- The chain map `X₁ / U → X₀ / V` to `X₁ / U' → X₀ / V'` induced by a pair of inclusions
`U ⊆ U'` and `V ⊆ V'`.  In degree `1` and in degree `0` it is the canonical surjection
between quotients by nested submodules. -/
public def quotByMap {U U' : Submodule S X.X₁} {V V' : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (h' : U' ≤ V'.comap X.d) (hU : U ≤ U') (hV : V ≤ V') :
    ChainMap (X.quotBy U V h) (X.quotBy U' V' h') where
  f₁ := Submodule.factor hU
  f₀ := Submodule.factor hV
  comm := by
    refine Submodule.linearMap_qext _ ?_
    ext x
    rfl

/-- In degree `1`, the comparison chain map is the canonical surjection `X₁ / U → X₁ / U'`. -/
@[simp] public theorem quotByMap_f₁ {U U' : Submodule S X.X₁} {V V' : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (h' : U' ≤ V'.comap X.d) (hU : U ≤ U') (hV : V ≤ V') :
    (X.quotByMap h h' hU hV).f₁ = Submodule.factor hU := rfl

/-- In degree `0`, the comparison chain map is the canonical surjection `X₀ / V → X₀ / V'`. -/
@[simp] public theorem quotByMap_f₀ {U U' : Submodule S X.X₁} {V V' : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (h' : U' ≤ V'.comap X.d) (hU : U ≤ U') (hV : V ≤ V') :
    (X.quotByMap h h' hU hV).f₀ = Submodule.factor hV := rfl

/-- The comparison chain maps compose: the comparison from the `U`-quotient to the
`U''`-quotient factors through the `U'`-quotient. -/
public theorem quotByMap_comp {U U' U'' : Submodule S X.X₁} {V V' V'' : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (h' : U' ≤ V'.comap X.d) (h'' : U'' ≤ V''.comap X.d)
    (hU : U ≤ U') (hV : V ≤ V') (hU' : U' ≤ U'') (hV' : V' ≤ V'') :
    (X.quotByMap h' h'' hU' hV').comp (X.quotByMap h h' hU hV) =
      X.quotByMap h h'' (hU.trans hU') (hV.trans hV') := by
  refine ChainMap.ext ?_ ?_
  · exact Submodule.factor_comp hU hU'
  · exact Submodule.factor_comp hV hV'

/-- The comparison chain map of a pair of submodules with itself is the identity. -/
public theorem quotByMap_self {U : Submodule S X.X₁} {V : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) :
    X.quotByMap h h le_rfl le_rfl = ChainMap.id (X.quotBy U V h) := by
  refine ChainMap.ext ?_ ?_
  · simp only [quotByMap_f₁, Submodule.mapQ_id, ChainMap.id_f₁]
    exact rfl
  · simp only [quotByMap_f₀, Submodule.mapQ_id, ChainMap.id_f₀]
    exact rfl

/-- A comparison chain map is surjective in degree `1`. -/
public theorem surjective_quotByMap_f₁ {U U' : Submodule S X.X₁} {V V' : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (h' : U' ≤ V'.comap X.d) (hU : U ≤ U') (hV : V ≤ V') :
    Function.Surjective (X.quotByMap h h' hU hV).f₁ :=
  Submodule.factor_surjective hU

/-- A comparison chain map is surjective in degree `0`. -/
public theorem surjective_quotByMap_f₀ {U U' : Submodule S X.X₁} {V V' : Submodule S X.X₀}
    (h : U ≤ V.comap X.d) (h' : U' ≤ V'.comap X.d) (hU : U ≤ U') (hV : V ≤ V') :
    Function.Surjective (X.quotByMap h h' hU hV).f₀ :=
  Submodule.factor_surjective hV

/-! ## Reduction modulo an ideal -/

/-- For every ideal `𝔞 ⊆ S` the differential of `X` carries `𝔞 X₁` into `𝔞 X₀`. -/
public theorem smul_top_le_comap_d (𝔞 : Ideal S) :
    (𝔞 • ⊤ : Submodule S X.X₁) ≤ (𝔞 • ⊤ : Submodule S X.X₀).comap X.d := by
  refine Submodule.map_le_iff_le_comap.mp ?_
  rw [Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

/-- The reduction `X ⊗_S S / 𝔞` of a two-term complex modulo an ideal `𝔞 ⊆ S`, realised on
the nose as the quotient complex `X₁ / 𝔞 X₁ --> X₀ / 𝔞 X₀`. -/
@[sga "7 IX 11.6" "more general"]
public def modIdeal (𝔞 : Ideal S) : TwoTerm S :=
  X.quotBy (𝔞 • ⊤) (𝔞 • ⊤) (X.smul_top_le_comap_d 𝔞)

/-- The differential of `X ⊗_S S / 𝔞` sends the class of `x` to the class of `d x`. -/
@[simp] public theorem modIdeal_d_mkQ (𝔞 : Ideal S) (x : X.X₁) :
    (X.modIdeal 𝔞).d (Submodule.mkQ _ x) = Submodule.mkQ (𝔞 • ⊤ : Submodule S X.X₀) (X.d x) :=
  rfl

/-- The transition chain map `X ⊗_S S / 𝔞 → X ⊗_S S / 𝔟` for `𝔞 ⊆ 𝔟`.  Taking
`𝔞 = 𝔟ⁿ⁺¹`, `𝔟 = 𝔟ⁿ` this is the transition map of the inverse system
`{X ⊗_S S / 𝔟ⁿ}`. -/
public def modIdealMap {𝔞 𝔟 : Ideal S} (h : 𝔞 ≤ 𝔟) :
    ChainMap (X.modIdeal 𝔞) (X.modIdeal 𝔟) :=
  X.quotByMap _ _ (Submodule.smul_mono_left h) (Submodule.smul_mono_left h)

/-- The transition maps of `{X ⊗_S S / 𝔞}` compose. -/
public theorem modIdealMap_comp {𝔞 𝔟 𝔠 : Ideal S} (h : 𝔞 ≤ 𝔟) (h' : 𝔟 ≤ 𝔠) :
    (X.modIdealMap h').comp (X.modIdealMap h) = X.modIdealMap (h.trans h') :=
  X.quotByMap_comp _ _ _ _ _ _ _

/-- The transition map of `{X ⊗_S S / 𝔞}` along the identity inclusion is the identity. -/
public theorem modIdealMap_self (𝔞 : Ideal S) :
    X.modIdealMap (le_refl 𝔞) = ChainMap.id (X.modIdeal 𝔞) :=
  X.quotByMap_self _

/-- The transition maps of `{X ⊗_S S / 𝔞}` are surjective in degree `1`. -/
public theorem surjective_modIdealMap_f₁ {𝔞 𝔟 : Ideal S} (h : 𝔞 ≤ 𝔟) :
    Function.Surjective (X.modIdealMap h).f₁ :=
  X.surjective_quotByMap_f₁ _ _ _ _

/-- The transition maps of `{X ⊗_S S / 𝔞}` are surjective in degree `0`. -/
public theorem surjective_modIdealMap_f₀ {𝔞 𝔟 : Ideal S} (h : 𝔞 ≤ 𝔟) :
    Function.Surjective (X.modIdealMap h).f₀ :=
  X.surjective_quotByMap_f₀ _ _ _ _

/-! ## The comparison of Stacks 0AJS (1) -/

/-- **The comparison chain maps of Stacks 0AJS (1).**  Let `X` be a two-term complex of
`S`-modules, let `𝔞 ⊆ 𝔟` be ideals of `S`, and let `U` be a submodule of `X₁` sandwiched
between `𝔞 X₁` and `𝔟 X₁` and carried into `𝔞 X₀` by the differential.  Then the quotient
complex `Y = (X₁ / U --> X₀ / 𝔞 X₀)` sits between the two reductions,

`X ⊗_S S/𝔞  ⟶  Y  ⟶  X ⊗_S S/𝔟`,

by degreewise surjective chain maps whose composite is the transition map of the system
`{X ⊗_S S / 𝔞}`.

In Stacks 0AJS (1) this is applied with `X = NL^∧_{B/A}`, `𝔞 = IⁿB`, `𝔟 = I^{n-c}B` and
`U` the image of `J ∩ Iⁿ A⟨x⟩` in `J / J²`, in which case `Y = NL_{Bₙ/Aₙ}`; the sandwich
`IⁿJ ⊆ J ∩ Iⁿ A⟨x⟩ ⊆ I^{n-c}J` is the Artin–Rees lemma (Stacks 00IN).  The degree-`0` terms
are *not* shifted: `Y` and `X ⊗_S S/𝔞` have the same degree-`0` term, which is the
statement `(⨁ᵢ B dxᵢ) ⊗_B Bₙ = ⨁ᵢ Bₙ dxᵢ`. -/
public theorem exists_sandwich_comparison {𝔞 𝔟 : Ideal S} (hab : 𝔞 ≤ 𝔟)
    {U : Submodule S X.X₁} (hlo : (𝔞 • ⊤ : Submodule S X.X₁) ≤ U)
    (hhi : U ≤ (𝔟 • ⊤ : Submodule S X.X₁)) (hd : U ≤ (𝔞 • ⊤ : Submodule S X.X₀).comap X.d) :
    ∃ (Y : TwoTerm.{u, v, w} S) (φ : ChainMap (X.modIdeal 𝔞) Y) (ψ : ChainMap Y (X.modIdeal 𝔟)),
      Function.Surjective φ.f₁ ∧ Function.Surjective φ.f₀ ∧
        Function.Surjective ψ.f₁ ∧ Function.Surjective ψ.f₀ ∧
          ψ.comp φ = X.modIdealMap hab := by
  refine ⟨X.quotBy U (𝔞 • ⊤) hd,
    X.quotByMap (X.smul_top_le_comap_d 𝔞) hd hlo le_rfl,
    X.quotByMap hd (X.smul_top_le_comap_d 𝔟) hhi (Submodule.smul_mono_left hab),
    X.surjective_quotByMap_f₁ _ _ _ _, X.surjective_quotByMap_f₀ _ _ _ _,
    X.surjective_quotByMap_f₁ _ _ _ _, X.surjective_quotByMap_f₀ _ _ _ _,
    X.quotByMap_comp _ _ _ _ _ _ _⟩

end TwoTerm

end NaiveCotangent

end
