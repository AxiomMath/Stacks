module

public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationExtensionGerm
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.AffineOpenOperator

/-!
# A raw operator over an affine preimage acts on germs through its value at the top

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components and let
`ν : X^ν ⟶ X` be its normalization. A raw operator `d` on the structure sheaf of `X^ν` over the
preimage `ν⁻¹U` of an open `U` of `X` is a family of additive maps of `Γ(X^ν, W)`, one for each
open `W ≤ ν⁻¹U`, and naturality of `d` says that the family commutes with restriction. Fix a
point `x` of `U`. The opens `ν⁻¹W'` with `W' ≤ U` and `x ∈ W'` compute the stalk
`(ν_* 𝒪_{X^ν})_x`, so such a family induces a single additive map of that stalk, sending the germ
at `x` of a section `z` over `ν⁻¹W'` to the germ of `d z`; this is
`Stacks.Curves.rawOpStalkFun`, built exactly as `Stacks.Curves.stalkFun` is, by choosing a
representative of the germ.

When `U` is affine the induced map is already pinned down by the single value of `d` at the top:
by Tag 0C3B the stalk is a localization of `Γ(X^ν, ν⁻¹U)` along the germ map, and a Leibniz
additive map of a localization is determined by its values on the image of the base. So if `d`
obeys the Leibniz rule and `g` is any Leibniz map of the stalk computing germs of the values of
`d` over `ν⁻¹U` itself, then `g` computes germs of the values of `d` over every `ν⁻¹W'` with
`W' ≤ U`.

The consequence this is wanted for is that two such operators cannot disagree. If `d` lives over
`ν⁻¹U` and `e` over `ν⁻¹V`, both affine, and the values of `d` and `e` at the top both extend one
vector field `D` on `X` along `ν^♯`, then each induces on `(ν_* 𝒪_{X^ν})_x` the Leibniz map of
`Stacks.Curves.exists_leibniz_of_extension`, and those two maps agree on the image of `𝒪_{X, x}`
and are therefore equal. So `d` and `e` have the same germ at every point of an open contained in
both `U` and `V`, and hence the same value over its preimage, the direct image of a sheaf being a
sheaf. This is the operator-level form of `Stacks.Curves.germ_eq_of_extension_of_extension`.

## Main results

* `Stacks.Curves.rawOpStalkFun_germ` — the map a natural raw operator induces on the stalk of the
  direct image sends the germ of `z` to the germ of `d z`, for `z` a section over the preimage of
  any open inside `U`.
* `Stacks.Curves.germ_rawOp_eq_of_leibniz` — **a natural Leibniz raw operator over `ν⁻¹U`, for
  `U` affine, acts on germs through its value at the top**: any Leibniz map of the stalk computing
  germs of the values of `d` over `ν⁻¹U` computes them over the preimage of every open inside `U`.
* `Stacks.Curves.rawOp_eq_of_extension_of_extension` — **two natural Leibniz raw operators over
  the preimages of two affine opens whose values at the top extend the same vector field agree
  over the preimage of any open inside both.**

## Implementation notes

The ambiguity in the shape of the answer is where the preimages enter. The stalk of the direct
image at `x : X` is computed by sections over the opens `ν⁻¹W'` for `W' : X.Opens`, whereas a raw
operator over `ν⁻¹U` is defined on sections over arbitrary opens of `X^ν` inside `ν⁻¹U`. The
agreement statement is therefore proved for an open of `X^ν` of the form `ν⁻¹W'`, which is the
shape in which it is consumed: reducing the agreement of two operators to the preimage of the
intersection of the two affine opens is exactly what `DiffOp.agreeOnCover_of_slice_eq` together
with `Stacks.AlgebraicGeometry.DifferentialsAffine.rawOp_ext` does, and
`AlgebraicGeometry.Scheme.Hom.preimage_inf` puts `ν⁻¹(U ⊓ V)` into that shape.

Sections over `ν⁻¹W'` are separated by their germs at the points of `W'` because the direct image
of a sheaf along a continuous map is a sheaf; no sheaf condition on `X^ν` itself is used, and in
particular no germ in a stalk of `𝒪_{X^ν}` appears anywhere below.

The map induced on the stalk by the value of `d` at the top is a hypothesis of
`Stacks.Curves.germ_rawOp_eq_of_leibniz` rather than a construction inside it. It is unique, and
the two ways it arises — as the localization of that value,
`Stacks.DerivationExtension.locLeibnizHom`, and as the map produced by
`Stacks.Curves.exists_leibniz_of_extension` — are both passed in as such a map, which keeps the
algebra structures on the stalk out of the statement.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.NormalizationStalkAmbient
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

section RawOpStalk

/-- Taking preimages along the normalization is monotone. -/
public theorem normalization_preimage_le
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {A B : X.Opens} (h : A ≤ B) :
    Scheme.normalization X hfin ⁻¹ᵁ A ≤ Scheme.normalization X hfin ⁻¹ᵁ B := fun _ hy => h hy

/-- Two sections of the direct image of the structure sheaf of the normalization over an open of
`X` with the same germ at every point of that open are equal: the direct image of a sheaf along a
continuous map is a sheaf. -/
public theorem section_eq_of_germ_eq
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {W : X.Opens}
    (s t : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ W))
    (h : ∀ (p : X) (hp : p ∈ W),
      ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ W p hp s
        = ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ W p hp t) :
    s = t := by
  have hF : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf)).IsSheaf :=
    ((TopCat.Sheaf.pushforward CommRingCat (Scheme.normalization X hfin).base).obj
      (Scheme.normalizationScheme X hfin).sheaf).property
  refine TopCat.Presheaf.IsSheaf.section_ext hF (U := op W) fun p hp => ?_
  obtain ⟨V, hpV, iU, iV, heq⟩ :=
    ((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).germ_eq p hp hp s t (h p hp)
  exact ⟨V, iU.le, hpV, heq⟩

/-- The germ at `x` of a section restricted to `A ⊓ U` is the germ of the section. -/
private theorem germ_res_inf_left {Y : TopCat} (F : Y.Presheaf CommRingCat) {A U : Opens Y}
    {x : Y} (hxA : x ∈ A) (hxU : x ∈ U) {z : F.stalk x} (s : F.obj (op A))
    (hs : F.germ A x hxA s = z) :
    F.germ (A ⊓ U) x ⟨hxA, hxU⟩ ((F.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op).hom s) = z :=
  (TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : A ⊓ U ≤ A)) x ⟨hxA, hxU⟩ s).trans hs

/-- The germ of the value of a natural raw operator on a representative of a germ does not depend
on the representative: two representatives agree on a smaller open, and a natural operator
commutes with restriction. Only representatives living over the preimage of an open inside `U`
are considered, and they are cofinal because `U` is an open containing `x`. -/
public theorem exists_germ_rawOp
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {x : X} (hxU : x ∈ U)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural) (z : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x)) :
    ∃ w : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x),
      ∀ (W : X.Opens) (hW : W ≤ U) (hx : x ∈ W)
        (s : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ W)),
        ((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).germ W x hx s = z →
          ((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).germ W x hx
            (d.unitOp (Over.mk (homOfLE (normalization_preimage_le hfin hW))) s) = w := by
  obtain ⟨U₀, hx₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf) z
  have hx₁ : x ∈ U₀ ⊓ U := ⟨hx₀, hxU⟩
  have hs₁ := germ_res_inf_left _ hx₀ hxU s₀ hs₀
  refine ⟨((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).germ (U₀ ⊓ U) x hx₁
    (d.unitOp (Over.mk (homOfLE (normalization_preimage_le hfin
        (inf_le_right : U₀ ⊓ U ≤ U))))
      ((((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).map
          (homOfLE (inf_le_left : U₀ ⊓ U ≤ U₀)).op).hom s₀)), fun W hW hx s hs => ?_⟩
  obtain ⟨V, hxV, iW, iW₀, heq⟩ :=
    ((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).germ_eq x hx hx₁ s _ (hs.trans hs₁.symm)
  refine TopCat.Presheaf.germ_ext _ V hxV iW iW₀ ?_
  have hL := hnat (Over.mk (homOfLE (normalization_preimage_le hfin (iW.le.trans hW))))
    (Over.mk (homOfLE (normalization_preimage_le hfin hW)))
    (Over.homMk (homOfLE (normalization_preimage_le hfin iW.le)) (Subsingleton.elim _ _)) s
  have hR := hnat (Over.mk (homOfLE (normalization_preimage_le hfin
      (iW₀.le.trans (inf_le_right : U₀ ⊓ U ≤ U)))))
    (Over.mk (homOfLE (normalization_preimage_le hfin (inf_le_right : U₀ ⊓ U ≤ U))))
    (Over.homMk (homOfLE (normalization_preimage_le hfin iW₀.le)) (Subsingleton.elim _ _))
    ((((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).map
        (homOfLE (inf_le_left : U₀ ⊓ U ≤ U₀)).op).hom s₀)
  exact hL.symm.trans ((congrArg _ heq).trans hR)

/-- The endomorphism of the stalk `(ν_* 𝒪_{X^ν})_x` induced by a natural raw operator over
`ν⁻¹U`, for `x` a point of `U`: the germ of a section over the preimage of an open inside `U` is
sent to the germ of the value of the operator on it. -/
public def rawOpStalkFun
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {x : X} (hxU : x ∈ U)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural) (z : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x)) :
    (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x) :=
  (exists_germ_rawOp hfin hxU d hnat z).choose

/-- **The germ computation rule.** `Stacks.Curves.rawOpStalkFun` sends the germ of a section `s`
over the preimage of an open `W ≤ U` to the germ of the value of the operator on `s`. -/
public theorem rawOpStalkFun_germ
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {x : X} (hxU : x ∈ U)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural) (W : X.Opens) (hW : W ≤ U) (hx : x ∈ W)
    (s : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ W)) :
    rawOpStalkFun hfin hxU d hnat
        (((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ W x hx s)
      = ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ W x hx
        (d.unitOp (Over.mk (homOfLE (normalization_preimage_le hfin hW))) s) :=
  ((exists_germ_rawOp hfin hxU d hnat _).choose_spec W hW hx s rfl).symm

/-- Two germs at a point of `U` are the germs of two sections over the preimage of one open
inside `U`: represent both over a common open and intersect it with `U`. -/
public theorem exists_germ_eq_pair_le
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {x : X} (hxU : x ∈ U)
    (z w : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x)) :
    ∃ (W : X.Opens) (_ : W ≤ U) (hx : x ∈ W)
      (s t : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ W)),
      ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ W x hx s = z ∧
        ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ W x hx t = w := by
  obtain ⟨W₁, hx₁, s, t, hs, ht⟩ := exists_germ_eq_pair
    ((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf) x z w
  have hx₂ : x ∈ W₁ ⊓ U := ⟨hx₁, hxU⟩
  refine ⟨W₁ ⊓ U, inf_le_right, hx₂,
    ((((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).map
        (homOfLE (inf_le_left : W₁ ⊓ U ≤ W₁)).op).hom s),
    ((((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).map
        (homOfLE (inf_le_left : W₁ ⊓ U ≤ W₁)).op).hom t), ?_, ?_⟩
  · exact germ_res_inf_left _ hx₁ hxU s hs
  · exact germ_res_inf_left _ hx₁ hxU t ht

/-- `Stacks.Curves.rawOpStalkFun` is additive. -/
public theorem rawOpStalkFun_add
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {x : X} (hxU : x ∈ U)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural) (z w : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x)) :
    rawOpStalkFun hfin hxU d hnat (z + w)
      = rawOpStalkFun hfin hxU d hnat z + rawOpStalkFun hfin hxU d hnat w := by
  obtain ⟨W, hW, hx, s, t, hs, ht⟩ := exists_germ_eq_pair_le hfin hxU z w
  subst hs ht
  rw [← map_add, rawOpStalkFun_germ hfin hxU d hnat W hW hx (s + t),
    rawOpStalkFun_germ hfin hxU d hnat W hW hx s,
    rawOpStalkFun_germ hfin hxU d hnat W hW hx t]
  exact (congrArg _ (map_add (d (Over.mk (homOfLE (normalization_preimage_le hfin hW)))) s t)).trans
    (map_add _ _ _)

/-- `Stacks.Curves.rawOpStalkFun` obeys the Leibniz rule, if the operator does. -/
public theorem rawOpStalkFun_mul
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} {x : X} (hxU : x ∈ U)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural)
    (hmul : ∀ (W : Over (Scheme.normalization X hfin ⁻¹ᵁ U)) (a b),
      d.unitOp W (a * b) = a * d.unitOp W b + b * d.unitOp W a)
    (z w : (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).stalk x)) :
    rawOpStalkFun hfin hxU d hnat (z * w)
      = z * rawOpStalkFun hfin hxU d hnat w + w * rawOpStalkFun hfin hxU d hnat z := by
  obtain ⟨W, hW, hx, s, t, hs, ht⟩ := exists_germ_eq_pair_le hfin hxU z w
  subst hs ht
  rw [← map_mul, rawOpStalkFun_germ hfin hxU d hnat W hW hx (s * t),
    rawOpStalkFun_germ hfin hxU d hnat W hW hx s,
    rawOpStalkFun_germ hfin hxU d hnat W hW hx t]
  exact (congrArg _ (hmul (Over.mk (homOfLE (normalization_preimage_le hfin hW))) s t)).trans
    ((map_add _ _ _).trans (congrArg₂ (· + ·) (map_mul _ _ _) (map_mul _ _ _)))

/-- **A natural Leibniz raw operator over `ν⁻¹U` acts on germs through its value at the top.**
Let `U` be an affine open of `X` containing `x`, let `d` be a raw operator on the structure sheaf
of the normalization over `ν⁻¹U` which is compatible with restriction and obeys the Leibniz rule,
and let `g` be a Leibniz additive map of the stalk `(ν_* 𝒪_{X^ν})_x` which computes the germs of
the values of `d` on the sections over `ν⁻¹U` itself. Then `g` computes the germs of the values
of `d` on the sections over `ν⁻¹W'` for *every* open `W' ≤ U` containing `x`.

By Tag 0C3B the stalk is a localization of `Γ(X^ν, ν⁻¹U)` along the germ map, and a Leibniz
additive map of a localization is determined by its values on the image of the base; the map
`Stacks.Curves.rawOpStalkFun` induced by `d` and the map `g` are two such and agree there. -/
public theorem germ_rawOp_eq_of_leibniz
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural)
    (hmul : ∀ (W : Over (Scheme.normalization X hfin ⁻¹ᵁ U)) (a b),
      d.unitOp W (a * b) = a * d.unitOp W b + b * d.unitOp W a)
    (g : (((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).stalk x) →+
      (((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).stalk x))
    (hgmul : ∀ z w, g (z * w) = z * g w + w * g z)
    (hgtop : ∀ s : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U),
      g (((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU s)
        = ((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU
          (d.unitOp (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ U))) s))
    {W' : X.Opens} (hW' : W' ≤ U) (hxW' : x ∈ W')
    (z : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ W')) :
    ((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).germ W' x hxW'
      (d.unitOp (Over.mk (homOfLE (normalization_preimage_le hfin hW'))) z)
    = g (((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).germ W' x hxW' z) := by
  let : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) :=
    ((Scheme.normalization X hfin).app U).hom.toAlgebra
  let : Algebra Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
      (((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).stalk x) :=
    (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU).hom.toAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
      (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl)
      (((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).stalk x) :=
    isLocalization_normalizationPushforwardStalk X hfin hU hxU
  have key : AddMonoidHom.mk' (rawOpStalkFun hfin hxU d hnat)
      (rawOpStalkFun_add hfin hxU d hnat) = g :=
    Stacks.DerivationExtension.eq_of_leibniz_of_localization
      (Algebra.algebraMapSubmonoid
        Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
        (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl) _ g
      (rawOpStalkFun_mul hfin hxU d hnat hmul) hgmul fun a => by
        change rawOpStalkFun hfin hxU d hnat
            (((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU a)
          = g (((Scheme.normalization X hfin).base _*
              (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU a)
        rw [rawOpStalkFun_germ hfin hxU d hnat U le_rfl hxU a, hgtop a]
        rfl
  rw [← rawOpStalkFun_germ hfin hxU d hnat W' hW' hxW' z]
  exact DFunLike.congr_fun key _

end RawOpStalk

section Agreement

variable [IsReduced X]

/-- **Two natural Leibniz raw operators over the preimages of two affine opens whose values at
the top extend the same vector field agree over the preimage of any open inside both.** Let `X`
be a reduced scheme over `k` whose quasi-compact opens have finitely many irreducible components,
let `ν : X^ν ⟶ X` be its normalization and let `D` be a vector field on `X`. Let `d` be a raw
operator on the structure sheaf of `X^ν` over the preimage of an affine open `U`, compatible with
restriction and Leibniz, whose value on `ν⁻¹U` extends `D` along `ν^♯`, and let `e` be such an
operator over the preimage of an affine open `V`. Then `d` and `e` have the same value on the
preimage of any open `W'` contained in both `U` and `V`.

This is the agreement hypothesis of `DiffOp.AgreeOnCover` for the cover of `X^ν` by the preimages
of an affine cover of `X`: reduced to the preimage of `U ⊓ V` by
`DiffOp.agreeOnCover_of_slice_eq` and
`Stacks.AlgebraicGeometry.DifferentialsAffine.rawOp_ext`, that hypothesis is an instance of this
statement. -/
public theorem rawOp_eq_of_extension_of_extension
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {hX : X ⟶ Spec (.of k)} (D : SheafDerivationOf hX)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (d : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ U))
    (hnat : d.IsNatural)
    (hmul : ∀ (W : Over (Scheme.normalization X hfin ⁻¹ᵁ U)) (a b),
      d.unitOp W (a * b) = a * d.unitOp W b + b * d.unitOp W a)
    (hdext : ∀ r : Γ(X, U),
      d.unitOp (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ U)))
          (((Scheme.normalization X hfin).app U).hom r)
        = ((Scheme.normalization X hfin).app U).hom (D.onSections r))
    (e : DiffOp.RawOp
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (SheafOfModules.unit (Scheme.normalizationScheme X hfin).ringCatSheaf)
      (Scheme.normalization X hfin ⁻¹ᵁ V))
    (hnate : e.IsNatural)
    (hmule : ∀ (W : Over (Scheme.normalization X hfin ⁻¹ᵁ V)) (a b),
      e.unitOp W (a * b) = a * e.unitOp W b + b * e.unitOp W a)
    (heext : ∀ r : Γ(X, V),
      e.unitOp (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ V)))
          (((Scheme.normalization X hfin).app V).hom r)
        = ((Scheme.normalization X hfin).app V).hom (D.onSections r))
    {W' : X.Opens} (hW'U : W' ≤ U) (hW'V : W' ≤ V)
    (hWU : Scheme.normalization X hfin ⁻¹ᵁ W' ≤ Scheme.normalization X hfin ⁻¹ᵁ U)
    (hWV : Scheme.normalization X hfin ⁻¹ᵁ W' ≤ Scheme.normalization X hfin ⁻¹ᵁ V) :
    d (Over.mk (homOfLE hWU)) = e (Over.mk (homOfLE hWV)) := by
  refine AddMonoidHom.ext fun z => section_eq_of_germ_eq hfin _ _ fun p hp => ?_
  obtain ⟨gU, hgUmul, hgUgerm, hgUalg⟩ :=
    exists_leibniz_of_extension hfin D hU (hW'U hp)
      (d (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ U))))
      (hmul (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ U)))) hdext
  obtain ⟨gV, hgVmul, hgVgerm, hgValg⟩ :=
    exists_leibniz_of_extension hfin D hV (hW'V hp)
      (e (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ V))))
      (hmule (Over.mk (CategoryStruct.id (Scheme.normalization X hfin ⁻¹ᵁ V)))) heext
  have hUV : gU = gV :=
    Stacks.AlgebraicGeometry.NormalizationQuotient.eq_of_leibniz_normalizationPushforwardStalk
      X hfin p gU gV hgUmul hgVmul fun a => by rw [hgUalg a, hgValg a]
  have h1 := germ_rawOp_eq_of_leibniz hfin hU (hW'U hp) d hnat hmul gU hgUmul hgUgerm hW'U hp z
  have h2 := germ_rawOp_eq_of_leibniz hfin hV (hW'V hp) e hnate hmule gV hgVmul hgVgerm hW'V hp z
  exact h1.trans ((DFunLike.congr_fun hUV _).trans h2.symm)

end Agreement

end Stacks.Curves

end
