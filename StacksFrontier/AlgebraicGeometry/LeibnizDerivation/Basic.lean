module

public import StacksFrontier.AlgebraicGeometry.DiagonalDerivation.Basic

/-!
# The four derivation axioms for the conormal class of `p₂^♯ b - p₁^♯ b`

[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) builds the comparison
`Ω_{X/S} ≅ C_Δ` out of the assignment `b ↦ p₂^♯ b - p₁^♯ b`, read in the conormal sheaf of the
diagonal. This file shows that this assignment satisfies the four derivation axioms — additivity,
the Leibniz rule, vanishing on `f⁻¹𝒪_S` and compatibility with restriction — over every open of
`X`, starting from the corresponding identities of `Stacks.DiagonalDerivation.delta` in the ring
`Γ(↑Δ.coborderRange, V)`.

For an open `U` of `X`, the open `Stacks.LeibnizDerivation.chart f U` of `Δ.coborderRange` is the
intersection of the two preimages of `U` under the two projections. Its preimage under
`Δ.liftCoborder` is `U`, and every open satisfying the two containments of the tag over `U` is
contained in it (`le_chart`).

The Leibniz rule holds in the conormal sheaf with coefficients `b` and `b'` themselves. The
identity in the ideal sheaf, `deltaIdealSection_mul`, has the two different lifts `p₂^♯ b` and
`p₁^♯ b'` as coefficients; the module structure of the pushforward of the conormal sheaf along
`Δ.liftCoborder` is restriction of scalars along the structure map of that morphism, and both
lifts have the same image there, namely `b` (`restrict_app_liftSndAt`,
`restrict_app_liftFstAt`).

## Main definitions

* `Stacks.LeibnizDerivation.chart`: the canonical open of `Δ.coborderRange` over an open of `X`.
* `Stacks.LeibnizDerivation.idealSection`: the section of the ideal sheaf of a morphism named by
  a section of the structure sheaf killed by that morphism.
* `Stacks.LeibnizDerivation.deltaAt`: `p₂^♯ b - p₁^♯ b` over `chart f U`.
* `Stacks.LeibnizDerivation.deltaIdealSection`: the corresponding section of the ideal sheaf of
  the diagonal.
* `Stacks.LeibnizDerivation.cls`: **the conormal class of `p₂^♯ b - p₁^♯ b`**, a section of the
  conormal sheaf of the diagonal over `U`. This is the value of the derivation of
  [Stacks, Tag 08S2].

## Main results

* `Stacks.LeibnizDerivation.chart_preimage`: `Δ.liftCoborder ⁻¹ᵁ chart f U = U`.
* `Stacks.LeibnizDerivation.le_chart`: every admissible auxiliary open is contained in the chart.
* `Stacks.LeibnizDerivation.app_delta_eq_zero`: the difference of two retractions on sections is
  killed by the structure map over the *whole* preimage, so it names a section of the ideal
  sheaf.
* `Stacks.LeibnizDerivation.cls_add`, `cls_zero`: additivity.
* `Stacks.LeibnizDerivation.cls_mul`: **the Leibniz rule**, with coefficients `b` and `b'`.
* `Stacks.LeibnizDerivation.cls_appLE_eq_zero`: vanishing on sections pulled back from `S`.
* `Stacks.LeibnizDerivation.cls_restrict`: compatibility with restriction.

## Implementation notes

`Γ(Y, V)` is the carrier of a `CommRingCat` object, while the module instances on the sections
of a sheaf of modules on `Y` are stated at the carrier of the corresponding `RingCat` object;
and the sections over `V` of a pushforward are the sections of the source over the preimage of
`V`. Each pair is definitionally equal and none is syntactically equal, and instance search
does not cross any of the gaps: `r • x` for `r : Γ(Y, V)` fails to synthesize `HSMul`. So the
scalars and the values pass through reducible identity abbreviations — `toXRing`, `idealValue`,
`idealSmul`, `quotientValue`, `clsValue` — whose declared result types are the ones the
instances are stated at.

The same gap makes `rw` fail in several places: `rw` type-checks its rewritten target at
`implicit` transparency, where the two spellings do not unify. The proofs that compose a step
across such a gap (`cls_add`, `cls_zero`, `cls_mul`) are therefore terms, which elaborate at
default transparency.

`AlgebraicGeometry.Scheme.Hom.appLE` carries a containment proof mentioning the morphism, so an
equation between morphisms cannot be rewritten inside it; `Stacks.DiagonalConormal.appLE_congr`
is the transport, and `Stacks.DiagonalConormal.appLE_retraction` is used in place of `rw`.

The ideal sheaf of Stacks Tag 01C2 is `Stacks.ClosedImmersion.idealSheaf`
(`StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs`); the conormal sheaf of Stacks Tag 01R2 is
`Stacks.Conormal.conormalSheaf` and the quotient map of Stacks Tag 01R3 is
`Stacks.Conormal.conormalQuotientMap`
(`StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison`).

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.LeibnizDerivation

/-! ### Spellings -/

/-- `Γ(Y, V)` in the `RingCat` spelling at which the module structures on the sections of a
sheaf of modules on `Y` are stated. -/
noncomputable abbrev xRing {Y : Scheme.{u}} (V : Y.Opens) : RingCat.{u} :=
  (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace).obj.obj (.op V)

/-- A section of the structure sheaf, read as a scalar for a sheaf of modules. This is the
identity map; only its declared type differs. -/
abbrev toXRing {Y : Scheme.{u}} {V : Y.Opens} (r : Γ(Y, V)) : xRing V := r

/-! ### The difference of two retractions is killed by the structure map -/

/-- **`delta b` is killed by the map on sections induced by `g`, over the whole preimage
`g ⁻¹ᵁ W`.** Compare `Stacks.DiagonalDerivation.app_delta_eq_zero`, which states this for an
`appLE` down to an open contained in `g ⁻¹ᵁ W`. -/
theorem app_delta_eq_zero {Z P : Scheme.{u}} (g : Z ⟶ P) {r₁ r₂ : P ⟶ Z}
    (hr₁ : g ≫ r₁ = 𝟙 Z) (hr₂ : g ≫ r₂ = 𝟙 Z) (U : Z.Opens) (W : P.Opens)
    (h₁ : W ≤ r₁ ⁻¹ᵁ U) (h₂ : W ≤ r₂ ⁻¹ᵁ U) (b : Γ(Z, U)) :
    (g.app W).hom (Stacks.DiagonalDerivation.delta r₁ r₂ U W h₁ h₂ b) = 0 := by
  have hWU : g ⁻¹ᵁ W ≤ U := by
    have h : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (r₁ ⁻¹ᵁ U) := g.preimage_mono h₁
    have e : g ⁻¹ᵁ (r₁ ⁻¹ᵁ U) = U := congrArg (fun m : Z ⟶ Z => m ⁻¹ᵁ U) hr₁
    exact e ▸ h
  have key : ∀ (r : P ⟶ Z) (h : W ≤ r ⁻¹ᵁ U), g ≫ r = 𝟙 Z →
      (g.app W).hom ((r.appLE U W h).hom b) =
        (Z.presheaf.map (homOfLE hWU).op).hom b := by
    intro r h hgr
    have happ : Scheme.Hom.app g W = g.appLE W (g ⁻¹ᵁ W) le_rfl := Scheme.Hom.app_eq_appLE _
    refine Eq.trans (congr($(happ) ((r.appLE U W h).hom b))) ?_
    exact Stacks.DiagonalConormal.appLE_retraction hgr U W (g ⁻¹ᵁ W) h le_rfl hWU b
  rw [Stacks.DiagonalDerivation.delta_eq, map_sub, key r₂ h₂ hr₂, key r₁ h₁ hr₁, sub_self]

/-! ### The section of the ideal sheaf named by a section of the kernel -/

/-- The section of the ideal sheaf of `k` whose image in the structure sheaf is a given section
killed by `k` on sections. -/
noncomputable def idealSection {A B : Scheme.{u}} (k : A ⟶ B) (O : B.Opens) (r : Γ(B, O))
    (hr : (k.app O).hom r = 0) :
    (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op O) :=
  ((Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff k O r).2 hr).choose

/-- The characterizing property of `idealSection`. -/
theorem ι_idealSection {A B : Scheme.{u}} (k : A ⟶ B) (O : B.Opens) (r : Γ(B, O))
    (hr : (k.app O).hom r = 0) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app (.op O) (idealSection k O r hr) = r :=
  ((Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff k O r).2 hr).choose_spec

/-- A section of the ideal sheaf is `idealSection` of its image. -/
theorem eq_idealSection {A B : Scheme.{u}} (k : A ⟶ B) (O : B.Opens) (r : Γ(B, O))
    (hr : (k.app O).hom r = 0)
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op O))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom k.toLRSHom.toShHom))).val.app (.op O) x = r) :
    x = idealSection k O r hr :=
  Stacks.Conormal.Locality.idealSheaf_section_injective k O
    (hx.trans (ι_idealSection k O r hr).symm)

/-! ### The canonical open of the coborder neighbourhood attached to an open of the source -/

section Chart

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The canonical open of the coborder neighbourhood of the diagonal over an open `U` of
`X`.** It is the intersection of the two preimages of `U` under the two projections, read on
the coborder neighbourhood. It is the largest open `V` of the coborder neighbourhood satisfying
`Δ.liftCoborder ⁻¹ᵁ V = U` together with the two containments of [Stacks, Tag 08S2]
(`chart_preimage`, `le_chart`). -/
noncomputable def chart (U : X.Opens) : (pullback.diagonal f).coborderRange.toScheme.Opens :=
  (((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f) ⁻¹ᵁ U) ⊓
    (((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f) ⁻¹ᵁ U)

/-- `chart f U` is contained in the preimage of `U` under the first projection. -/
theorem chart_le_fst (U : X.Opens) :
    chart f U ≤ ((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f) ⁻¹ᵁ U :=
  inf_le_left

/-- `chart f U` is contained in the preimage of `U` under the second projection. -/
theorem chart_le_snd (U : X.Opens) :
    chart f U ≤ ((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f) ⁻¹ᵁ U :=
  inf_le_right

/-- **The preimage of `chart f U` under the canonical closed factorization of the diagonal is
`U` itself.** -/
theorem chart_preimage (U : X.Opens) :
    (pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U = U := by
  have key : ∀ p : (pullback.diagonal f).coborderRange.toScheme ⟶ X,
      (pullback.diagonal f).liftCoborder ≫ p = 𝟙 X →
        (pullback.diagonal f).liftCoborder ⁻¹ᵁ (p ⁻¹ᵁ U) = U :=
    fun p hp => congrArg (fun m : X ⟶ X => m ⁻¹ᵁ U) hp
  rw [chart, Scheme.Hom.preimage_inf, key _ (Stacks.DiagonalConormal.liftCoborder_comp_fst f),
    key _ (Stacks.DiagonalConormal.liftCoborder_comp_snd f), inf_idem]

/-- `U` is contained in the preimage of `chart f U`. -/
theorem le_chart_preimage (U : X.Opens) :
    U ≤ (pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U :=
  (chart_preimage f U).ge

/-- The preimage of `chart f U` is contained in `U`. -/
theorem chart_preimage_le (U : X.Opens) :
    (pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U ≤ U :=
  (chart_preimage f U).le

/-- **`chart f U` is the largest admissible open.** Any open `V` of the coborder neighbourhood
satisfying the two containments of [Stacks, Tag 08S2] over `U` is contained in `chart f U`. -/
theorem le_chart (U : X.Opens) (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤ (pullback.fst f f) ⁻¹ᵁ U)
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤ (pullback.snd f f) ⁻¹ᵁ U) :
    V ≤ chart f U :=
  le_inf (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₁)
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₂)

/-- `chart` is monotone. -/
theorem chart_mono {U U' : X.Opens} (h : U ≤ U') : chart f U ≤ chart f U' :=
  inf_le_inf (Scheme.Hom.preimage_mono _ h) (Scheme.Hom.preimage_mono _ h)

end Chart

/-! ### The conormal class of `p₂^♯ b - p₁^♯ b` -/

section Class

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`p₁^♯ b` as a section of `𝒪_{↑Δ.coborderRange}` over `chart f U`.** -/
noncomputable def liftFstAt (U : X.Opens) (b : Γ(X, U)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, chart f U) :=
  ((((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f).appLE U (chart f U)
    (chart_le_fst f U)).hom) b

/-- **`p₂^♯ b` as a section of `𝒪_{↑Δ.coborderRange}` over `chart f U`.** -/
noncomputable def liftSndAt (U : X.Opens) (b : Γ(X, U)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, chart f U) :=
  ((((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f).appLE U (chart f U)
    (chart_le_snd f U)).hom) b

/-- **`p₂^♯ b - p₁^♯ b` over the canonical open `chart f U`.** -/
noncomputable def deltaAt (U : X.Opens) (b : Γ(X, U)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, chart f U) :=
  Stacks.DiagonalDerivation.delta ((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f)
    ((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f) U (chart f U)
    (chart_le_fst f U) (chart_le_snd f U) b

/-- `deltaAt` is the difference of the two sections `p₁^♯ b` and `p₂^♯ b`. -/
theorem deltaAt_eq (U : X.Opens) (b : Γ(X, U)) :
    deltaAt f U b = liftSndAt f U b - liftFstAt f U b :=
  rfl

/-- A pullback along a retraction `p` of `Δ.liftCoborder` restricts to the original section. -/
private theorem restrict_app_appLE {p : (pullback.diagonal f).coborderRange.toScheme ⟶ X}
    (hp : (pullback.diagonal f).liftCoborder ≫ p = 𝟙 X) (U : X.Opens) (hU : chart f U ≤ p ⁻¹ᵁ U)
    (b : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_chart_preimage f U)).op).hom
        ((((pullback.diagonal f).liftCoborder.app (chart f U)).hom)
          ((p.appLE U (chart f U) hU).hom b)) = b := by
  have h : (((pullback.diagonal f).liftCoborder.app (chart f U)).hom)
      ((p.appLE U (chart f U) hU).hom b) =
      (X.presheaf.map (homOfLE (chart_preimage_le f U)).op).hom b := by
    refine Eq.trans (congr($(Scheme.Hom.app_eq_appLE
      (pullback.diagonal f).liftCoborder) ((p.appLE U (chart f U) hU).hom b))) ?_
    exact Stacks.DiagonalConormal.appLE_retraction hp U (chart f U)
      ((pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U) hU le_rfl (chart_preimage_le f U) b
  rw [h, ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  exact Stacks.DiagonalConormal.presheaf_map_self U le_rfl b

/-- **`p₂^♯ b` restricts to `b`.** The structure map of the canonical closed factorization of
the diagonal sends `p₂^♯ b` to the restriction of `b` to `Δ.liftCoborder ⁻¹ᵁ chart f U`, whose
restriction to `U` — which is the same open — is `b`. -/
theorem restrict_app_liftSndAt (U : X.Opens) (b : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_chart_preimage f U)).op).hom
        ((((pullback.diagonal f).liftCoborder.app (chart f U)).hom) (liftSndAt f U b)) = b :=
  restrict_app_appLE f (Stacks.DiagonalConormal.liftCoborder_comp_snd f) U _ b

/-- `p₁^♯ b` also restricts to `b`; see `restrict_app_liftSndAt`. -/
theorem restrict_app_liftFstAt (U : X.Opens) (b : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_chart_preimage f U)).op).hom
        ((((pullback.diagonal f).liftCoborder.app (chart f U)).hom) (liftFstAt f U b)) = b :=
  restrict_app_appLE f (Stacks.DiagonalConormal.liftCoborder_comp_fst f) U _ b

/-- **`p₂^♯ b - p₁^♯ b` is killed by the structure map of the canonical closed factorization of
the diagonal**, over the whole of `chart f U`. -/
theorem app_deltaAt_eq_zero (U : X.Opens) (b : Γ(X, U)) :
    (((pullback.diagonal f).liftCoborder.app (chart f U)).hom) (deltaAt f U b) = 0 :=
  app_delta_eq_zero (pullback.diagonal f).liftCoborder
    (Stacks.DiagonalConormal.liftCoborder_comp_fst f)
    (Stacks.DiagonalConormal.liftCoborder_comp_snd f) U (chart f U)
    (chart_le_fst f U) (chart_le_snd f U) b

/-- **The section of the ideal sheaf of the diagonal named by `p₂^♯ b - p₁^♯ b`.** -/
noncomputable def deltaIdealSection (U : X.Opens) (b : Γ(X, U)) :
    (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op (chart f U)) :=
  idealSection (pullback.diagonal f).liftCoborder (chart f U) (deltaAt f U b)
    (app_deltaAt_eq_zero f U b)

/-- The characterizing property of `deltaIdealSection`. -/
theorem ι_deltaIdealSection (U : X.Opens) (b : Γ(X, U)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op (chart f U))
      (deltaIdealSection f U b) = deltaAt f U b :=
  ι_idealSection _ _ _ _

/-- The canonical quotient map from the ideal sheaf of the diagonal to the pushforward of its
conormal sheaf, at the defining closed factorization. -/
noncomputable abbrev quotientMap :
    Stacks.ClosedImmersion.idealSheaf
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom ⟶
      (modulePushforward (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).obj
        (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) :=
  Stacks.Conormal.conormalQuotientMap (pullback.diagonal f)
    (pullback.diagonal f).coborderRange (pullback.diagonal f).liftCoborder
    (pullback.diagonal f).liftCoborder_ι

/-- **The conormal class of `p₂^♯ b - p₁^♯ b`.** This is the value of the canonical derivation
of [Stacks, Tag 08S2] on a section `b` of `𝒪_X` over `U`: push the ideal section named by
`p₂^♯ b - p₁^♯ b` over `chart f U` into the conormal sheaf, and read the result over `U`, which
is the preimage of `chart f U`. -/
noncomputable def cls (U : X.Opens) (b : Γ(X, U)) :
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) :=
  ((Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.map
      (homOfLE (le_chart_preimage f U)).op).hom
    (((quotientMap f).val.app (.op (chart f U))).hom (deltaIdealSection f U b))

/-- The restriction map of the conormal sheaf from `chart f U`'s preimage down to `U`, as a
linear map. -/
noncomputable abbrev clsRestrict (U : X.Opens) :=
  ((Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.map
    (homOfLE (le_chart_preimage f U)).op).hom

/-- The canonical quotient map on sections over `chart f U`, as a linear map. -/
noncomputable abbrev quotientApp (V : (pullback.diagonal f).coborderRange.toScheme.Opens) :=
  ((quotientMap f).val.app (.op V)).hom

/-- `cls` written through the two named linear maps. -/
theorem cls_eq (U : X.Opens) (b : Γ(X, U)) :
    cls f U b =
      clsRestrict f U (quotientApp f (chart f U) (deltaIdealSection f U b)) :=
  rfl

/-! ### Additivity -/

/-- The inclusion of the ideal sheaf of the diagonal into the structure sheaf, on sections over
`chart f U`, as a linear map. -/
noncomputable abbrev idealι (V : (pullback.diagonal f).coborderRange.toScheme.Opens) :=
  ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
    (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V)).hom

/-- `deltaAt` sends `0` to `0`. -/
theorem deltaAt_zero (U : X.Opens) : deltaAt f U 0 = 0 :=
  Stacks.DiagonalDerivation.delta_zero _ _ _ _ _ _

/-- `deltaAt` is additive. -/
theorem deltaAt_add (U : X.Opens) (b b' : Γ(X, U)) :
    deltaAt f U (b + b') = deltaAt f U b + deltaAt f U b' :=
  Stacks.DiagonalDerivation.delta_add _ _ _ _ _ _ b b'

/-- `deltaIdealSection` is additive. -/
theorem deltaIdealSection_add (U : X.Opens) (b b' : Γ(X, U)) :
    deltaIdealSection f U (b + b') = deltaIdealSection f U b + deltaIdealSection f U b' := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder (chart f U) ?_
  refine (ι_deltaIdealSection f U (b + b')).trans ?_
  refine (deltaAt_add f U b b').trans ?_
  refine Eq.trans (congrArg₂ (· + ·) (ι_deltaIdealSection f U b).symm
    (ι_deltaIdealSection f U b').symm) ?_
  exact (map_add (idealι f (chart f U)) (deltaIdealSection f U b)
    (deltaIdealSection f U b')).symm

/-- `deltaIdealSection` kills `0`. -/
theorem deltaIdealSection_zero (U : X.Opens) : deltaIdealSection f U 0 = 0 := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder (chart f U) ?_
  refine (ι_deltaIdealSection f U 0).trans ?_
  exact (deltaAt_zero f U).trans (map_zero (idealι f (chart f U))).symm

/-- **The conormal class is additive.** -/
theorem cls_add (U : X.Opens) (b b' : Γ(X, U)) :
    cls f U (b + b') = cls f U b + cls f U b' :=
  have h : quotientApp f (chart f U) (deltaIdealSection f U (b + b')) =
      quotientApp f (chart f U) (deltaIdealSection f U b) +
        quotientApp f (chart f U) (deltaIdealSection f U b') :=
    (congrArg (quotientApp f (chart f U)) (deltaIdealSection_add f U b b')).trans
      (map_add (quotientApp f (chart f U)) _ _)
  (congrArg (clsRestrict f U) h).trans (map_add (clsRestrict f U) _ _)

/-- **The conormal class of `0` is `0`.** -/
theorem cls_zero (U : X.Opens) : cls f U 0 = 0 :=
  have h : quotientApp f (chart f U) (deltaIdealSection f U 0) = 0 :=
    (congrArg (quotientApp f (chart f U)) (deltaIdealSection_zero f U)).trans
      (map_zero (quotientApp f (chart f U)))
  (congrArg (clsRestrict f U) h).trans (map_zero (clsRestrict f U))

/-! ### The Leibniz identity -/

/-- The image of a section of the ideal sheaf in the structure sheaf, declared at the `Γ`
spelling so that the ring operations of `Γ(↑Δ.coborderRange, V)` are available on it. -/
noncomputable abbrev idealValue (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V)) :
    Γ((pullback.diagonal f).coborderRange.toScheme, V) :=
  idealι f V x

/-- A section of `𝒪_{↑Δ.coborderRange}` acting on a section of the ideal sheaf of the
diagonal. -/
noncomputable abbrev idealSmul (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (r : Γ((pullback.diagonal f).coborderRange.toScheme, V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V)) :
    (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V) :=
  toXRing r • x

/-- The value of the quotient map, declared at the conormal-sheaf spelling. -/
noncomputable abbrev quotientValue (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V)) :
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj
      (.op ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :=
  quotientApp f V x

/-- The restriction of a conormal section from `Δ.liftCoborder ⁻¹ᵁ chart f U` down to `U`,
declared at the conormal-sheaf spelling. -/
noncomputable abbrev clsValue (U : X.Opens)
    (z : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj
      (.op ((pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U))) :
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) :=
  clsRestrict f U z

/-- The inclusion of the ideal sheaf into the structure sheaf is linear: a scalar comes out as
a product of sections. -/
theorem idealValue_idealSmul (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (r : Γ((pullback.diagonal f).coborderRange.toScheme, V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V)) :
    idealValue f V (idealSmul f V r x) = r * idealValue f V x :=
  map_smul (idealι f V) (toXRing r) x

/-- **The quotient map is linear, and the scalars of its target are read through the structure
map of the diagonal's closed factorization.** The target is the pushforward of the conormal
sheaf, whose module structure is restriction of scalars along that map, so a scalar
`r : Γ(↑Δ.coborderRange, V)` acts as the section `Δ.liftCoborder^♯ r` of `𝒪_X`. -/
theorem quotientValue_idealSmul (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (r : Γ((pullback.diagonal f).coborderRange.toScheme, V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V)) :
    quotientValue f V (idealSmul f V r x) =
      toXRing ((((pullback.diagonal f).liftCoborder.app V).hom) r) • quotientValue f V x :=
  map_smul (quotientApp f V) (toXRing r) x

/-- The restriction maps of the conormal sheaf are semilinear. -/
theorem clsValue_smul (U : X.Opens)
    (t : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U))
    (z : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj
      (.op ((pullback.diagonal f).liftCoborder ⁻¹ᵁ chart f U))) :
    clsValue f U (toXRing t • z) =
      toXRing ((X.presheaf.map (homOfLE (le_chart_preimage f U)).op).hom t) • clsValue f U z :=
  PresheafOfModules.map_smul _ _ (toXRing t) z

/-- `idealValue` of `deltaIdealSection` is `deltaAt`. -/
theorem idealValue_deltaIdealSection (U : X.Opens) (b : Γ(X, U)) :
    idealValue f (chart f U) (deltaIdealSection f U b) = deltaAt f U b :=
  ι_deltaIdealSection f U b

/-- **The exact Leibniz identity for `deltaAt`**:
`δ(b b') = p₂^♯ b · δ(b') + p₁^♯ b' · δ(b)`. -/
theorem deltaAt_mul (U : X.Opens) (b b' : Γ(X, U)) :
    deltaAt f U (b * b') =
      liftSndAt f U b * deltaAt f U b' + liftFstAt f U b' * deltaAt f U b :=
  Stacks.DiagonalDerivation.delta_mul _ _ _ _ _ _ b b'

/-- **The Leibniz identity in the ideal sheaf of the diagonal**, with the lifts `p₂^♯ b` and
`p₁^♯ b'` as coefficients. -/
theorem deltaIdealSection_mul (U : X.Opens) (b b' : Γ(X, U)) :
    deltaIdealSection f U (b * b') =
      idealSmul f (chart f U) (liftSndAt f U b) (deltaIdealSection f U b') +
        idealSmul f (chart f U) (liftFstAt f U b') (deltaIdealSection f U b) := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder (chart f U) ?_
  refine Eq.trans ((idealValue_deltaIdealSection f U (b * b')).trans
    (deltaAt_mul f U b b')) ?_
  refine Eq.trans ?_ (map_add (idealι f (chart f U))
    (idealSmul f (chart f U) (liftSndAt f U b) (deltaIdealSection f U b'))
    (idealSmul f (chart f U) (liftFstAt f U b') (deltaIdealSection f U b))).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Eq.trans (congrArg (liftSndAt f U b * ·)
      (idealValue_deltaIdealSection f U b').symm)
      (idealValue_idealSmul f (chart f U) (liftSndAt f U b) (deltaIdealSection f U b')).symm
  · exact Eq.trans (congrArg (liftFstAt f U b' * ·)
      (idealValue_deltaIdealSection f U b).symm)
      (idealValue_idealSmul f (chart f U) (liftFstAt f U b') (deltaIdealSection f U b)).symm

/-- **The Leibniz identity for the conormal class**, with the coefficients `b` and `b'`
themselves: `δ(b b') = b · δ(b') + b' · δ(b)`. -/
theorem cls_mul (U : X.Opens) (b b' : Γ(X, U)) :
    cls f U (b * b') = toXRing b • cls f U b' + toXRing b' • cls f U b := by
  have hq : quotientValue f (chart f U) (deltaIdealSection f U (b * b')) =
      toXRing ((((pullback.diagonal f).liftCoborder.app (chart f U)).hom) (liftSndAt f U b)) •
          quotientValue f (chart f U) (deltaIdealSection f U b') +
        toXRing ((((pullback.diagonal f).liftCoborder.app (chart f U)).hom)
            (liftFstAt f U b')) •
          quotientValue f (chart f U) (deltaIdealSection f U b) := by
    refine Eq.trans (congrArg (quotientApp f (chart f U))
      (deltaIdealSection_mul f U b b')) ?_
    refine Eq.trans (map_add (quotientApp f (chart f U)) _ _) ?_
    exact congrArg₂ (· + ·)
      (quotientValue_idealSmul f (chart f U) (liftSndAt f U b) (deltaIdealSection f U b'))
      (quotientValue_idealSmul f (chart f U) (liftFstAt f U b') (deltaIdealSection f U b))
  refine Eq.trans (congrArg (clsRestrict f U) hq) ?_
  refine Eq.trans (map_add (clsRestrict f U) _ _) ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans (clsValue_smul f U _ _) ?_
    exact congrArg (fun t : Γ(X, U) => toXRing t • cls f U b')
      (restrict_app_liftSndAt f U b)
  · refine Eq.trans (clsValue_smul f U _ _) ?_
    exact congrArg (fun t : Γ(X, U) => toXRing t • cls f U b)
      (restrict_app_liftFstAt f U b')

/-! ### Vanishing on sections pulled back from the base -/

/-- **`p₂^♯ b - p₁^♯ b` vanishes on sections pulled back from `S`.** -/
theorem deltaAt_appLE_eq_zero (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (a : Γ(S, V)) :
    deltaAt f U ((f.appLE V U hUV).hom a) = 0 :=
  Stacks.DiagonalDerivation.delta_appLE_eq_zero _ _ _ _ _ _ f
    (by rw [Category.assoc, Category.assoc, pullback.condition]) V hUV a

/-- The ideal section of a pullback from `S` is zero. -/
theorem deltaIdealSection_appLE_eq_zero (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (a : Γ(S, V)) : deltaIdealSection f U ((f.appLE V U hUV).hom a) = 0 := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder (chart f U) ?_
  refine Eq.trans (idealValue_deltaIdealSection f U _) ?_
  exact (deltaAt_appLE_eq_zero f V U hUV a).trans (map_zero (idealι f (chart f U))).symm

/-- **The conormal class vanishes on sections pulled back from `S`.** This is the third
derivation axiom. -/
theorem cls_appLE_eq_zero (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (a : Γ(S, V)) :
    cls f U ((f.appLE V U hUV).hom a) = 0 :=
  have h : quotientApp f (chart f U)
      (deltaIdealSection f U ((f.appLE V U hUV).hom a)) = 0 :=
    (congrArg (quotientApp f (chart f U))
      (deltaIdealSection_appLE_eq_zero f V U hUV a)).trans
      (map_zero (quotientApp f (chart f U)))
  (congrArg (clsRestrict f U) h).trans (map_zero (clsRestrict f U))

/-! ### Compatibility with restriction -/

/-- `deltaAt` commutes with restriction, the charts being monotone. -/
theorem deltaAt_restrict {U U' : X.Opens} (h : U' ≤ U) (b : Γ(X, U)) :
    ((pullback.diagonal f).coborderRange.toScheme.presheaf.map
        (homOfLE (chart_mono f h)).op).hom (deltaAt f U b) =
      deltaAt f U' ((X.presheaf.map (homOfLE h).op).hom b) :=
  Stacks.DiagonalDerivation.delta_restrict _ _ _ _ _ _ U' h (chart f U') (chart_mono f h) _ _ b

/-- `deltaIdealSection` commutes with restriction. -/
theorem deltaIdealSection_restrict {U U' : X.Opens} (h : U' ≤ U) (b : Γ(X, U)) :
    (Stacks.ClosedImmersion.idealSheaf
          (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (chart_mono f h)).op (deltaIdealSection f U b) =
      deltaIdealSection f U' ((X.presheaf.map (homOfLE h).op).hom b) := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder (chart f U') ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val
    (homOfLE (chart_mono f h)).op (deltaIdealSection f U b)) ?_
  refine Eq.trans (Stacks.Conormal.Locality.unitModule_val_map (chart_mono f h) _) ?_
  refine Eq.trans (congrArg
    (((pullback.diagonal f).coborderRange.toScheme.presheaf.map
      (homOfLE (chart_mono f h)).op).hom) (idealValue_deltaIdealSection f U b)) ?_
  exact (deltaAt_restrict f h b).trans (idealValue_deltaIdealSection f U' _).symm

/-- **The conormal class commutes with restriction.** This is the fourth derivation axiom. -/
theorem cls_restrict {U U' : X.Opens} (h : U' ≤ U) (b : Γ(X, U)) :
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.map (homOfLE h).op (cls f U b) =
      cls f U' ((X.presheaf.map (homOfLE h).op).hom b) := by
  have hhom : (homOfLE (le_chart_preimage f U)).op ≫ (homOfLE h).op =
      (homOfLE ((pullback.diagonal f).liftCoborder.preimage_mono (chart_mono f h))).op ≫
        (homOfLE (le_chart_preimage f U')).op := rfl
  refine Eq.trans (PresheafOfModules.map_comp_apply _ (homOfLE (le_chart_preimage f U)).op
    (homOfLE h).op (quotientValue f (chart f U) (deltaIdealSection f U b))).symm ?_
  refine Eq.trans (PresheafOfModules.congr_map_apply _ hhom
    (quotientValue f (chart f U) (deltaIdealSection f U b))) ?_
  refine Eq.trans (PresheafOfModules.map_comp_apply _
    (homOfLE ((pullback.diagonal f).liftCoborder.preimage_mono (chart_mono f h))).op
    (homOfLE (le_chart_preimage f U')).op
    (quotientValue f (chart f U) (deltaIdealSection f U b))) ?_
  refine congrArg (clsRestrict f U') ?_
  refine Eq.trans (Stacks.Conormal.Locality.conormalQuotientMap_restrict
    (pullback.diagonal f) (pullback.diagonal f).coborderRange
    (pullback.diagonal f).liftCoborder (pullback.diagonal f).liftCoborder_ι
    (chart_mono f h) (deltaIdealSection f U b)) ?_
  exact congrArg (quotientApp f (chart f U')) (deltaIdealSection_restrict f h b)

end Class

end Stacks.LeibnizDerivation

end
