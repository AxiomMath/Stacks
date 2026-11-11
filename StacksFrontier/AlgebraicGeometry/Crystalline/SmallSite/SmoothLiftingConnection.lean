module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingTwistedDifferential

/-!
# [Stacks, Tag 07MW] part (2): the canonical integrable connection on `F_Y`

Remark [Stacks, Tag 07MW] fixes a prime `p`, a divided power ring `(A, I, γ)` with `p` nilpotent
in `A`, `S = Spec A`, `S₀ = Spec(A/I)`, `Y` smooth over `S` and `X = Y ×_S S₀`
(`...SmallSite.Situation07MW`).  Part (2) asserts: for a crystal `F` in quasi-coherent
`𝒪_{X/S}`-modules, the restriction `F_Y` of `F` to the object `(X, Y, γ)` of part (1) comes endowed
with a canonical integrable connection `∇ : F_Y ⟶ F_Y ⊗_{𝒪_Y} Ω_{Y/S}`.

**This file proves part (2)**, unconditionally given the data of the remark and
`hF : F.IsQuasicoherentOnSite` (this library's spelling of "crystal in quasi-coherent modules"):
`Situation07MW.moduleWithConnection hF` is an
`AlgebraicGeometry.Scheme.Hom.ModuleWithConnection T.toBase` whose module is `F_Y`
(`moduleWithConnection_module`, by `rfl`), whose connection satisfies the Leibniz rule of
`AlgebraicGeometry.Scheme.Hom.ModuleConnection`, and whose twisted de Rham differential satisfies
`d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`, squares to zero and is `f^{-1}𝒪_S`-linear; integrability is the
vanishing of the degree-zero composite.

## The connection is the canonical one

* `moduleWithConnection_connection_d` — on every open, `∇` is the degree-zero differential of the
  de Rham complex `F ⊗ Ω^•_{X/S}` of [Stacks, Tag 07LM], restricted to `Y`, read on `s ⊗ 1`
  through [Stacks, Tag 07IZ] and `Ω^1_{Y/S} ≅ Ω_{Y/S}`;
* `moduleWithConnection_connection_d_eq_crystalConnectionCris` — for a crystal (`IsSheafCrystal F`)
  this is the restriction to `Y` of the canonical connection `...SmallSite.crystalConnectionCris`
  of [Stacks, Tag 07J6];
* `moduleWithConnection_connection_d_eq_canonical` — the same for every crystal in quasi-coherent
  modules, these being crystals by [Stacks, Tag 07IT];
* `moduleWithConnection_connection_d_affine` — over an affine open of `Y` lying over an affine
  open of `S`, `∇` is the ring-level connection `p₁^* s - p₀^* s` of [Stacks, Tag 07J6]
  (`...SmallSite.AffineConnection.ringConnection`);
* `moduleWithConnection_differential_d` — the twisted differential in degree `q` is the restriction
  to `Y` of the differential of [Stacks, Tag 07LM] in degree `q`.

## Implementation notes

The identification of the restriction of `F ⊗ Ω^q_{X/S}` to `Y` with `F_Y ⊗ Ω^q_{Y/S}` used here is
`...SmallSite.tensorFormsAmbientIso` at the comparison `Situation07MW.formsComparison`, whose value
on pure tensors is known (`x ⊗ ω ↦ x ⊗ ω`).  The library has a second identification of the same
sheaves, `...SmallSite.restrictTensorDifferentialFormsSheafIso`, through which
`...SmallSite.CrystalDeRhamSheafData.ambientD` of [Stacks, Equation 07LP] is defined; the two
are not compared here, so the differential is stated against `crystalDeRhamDifferential`
restricted to `Y` rather than against `ambientD`.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Hom
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)
  {F : SheafOfModules.{u} (structureSheaf S)} (hF : F.IsQuasicoherentOnSite)

/-- **The canonical connection on `F_Y`** relative to `Y ⟶ S`: `connectionApp`, with its Leibniz
rule `connectionApp_smul`. -/
def moduleConnection : ModuleConnection T.toBase (T.liftingModule F) where
  d U := AddMonoidHom.mk' (T.connectionApp hF U) (T.connectionApp_add hF U)
  d_restrict k s := T.connectionApp_restrict hF k s
  leibniz U b s := T.connectionApp_smul hF U b s

/-- The twisted de Rham differential `F_Y ⊗ Ω^q_{Y/S} ⟶ F_Y ⊗ Ω^{q+1}_{Y/S}` in degree `q`, as a
morphism of sheaves of `f^{-1}𝒪_S`-modules (`twistedDifferentialApp_baseScalar_smul`). -/
def twistedDifferential (q : ℕ) :
    twistedTerm T.toBase (T.liftingModule F) q ⟶
      twistedTerm T.toBase (T.liftingModule F) (q + 1) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (T.twistedDifferentialApp hF q U)
      naturality U V k := by
        ext x
        exact (T.twistedDifferentialApp_restrict hF q k x).symm }
    (fun U r x ↦ T.twistedDifferentialApp_baseScalar_smul hF q U r x)

/-- `twistedDifferential` on sections is `twistedDifferentialApp`. -/
theorem twistedDifferential_val_app (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (x : (twistedForms T.toBase (T.liftingModule F) q).val.obj U) :
    (T.twistedDifferential hF q).val.app U x = T.twistedDifferentialApp hF q U x :=
  rfl

/-- **The twisted de Rham differential of the canonical connection on `F_Y`**: the wedge pairing is
`twistedFormsWedgeSection` and the differential is `twistedDifferential`, with the Leibniz rule
`twistedDifferentialApp_twistedTmul`. -/
def twistedDeRhamDifferential : TwistedDeRhamDifferential (T.moduleConnection hF) where
  wedge q U η ω := twistedFormsWedgeSection T.toBase (T.liftingModule F) q U η ω
  wedge_add q U η η' ω := twistedFormsWedgeSection_add T.toBase (T.liftingModule F) q U η η' ω
  wedge_restrict q _ _ k η ω := twistedFormsWedgeSection_restrict T.toBase (T.liftingModule F) q k
      η ω
  wedge_tmul q U s α ω := twistedFormsWedgeSection_tmul T.toBase (T.liftingModule F) q U s α ω
  d q := T.twistedDifferential hF q
  d_tmul q U s ω := T.twistedDifferentialApp_twistedTmul hF q U s ω

/-- **The twisted de Rham sequence of `F_Y` is a complex**: consecutive differentials compose to
zero, those of the de Rham complex of [Stacks, Tag 07LM] doing so. -/
theorem twistedDeRhamDifferential_isComplex : (T.twistedDeRhamDifferential hF).IsComplex := by
  intro q
  ext U x
  exact T.twistedDifferentialApp_comp hF q U x

/-- **[Stacks, Tag 07MW] part (2): the restriction `F_Y` of a crystal in quasi-coherent
`𝒪_{X/S}`-modules to the smooth lifting `(X, Y, γ)` carries a canonical integrable connection.**
The module is `F_Y`, the connection is `moduleConnection`, the twisted de Rham differential is
`twistedDeRhamDifferential` (the restriction to `Y` of the de Rham complex of
[Stacks, Tag 07LM]), and integrability is `twistedDeRhamDifferential_isComplex` in degree zero.
That the connection is the canonical one of [Stacks, Tag 07J6] is
`moduleWithConnection_connection_d_eq_canonical`. -/
@[stacks 07MW "(2): the restriction F_Y of a crystal F in quasi-coherent O_{X/S}-modules comes \
endowed with a canonical integrable connection F_Y ⟶ F_Y ⊗ Ω_{Y/S}, the restriction of the 07J6 \
connection, with its twisted de Rham complex"]
def moduleWithConnection : ModuleWithConnection T.toBase where
  module := T.liftingModule F
  connection := T.moduleConnection hF
  differential := T.twistedDeRhamDifferential hF
  isComplex := T.twistedDeRhamDifferential_isComplex hF
  isIntegrable := (T.twistedDeRhamDifferential_isComplex hF).isIntegrable

/-- The module of `moduleWithConnection` is the restriction `F_Y` of `F` to `(X, Y, γ)`. -/
theorem moduleWithConnection_module :
    (T.moduleWithConnection hF).module = crysAmbientSchemeModules F T.crystallineThickening :=
  rfl

/-- **The connection is the degree-zero differential of [Stacks, Tag 07LM], restricted to `Y`.** -/
theorem moduleWithConnection_connection_d (U : (T.Y.Opens)ᵒᵖ) (s : (T.liftingModule F).val.obj U) :
    (T.moduleWithConnection hF).connection.d U s =
      (T.twistedFormsOneIso (F := F)).hom.val.app U
        ((T.twistedFormsRestrictionIso F (0 + 1)).hom.app U
          ((crystalDeRhamDifferential hF 0).hom.app
            (op (T.crystallineThickening.restrictOpen U.unop))
            ((T.twistedFormsRestrictionIso F 0).inv.app U
              (ULift.up (twistedTmul T.toBase (T.liftingModule F) 0 U s (T.formsOne U)))))).down :=
  rfl

/-- **For a crystal, the connection is the canonical connection `crystalConnectionCris` of
[Stacks, Tag 07J6], restricted to `Y`.** -/
theorem moduleWithConnection_connection_d_eq_crystalConnectionCris (hC : IsSheafCrystal F)
    (U : (T.Y.Opens)ᵒᵖ) (s : (T.liftingModule F).val.obj U) :
    (T.moduleWithConnection hF).connection.d U s =
      (T.twistedFormsOneIso (F := F)).hom.val.app U
        ((T.twistedFormsRestrictionIso F (0 + 1)).hom.app U
          ((crystalConnectionCris hC).hom.app (op (T.crystallineThickening.restrictOpen U.unop))
            ((tensorDifferentialFormsSheafZeroIso S F).hom.hom.app
              (op (T.crystallineThickening.restrictOpen U.unop))
              ((T.twistedFormsRestrictionIso F 0).inv.app U
                (ULift.up (twistedTmul T.toBase (T.liftingModule F) 0 U s (T.formsOne U))))))).down
                    := by
  rw [moduleWithConnection_connection_d, crystalDeRhamDifferential_zero_eq hF hC]
  rfl

/-- **The connection is the canonical connection `crystalConnectionCris` of [Stacks, Tag 07J6],
restricted to `Y`**: a crystal in quasi-coherent modules is a crystal
(`...SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`, [Stacks, Tag 07IT]), so
`moduleWithConnection_connection_d_eq_crystalConnectionCris` applies. -/
theorem moduleWithConnection_connection_d_eq_canonical
    (U : (T.Y.Opens)ᵒᵖ) (s : (T.liftingModule F).val.obj U) :
    (T.moduleWithConnection hF).connection.d U s =
      (T.twistedFormsOneIso (F := F)).hom.val.app U
        ((T.twistedFormsRestrictionIso F (0 + 1)).hom.app U
          ((crystalConnectionCris (isSheafCrystal_of_isQuasicoherentOnSite F hF)).hom.app
            (op (T.crystallineThickening.restrictOpen U.unop))
            ((tensorDifferentialFormsSheafZeroIso S F).hom.hom.app
              (op (T.crystallineThickening.restrictOpen U.unop))
              ((T.twistedFormsRestrictionIso F 0).inv.app U
                (ULift.up
                  (twistedTmul T.toBase (T.liftingModule F) 0 U s (T.formsOne U))))))).down :=
  T.moduleWithConnection_connection_d_eq_crystalConnectionCris hF
    (isSheafCrystal_of_isQuasicoherentOnSite F hF) U s

/-- **Over an affine-over-affine open the connection is the ring-level canonical connection of
[Stacks, Tag 07J6]** `s ↦ p₁^* s - p₀^* s` of the corresponding object of `Cris(X/S)`. -/
theorem moduleWithConnection_connection_d_affine {W : T.Y.Opens} (hW : IsAffineOpen W)
    [IsAffine (T.crystallineThickening.restrictOpen W).obj.thickening.target.scheme]
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V)
    (h : W ≤ T.crystallineThickening.obj.toBase.hom ⁻¹ᵁ V)
    (x : F.val.obj (op (T.crystallineThickening.restrictOpen W))) :
    (T.moduleWithConnection hF).connection.d (op W) x =
      T.connectionComparison F W (AffineConnection.ringConnection
        (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV
          h).top_le_preimage_baseOpen
        (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV
          h).isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF
          (AffineOverAffineCrystallineThickening.restrictOpen T.crystallineThickening hW hV h))
        x) :=
  T.connectionApp_affine hF hW hV h x

/-- **The twisted de Rham differential is the differential of [Stacks, Tag 07LM], restricted to
`Y`.** -/
theorem moduleWithConnection_differential_d (q : ℕ) (U : (T.Y.Opens)ᵒᵖ)
    (x : (twistedForms T.toBase (T.liftingModule F) q).val.obj U) :
    ((T.moduleWithConnection hF).differential.d q).val.app U x =
      ((T.twistedFormsRestrictionIso F (q + 1)).hom.app U
        ((crystalDeRhamDifferential hF q).hom.app
          (op (T.crystallineThickening.restrictOpen U.unop))
          ((T.twistedFormsRestrictionIso F q).inv.app U (ULift.up x)))).down :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW
