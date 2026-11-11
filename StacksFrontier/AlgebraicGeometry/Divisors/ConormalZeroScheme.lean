module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist

/-!
# The conormal sheaf of the zero scheme of a regular section

Let `L` be an invertible module on a scheme `X`, let `s` be a regular global section of `L`
([Stacks, Tag 01WY]) and let `i : Z ⟶ X` be the inclusion of its zero scheme
([Stacks, Tag 02OQ]). The ideal sheaf `ℐ` of `Z` is the image of multiplication by `s`, so it is
isomorphic to `L^∨`, and the conormal sheaf `𝒞_{Z/X} = i^* ℐ` of [Stacks, Tag 01R2] is

`𝒞_{Z/X} ≅ i^*(L^∨)`.

On `𝐏ⁿ` and for a hypersurface of degree `d` this reads `𝒞_{Z/𝐏ⁿ} ≅ i^* 𝒪(-d)`.

The statement is given in two forms. The first takes the dual to be any invertible `M` together
with a trivialization `M ⊗ L ≅ 𝒪_X`, which is the form a twisting sheaf provides
(`𝒪(-d) ⊗ 𝒪(d) ≅ 𝒪`); the second uses the dual
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L` itself.

## Main definitions

* `AlgebraicGeometry.conormalSheafIsoPullbackIdealSheafOfIsClosedImmersion`: for a closed
  immersion `i : Z ⟶ X`, the conormal sheaf of `i` is `i^*` of the ideal sheaf of `i`, the kernel
  of `𝒪_X ⟶ i_* 𝒪_Z`.
* `AlgebraicGeometry.idealSheafIsoOfShortExact`: a short exact sequence
  `0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_Z ⟶ 0` ending in the canonical map identifies `M` with that ideal sheaf.
* `AlgebraicGeometry.conormalSheafZeroSchemeIso`: **`𝒞_{Z(s)/X} ≅ i^* M`** for invertible `M`
  with `M ⊗ L ≅ 𝒪_X`.
* `AlgebraicGeometry.conormalShortComplexX₁ZeroSchemeIso`: the same, with the conormal sheaf
  spelled as the first term of the conormal sequence
  `Stacks.ConormalSequenceRight.conormalShortComplex`.
* `AlgebraicGeometry.conormalSheafZeroSchemeIsoDual` and
  `AlgebraicGeometry.conormalSheafZeroSchemeIsoDualOfIsRegularSection`:
  **`𝒞_{Z(s)/X} ≅ i^*(L^∨)`**.

## Main results

* `AlgebraicGeometry.shortExact_tensorSection_unitToPushforwardUnit`: for a regular section and
  `M ⊗ L ≅ 𝒪_X`, the sequence `0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0` is short exact with second map
  the canonical map of structure sheaves. This sharpens
  `AlgebraicGeometry.exists_shortExact_zeroScheme_unit_of_isRegularSection`, which does not
  name its second map.

## Implementation notes

The conormal sheaf of the library (`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf`,
definitionally the first term of `Stacks.ConormalSequenceRight.conormalShortComplex`) is formed
on the open `i.coborderRange` through the closed factor `i.liftCoborder`. For a closed immersion
that open is everything, and `X ⟶ i.coborderRange` (`AlgebraicGeometry.toCoborderRange`) is an
open immersion through which `i` factors as `i.liftCoborder`;
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` then moves the conormal sheaf to `i^*` of the
ideal sheaf of `i` on `X` itself.

The ideal sheaf is the categorical kernel of `𝒪_X ⟶ i_* 𝒪_Z`. The twisted zero-scheme sequence
of [Stacks, Tag 0C6K] (`AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection`) ends
in the unit `M ⊗ L ⟶ i_* i^*(M ⊗ L)`; transporting it along `M ⊗ L ≅ 𝒪_X` and
`i^* 𝒪_X ≅ 𝒪_Z` turns that unit into the canonical map
(`AlgebraicGeometry.unit_app_comp_pushforward_map_pullbackUnitIso`), and the kernel half of the
short exact sequence is the identification `M ≅ ℐ`. The dual form uses instead
`AlgebraicGeometry.isIso_zeroSchemeIdealModuleHom`, `L^∨ ≅ ℐ`.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **The coborder range of a closed immersion is everything**: a closed immersion is closed in
`X` itself, so `⊤` is one of the opens in which its image is closed. -/
theorem top_le_coborderRange_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : ⊤ ≤ i.coborderRange := by
  have : IsClosedImmersion (i ≫ X.topIso.inv) := inferInstance
  exact Stacks.Conormal.le_coborderRange_of_comp_eq i ⊤ (i ≫ X.topIso.inv)
    (by rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id])

/-- For a closed immersion `i : Z ⟶ X`, the open immersion `X ⟶ i.coborderRange` through which
`i` factors as its closed factor `i.liftCoborder` (`comp_toCoborderRange`). -/
def toCoborderRange {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    X ⟶ i.coborderRange.toScheme :=
  X.topIso.inv ≫ X.homOfLE (top_le_coborderRange_of_isClosedImmersion i)

/-- `toCoborderRange i` is an open immersion, being an isomorphism followed by the inclusion of
an open. -/
instance isOpenImmersion_toCoborderRange {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsOpenImmersion (toCoborderRange i) := by
  unfold toCoborderRange; infer_instance

/-- A closed immersion followed by `toCoborderRange` is its canonical closed factor
`i.liftCoborder`. -/
theorem comp_toCoborderRange {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    i ≫ toCoborderRange i = i.liftCoborder := by
  refine (cancel_mono i.coborderRange.ι).1 ?_
  rw [Scheme.Hom.liftCoborder_ι, toCoborderRange, Category.assoc, Category.assoc,
    Scheme.homOfLE_ι, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]

/-- **The conormal sheaf of a closed immersion is the pullback of its ideal sheaf.** For a closed
immersion `i : Z ⟶ X`, `𝒞_{Z/X}` — defined on `i.coborderRange` — is `i^* ℐ` for the ideal sheaf
`ℐ = ker(𝒪_X ⟶ i_* 𝒪_Z)` on `X`. -/
def conormalSheafIsoPullbackIdealSheafOfIsClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i ≅
      (modulePullback i.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) :=
  Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i ≪≫
    Stacks.Conormal.pullbackIdealSheafIsoOfCompEq i (toCoborderRange i) i.liftCoborder
      (comp_toCoborderRange i)

variable (X : Scheme.{u}) (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
  (hreg : ∀ U : X.Opens, Function.Injective fun r : Γ(X, U) =>
    r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)

/-- **The conormal sheaf of the zero scheme of a nonzerodivisor section is the pullback of the
dual**: `𝒞_{Z(s)/X} ≅ i^*(L^∨)` for an invertible `L` and a global section `s` multiplication by
which is injective on every open. The dual is identified with the ideal sheaf by
`AlgebraicGeometry.isIso_zeroSchemeIdealModuleHom`. -/
def conormalSheafZeroSchemeIsoDual :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf (zeroScheme X L s).subschemeι ≅
      (Scheme.Modules.pullback (zeroScheme X L s).subschemeι).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) :=
  have := isIso_zeroSchemeIdealModuleHom L s hreg
  conormalSheafIsoPullbackIdealSheafOfIsClosedImmersion (zeroScheme X L s).subschemeι ≪≫
    (Scheme.Modules.pullback (zeroScheme X L s).subschemeι).mapIso
      (asIso (zeroSchemeIdealModuleHom L s)).symm

/-- **`𝒞_{Z(s)/X} ≅ i^*(L^∨)` for a regular section** ([Stacks, Tag 01WY]), the form of
`conormalSheafZeroSchemeIsoDual` with the hypothesis written as
`Stacks.Divisors.IsRegularSection`. -/
def conormalSheafZeroSchemeIsoDualOfIsRegularSection (t : L.sections)
    (ht : IsRegularSection X.sheaf.obj X.ringCatSheaf.property t) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf
        (zeroScheme X L (t.eval (op ⊤))).subschemeι ≅
      (Scheme.Modules.pullback (zeroScheme X L (t.eval (op ⊤))).subschemeι).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) :=
  conormalSheafZeroSchemeIsoDual X L (t.eval (op ⊤))
    (injective_smul_res_of_isRegularSection L t ht)

/-- **A short exact sequence `0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_Z ⟶ 0` ending in the canonical map of
structure sheaves identifies `M` with the ideal sheaf of `i`**, the kernel of that map. -/
def idealSheafIsoOfShortExact {Z X : Scheme.{u}} (i : Z ⟶ X) {M : X.Modules}
    (f : M ⟶ X.unitModule) (w : f ≫ Scheme.Modules.unitToPushforwardUnit i = 0)
    (h : (ShortComplex.mk f (Scheme.Modules.unitToPushforwardUnit i) w).ShortExact) :
    M ≅ Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom :=
  IsLimit.conePointUniqueUpToIso h.fIsKernel (limit.isLimit _)


section Twist

open MonoidalCategory

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the `𝒪_X`-modules
of a scheme, as in `StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist`. -/
local instance conormalZeroSchemeModulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal Y.sheaf.obj Y.ringCatSheaf.property

/-- **The unit at a trivialized module is the canonical map of structure sheaves.** For a
morphism `i : Z ⟶ X` and `α : A ≅ 𝒪_X`, the unit `A ⟶ i_* i^* A` followed by
`i_*(i^* α ≫ (i^* 𝒪_X ≅ 𝒪_Z))` is `α` followed by `𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem unit_app_comp_pushforward_map_pullbackUnitIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    {A : X.Modules} (α : A ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullback i).map α.hom ≫ (Scheme.Modules.pullbackUnitIso i).hom) =
      α.hom ≫ Scheme.Modules.unitToPushforwardUnit i := by
  have h1 := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality α.hom
  have h2 : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackUnitIso i).hom =
        Scheme.Modules.unitToPushforwardUnit i := by
    have h := Scheme.Modules.pullbackUnitIso_homEquiv i
    rwa [Adjunction.homEquiv_unit] at h
  have h3 : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullback i).map α.hom ≫ (Scheme.Modules.pullbackUnitIso i).hom) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map α.hom)) ≫
          (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackUnitIso i).hom :=
    (congrArg (fun m => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫ m)
      ((Scheme.Modules.pushforward i).map_comp _ _)).trans (Category.assoc _ _ _).symm
  exact h3.trans ((congrArg (fun m => m ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackUnitIso i).hom) h1.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (fun m => α.hom ≫ m) h2)))

variable (X : Scheme.{u}) (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
  (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  (α : (M ⊗ L : X.Modules) ≅ SheafOfModules.unit X.ringCatSheaf)

/-- Multiplication by `s` on `M`, read in `𝒪_X` through `α : M ⊗ L ≅ 𝒪_X`, followed by the
canonical map `𝒪_X ⟶ i_* 𝒪_{Z(s)}`, is zero. No regularity is needed. -/
theorem tensorSection_comp_unitToPushforwardUnit_eq_zero :
    (((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫ α.hom) ≫
      Scheme.Modules.unitToPushforwardUnit (zeroScheme X L (s.eval (op ⊤))).subschemeι = 0 := by
  exact (Category.assoc _ _ _).trans ((congrArg (fun m => ((ρ_ M).inv ≫
      M ◁ L.unitHomEquiv.symm s) ≫ m)
    (unit_app_comp_pushforward_map_pullbackUnitIso _ α).symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ _)
      (tensorSection_comp_unit_zeroScheme_eq_zero X L s M)).trans zero_comp)))

/-- **The zero-scheme sequence of a regular section, trivialized, with its maps named.** For
invertible `L`, `M` on `X`, a regular section `s` of `L` and `α : M ⊗ L ≅ 𝒪_X`,

`0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0`

is short exact, the first map being multiplication by `s` read through `α` and the second the
canonical map of structure sheaves. It is the twisted sequence of [Stacks, Tag 0C6K]
(`AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection`) transported along `α`. -/
theorem shortExact_tensorSection_unitToPushforwardUnit
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    (ShortComplex.mk _ _
      (tensorSection_comp_unitToPushforwardUnit_eq_zero X L s M α)).ShortExact := by
  obtain ⟨w₀, hse⟩ := shortExact_zeroScheme_twist_of_isRegularSection X L s hs M
  refine ShortComplex.shortExact_of_iso ?_ hse
  exact ShortComplex.isoMk (Iso.refl _) α
    ((Scheme.Modules.pushforward _).mapIso
      ((Scheme.Modules.pullback _).mapIso α ≪≫ Scheme.Modules.pullbackUnitIso _))
    (Category.id_comp _) (unit_app_comp_pushforward_map_pullbackUnitIso _ α).symm

/-- **The conormal sheaf of the zero scheme of a regular section.** For an invertible `L` on `X`,
a regular global section `s` of `L` ([Stacks, Tag 01WY]) with zero scheme `Z(s)` and inclusion
`i`, and an invertible `M` with `α : M ⊗ L ≅ 𝒪_X` (so `M ≅ L^∨`),

`𝒞_{Z(s)/X} ≅ i^* M`.

On `𝐏ⁿ`, with `L = 𝒪(d)`, `M = 𝒪(-d)` and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegTensorIsoUnit`, this is
`𝒞_{Z/𝐏ⁿ} ≅ i^* 𝒪(-d)`. -/
def conormalSheafZeroSchemeIso (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf
        (zeroScheme X L (s.eval (op ⊤))).subschemeι ≅
      (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj M :=
  conormalSheafIsoPullbackIdealSheafOfIsClosedImmersion
      (zeroScheme X L (s.eval (op ⊤))).subschemeι ≪≫
    (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).mapIso
      (idealSheafIsoOfShortExact _ _ _
        (shortExact_tensorSection_unitToPushforwardUnit X L s M α hs)).symm

/-- **`conormalSheafZeroSchemeIso` with the conormal sheaf spelled as the first term of the
conormal sequence** `𝒞_{Z/X} ⟶ i^* Ω_{X/S} ⟶ Ω_{Z/S}` of [Stacks, Tag 01UZ], for any `p : X ⟶ S`;
the two spellings agree definitionally. -/
def conormalShortComplexX₁ZeroSchemeIso
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    {S : Scheme.{u}} (p : X ⟶ S) :
    (Stacks.ConormalSequenceRight.conormalShortComplex
        (zeroScheme X L (s.eval (op ⊤))).subschemeι p).X₁ ≅
      (Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj M :=
  conormalSheafZeroSchemeIso X L s M α hs

end Twist

end AlgebraicGeometry

end
