module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.ComparisonFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# The canonical connection on a crystal in `𝒪_{X/S}`-modules

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and let `F` be a
crystal in `𝒪_{X/S}`-modules on the big crystalline site, that is, a sheaf of `𝒪_{X/S}`-modules
all of whose comparison maps `c_f : f^* F_{T'} ⟶ F_T` are isomorphisms
(`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`).  [Stacks, Tag 07J6] says that `F`
carries a canonical integrable connection, and the recipe of its proof is this.  Over an object
`(U, T, δ)` of the site let `(U, T', δ')` be the first-order universal thickening of
[Stacks, Tag 07J2], with its two projections `p₀, p₁ : T' ⟶ T` and the diagonal `i : T ⟶ T'`
satisfying `p₀ ∘ i = p₁ ∘ i = id`.  The crystal condition gives isomorphisms
`c₀ : p₀^* F_T ≅ F_{T'}` and `c₁ : p₁^* F_T ≅ F_{T'}`, and with `c = c₁⁻¹ ∘ c₀` the connection of
the tag is

`∇(s) = p₁^* s - c (p₀^* s)`,

a section of `p₁^* F_T` killed by pulling back along `i`, hence a section of the ideal
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}` of `i`.

This module builds that map.  Transported along the isomorphism `c₁` the two terms of the recipe
are the two `f`-maps of `F` along `p₁` and `p₀` — this is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf_eq_moduleComparisonSheaf`, that
the `f`-map is the transpose of the comparison map along the adjunction — so on the sections of
`F` over the object the connection is the difference `s ↦ p₁^* s - p₀^* s` of the two restriction
maps of `F` along the two projections, a section of `F` over `(U, T', δ')` killed by restriction
along `i`.  That difference is `Crystalline.GlobalCrystallineSituation.crystalConnection`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crystalConnection` — **the canonical connection of
  [Stacks, Tag 07J6]** on the sections of a sheaf of `𝒪_{X/S}`-modules over an object of
  `CRIS(X/S)`: the difference `p₁^* s - p₀^* s` of the restrictions along the two projections of
  the first-order universal thickening.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningDiffSection` — a divided power
  differential of `T` read as a section of `𝒪_{T'}`, through the square-zero summand of the
  structure sheaf of the thickening.
* `Crystalline.GlobalCrystallineSituation.FirstOrderThickeningHom` — the functoriality datum of
  the first-order universal thickening: a morphism `T'_A ⟶ T'_B` of the site above a morphism
  `A ⟶ B` of the site commuting with both projections.

## Main results

* `Crystalline.GlobalCrystallineSituation.crystalConnection_map_ι` — **the connection takes values
  in the ideal of the diagonal `i : T ⟶ T'`**, which by [Stacks, Tag 07J2] is
  `Ω_{T/S,δ} = (Ω_{X/S})_T`.
* `Crystalline.GlobalCrystallineSituation.crystalConnection_smul` — **the Leibniz rule**
  `∇(b · s) = p₁(b) · ∇(s) + d b · p₀^* s`, with `d = d_{T/S,δ}` the universal divided power
  derivation and a differential read as a section of `𝒪_{T'}`.
* `Crystalline.GlobalCrystallineSituation.firstOrderThickeningDiffSection_smul_balanced` — the
  differential term of the Leibniz rule is balanced over `𝒪_T` in the section and the
  differential, so it is a function of `s ⊗ d b`.
* `Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_unit_app` — **the comparison
  map carries the pullback `g^* s` of a section to its restriction along `g`**, that is, to the
  `f`-map of [Stacks, Tag 07IQ]; this is the first term of the tag's `∇`.
* `Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_apply_unit_app` — **the
  comparison map carries the tag's `c (g^* s)` to the restriction of `s` along `g`**; with
  `g = p₀`, `h = p₁` this is the second term of the tag's `∇`, so the two together say that `c₁`
  carries `p₁^* s - c (p₀^* s)` to `crystalConnection`.
* `Crystalline.GlobalCrystallineSituation.crystalComp` — **the morphism `c = c₁⁻¹ ∘ c₀` of the
  tag**, for a crystal, with its defining property
  `Crystalline.GlobalCrystallineSituation.crystalComp_comp_moduleComparisonSheaf`.
* `Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_apply_crystalComp` — the
  previous identification **at the tag's own hypothesis that `F` is a crystal**, nothing else
  assumed.
* `Crystalline.GlobalCrystallineSituation.exists_comp_moduleComparisonSheaf_eq` — **for a crystal
  the morphism `c` of the tag exists**, which is the only use the construction makes of the crystal
  hypothesis.
* `Crystalline.GlobalCrystallineSituation.moduleSiteRestrict_restrictOpenMap_top` — the bridge
  between the sections over an object and the sections of `F_T` over the whole of `T`.
* `Crystalline.GlobalCrystallineSituation.crystalConnection_naturality` — **naturality in the
  object of the site**, against the functoriality datum of the thickening, which
  `StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningFunctorial.lean` constructs.
* `Crystalline.GlobalCrystallineSituation.crystalConnection_restrict_q₁₂` — the step of the
  integrability argument of [Stacks, Tag 07J3]: the connection carried along `q₁₂` to the
  second-order thickening is the difference `q₂^* s - q₁^* s`.
* `Crystalline.GlobalCrystallineSituation.crystalConnection_unit` — the construction specialises
  at `F = 𝒪_{X/S}` to the universal divided power derivation `d_{T/S,δ}`.

## What is and is not proved

[Stacks, Tag 07J6] itself — a crystal on the small site `Cris(X/S)` has a canonical integrable
connection — is formalized, with no quasi-coherence hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalIntegrableConnectionCris.lean`,
in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`: the connection
`crystalConnectionCris : F ⟶ F ⊗ Ω_{X/S}`, a morphism of abelian sheaves on `Cris(X/S)`, and the
theorems `crystalConnectionCris_isConnection` and `crystalConnectionCris_isIntegrable`.  This
module is about the big site `CRIS(X/S)` and carries no attribute for that tag.

The quantifier runs over sheaves of `𝒪_{X/S}`-modules, not over one of them.  The construction
below and the Leibniz rule hold for every sheaf of `𝒪_{X/S}`-modules; the crystal hypothesis
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal` is what makes this difference *the* map of
[Stacks, Tag 07J6].  The tag's `∇(s) = p₁^* s - c (p₀^* s)` is a section of `p₁^* F_T`, and
`moduleComparisonSheaf_app_unit_app` together with
`moduleComparisonSheaf_app_apply_crystalComp` identify its image under the comparison isomorphism
`c₁` term by term with the two restriction maps whose difference is the connection below; the
morphism `c` of the tag is `crystalComp`, built from the crystal condition and nothing else.  So
nothing here is weaker than the tag for a crystal; what is weaker is the target.

Three parts of the tag are discussed below.  All three are proved — the first at the level of
sheaves of `𝒪_T`-modules, for a crystal and with no further hypothesis, in
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealKernelCrystal.lean`, and the third at
the same level in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSheafIntegrable.lean` — but the third
cannot be stated in the spelling of this module, whose connection has the ideal of `i` as its
target rather than `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`.

1. **The target of `∇` is the ideal of `i`, and that ideal is `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`.**  The
   tag reads
   `∇(s)` as a section of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` by identifying that module with the kernel of
   `p₁^* F_T → F_T`, using `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`.  Here `∇(s)` is a section of `F` over
   `(U, T', δ')` killed by restriction along `i`, that is, a section of the ideal of `i`.  The
   canonical map in one direction is built outright, with no hypothesis, as
   `Crystalline.GlobalCrystallineSituation.diffAction` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionTensor.lean`: it is
   `ω ⊗ s ↦ ω · p₀^* s`, the second term of the Leibniz rule, well defined because that term is
   balanced by `firstOrderThickeningDiffSection_smul_balanced`.  Its inverse exists at the level
   of sheaves of `𝒪_T`-modules, which is where the tag puts the identification:
   `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isSheafCrystal` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealKernelCrystal.lean`.  On *global
   sections* `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean` reduces having
   it to a single bijectivity statement about one explicitly written map,
   `Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`.

   That reduction also shows why the gap cannot be closed in the spelling of global sections: on
   them the statement is **false**, not merely unproved.  The source of that map is the algebraic
   tensor product `Γ(T, Ω_{T/S,δ}) ⊗ Γ(T, F_T)`, the target the tag names is the *sheaf* tensor
   product, and `Γ` does not commute with `⊗`; the module documentation of
   `FirstOrderIdealSheaf.lean` carries the counterexample over `ℙ¹`.  The identification has to be
   stated on the sheaves of modules on `T`, and there it is unconditionally true, because
   `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`.

   At that level the chain is complete.  Unconditionally,
   `Crystalline.firstOrderThickeningTensorBiprodIso` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderStructureTensorSplitting.lean` splits
   `F_T ⊗_{𝒪_T} p₀_* 𝒪_{T'}` as `(F_T ⊗_{𝒪_T} Ω_{T/S,δ}) ⊞ F_T`, and
   `Crystalline.GlobalCrystallineSituation.firstOrderAmbientBiprodIso` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderAmbientSplitting.lean` splits
   `p₀_* F_{T'}` as `Crystalline.GlobalCrystallineSituation.firstOrderAmbientKernel ⊞ F_T`.  The
   crystal condition identifies `p₀^* F_T` with `F_{T'}`, by
   `Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf` at `p₀`, and
   `Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsModules/AmbientSchemeComparison.lean`
   carries that pullback to `AlgebraicGeometry.Scheme.Modules.pullback` along `p₀`.  The
   comparison morphism between the two sources,
   `Crystalline.firstOrderThickeningProjectionFormulaMap` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderProjectionFormulaMap.lean`, is an
   **isomorphism** for every `F_T`, by
   `Crystalline.isIso_firstOrderThickeningProjectionFormulaMap` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderProjectionFormulaIso.lean`: `p₀` is the
   identity on underlying spaces (`firstOrderThickeningSiteP₀_base` of
   `FirstOrderIdealSheaf.lean`), hence a closed embedding, and [Stacks, Tag 0FZE] at a closed
   embedding needs no quasi-coherence.  So the identification holds with the crystal
   hypothesis as its only input, entering through `moduleComparisonSheaf`.

   A second, independent spelling mismatch sits in the same place: already for `F = 𝒪_{X/S}` the
   kernel of `𝒪_{T'} → 𝒪_T` is the module of sections of the *sheaf* `Ω_{T/S,δ}`, whereas the
   presheaf `Ω_{X/S}` of [Stacks, Tag 07IX], in which
   `Crystalline.GlobalCrystallineSituation.structureSheafConnection` and the de Rham complex of
   [Stacks, Tag 07J4] are written, has strictly smaller sections over an object in general; the
   two are identified by
   `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIso` only after
   sheafification.
2. **Naturality in `T` is proved.**  The tag's `∇` is a morphism of abelian sheaves on
   `Cris(X/S)`, which for the family built here is `crystalConnection_naturality`; it is stated
   given a `FirstOrderThickeningHom`, the datum of the induced morphism of thickenings, and that
   datum is **constructed** for every morphism of the site, in
   `StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningFunctorial.lean` as
   `Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap` with its two commutation
   relations.  `Crystalline.GlobalCrystallineSituation.crystalConnection_naturality'` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionNaturality.lean` is the clause with
   nothing assumed.  The functoriality of `(U, T, δ) ↦ (U, T', δ')` needs the functoriality of
   `Ω_{T/S,δ}` at the level of sheaves, not only at the level of rings
   (`Crystalline.dpConstMap`), and it is available: the sheaf of divided power
   differentials has the universal property of a divided power derivation into an arbitrary sheaf
   of modules, `Crystalline.universalDPSchemeDerivation_isUniversal`, and the map is the one that
   property produces.  What remains without a naturality statement is the connection of the
   separately treated case `F = 𝒪_{X/S}`,
   `Crystalline.GlobalCrystallineSituation.structureSheafConnection`, which is written in the
   presheaf spelling of `Ω`.
3. **Integrability is proved, but not in this spelling.**  Integrability is the vanishing of
   `∇ ∘ ∇`, which presupposes the extension of `∇` to a map `F_T ⊗ Ω → F_T ⊗ Ω²`, hence the
   identification of (1) in degrees one and two.  Those identifications are statements about
   sheaves on `T`, so integrability cannot be stated for the connection of this module, whose
   target is the sections of `F` over `(U, T', δ')`.  It is stated and proved where the source
   states it, on the sections over each open of `T`, as
   `Crystalline.GlobalCrystallineSituation.crystalConnectionSheaf_isIntegrable` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSheafIntegrable.lean`.

   The source's proof is a computation on the second-order thickening `(U, T'', δ'')` of
   [Stacks, Tag 07J3] with the maps `q₀, q₁, q₂, q₀₁, q₁₂, q₀₂`; in the spelling used here the
   cocycle condition `q₁₂^* c ∘ q₀₁^* c = q₀₂^* c` on which that computation rests becomes an
   identity between restriction maps of `F` along equal morphisms of the site, and all of the
   content sits in reading the outcome inside `F_T ⊗ Ω²`.  The maps and relations of the
   second-order thickening are available on the structure sheaves
   (`Crystalline.secondOrderThickeningQ₁₂` and the two relations
   `Crystalline.secondOrderThickeningQ₁_eq_Q₁₂_comp_P₀`,
   `Crystalline.secondOrderThickeningQ₂_eq_Q₁₂_comp_P₁`, with the two-form differential
   `Crystalline.dpDeRham`).  The step of the source's proof that those relations give,
   `crystalConnection_restrict_q₁₂`, is proved here against the datum
   `SecondOrderThickeningSiteData`, and that datum is **constructed** —
   `Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteData` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSecondOrder.lean`, where the step
   is restated with nothing assumed.

## Implementation notes

The sections of `F` over an object are taken as the sections of the presheaf of modules
underlying `F` at that object — which is what `Γ(T, F_T)` is, the restriction `F_T` of
[Stacks, Tag 07IQ] being by definition `W ↦ F(U ∩ W, W, δ|_W)` — rather than as the global
sections of the sheaf `F_T` on `T`, which are the same group only up to the canonical isomorphism
between an object and its restriction to the whole ambient scheme.  Restriction along a morphism
of the site is then the semilinear map `PresheafOfModules.restrictₛₗ`, whose target is the module
of sections rather than its restriction of scalars; this is what makes the difference of two such
restrictions typecheck without transport.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- The restriction map of a presheaf of modules along an identity is the identity. -/
private theorem map_id_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} R) (X : Cᵒᵖ) (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [← PresheafOfModules.presheaf_map_apply_coe, N.presheaf.map_id]
  rfl

/-! ### Sections of a module on the site, and of `𝒪_{T'}` -/

/-- **The ring of sections of `𝒪_{X/S}` over an object of `CRIS(X/S)`**, in the spelling over
which the sections of a sheaf of `𝒪_{X/S}`-modules there form a module: it is the ring
`Γ(T, 𝒪_T)` for `(U, T, δ)` the object. -/
abbrev crysSheafRing (S : GlobalCrystallineSituation.{u}) (A : Thickening S) : Type u :=
  (crystallineStructureSheaf S).obj.obj (op A)

/-- **The map on the sections of `𝒪_{X/S}` induced by a morphism of `CRIS(X/S)`**: the map on
global sections of the ambient schemes. -/
abbrev crysSheafRingMap {A B : Thickening S} (g : A ⟶ B) :
    crysSheafRing S B →+* crysSheafRing S A :=
  ((crystallineStructureSheaf S).obj.map g.op).hom

/-- **The restriction map of a sheaf of `𝒪_{X/S}`-modules along a morphism of `CRIS(X/S)`**, on
sections over the objects: the map `F(B) → F(A)` of a morphism `A ⟶ B`, semilinear over the map
of the structure sheaf. -/
abbrev moduleSiteRestrict (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A B : Thickening S} (g : A ⟶ B) :
    M.val.obj (op B) →ₛₗ[crysSheafRingMap g] M.val.obj (op A) :=
  M.val.restrictₛₗ g.op

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- Restricting along a composite of morphisms of the site is restricting along the two
factors. -/
theorem moduleSiteRestrict_comp {A B C : Thickening S} (g : A ⟶ B) (h : B ⟶ C)
    (x : M.val.obj (op C)) :
    moduleSiteRestrict M g (moduleSiteRestrict M h x) = moduleSiteRestrict M (g ≫ h) x := by
  have hx := M.val.map_comp_apply h.op g.op x
  rw [← op_comp] at hx
  exact hx.symm

/-- Restricting along an identity of the site does nothing. -/
theorem moduleSiteRestrict_id (A : Thickening S) (x : M.val.obj (op A)) :
    moduleSiteRestrict M (𝟙 A) x = x :=
  map_id_apply M.val (op A) x

/-- **A divided power differential of `T`, read as a section of `𝒪_{T'}`.**  The structure sheaf
of the first-order universal thickening is `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`, and this is the inclusion
of the second summand, which is an ideal of square zero. -/
def firstOrderThickeningDiffSection (A : Thickening S)
    (ω : Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤)) :
    crysSheafRing S (firstOrderThickeningObject S A) :=
  firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤) ω

/-- The sections of `Ω_{T/S,δ}` over the whole ambient scheme, as a module over the sections of
`𝒪_{X/S}` over the object: the two rings of scalars are both `Γ(T, 𝒪_T)`. -/
instance moduleDiffSections (A : Thickening S) :
    Module (crysSheafRing S A)
      Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤) :=
  inferInstanceAs (Module Γ(A.thickening.target.scheme, ⊤)
    Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤))

/-- **The difference of the two projections is the universal divided power derivation.**  On the
sections of `𝒪_{X/S}` over an object, `p₁ - p₀` is `d_{T/S,δ}` followed by the inclusion of the
square-zero summand of `𝒪_{T'}`; this is [Stacks, Tag 07J2] read on the sections of the site. -/
theorem crysSheafRingMap_siteP₁_sub_siteP₀ (A : Thickening S) (b : crysSheafRing S A) :
    crysSheafRingMap (firstOrderThickeningSiteP₁ S A) b -
        crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b =
      firstOrderThickeningDiffSection A
        (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) :=
  firstOrderThickeningP₁_sub_P₀ A.thickening.target S.S.scheme A.toBase.hom (op ⊤) b

/-- **The sections of `𝒪_{X/S}` over an object form a commutative ring**: they are the global
sections of the ambient scheme.  The spelling over which the sections of a sheaf of modules form a
module is the one in which `𝒪_{X/S}` is a sheaf of not necessarily commutative rings, so
commutativity is recorded by hand. -/
theorem crysSheafRing_mul_comm (A : Thickening S) (x y : crysSheafRing S A) : x * y = y * x :=
  mul_comm (G := Γ(A.thickening.target.scheme, ⊤)) x y

/-- Multiplying the square-zero inclusion of a differential by a section pulled back along `p₀`
scales the differential: `p₀(b) · ω = b · ω`. -/
theorem crysSheafRingMap_siteP₀_mul_diffSection (A : Thickening S) (b : crysSheafRing S A)
    (ω : Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤)) :
    crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b *
        firstOrderThickeningDiffSection A ω =
      firstOrderThickeningDiffSection A (b • ω) :=
  mul_firstOrderThickeningInr A.thickening.target S.S.scheme A.toBase.hom (op ⊤) _ ω

/-- Multiplying the square-zero inclusion of a differential by a section pulled back along `p₀`
scales the differential, in the other order. -/
theorem diffSection_mul_crysSheafRingMap_siteP₀ (A : Thickening S) (b : crysSheafRing S A)
    (ω : Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤)) :
    firstOrderThickeningDiffSection A ω *
        crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b =
      firstOrderThickeningDiffSection A (b • ω) :=
  (crysSheafRing_mul_comm (firstOrderThickeningObject S A) _ _).trans
    (crysSheafRingMap_siteP₀_mul_diffSection A b ω)

/-! ### The connection -/

/-- **Stacks Project, Tag 07J6.**  The canonical connection of a crystal in `𝒪_{X/S}`-modules, on
the sections over an object `(U, T, δ)` of `CRIS(X/S)`: the difference `p₁^* s - p₀^* s` of the
restrictions of `s` along the two projections of the first-order universal thickening
`(U, T', δ')` of [Stacks, Tag 07J2].

For a crystal this is the map `∇(s) = p₁^* s - c (p₀^* s)` of the tag, read through the comparison
isomorphism `c₁ : p₁^* F_T ≅ F_{T'}` under which the two terms become the two `f`-maps of `F`.
Its values are killed by restriction along the diagonal `i : T ⟶ T'`, so they are sections of the
ideal of `i`, which [Stacks, Tag 07J2] identifies with `Ω_{T/S,δ} = (Ω_{X/S})_T`. -/
def crystalConnection (A : Thickening S) :
    M.val.obj (op A) →+ M.val.obj (op (firstOrderThickeningObject S A)) :=
  AddMonoidHom.mk'
    (fun s ↦ moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) s -
      moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s)
    (fun s t ↦ by
      simp only [map_add]
      abel)

/-- The canonical connection sends `s` to the difference `p₁^* s - p₀^* s` of its restrictions
along the two projections of the first-order universal thickening. -/
theorem crystalConnection_apply (A : Thickening S) (s : M.val.obj (op A)) :
    crystalConnection M A s =
      moduleSiteRestrict M (firstOrderThickeningSiteP₁ S A) s -
        moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s := rfl

/-- Restricting the connection along `k` gives the difference of the restrictions along
`k ≫ p₁` and `k ≫ p₀`. -/
private theorem moduleSiteRestrict_crystalConnection (A : Thickening S) {C : Thickening S}
    (k : C ⟶ firstOrderThickeningObject S A) (s : M.val.obj (op A)) :
    moduleSiteRestrict M k (crystalConnection M A s) =
      moduleSiteRestrict M (k ≫ firstOrderThickeningSiteP₁ S A) s -
        moduleSiteRestrict M (k ≫ firstOrderThickeningSiteP₀ S A) s := by
  rw [crystalConnection_apply, map_sub, moduleSiteRestrict_comp, moduleSiteRestrict_comp]

/-- **The connection takes values in the ideal of the diagonal.**  Both projections retract the
diagonal `i : T ⟶ T'`, so both terms of `∇(s)` restrict to `s` along `i` and the difference
restricts to zero.  By [Stacks, Tag 07J2] the ideal of `i` is `Ω_{T/S,δ} = (Ω_{X/S})_T`, which is
how [Stacks, Tag 07J6] reads `∇(s)` as a section of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`. -/
theorem crystalConnection_map_ι (A : Thickening S) (s : M.val.obj (op A)) :
    moduleSiteRestrict M (firstOrderThickeningSiteι S A) (crystalConnection M A s) = 0 := by
  rw [moduleSiteRestrict_crystalConnection, firstOrderThickeningSiteι_comp_P₁,
    firstOrderThickeningSiteι_comp_P₀, sub_self]

/-- **The Leibniz rule for the canonical connection.**  For a section `b` of `𝒪_{X/S}` over the
object and a section `s` of `F`,

`∇(b · s) = p₁(b) · ∇(s) + d b · p₀^* s`,

where `d = d_{T/S,δ}` is the universal divided power derivation and a differential is read as a
section of `𝒪_{T'}` through the square-zero summand.  This is the rule
`∇(f s) = f ∇(s) + s ⊗ d f` of [Stacks, Tag 07J6]: the scalars of the first term are read through
`p₁`, which is how `𝒪_T` acts on sections over `(U, T', δ')` of the ideal of the diagonal, and the
second term is the image of `s ⊗ d b` under the canonical map
`F_T ⊗_{𝒪_T} Ω_{T/S,δ} → ker (p₁^* F_T → F_T)`, by
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningDiffSection_smul_balanced`. -/
theorem crystalConnection_smul (A : Thickening S) (b : crysSheafRing S A)
    (s : M.val.obj (op A)) :
    crystalConnection M A (b • s) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S A) b • crystalConnection M A s +
        firstOrderThickeningDiffSection A
            (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) •
          moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s := by
  rw [crystalConnection_apply, crystalConnection_apply, map_smulₛₗ, map_smulₛₗ, smul_sub,
    ← crysSheafRingMap_siteP₁_sub_siteP₀, sub_smul]
  abel

/-- **The differential term of the Leibniz rule is balanced over `𝒪_T`.**  Moving a scalar `b`
from the section to the differential does not change `ω · p₀^* s`, because multiplying the
square-zero inclusion of `ω` by `p₀(b)` is the square-zero inclusion of `b · ω`.  So that term is
a function of `s ⊗ ω`: it is the canonical map
`F_T ⊗_{𝒪_T} Ω_{T/S,δ} → ker (p₁^* F_T → F_T)` of [Stacks, Tag 07J6]. -/
theorem firstOrderThickeningDiffSection_smul_balanced (A : Thickening S)
    (b : crysSheafRing S A)
    (ω : Γ(dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom, ⊤))
    (s : M.val.obj (op A)) :
    firstOrderThickeningDiffSection A ω •
        moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) (b • s) =
      firstOrderThickeningDiffSection A (b • ω) •
        moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s := by
  rw [map_smulₛₗ, smul_smul, diffSection_mul_crysSheafRingMap_siteP₀]

/-! ### Naturality in the object -/

/-- **The functoriality datum of the first-order universal thickening.**  For a morphism
`g : (U, T, δ) ⟶ (U₁, T₁, δ₁)` of `CRIS(X/S)`, a morphism of the site between the first-order
universal thickenings of [Stacks, Tag 07J2] commuting with both projections.
[Stacks, Tag 07J6] uses the functoriality of `T ↦ T'` to turn the family of connections into a
morphism of abelian sheaves on the site; this structure is that input, and it is constructed for
every morphism of the site by
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionNaturality.lean`, out of
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningSiteMap`. -/
structure FirstOrderThickeningHom {A B : Thickening S} (g : A ⟶ B) where
  /-- The morphism of the site between the two first-order thickenings. -/
  hom : firstOrderThickeningObject S A ⟶ firstOrderThickeningObject S B
  /-- It commutes with the first projection. -/
  comp_p₀ : hom ≫ firstOrderThickeningSiteP₀ S B = firstOrderThickeningSiteP₀ S A ≫ g
  /-- It commutes with the second projection. -/
  comp_p₁ : hom ≫ firstOrderThickeningSiteP₁ S B = firstOrderThickeningSiteP₁ S A ≫ g

/-- **Naturality of the canonical connection in the object of the site**, given the functoriality
datum of the first-order universal thickening: the connection commutes with the restriction maps
of `F`.  This is the statement of [Stacks, Tag 07J6] that the family of connections is a morphism
of abelian sheaves on `Cris(X/S)`, and it needs nothing of `F`: both terms of `∇` are restrictions
of `F` along a morphism of the site, and the datum identifies the two composites.

The datum is supplied for every morphism of the site in
`StacksFrontier/AlgebraicGeometry/Crystalline/UniversalThickeningFunctorial.lean`, so this statement
has an unconditional form,
`Crystalline.GlobalCrystallineSituation.crystalConnection_naturality'` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionNaturality.lean`; that form is where
the naturality clause of [Stacks, Tag 07J6] is registered, this one being its restatement with
the datum taken as an argument. -/
theorem crystalConnection_naturality {A B : Thickening S} (g : A ⟶ B)
    (G : FirstOrderThickeningHom g) (s : M.val.obj (op B)) :
    moduleSiteRestrict M G.hom (crystalConnection M B s) =
      crystalConnection M A (moduleSiteRestrict M g s) := by
  rw [moduleSiteRestrict_crystalConnection, G.comp_p₁, G.comp_p₀, crystalConnection_apply,
    moduleSiteRestrict_comp, moduleSiteRestrict_comp]

/-! ### The connection is the map of the tag -/

/-- **The comparison map carries the pullback of a section to its restriction.**  For a morphism
`g` of the site and a section `s` of `F_{T'}` over an open `W`, the comparison map `c_g` applied to
the pullback `g^* s` — the unit of the adjunction between pullback and pushforward applied to `s` —
is the restriction of `s` along the restriction of `g` over `W`, which is the `f`-map of
[Stacks, Tag 07IQ].  This holds for every sheaf of `𝒪_{X/S}`-modules: the `f`-map *is* the
transpose of `c_g` along the adjunction, and the transpose of a morphism is the unit followed by
its pushforward. -/
theorem moduleComparisonSheaf_app_unit_app {A B : Thickening S} (g : A ⟶ B)
    (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (s : (Thickening.moduleRestrictionSheaf M B).val.obj W) :
    (Thickening.moduleComparisonSheaf M g).val.app
        (op ((Opens.map g.targetHom.hom.base).obj W.unop))
        (((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (Thickening.ringRestrictionSheafFMap g)).unit.app
          (Thickening.moduleRestrictionSheaf M B)).val.app W s) =
      M.val.map (Thickening.restrictOpenMap g W.unop).op s := by
  have h := Thickening.moduleFMapSheaf_eq_moduleComparisonSheaf M g
  rw [Adjunction.homEquiv_unit] at h
  exact (congrArg (fun k ↦ k.val.app W s) h).symm

/-- **The comparison map carries the tag's `c (g^* s)` to the restriction of `s` along `g`.**  Let
`g, h : (U, T, δ) ⟶ (U₁, T₁, δ₁)` be two morphisms of the site and let
`c : g^* F_{T₁} ⟶ h^* F_{T₁}` be a morphism with `c_h ∘ c = c_g` — which is exactly the defining
property of the isomorphism `c = c_h⁻¹ ∘ c_g` that [Stacks, Tag 07J6] forms out of the two
comparison isomorphisms of a crystal, and which determines `c` whenever `c_h` is a monomorphism.
Then `c_h (c (g^* s))` is the restriction of `s` along `g`.

With `g = p₀` and `h = p₁` this is the second term of the tag's `∇(s) = p₁^* s - c (p₀^* s)`, and
`Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_unit_app` with `g = p₁` is the
first: so `c₁` carries the tag's map to `p₁^* s - p₀^* s`, which is
`Crystalline.GlobalCrystallineSituation.crystalConnection`.  For a crystal such a `c` is
`Crystalline.GlobalCrystallineSituation.crystalComp`, and that is the only place where the crystal
hypothesis is needed; the form of this statement at that `c`, and hence at the tag's own
hypothesis, is
`Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_apply_crystalComp`, which is
where this clause of [Stacks, Tag 07J6] is registered. -/
theorem moduleComparisonSheaf_app_apply_unit_app {A B : Thickening S} (g h : A ⟶ B)
    (c : (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).obj
          (Thickening.moduleRestrictionSheaf M B) ⟶
        (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap h)).obj
          (Thickening.moduleRestrictionSheaf M B))
    (hc : c ≫ Thickening.moduleComparisonSheaf M h = Thickening.moduleComparisonSheaf M g)
    (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (s : (Thickening.moduleRestrictionSheaf M B).val.obj W) :
    (Thickening.moduleComparisonSheaf M h).val.app
        (op ((Opens.map g.targetHom.hom.base).obj W.unop))
        (c.val.app (op ((Opens.map g.targetHom.hom.base).obj W.unop))
          (((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (Thickening.ringRestrictionSheafFMap g)).unit.app
            (Thickening.moduleRestrictionSheaf M B)).val.app W s)) =
      M.val.map (Thickening.restrictOpenMap g W.unop).op s :=
  (congrArg (fun k ↦ k.val.app (op ((Opens.map g.targetHom.hom.base).obj W.unop))
      (((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g)).unit.app
        (Thickening.moduleRestrictionSheaf M B)).val.app W s)) hc).trans
    (moduleComparisonSheaf_app_unit_app M g W s)

/-- **The restriction of a morphism of the site over the whole ambient scheme is the morphism
itself**, read on sections through the canonical isomorphisms between an object and its restriction
to the whole of its ambient scheme.  This is the bridge between the sections over an object, in
which `Crystalline.GlobalCrystallineSituation.crystalConnection` is written, and the sections of
the restricted sheaf `F_T` over the whole of `T`, in which the `f`-maps and the comparison maps of
[Stacks, Tag 07IQ] — and hence the two theorems above — are written. -/
theorem moduleSiteRestrict_restrictOpenMap_top {A B : Thickening S} (g : A ⟶ B)
    (t : M.val.obj (op B)) :
    moduleSiteRestrict M (Thickening.restrictOpenMap g ⊤)
        (moduleSiteRestrict M (B.restrictOpenHom ⊤) t) =
      moduleSiteRestrict M (A.restrictOpenHom (g.targetHom.hom ⁻¹ᵁ ⊤))
        (moduleSiteRestrict M g t) := by
  rw [moduleSiteRestrict_comp, moduleSiteRestrict_comp,
    Thickening.restrictOpenMap_restrictOpenHom]

/-- **The morphism `c = c_h⁻¹ ∘ c_g` of [Stacks, Tag 07J6]**, for a crystal in
`𝒪_{X/S}`-modules and two parallel morphisms `g, h : (U, T, δ) ⟶ (U₁, T₁, δ₁)` of the site: the
composite of the comparison map along `g` with the inverse of the comparison map along `h`, both
of which the crystal condition `Crystalline.GlobalCrystallineSituation.IsSheafCrystal` makes
isomorphisms.  With `g = p₀` and `h = p₁` this is the map `c = c₁⁻¹ ∘ c₀` out of which the tag
builds its `∇(s) = p₁^* s - c (p₀^* s)`. -/
def crystalComp (hM : IsSheafCrystal M) {A B : Thickening S} (g h : A ⟶ B) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).obj
        (Thickening.moduleRestrictionSheaf M B) ⟶
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap h)).obj
        (Thickening.moduleRestrictionSheaf M B) :=
  haveI := hM A B h
  Thickening.moduleComparisonSheaf M g ≫ inv (Thickening.moduleComparisonSheaf M h)

/-- **The defining property of the morphism `c` of [Stacks, Tag 07J6]**: `c_h ∘ c = c_g`.  It
determines `c` whenever `c_h` is a monomorphism, and in particular for a crystal. -/
theorem crystalComp_comp_moduleComparisonSheaf (hM : IsSheafCrystal M) {A B : Thickening S}
    (g h : A ⟶ B) :
    crystalComp M hM g h ≫ Thickening.moduleComparisonSheaf M h =
      Thickening.moduleComparisonSheaf M g := by
  have := hM A B h
  show (Thickening.moduleComparisonSheaf M g ≫ inv (Thickening.moduleComparisonSheaf M h)) ≫
    Thickening.moduleComparisonSheaf M h = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **For a crystal, the morphism `c` of [Stacks, Tag 07J6] exists.**  It is
`Crystalline.GlobalCrystallineSituation.crystalComp`, and this is the only use the construction of
the tag makes of the crystal hypothesis. -/
theorem exists_comp_moduleComparisonSheaf_eq {A B : Thickening S} (hM : IsSheafCrystal M)
    (g h : A ⟶ B) :
    ∃ c : (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g)).obj
          (Thickening.moduleRestrictionSheaf M B) ⟶
        (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap h)).obj
          (Thickening.moduleRestrictionSheaf M B),
      c ≫ Thickening.moduleComparisonSheaf M h = Thickening.moduleComparisonSheaf M g :=
  ⟨crystalComp M hM g h, crystalComp_comp_moduleComparisonSheaf M hM g h⟩

/-- **The comparison map carries the tag's `c (g^* s)` to the restriction of `s` along `g`, for a
crystal.**  This is
`Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_apply_unit_app` at the morphism
`c = c_h⁻¹ ∘ c_g` that the crystal condition supplies, so the only input is the crystal
hypothesis of [Stacks, Tag 07J6] itself.

With `g = p₀` and `h = p₁` this is the second term of the tag's `∇(s) = p₁^* s - c (p₀^* s)`, and
`Crystalline.GlobalCrystallineSituation.moduleComparisonSheaf_app_unit_app` with `g = p₁` is the
first; so `c₁` carries the tag's map to the difference `p₁^* s - p₀^* s` of the two restriction
maps, which is `Crystalline.GlobalCrystallineSituation.crystalConnection`. -/
theorem moduleComparisonSheaf_app_apply_crystalComp (hM : IsSheafCrystal M)
    {A B : Thickening S} (g h : A ⟶ B) (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (s : (Thickening.moduleRestrictionSheaf M B).val.obj W) :
    (Thickening.moduleComparisonSheaf M h).val.app
        (op ((Opens.map g.targetHom.hom.base).obj W.unop))
        ((crystalComp M hM g h).val.app
          (op ((Opens.map g.targetHom.hom.base).obj W.unop))
          (((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (Thickening.ringRestrictionSheafFMap g)).unit.app
            (Thickening.moduleRestrictionSheaf M B)).val.app W s)) =
      M.val.map (Thickening.restrictOpenMap g W.unop).op s :=
  moduleComparisonSheaf_app_apply_unit_app M g h (crystalComp M hM g h)
    (crystalComp_comp_moduleComparisonSheaf M hM g h) W s

/-! ### Towards integrability: the second-order thickening -/

/-- **The datum of the second-order universal thickening of [Stacks, Tag 07J3] as an object of the
site.**  The integrability half of [Stacks, Tag 07J6] is a computation on `(U, T'', δ'')` through
the three maps `q₀, q₁, q₂ : T'' ⟶ T` and the three maps `q₀₁, q₁₂, q₀₂ : T'' ⟶ T'`, of which the
argument consumes `q₁₂` and the two relations `q₁ = q₁₂ ∘ p₀` and `q₂ = q₁₂ ∘ p₁`.  Those exist in
the library on the structure sheaves — `Crystalline.secondOrderThickeningQ₁₂`,
`Crystalline.secondOrderThickeningQ₁_eq_Q₁₂_comp_P₀` and
`Crystalline.secondOrderThickeningQ₂_eq_Q₁₂_comp_P₁` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningDeRham.lean`, together with the
sheaf `Crystalline.secondOrderThickeningSheaf`.  This structure is that datum, in the shape in
which the computation consumes it; it is **constructed** — the object of the site is
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject` and the two relations are
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₁₂_comp_P₀` and
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteQ₁₂_comp_P₁`, assembled in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSecondOrder.lean` as
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningSiteData`. -/
structure SecondOrderThickeningSiteData (A : Thickening S) where
  /-- The object `(U, T'', δ'')` of the site. -/
  obj : Thickening S
  /-- The morphism `q₁₂ : T'' ⟶ T'`. -/
  q₁₂ : obj ⟶ firstOrderThickeningObject S A
  /-- The morphism `q₁ : T'' ⟶ T`. -/
  q₁ : obj ⟶ A
  /-- The morphism `q₂ : T'' ⟶ T`. -/
  q₂ : obj ⟶ A
  /-- The relation `q₁ = q₁₂ ∘ p₀`. -/
  q₁_eq : q₁₂ ≫ firstOrderThickeningSiteP₀ S A = q₁
  /-- The relation `q₂ = q₁₂ ∘ p₁`. -/
  q₂_eq : q₁₂ ≫ firstOrderThickeningSiteP₁ S A = q₂

/-- **The connection carried to the second-order thickening is the second-order difference.**
Restricting `∇(s)` along `q₁₂` gives `q₂^* s - q₁^* s`, by the two relations
`q₁ = q₁₂ ∘ p₀` and `q₂ = q₁₂ ∘ p₁` of [Stacks, Tag 07J3].  This is the step by which the proof of
[Stacks, Tag 07J6] moves `∇(s)` onto `T''`.  It is stated over the datum
`SecondOrderThickeningSiteData` so that the computation does not depend on how `(U, T'', δ'')` is
built; the datum itself is constructed, in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalConnectionSecondOrder.lean`, where
`Crystalline.GlobalCrystallineSituation.crystalConnection_restrict_q₁₂'` is this same conclusion
with no datum assumed.  It is *not* integrability: the remaining steps read the outcome inside
`F_T ⊗ Ω²_{T/S,δ}` through the identification of the ideal of the diagonal with `F_T ⊗ Ω`, which is
the gap described in the module documentation, the two-form `d ω` being
`Crystalline.dpDeRham`. -/
theorem crystalConnection_restrict_q₁₂ (A : Thickening S)
    (D : SecondOrderThickeningSiteData A) (s : M.val.obj (op A)) :
    moduleSiteRestrict M D.q₁₂ (crystalConnection M A s) =
      moduleSiteRestrict M D.q₂ s - moduleSiteRestrict M D.q₁ s := by
  rw [moduleSiteRestrict_crystalConnection, D.q₁_eq, D.q₂_eq]

/-! ### The case `F = 𝒪_{X/S}` -/

/-- **The construction specialises at `F = 𝒪_{X/S}` to the universal divided power derivation.**
The structure sheaf of the big crystalline site is a crystal in `𝒪_{X/S}`-modules
(`Crystalline.GlobalCrystallineSituation.isSheafCrystal_unit`), and for it the connection built
here is `b ↦ d_{T/S,δ} b`, read inside the ideal of the diagonal through the square-zero summand
of `𝒪_{T'}`.  This is the connection `d_{X/S}` of
`Crystalline.GlobalCrystallineSituation.structureSheafConnection`, up to the two spellings of `Ω`
discussed in the module documentation: there the differential is the universal derivation into the
*presheaf* `Ω_{X/S}` of [Stacks, Tag 07IX], here it is its image in the sheaf `Ω_{T/S,δ}`. -/
theorem crystalConnection_unit (A : Thickening S)
    (b : (SheafOfModules.unit (crystallineStructureSheaf S)).val.obj (op A)) :
    crystalConnection (SheafOfModules.unit (crystallineStructureSheaf S)) A b =
      firstOrderThickeningDiffSection A
        (sheafApp A.thickening.target S.S.scheme A.toBase.hom ⊤ b) :=
  crysSheafRingMap_siteP₁_sub_siteP₀ A b

end Crystalline.GlobalCrystallineSituation

end

end
