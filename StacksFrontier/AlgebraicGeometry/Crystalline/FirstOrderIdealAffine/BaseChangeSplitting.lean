module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnectionGeneral
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The base-change map of [Stacks, Tag 07J6] is a base change of scalars

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules on the big crystalline site and let `(U, T, δ)` be an object of `CRIS(X/S)`
with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2].  Write
`D = Γ(T, 𝒪_T)`, `D' = Γ(T', 𝒪_{T'})`, `Ω = Γ(T, Ω_{T/S,δ})` and `Mod = F(U, T, δ)`.

`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean` reduces the datum
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` of [Stacks, Tag 07J6] to
bijectivity of one explicitly written map,
`Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`,

`Mod × (Ω ⊗_D Mod) ⟶ F(U, T', δ')`,  `(s, z) ↦ p₀^* s + diffAction z`.

This module identifies that map with a **base change of scalars** along
`p₀ : D ⟶ D'`, which is the form in which the statement is recognisable and in which an affine
proof can consume it:

`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`, the map

`D' ⊗_D Mod ⟶ F(U, T', δ')`,  `t ⊗ s ↦ t · p₀^* s`,

is bijective **if and only if** `firstOrderSectionsMap` is.  That equivalence is unconditional:
no crystal hypothesis, no quasi-coherence, no affineness.  It is the splitting `D' = D ⊕ Ω` of
[Stacks, Tag 07J2], read through the tensor product as `(D ⊕ Ω) ⊗_D Mod = Mod ⊕ (Ω ⊗_D Mod)`.

The module then **proves that base change of scalars bijective** on an object whose ambient
scheme is affine, for `F` a crystal with `F_T` quasi-coherent, and so produces the datum
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` of [Stacks, Tag 07J6] on such
an object out of the source's own crystal hypothesis.  On an affine object the global sections
functor commutes with the tensor product for a quasi-coherent module, which is why the chain
below computes: it is

`D' ⊗_D Γ(T, F_T) ≅ Γ(T', p₀^* F_T) ≅ Γ(T', F_{T'})`,

the first isomorphism `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `U = V = ⊤` and
the second the crystal condition.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.algebraCrysSheafRingSiteP₀` — the sections of
  `𝒪_{X/S}` over `(U, T', δ')` as a `D`-algebra, through `p₀`.
* `Crystalline.GlobalCrystallineSituation.extensionSectionsMap` — the base change of scalars
  `D' ⊗_D Mod ⟶ F(U, T', δ')`, `t ⊗ s ↦ t · p₀^* s`.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.firstOrderSplitTensorEquiv` — the splitting
  `Mod × (Ω ⊗_D Mod) ≃+ D' ⊗_D Mod` induced by `D' = D ⊕ Ω`.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.firstOrderCrysPullbackAdjunction` and
  `Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction` — the two
  adjunctions whose left adjoints `Thickening.ambientSchemePullbackIso` identifies.
* `Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison` — the comparison map
  `p₀^* F_T ⟶ F_{T'}` of [Stacks, Tag 07IQ], read along the morphism `p₀ : T' ⟶ T` of ambient
  schemes.
* `Crystalline.GlobalCrystallineSituation.affineCrossEquiv` — the change of spelling between the
  tensor product `D' ⊗_D Mod` of `extensionSectionsMap` and the tensor product
  `Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)` of
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.ambientFirstOrderComparison` — the comparison map
  `p₀^* F_T ⟶ F_{T'}` with **both** sides read over the structure sheaf of the ambient scheme, so
  that it can be composed with the affine base-change comparison.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.affineChainTailHom` — the tail of the affine chain:
  the sections of `p₀^* F_T` over the whole of `T'` carried to `F(U, T', δ')`.
* `Crystalline.GlobalCrystallineSituation.affineExtensionHom` — the affine chain itself, the
  additive map `D' ⊗_D Mod ⟶ F(U, T', δ')` composite of the three factors.
* `Crystalline.GlobalCrystallineSituation.affineExtensionFun` — that chain with its middle factor
  left as a morphism of `ModuleCat` rather than bundled as an additive map, which is the form in
  which the normalisation of the base-change comparison applies to it.
* `Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfIsSheafCrystal` — **the datum
  of [Stacks, Tag 07J6] on an object with affine ambient scheme, for a crystal with `F_T`
  quasi-coherent.**

## Main results

* `Crystalline.GlobalCrystallineSituation.siteP₀_siteι_add_diffSection` — **the splitting
  `D' = D ⊕ Ω` of [Stacks, Tag 07J2] on global sections**: a section of `𝒪_{T'}` is the sum of
  `p₀` of its restriction along the diagonal and of its differential component.
* `Crystalline.GlobalCrystallineSituation.crysDiffPart_smul` and
  `Crystalline.GlobalCrystallineSituation.crysSheafRingMapSiteιLinear` — the two components of
  that splitting are `D`-linear, the scalars acting on `D'` through `p₀`.
* `Crystalline.GlobalCrystallineSituation.extensionSectionsMap_firstOrderSplitTensorEquiv` — the
  triangle: the base change of scalars, precomposed with the splitting, is
  `Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap`.
* `bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap`
  — **the two bijectivity statements are equivalent.**
* `Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison_pullbackSection` — **the
  normalisation of the comparison map of [Stacks, Tag 07IQ] along `p₀ : T' ⟶ T`**: it carries the
  pullback of a section of `F_T` to the restriction of that section along `p₀`.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.isIso_affineFirstOrderComparison` — **that comparison
  map is an isomorphism for a crystal.**
* `ringRestrictionSheafStructureIso_inv_app_top_eq_crysSheafRingMap_restrictOpenHom`
  — the scalars of `Γ(T, 𝒪_T)` on `Γ(T, F_T)` act through the restriction map of the site along
  the structure morphism of the restriction of the object to the whole of its ambient scheme.
* `Crystalline.GlobalCrystallineSituation.ambientFirstOrderComparison_ambientPullbackSectionTop`
  — **the normalisation of the comparison map in the ambient spelling**: it carries the pullback
  of a section of `F_T` to the restriction of that section along `p₀`.  No hypothesis.
* `Crystalline.GlobalCrystallineSituation.affineChainTailHom_smul_ambientPullbackSectionTop` —
  **the whole of the computation that follows the base-change comparison**: the tail of the chain
  carries `t · p₀^* a` to `t · p₀^* a` read over the object.
* `Crystalline.GlobalCrystallineSituation.bijective_affineChainTailHom`,
  `Crystalline.GlobalCrystallineSituation.bijective_affineBaseChangeTopHom`,
  `Crystalline.GlobalCrystallineSituation.bijective_affineCrossModule` and
  `Crystalline.GlobalCrystallineSituation.bijective_affineExtensionHom` — **each factor of the
  affine chain is a bijection, and so is the chain**, for a crystal on an object with affine
  ambient scheme and quasi-coherent `F_T`.
* `Crystalline.GlobalCrystallineSituation.affineExtensionHom_tmul` and
  `Crystalline.GlobalCrystallineSituation.extensionSectionsMap_eq_affineExtensionHom` — **the
  affine chain is the base change of scalars**, on a pure tensor and hence everywhere.
* `Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMap` and
  `Crystalline.GlobalCrystallineSituation.bijective_firstOrderSectionsMap_of_isSheafCrystal` —
  **the base change of scalars, and so the canonical map of [Stacks, Tag 07J6] on global
  sections, is bijective** for a crystal on an object with affine ambient scheme and
  quasi-coherent `F_T`.

## What is and is not proved

The reduction is unconditional and complete, and bijectivity is proved on an **affine** object
for a crystal with `F_T` quasi-coherent.  For a general object it is false; the ℙ¹
counterexample is recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealSheaf.lean`, and what rules it out here
is affineness, under which the global sections functor commutes with the tensor product for a
quasi-coherent module.  Everything up to and including the equivalence of the two bijectivity
statements is hypothesis-free; the crystal hypothesis enters only through the comparison map
`p₀^* F_T ⟶ F_{T'}` being an isomorphism, and affineness and quasi-coherence only through the
affine base-change comparison.

### The two inputs the affine proof consumes

On an object whose ambient scheme is affine, with `F` locally quasi-coherent and a crystal, the
proof of bijectivity of `extensionSectionsMap` runs

`D' ⊗_D Γ(T, F_T) ≅ Γ(T', p₀^* F_T) ≅ Γ(T', F_{T'})`,

the first isomorphism being `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at
`U = V = ⊤` — the sections of a pullback of a quasi-coherent module over a compatible pair of
affine opens are the base change — and the second the crystal condition
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, which makes
`Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf` at `p₀` an
isomorphism.  `Crystalline.GlobalCrystallineSituation.isAffine_firstOrderThickeningObject` and
`Crystalline.GlobalCrystallineSituation.isQuasicoherent_ambientModuleRestriction` supply the two
hypotheses those two inputs need, and
`Crystalline.GlobalCrystallineSituation.Thickening.ambientSchemePullbackIso` identifies the
pullback of sheaves of modules along the crystalline `f`-map with the pullback along the
morphism of ambient schemes, which is the spelling the affine statement is about.

Two further bookkeeping inputs that the chain needs are proved below, because they are the two
places where the sections over an *object of the site* have to be matched with the sections of
the *restricted sheaf over the whole ambient scheme*, which are not the same expression:

* `Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀` — the restriction
  map `D ⟶ D'` of the site along `p₀` is the map on sections of the morphism of ambient schemes.
  Stated pointwise, and that is not a stylistic choice: the two `RingHom` types differ by the
  instance path through `RingCat` (which `crysSheafRingMap` uses) and through `CommRingCat`
  (which `AlgebraicGeometry.Scheme.Hom.appLE` uses), and the equation of the two ring
  homomorphisms is not type-correct as stated at the `instances` transparency level even though
  the carriers are definitionally equal.
* `Crystalline.GlobalCrystallineSituation.bijective_moduleSiteRestrict_restrictOpenHom_top` — the
  sections of `F` over an object and over its restriction to the whole of its ambient scheme are
  the same, because the structure morphism of that restriction is an isomorphism.

### The comparison `p₀^* F_T ⟶ F_{T'}` on ambient schemes, and its normalisation

The second half of that chain is proved here, unconditionally as to its shape and under the
crystal hypothesis as to its bijectivity.  Write

`c : p₀^* F_T ⟶ F_{T'}`,
`Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison`,

for the comparison map of [Stacks, Tag 07IQ] read along the morphism `p₀ : T' ⟶ T` of *ambient
schemes* rather than along the crystalline `f`-map: it is the adjoint transpose of the `f`-map
`F_T ⟶ (p₀)_* F_{T'}` through
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction`.  Two statements
about it are proved:

* `Crystalline.GlobalCrystallineSituation.affineFirstOrderComparison_pullbackSection` — **the
  normalisation**: `c` carries `AlgebraicGeometry.Scheme.Modules.pullbackSection`, that is the
  pullback `p₀^* a` of a section `a` of `F_T` over the whole of `T`, to the restriction of `a`
  along `p₀`.  This is the statement that the composite isomorphism of the chain carries `1 ⊗ s`
  to `p₀^* s`, because
  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` carries `1 ⊗ a` to exactly
  that pullback of sections.  It holds for every sheaf of `𝒪_{X/S}`-modules: no crystal
  hypothesis, no quasi-coherence, no affineness.
* `Crystalline.GlobalCrystallineSituation.isIso_affineFirstOrderComparison` and
  `Crystalline.GlobalCrystallineSituation.bijective_affineFirstOrderComparison_val_app` — for a
  crystal, `c` is an isomorphism, hence bijective on sections over every open of `T'`.

The normalisation is where the two pullback–pushforward adjunctions have to be compared, and the
ingredients are these.  `Thickening.ambientSchemePullbackIso` is
`CategoryTheory.Adjunction.leftAdjointUniq` of

* `Crystalline.GlobalCrystallineSituation.firstOrderCrysPullbackAdjunction`, the restriction of
  scalars along `Thickening.ringRestrictionSheafStructureIso` composed with
  `SheafOfModules.pullbackPushforwardAdjunction` at the crystalline `f`-map, and
* `Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` at `p₀` composed with a
  restriction of scalars and transported along `Thickening.ambientSchemePushforwardIso`

(`Crystalline.GlobalCrystallineSituation.ambientSchemePullbackIso_eq`), and the two transposes
are related by `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_homEquiv_symm`.  The unit of
the second adjunction is computed on sections in
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientPullbackAdjunction_unit_app_val_app`:
it is the unit of Mathlib's adjunction for `p₀`, because the two further factors —
`CategoryTheory.Adjunction.ofNatIsoRight` at `Thickening.ambientSchemePushforwardIso` and the
unit of `Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso` — are the identity on sections
(`Thickening.ambientSchemePushforwardIso_inv_app_val_app` and
`Stacks.SheafOfModules.restrictScalarsAdjunctionOfIso_unit_app_val_app`).  The transpose through
the first adjunction is `Thickening.moduleComparisonSheaf` up to the pullback of the counit of
that restriction of scalars
(`Crystalline.GlobalCrystallineSituation.crysPullbackAdjunction_homEquiv_symm_moduleFMapSheaf`),
and that counit is an isomorphism because it too is the identity on sections
(`Stacks.SheafOfModules.isIso_restrictScalarsAdjunctionOfIso_counit_app`).

### The two changes of spelling, and what still separates this from bijectivity

The two changes of spelling between the ring over which `extensionSectionsMap` extends scalars and
the ring over which `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` does are proved below.

* the scalars of `Γ(T, 𝒪_T)` on `Γ(T, F_T)` act through
  `Thickening.ringRestrictionSheafStructureIso`, whose component over an open is
  `AlgebraicGeometry.Scheme.Opens.topIso`, whereas
  `Crystalline.GlobalCrystallineSituation.bijective_moduleSiteRestrict_restrictOpenHom_top` is
  semilinear over `crysSheafRingMap (A.restrictOpenHom ⊤)`.  That those two maps
  `Γ(T, 𝒪_T) ⟶ Γ(T|_⊤, 𝒪)` agree, pointwise, is
  `ringRestrictionSheafStructureIso_inv_app_top_eq_crysSheafRingMap_restrictOpenHom`.
* the two tensor products `D' ⊗_D Mod` — the one in `extensionSectionsMap`, over the `D`-algebra
  `Crystalline.GlobalCrystallineSituation.algebraCrysSheafRingSiteP₀`, that is
  `(crysSheafRingMap p₀).toAlgebra`, and the one in the affine comparison, over
  `ModuleCat.extendScalars (p₀.targetHom.hom.appLE ⊤ ⊤ _).hom` — are **different types**.  Their
  carriers and their ring structures are definitionally equal, but their scalar actions are
  built from the two ring homomorphisms of
  `Crystalline.GlobalCrystallineSituation.appLE_top_eq_crysSheafRingMap_siteP₀`, which are equal
  only pointwise, by that theorem, and not as terms.  The additive equivalence between them is
  `Crystalline.GlobalCrystallineSituation.affineCrossEquiv`, built from a pair of mutually inverse
  additive maps with their two balancedness checks.

### The affine chain, and the one step that is still missing

The composite

`D' ⊗_D Mod  ⟶  Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T)  ⟶  Γ(T', p₀^* F_T)  ⟶  F(U, T', δ')`

is built below as `Crystalline.GlobalCrystallineSituation.affineExtensionHom`, an additive map,
and **each of its three factors is proved bijective**, hence so is the composite
(`...bijective_affineExtensionHom`): the first is `affineCrossEquiv`, the second is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at `⊤, ⊤` under quasi-coherence and
affineness, and the third is `...affineChainTailHom`, whose three factors are the comparison map
of a crystal and the two changes of spelling.  The computation that follows the base-change
comparison is proved in full, on an arbitrary scalar multiple of a pullback of a section
(`...affineChainTailHom_smul_ambientPullbackSectionTop`), and the value of
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` on a pure tensor is put in exactly
that form by `...extensionSectionsMap_tmul_restrictOpenMapTop`.

The last step is that the chain and `extensionSectionsMap` agree on a pure tensor, i.e. that

`(affinePullbackSectionsBaseChangeIso p₀ F_T ⊤ ⊤).hom (affineCrossModule (t ⊗ s))`

is `t · p₀^*(s)` read in the ambient spelling.  Both halves of that are available —
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_tmul` and
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` — and the difficulty is not
mathematical but that the pure tensor has two elaborations whose hidden instance arguments
differ: the first factor of the tensor product inside `ModuleCat.extendScalars` is
`(ModuleCat.restrictScalars p₀).obj Γ(T', 𝒪_{T'})` whereas the notation `⊗ₜ[R, f]` that
`ModuleCat.ExtendScalars`'s own lemmas are stated with writes `Γ(T', 𝒪_{T'})` with a
`Module.compHom` instance, so the two `Module Γ(T, 𝒪_T) Γ(T', 𝒪_{T'})` instances are
definitionally equal only after the `CommRingCat` carrier's ring structure is unfolded.  Mathlib
itself buys that crossing with a `backward.isDefEq.respectTransparency` option around its
`ModuleCat.ExtendScalars` section, which is not available here.

The way the step is taken is to cross that boundary only where it is affordable, namely in a
declaration whose *expected* type is the extension of scalars, and never between two
already-elaborated terms.  `Crystalline.GlobalCrystallineSituation.affineCrossModule`,
`...affineCrossModule_tmul`, `...affineBaseChangeTopHom_affineCrossModule_tmul`,
`...affineBaseChangeTop_tmul` and `...affineBaseChangeTopIso_hom_tmul` each cross it once, in
that position; the composite is then assembled through
`Crystalline.GlobalCrystallineSituation.affineExtensionFun`, which applies the base-change
comparison as a morphism of `ModuleCat` so that no coercion has to be identified with another
one at a pure-tensor argument.  See the section comment above
`Crystalline.GlobalCrystallineSituation.affineBaseChangeTop_one_tmul`.

No datum, hypothesis structure or weakened statement stands in for any of this, and nothing below
raises a heartbeat budget.

Nothing in this module carries a `@[stacks]` attribute.  The identification of the base-change
map with an extension of scalars is bookkeeping internal to the construction of the connection
of [Stacks, Tag 07J6], which is tagged where it is built.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry TensorProduct ChangeOfRings

universe v₁ u₁ u

noncomputable section

namespace Stacks.SheafOfModules

/-- A presheaf of modules acts trivially through the identity morphism. -/
private theorem val_map_id_apply {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (N : _root_.SheafOfModules.{u} R) (W : Cᵒᵖ) (x : N.val.obj W) :
    N.val.map (𝟙 W) x = x := by
  rw [N.val.map_id W]; rfl

/-- **The unit of the adjunction of restrictions of scalars along an isomorphism of sheaves of
rings is the identity on sections.** -/
theorem restrictScalarsAdjunctionOfIso_unit_app_val_app {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (e : R ≅ R')
    (N : _root_.SheafOfModules.{u} R') (W : Cᵒᵖ) (x : N.val.obj W) :
    ((restrictScalarsAdjunctionOfIso e).unit.app N).val.app W x = x :=
  val_map_id_apply N W x

/-- **The counit of the adjunction of restrictions of scalars along an isomorphism of sheaves of
rings is the identity on sections.** -/
theorem restrictScalarsAdjunctionOfIso_counit_app_val_app {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (e : R ≅ R')
    (N : _root_.SheafOfModules.{u} R) (W : Cᵒᵖ) (x : N.val.obj W) :
    ((restrictScalarsAdjunctionOfIso e).counit.app N).val.app W x = x :=
  val_map_id_apply N W x

/-- A morphism of sheaves of modules which is an isomorphism is an isomorphism on sections. -/
theorem isIso_val_app_of_isIso {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {N N' : _root_.SheafOfModules.{u} R} (φ : N ⟶ N') [IsIso φ]
    (W : Cᵒᵖ) : IsIso (φ.val.app W) :=
  ⟨(inv φ).val.app W, congrArg (fun k : N ⟶ N ↦ k.val.app W) (IsIso.hom_inv_id φ),
    congrArg (fun k : N' ⟶ N' ↦ k.val.app W) (IsIso.inv_hom_id φ)⟩

/-- **The counit of the adjunction of restrictions of scalars along an isomorphism of sheaves of
rings is an isomorphism.**  It is the identity on sections, and so is the unit of the adjunction
read in the other direction, so the two are mutually inverse. -/
instance isIso_restrictScalarsAdjunctionOfIso_counit_app {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (e : R ≅ R')
    (N : _root_.SheafOfModules.{u} R) :
    IsIso ((restrictScalarsAdjunctionOfIso e).counit.app N) := by
  refine ⟨(restrictScalarsAdjunctionOfIso e.symm).unit.app N, ?_, ?_⟩ <;> ext W x
  · change N.val.map (𝟙 W) (N.val.map (𝟙 W) x) = x
    rw [N.val.map_id W]; rfl
  · change N.val.map (𝟙 W) (N.val.map (𝟙 W) x) = x
    rw [N.val.map_id W]; rfl

/-- **The adjoint transpose through the adjunction of restrictions of scalars along an
isomorphism of sheaves of rings is the morphism itself, on sections.**  The unit of that
adjunction is the identity on sections and a restriction of scalars does not move them, so the
transpose of a morphism out of a restriction of scalars is that morphism, read over the other
sheaf of rings. -/
theorem restrictScalarsAdjunctionOfIso_homEquiv_val_app {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (e : R ≅ R')
    {N : _root_.SheafOfModules.{u} R'} {N' : _root_.SheafOfModules.{u} R}
    (φ : (_root_.SheafOfModules.restrictScalars e.hom).obj N ⟶ N') (W : Cᵒᵖ)
    (y : N.val.obj W) :
    (((restrictScalarsAdjunctionOfIso e).homEquiv N N') φ).val.app W y = φ.val.app W y := by
  rw [Adjunction.homEquiv_unit]
  change ((_root_.SheafOfModules.restrictScalars e.inv).map φ).val.app W
      (((restrictScalarsAdjunctionOfIso e).unit.app N).val.app W y) = _
  rw [restrictScalarsAdjunctionOfIso_unit_app_val_app]
  rfl

end Stacks.SheafOfModules

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The splitting of the sections of `𝒪_{T'}` -/

/-- **`p₀` splits the restriction along the diagonal**, on the sections of `𝒪_{X/S}`. -/
theorem crysSheafRingMap_siteι_siteP₀ (A : Thickening S) (b : crysSheafRing S A) :
    crysSheafRingMap (firstOrderThickeningSiteι S A)
      (crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b) = b :=
  moduleSiteRestrict_siteι_siteP₀ (SheafOfModules.unit (crystallineStructureSheaf S)) A b

/-- **`p₀` lands in the first summand**: the differential component of a section pulled back
along `p₀` vanishes. -/
@[simp]
theorem crysDiffPart_siteP₀ (A : Thickening S) (b : crysSheafRing S A) :
    crysDiffPart A (crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b) = 0 := rfl

/-- The differential component of a section of `𝒪_{T'}`, as an additive map. -/
def crysDiffPartHom (A : Thickening S) :
    crysSheafRing S (firstOrderThickeningObject S A) →+ crysDiffSections A :=
  AddMonoidHom.mk' (crysDiffPart A) (crysDiffPart_add A)

/-- The differential component, as an additive map, is the differential component. -/
@[simp]
theorem crysDiffPartHom_apply (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    crysDiffPartHom A t = crysDiffPart A t := rfl

/-- **The splitting `𝒪_{T'}(T') = 𝒪_T(T) ⊕ Ω` of [Stacks, Tag 07J2]**, written as the statement
that the two components recover the section. -/
theorem siteP₀_siteι_add_diffSection (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    crysSheafRingMap (firstOrderThickeningSiteP₀ S A)
          (crysSheafRingMap (firstOrderThickeningSiteι S A) t) +
        firstOrderThickeningDiffSection A (crysDiffPart A t) = t := by
  set b := crysSheafRingMap (firstOrderThickeningSiteι S A) t with hb
  have hker : crysSheafRingMap (firstOrderThickeningSiteι S A)
      (t - crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b) = 0 := by
    rw [map_sub, crysSheafRingMap_siteι_siteP₀, ← hb, sub_self]
  have hpart : crysDiffPart A (t - crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b) =
      crysDiffPart A t := by
    have := map_sub (crysDiffPartHom A) t (crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b)
    rw [crysDiffPartHom_apply, crysDiffPartHom_apply, crysDiffPartHom_apply,
      crysDiffPart_siteP₀, sub_zero] at this
    exact this
  have := firstOrderThickeningDiffSection_crysDiffPart A _ hker
  rw [hpart] at this
  rw [this]
  abel

/-! ### The base change of the sections along `p₀` -/

/-- The sections of `𝒪_{X/S}` over the first-order universal thickening, as an algebra over the
sections over the object, through `p₀`. -/
instance algebraCrysSheafRingSiteP₀ (A : Thickening S) :
    Algebra (crysSheafRing S A) (crysSheafRing S (firstOrderThickeningObject S A)) :=
  (crysSheafRingMap (firstOrderThickeningSiteP₀ S A)).toAlgebra

/-- The structure map of that algebra is the restriction map of `𝒪_{X/S}` along `p₀`. -/
theorem algebraMap_crysSheafRing_siteP₀ (A : Thickening S) (b : crysSheafRing S A) :
    algebraMap (crysSheafRing S A) (crysSheafRing S (firstOrderThickeningObject S A)) b =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b := rfl

/-- The scalars of `Γ(T, 𝒪_T)` act on `Γ(T', 𝒪_{T'})` by multiplication after `p₀`. -/
theorem crysSheafRing_smul_def (A : Thickening S) (b : crysSheafRing S A)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    b • t = crysSheafRingMap (firstOrderThickeningSiteP₀ S A) b * t := rfl

/-- **The differential component is semilinear over `p₀`.** -/
theorem crysDiffPart_smul (A : Thickening S) (b : crysSheafRing S A)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    crysDiffPart A (b • t) = b • crysDiffPart A t := by
  obtain ⟨c, ω, rfl⟩ : ∃ c ω, t = crysSheafRingMap (firstOrderThickeningSiteP₀ S A) c +
      firstOrderThickeningDiffSection A ω :=
    ⟨crysSheafRingMap (firstOrderThickeningSiteι S A) t, crysDiffPart A t,
      (siteP₀_siteι_add_diffSection A t).symm⟩
  rw [crysSheafRing_smul_def, mul_add, ← map_mul, crysSheafRingMap_siteP₀_mul_diffSection,
    crysDiffPart_add, crysDiffPart_add, crysDiffPart_siteP₀, crysDiffPart_siteP₀,
    crysDiffPart_diffSection, crysDiffPart_diffSection, zero_add, zero_add]

/-- **Restriction along the diagonal, as a map of `Γ(T, 𝒪_T)`-modules.**  It is linear and not
only semilinear because the scalars act on `𝒪_{T'}(T')` through `p₀`, which `i` splits. -/
def crysSheafRingMapSiteιLinear (A : Thickening S) :
    crysSheafRing S (firstOrderThickeningObject S A) →ₗ[crysSheafRing S A] crysSheafRing S A where
  toFun := crysSheafRingMap (firstOrderThickeningSiteι S A)
  map_add' := map_add _
  map_smul' b t := by
    rw [crysSheafRing_smul_def, map_mul, crysSheafRingMap_siteι_siteP₀, smul_eq_mul,
      RingHom.id_apply]

/-- Restriction along the diagonal, read linearly, is restriction along the diagonal. -/
@[simp]
theorem crysSheafRingMapSiteιLinear_apply (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    crysSheafRingMapSiteιLinear A t = crysSheafRingMap (firstOrderThickeningSiteι S A) t := rfl

/-- **The differential component, as a map of `Γ(T, 𝒪_T)`-modules.** -/
def crysDiffPartLinear (A : Thickening S) :
    crysSheafRing S (firstOrderThickeningObject S A) →ₗ[crysSheafRing S A] crysDiffSections A where
  toFun := crysDiffPart A
  map_add' := crysDiffPart_add A
  map_smul' := crysDiffPart_smul A

/-- The differential component, read linearly, is the differential component. -/
@[simp]
theorem crysDiffPartLinear_apply (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) :
    crysDiffPartLinear A t = crysDiffPart A t := rfl

/-- **A differential, read as a section of `𝒪_{T'}`, linearly in the differential.**  The
scalars of `Γ(T, 𝒪_T)` act on `𝒪_{T'}(T')` through `p₀`, and `p₀(b) · ω = b · ω`. -/
def firstOrderDiffSectionLinear (A : Thickening S) :
    crysDiffSections A →ₗ[crysSheafRing S A]
      crysSheafRing S (firstOrderThickeningObject S A) where
  toFun := firstOrderThickeningDiffSection A
  map_add' := firstOrderThickeningDiffSection_add A
  map_smul' b ω := (crysSheafRingMap_siteP₀_mul_diffSection A b ω).symm

/-- A differential read linearly as a section of `𝒪_{T'}` is that reading. -/
@[simp]
theorem firstOrderDiffSectionLinear_apply (A : Thickening S) (ω : crysDiffSections A) :
    firstOrderDiffSectionLinear A ω = firstOrderThickeningDiffSection A ω := rfl

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- The bilinear datum of
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap`. -/
def extensionSectionsAux (A : Thickening S) :
    crysSheafRing S (firstOrderThickeningObject S A) →+
      (M.val.obj (op A) →+ M.val.obj (op (firstOrderThickeningObject S A))) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ t • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s)
      (fun s s' ↦ by rw [map_add, smul_add]))
    (fun t t' ↦ by
      ext s
      change (t + t') • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s =
        t • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s +
          t' • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s
      rw [add_smul])

/-- **The base change of the sections of `F` along `p₀`**, on the algebraic tensor product of
global sections: the map `Γ(T', 𝒪_{T'}) ⊗_{Γ(T, 𝒪_T)} Γ(T, F_T) ⟶ Γ(T', F_{T'})` sending
`b ⊗ s` to `b · p₀^* s`. -/
def extensionSectionsMap (A : Thickening S) :
    crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →+
      M.val.obj (op (firstOrderThickeningObject S A)) :=
  TensorProduct.liftAddHom (extensionSectionsAux M A) (fun b t s ↦ by
    change (b • t) • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s =
      t • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) (b • s)
    rw [map_smulₛₗ, crysSheafRing_smul_def, smul_smul, mul_comm])

/-- **The base change of scalars on a pure tensor**: `t ⊗ s ↦ t · p₀^* s`. -/
@[simp]
theorem extensionSectionsMap_tmul (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) (s : M.val.obj (op A)) :
    extensionSectionsMap M A (t ⊗ₜ[crysSheafRing S A] s) =
      t • moduleSiteRestrict M (firstOrderThickeningSiteP₀ S A) s :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-! ### The splitting of the base change -/

/-- The reading of the second summand of the splitting `Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω` inside
the base change, `Ω ⊗_D Γ(T, F_T) ⟶ Γ(T', 𝒪_{T'}) ⊗_D Γ(T, F_T)`. -/
def firstOrderDiffTensorMap (A : Thickening S) :
    crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A) →ₗ[crysSheafRing S A]
      crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) :=
  TensorProduct.map (firstOrderDiffSectionLinear A) LinearMap.id

/-- The second summand of the splitting, on a pure tensor. -/
@[simp]
theorem firstOrderDiffTensorMap_tmul (A : Thickening S) (ω : crysDiffSections A)
    (s : M.val.obj (op A)) :
    firstOrderDiffTensorMap M A (ω ⊗ₜ[crysSheafRing S A] s) =
      firstOrderThickeningDiffSection A ω ⊗ₜ[crysSheafRing S A] s :=
  TensorProduct.map_tmul _ _ ω s

/-- **The splitting of [Stacks, Tag 07J2], read on the base change of the sections**: the map
`Γ(T, F_T) × (Ω ⊗_D Γ(T, F_T)) ⟶ Γ(T', 𝒪_{T'}) ⊗_D Γ(T, F_T)`, `(s, z) ↦ 1 ⊗ s + z`. -/
def firstOrderSplitTensor (A : Thickening S) :
    M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) →+
      crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) :=
  AddMonoidHom.mk'
    (fun x ↦ (1 : crysSheafRing S (firstOrderThickeningObject S A)) ⊗ₜ[crysSheafRing S A] x.1 +
      firstOrderDiffTensorMap M A x.2)
    (fun x y ↦ by
      change (1 : crysSheafRing S (firstOrderThickeningObject S A)) ⊗ₜ[crysSheafRing S A]
            (x.1 + y.1) + firstOrderDiffTensorMap M A (x.2 + y.2) = _
      rw [TensorProduct.tmul_add, map_add]
      abel)

/-- The splitting of the base change, on a pair. -/
@[simp]
theorem firstOrderSplitTensor_apply (A : Thickening S) (s : M.val.obj (op A))
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    firstOrderSplitTensor M A (s, z) =
      (1 : crysSheafRing S (firstOrderThickeningObject S A)) ⊗ₜ[crysSheafRing S A] s +
        firstOrderDiffTensorMap M A z := rfl

/-- **The inverse of the splitting of
`Crystalline.GlobalCrystallineSituation.firstOrderSplitTensor`**: a pure tensor `t ⊗ s` goes to
the pair `(i^*(t) · s, dpart(t) ⊗ s)` of its two components under the splitting
`Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω` of [Stacks, Tag 07J2]. -/
def firstOrderSplitTensorInv (A : Thickening S) :
    crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) →ₗ[
        crysSheafRing S A]
      M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :=
  LinearMap.prod
    ((TensorProduct.lid (crysSheafRing S A) (M.val.obj (op A))).toLinearMap ∘ₗ
      TensorProduct.map (crysSheafRingMapSiteιLinear A) LinearMap.id)
    (TensorProduct.map (crysDiffPartLinear A) LinearMap.id)

/-- The inverse of the splitting, on a pure tensor. -/
@[simp]
theorem firstOrderSplitTensorInv_tmul (A : Thickening S)
    (t : crysSheafRing S (firstOrderThickeningObject S A)) (s : M.val.obj (op A)) :
    firstOrderSplitTensorInv M A (t ⊗ₜ[crysSheafRing S A] s) =
      (crysSheafRingMap (firstOrderThickeningSiteι S A) t • s,
        crysDiffPart A t ⊗ₜ[crysSheafRing S A] s) := by
  refine Prod.ext ?_ ?_ <;>
    simp [firstOrderSplitTensorInv, crysSheafRingMapSiteιLinear, crysDiffPartLinear]

/-- The differential component of the unit section of `𝒪_{T'}` vanishes. -/
@[simp]
theorem crysDiffPart_one (A : Thickening S) :
    crysDiffPart A (1 : crysSheafRing S (firstOrderThickeningObject S A)) = 0 := by
  rw [← map_one (crysSheafRingMap (firstOrderThickeningSiteP₀ S A)), crysDiffPart_siteP₀]

/-- The inverse of the splitting undoes the second summand. -/
theorem firstOrderSplitTensorInv_firstOrderDiffTensorMap (A : Thickening S)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    firstOrderSplitTensorInv M A (firstOrderDiffTensorMap M A z) = (0, z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s =>
      rw [firstOrderDiffTensorMap_tmul, firstOrderSplitTensorInv_tmul,
        crysSheafRingMap_siteι_diffSection, crysDiffPart_diffSection, zero_smul]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', Prod.mk_add_mk, add_zero]

/-- **The splitting of [Stacks, Tag 07J2] on the base change of the sections**, as an additive
equivalence `Γ(T, F_T) × (Ω ⊗_D Γ(T, F_T)) ≃+ Γ(T', 𝒪_{T'}) ⊗_D Γ(T, F_T)`. -/
def firstOrderSplitTensorEquiv (A : Thickening S) :
    M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) ≃+
      crysSheafRing S (firstOrderThickeningObject S A) ⊗[crysSheafRing S A] M.val.obj (op A) where
  toFun := firstOrderSplitTensor M A
  invFun := firstOrderSplitTensorInv M A
  map_add' := map_add (firstOrderSplitTensor M A)
  left_inv x := by
    rw [firstOrderSplitTensor_apply, map_add, firstOrderSplitTensorInv_tmul,
      firstOrderSplitTensorInv_firstOrderDiffTensorMap, map_one, crysDiffPart_one, one_smul,
      TensorProduct.zero_tmul, Prod.mk_add_mk, add_zero, zero_add]
  right_inv t := by
    induction t using TensorProduct.inductionOn with
    | tmul t s =>
        rw [firstOrderSplitTensorInv_tmul, firstOrderSplitTensor_apply,
          firstOrderDiffTensorMap_tmul, ← TensorProduct.smul_tmul, crysSheafRing_smul_def,
          mul_one, ← TensorProduct.add_tmul, siteP₀_siteι_add_diffSection]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']

/-! ### The two base-change maps agree -/

/-- **On the second summand the base change of the sections is the canonical map of
[Stacks, Tag 07J6].** -/
theorem extensionSectionsMap_firstOrderDiffTensorMap (A : Thickening S)
    (z : crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A)) :
    extensionSectionsMap M A (firstOrderDiffTensorMap M A z) = diffAction M A z := by
  induction z using TensorProduct.inductionOn with
  | tmul ω s => rw [firstOrderDiffTensorMap_tmul, extensionSectionsMap_tmul, diffAction_tmul]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- **The base-change map on global sections of
`Crystalline.GlobalCrystallineSituation.firstOrderSectionsMap` is the base change of the sections
along `p₀`**, read through the splitting `Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω` of
[Stacks, Tag 07J2]. -/
theorem extensionSectionsMap_firstOrderSplitTensorEquiv (A : Thickening S)
    (x : M.val.obj (op A) × (crysDiffSections A ⊗[crysSheafRing S A] M.val.obj (op A))) :
    extensionSectionsMap M A (firstOrderSplitTensorEquiv M A x) = firstOrderSectionsMap M A x := by
  obtain ⟨s, z⟩ := x
  change extensionSectionsMap M A (firstOrderSplitTensor M A (s, z)) = _
  rw [firstOrderSplitTensor_apply, map_add, extensionSectionsMap_tmul,
    extensionSectionsMap_firstOrderDiffTensorMap, one_smul, firstOrderSectionsMap_apply]

/-- **The bijectivity of [Stacks, Tag 07J6] on global sections is the bijectivity of the base
change of the sections along `p₀`.**  Unconditional: the two maps differ by the additive
equivalence `Γ(T', 𝒪_{T'}) ⊗_D Γ(T, F_T) ≅ Γ(T, F_T) ⊕ (Ω ⊗_D Γ(T, F_T))` that the splitting
`Γ(T', 𝒪_{T'}) = Γ(T, 𝒪_T) ⊕ Ω` of [Stacks, Tag 07J2] induces. -/
theorem bijective_firstOrderSectionsMap_iff_bijective_extensionSectionsMap (A : Thickening S) :
    Function.Bijective (firstOrderSectionsMap M A) ↔
      Function.Bijective (extensionSectionsMap M A) := by
  rw [show (firstOrderSectionsMap M A : _ → _) =
      (extensionSectionsMap M A) ∘ (firstOrderSplitTensorEquiv M A) from
    funext fun x ↦ (extensionSectionsMap_firstOrderSplitTensorEquiv M A x).symm,
    EquivLike.bijective_comp]

end Crystalline.GlobalCrystallineSituation

end

end
