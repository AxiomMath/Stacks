module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientTwistDownFactor
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwistedPullbackModuleSituation

/-!
# The twist-indexed maps of [Stacks, Tag 0GAA] on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`. `BitUniformityIII/BlowupTwistedPullbackModuleSituation.lean` exhibits
`Stacks.LocalCohomology.UniformityIII.ModuleSituation` on that blowup. The three remaining clauses
of [Stacks, Tag 0GAA] are stated for
`Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`, which carries nine further fields;
this file supplies **five** of them on the blowup, namely the five that are about the maps
`𝒪_X(q) ⟶ 𝒪_X(q')` of `q' ≤ q` induce on cohomology:

| field | here |
| - | - |
| `Htr` | `Stacks.LocalCohomology.UniformityIII.blowupHtr` |
| `HGtr` | `Stacks.LocalCohomology.UniformityIII.blowupHGtr` |
| `HGtr_trans` | `Stacks.LocalCohomology.UniformityIII.blowupHGtr_comp` |
| `pullbackToImage_tr` | `Stacks.LocalCohomology.UniformityIII.blowupHtr_comp_δ_free` |
| `kernelToImage_tr` | `Stacks.LocalCohomology.UniformityIII.toCycles_comp_blowupHGtr` |

The four fields it does *not* supply are `dotted`, `kernelToImage_dotted`, `secM` and
`secM_freeSections`. The first two are **proved**, at the declared types of the fields, in
`BitUniformityIII/BlowupTwistDownVanishing.lean` — `…blowupDotted` and
`…kernelToImage_blowupDotted` — on the vanishing of `ℱ(q) ⟶ p^*K(q) ⟶ p^*K(q - c)` proved there.
The last two need the canonical maps `I^qM ⟶ H⁰(X, p^*M(q))`, which nothing constructs, so no
`TwistedModuleSituation` is constructed anywhere yet.

The five fields below are still stated as morphisms of `CategoryTheory.ModuleCat` rather than as
`A`-linear maps between the `ModuleSituation`'s own `H` and `HG`. That passage costs nothing —
the fields of `…blowupModuleSituationOf` are `.hom` of `blowupHmodMap` — but it has not been
carried out for them.

**[Stacks, Tag 0GA9] is not an available input to that vanishing**, and a comparison with the
ideal-sheaf blowup would not make it one. Its Lean form
`AlgebraicGeometry.schemeTheoreticSupport_iff_exceptionalTwistContraction_eq_zero` asks for
`[F.IsQuasicoherent]` **and** `[F.IsFiniteType]`. Quasi-coherence of `ℱ(q)` is available
(`Stacks.LocalCohomology.UniformityIII.isQuasicoherent_twistedPullbackSupported`); finite type has
no producer anywhere in the tree for `ℱ(q)`, so the tag does not apply to it even on
`AlgebraicGeometry.blowUp`, where it is stated.

What the vanishing can be built from instead, with no appeal to 0GA9, is the cover of `Proj` by
the basic opens `D₊(b⁽¹⁾)`, `b ∈ I`
(`Stacks.Blowup.iSup_basicOpen_reesDegOne_eq_top`), together with
[Stacks, Tag 0GA8] on this blowup — proved, with no comparison with the ideal-sheaf blowup, as
`Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero` — and the `c`-step
scalar/twist law of `BitUniformityIII/TwistDownMultiplication.lean`. The relevant order of that
law is `Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOnePow`, and its form inside
the geometric factor is
`Stacks.Blowup.twistDownFactorMap_comp_twistScalarFactorMap_reesDegOnePow`: it exhibits
`twistDownFactorMap I q (q - c)` followed by multiplication by `(b⁽¹⁾)^c` as multiplication by
`b^c ∈ I^c`, which 0GA8 kills on `ℱ(q)`; on `D₊(b⁽¹⁾)` multiplication by `(b⁽¹⁾)^c` is invertible,
so the twisted-down map itself vanishes there.

**Both halves of the local-to-global step are available**: the invertibility of `(b⁽¹⁾)^c` on
`D₊(b⁽¹⁾)` and the gluing of the local vanishings.

* the invertibility is proved, as
  `Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_twistScalarSheafMap_pow_app` for the
  twisting sheaves themselves and
  `…bijective_twistSheafScalarMap_pow_app` for the twists `ℱ(n) = ℱ ⊗ 𝒪(n)` of an arbitrary
  sheaf of modules, in
  `StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistScalarTriviality.lean`: for
  every open `W ⊆ D₊(f)` and **every integer** twist, multiplication by `f ^ m` is a bijection on
  the sections over `W`. The integer twist is the point — `q - c` is negative for small `q`, and
  the other laws of that file ask for natural exponents. The underlying local
  triviality is [Stacks, Tag 01MS],
  `Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom`;
* the gluing never needed proving. `TopCat.Sheaf.eq_hom_of_restrict` of
  `StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluing.lean` says that a morphism of presheaves
  of `𝒪`-modules into a *sheaf* is determined by its restrictions to a covering, with no
  compatibility hypothesis; taking the local morphisms to be `0` is exactly "vanishing on a cover
  implies zero". `TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf` is its sections form.

**The tensor slot is handled too, in both halves.** The degree-zero half
is `TopDegreeBaseChange/GeometricFactorBaseScalar.lean`, proved without any braiding; the
degree-`c` half is `TensorSectionNonvanishing/ProjTwistLeftSlotScalar.lean`, proved with it, and
the paragraphs below describe what it needs. The reason the two halves differ is this:
`Stacks.Blowup.twistedGeometricFactor I q` is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula`, whose tensor step is
`Stacks.SheafOfModules.tensorLeftFunctor` at the fixed factor: the twist `𝒪_X(q)` sits in the
**left** slot, `𝒪_X(q) ⊗ p^*Ñ`, and `geometricFactorFormulaMap` — hence
`Stacks.Blowup.twistScalarFactorMap` and `Stacks.Blowup.twistDownFactorMap` — is `φ ⊗ 𝟙`. Every
twisting result of `TensorSectionNonvanishing/` is stated at the **right** slot:
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafOfModules 𝒮 ℱ m` is `ℱ ⊗ 𝒪(m)` and
`…twistSheafScalarMap` is `𝟙 ⊗ φ`. So the two local statements above, and the degree-zero
identification below, apply to `p^*Ñ ⊗ 𝒪_X(q)` and not yet to the geometric factor.

**For a base scalar the transport needs no braiding.** A scalar in the fixed
left slot is that scalar on the tensor product, by
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap_smul_id_app` of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/GeometricFactorBaseScalar.lean`: there `φ ⊗ 𝟙`
and `𝟙 ⊗ φ` are endomorphisms of *the same* object and agree already on the pure tensors of
local sections — `Stacks.RingedSpace.map_smul_tmul` against `map_tmul_smul`, the mirror of
`AlgebraicGeometry.tensorLeft_linear`'s own last step. The braiding is not needed for this case.

**For the degree-`c` scalar the braiding is unavoidable, and it costs one commuting square.**
`twistScalarSheafMap … ((b⁽¹⁾)^c) : 𝒪_X(q-c) ⟶ 𝒪_X(q)` is not an endomorphism, so `φ ⊗ 𝟙` and
`𝟙 ⊗ φ` land in different objects and only a braiding relates them. The whole of what is needed
is `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_naturality` —
`swap ≫ (g ⊗ f) = (f ⊗ g) ≫ swap`, so at `g = 𝟙` it turns `φ ⊗ 𝟙` into `𝟙 ⊗ φ` — conjugated
into a statement about the maps on sections, in
`TensorSectionNonvanishing/ProjTwistLeftSlotScalar.lean`.

**Three points about the proof that are easy to get wrong.**

* `Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt` is **not** needed. The braiding
  never has to be computed on a pure tensor: the invertibility is a `Function.Bijective`
  of a map on sections, and conjugating a bijection by two bijections is a statement about four
  bare functions. The only categorical input is that an isomorphism of sheaves of modules is
  bijective on sections.
* The **three spellings of the tensor product cost nothing.**
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, which `tensorLeftFunctor` and so
  `geometricFactorFormula` are built from;
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, which `tensorSheafMap` and the
  braiding are stated at; and `twistSheafOfModules` — all three are equal by `rfl`, as are the
  morphisms (`Stacks.TensorSheafDedup.tensorSheaf_eq` and `…tensorSheafMap_eq_sheafifyMap`, both
  `rfl`). No whiskering bridge is used:
  `Stacks.SheafOfModules.TensorPower.tensorSheafMap_id_left_eq_whiskerLeft` (the site-level form;
  a ringed-space form of the same name exists in `Stacks.TensorSheafSpellingIso`) and
  `AlgebraicGeometry.tensorSheafMap_id_left_eq` are both about the
  *right*-hand slot and neither enters.
* The one comparison that is **not** `rfl` is the left-slot one:
  `(tensorFactorMap f).app M = tensorSheafMap f (𝟙 M)`, i.e. `f ▷ M` against `f ⊗ₘ 𝟙 M` at the
  level of presheaves of modules. It is `MonoidalCategory.tensorHom_id` sheafified by `congrArg`,
  the device of `TopDegreeBaseChange/GeometricFactorBaseScalar.lean`, and it is one line.

**The second bridge holds at every integer twist.** 0GA8 is formalized in the form
`a • 𝟙 ℱ(q) = 0` for the canonical `A`-linear structure `Stacks.Blowup.blowUpModulesLinear`,
while the `c`-step law delivers multiplication by the *degree-zero homogeneous* scalar
`Stacks.Blowup.reesConst I (b^c)`. These are the same morphism, and
`BitUniformityIII/BlowupDegreeZeroScalar.lean` proves it in three steps:

* `AlgebraicGeometry.globalSmulCenter_appTop_eq_baseScalar` — the base scalar
  `AlgebraicGeometry.baseScalar` of a scheme over `Spec(A)` is
  `Stacks.RegularSequence.globalSmulCenter` at the global function the scalar pulls back to. Both
  multiply the sections over every open by `AlgebraicGeometry.baseRingToSections`, so the proof
  is `CatCenter.ext` and `rfl`;
* `Stacks.LocalCohomology.UniformityIII.twistScalarSheafMap_reesConst_eq_globalSmulCenter_int` —
  the `AmbientKernelLift.lean` statement at every **integer** twist. Its own input
  `…ProjTwistedSections.twistScalarSheafMap_zero_eq_globalSmulCenter` is already stated for every
  integer, and the only obstacle is that
  `Stacks.LocalCohomology.UniformityIII.blowupTwist` is indexed by `ℕ`; the integer-indexed
  `Stacks.Blowup.blowUpTwist` removes it. The integer index is the point: the dotted arrow's
  source twist `q - c` is negative for small `q`;
* `Stacks.LocalCohomology.UniformityIII.twistScalarFactorMap_reesConst_app_eq_smul_id` — the same
  inside the geometric factor, through the base-scalar tensor slot above. The right-slot form
  `…TwistSectionsCoeffAction.tensorSheafMap_id_globalSmulCenter` is not needed.

**What the two bridges give, and what follows from them.**
`BitUniformityIII/BlowupTwistDownAnnihilation.lean` composes the `c`-step law with them and
proves `…kernelι_comp_twistDown_comp_twistScalar_eq_zero_of_mem`: the inclusion of `ℱ(q)`,
followed by twisting down to `q - c` and then by multiplication by `(b⁽¹⁾)^c`, is zero, for every
`b ∈ I` and every integer `q`. Dropping the trailing factor is the local step — invertibility of
`(b⁽¹⁾)^c` on `D₊(b⁽¹⁾)`, the cover, and the gluing — and all three are available, so
`BitUniformityIII/BlowupTwistDownVanishing.lean` proves
`…kernelι_comp_twistDown_eq_zero_of_mem` and, from it, the dotted arrow
`…dottedOfPresentation` with its factorisation
`…blowupHmodMap_dottedOfPresentation_comp_toCycles`.

## Where the content is

All of it is in `BitUniformityIII/AmbientTwistDown.lean` and
`BitUniformityIII/AmbientTwistDownFactor.lean`: the family
`Stacks.Blowup.twistDownFactorMap I q q'` of natural transformations
`𝒪_X(q) ⊗ p^*(-) ⟶ 𝒪_X(q') ⊗ p^*(-)`, and its composition law. What is added here is only the
passage to cohomology, and it is formal:

* `Htr` is that transformation at an `A`-module, pushed through `Hⁱ(X, -)`;
* `HGtr` is it pushed through `CategoryTheory.ShortComplex.cyclesMap` and then `Hⁱ(X, -)`, since
  `𝒢` is `CategoryTheory.ShortComplex.cycles` of the twisted-pullback complex;
* the two naturality statements are `CategoryTheory.ShortComplex.toCycles_naturality` and the
  field `CategoryTheory.DeltaFunctor.δ_naturality` of the blowup's δ-functor
  `Stacks.LocalCohomology.UniformityIII.blowupDeltaMod`, applied to the morphism
  `Stacks.LocalCohomology.UniformityIII.twistDownFreeSequenceMap` of short exact sequences that
  the family induces.

Nothing here mentions the exponent `c` or the vanishing degree `d`: these are the twist
bookkeeping of Tag 0GAA, not its arithmetic, and no clause of the tag is proved in this file.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupHtr`: **the field `Htr`** —
  `Hⁱ(X, p^*M(q)) ⟶ Hⁱ(X, p^*M(q'))`.
* `Stacks.LocalCohomology.UniformityIII.blowupHGtr`: **the field `HGtr`** —
  `Hⁱ(X, 𝒢(q)) ⟶ Hⁱ(X, 𝒢(q'))`.
* `Stacks.LocalCohomology.UniformityIII.twistDownFreeSequenceMap`: the morphism of short exact
  sequences `(0 → 𝒢(q) → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0) ⟶ (\text{the same at } q')`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.blowupHtr_self`,
  `…blowupHtr_comp`, `…blowupHGtr_self` and `…blowupHGtr_comp`: the two families are functorial;
  `blowupHGtr_comp` is **the field `HGtr_trans`**.
* `Stacks.LocalCohomology.UniformityIII.blowupHtr_comp_δ_free`: **the field
  `pullbackToImage_tr`** — the connecting map of the first sequence is natural in the twist.
* `Stacks.LocalCohomology.UniformityIII.toCycles_comp_blowupHGtr`: **the field
  `kernelToImage_tr`** — `Hⁱ(X, p^*K(q)) ⟶ Hⁱ(X, 𝒢(q))` is natural in the twist.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- `Hⁱ(X, -)` of a morphism of sheaves depends on the morphism alone, so a morphism may be
rewritten underneath it. This is the congruence lemma that replaces a `rw` under
`Stacks.LocalCohomology.UniformityIII.blowupHmodMap`, whose motive check is what exhausts the
heartbeat budget on a morphism of sheaves of modules; it is proved by `subst` and proof
irrelevance. -/
theorem blowupHmodMap_congr (i : ℕ) {F G : (blowupScheme I).Modules} {φ ψ : F ⟶ G} (h : φ = ψ) :
    blowupHmodMap I i φ = blowupHmodMap I i ψ := by
  subst h
  rfl

/-- `Hⁱ(X, -)` sends a morphism equal to the identity to the identity. -/
private theorem blowupHmodMap_eq_id (i : ℕ) {F : (blowupScheme I).Modules} {φ : F ⟶ F}
    (h : φ = 𝟙 _) : blowupHmodMap I i φ = 𝟙 _ :=
  (blowupHmodMap_congr I i h).trans (((blowupΓmod I).rightDerived i).map_id _)

/-- `Hⁱ(X, -)` sends a composite equal to `χ` to a composite equal to `Hⁱ(X, χ)`. -/
private theorem blowupHmodMap_comp_eq (i : ℕ) {F G H : (blowupScheme I).Modules}
    {φ : F ⟶ G} {ψ : G ⟶ H} {χ : F ⟶ H} (h : φ ≫ ψ = χ) :
    blowupHmodMap I i φ ≫ blowupHmodMap I i ψ = blowupHmodMap I i χ :=
  (((blowupΓmod I).rightDerived i).map_comp _ _).symm.trans (blowupHmodMap_congr I i h)

/-- The twisting-down transformation `𝒪_X(q) ⊗ p^*(-) ⟶ 𝒪_X(q') ⊗ p^*(-)` read at the
`CategoryTheory.SheafOfModules` view of the category of sheaves of modules on the blowup, which is
where the right derived functors of `blowupΓmod` are elaborated.

The term is `Stacks.Blowup.twistDownFactorMap` itself, which typechecks here because the two
views are definitionally equal; the restatement is needed for the same reason
`Stacks.LocalCohomology.UniformityIII.twistedPullbackFunctor` is. -/
abbrev twistedPullbackTwistDown (q q' : ℤ) (hq : q' ≤ q) :
    twistedPullbackFunctor I q ⟶ twistedPullbackFunctor I q' :=
  Stacks.Blowup.twistDownFactorMap I q q' hq

section ShortComplex

variable {S : ShortComplex (ModuleCat.{u} A)}

/-- The morphism of twisted-pullback complexes `S ⊗ 𝒪_X(q) ⟶ S ⊗ 𝒪_X(q')` the twisting-down
transformation induces, for a short complex `S` of `A`-modules. -/
abbrev twistDownShortComplexMap (q q' : ℤ) (hq : q' ≤ q) :
    S.map (twistedPullbackFunctor I q) ⟶ S.map (twistedPullbackFunctor I q') :=
  S.mapNatTrans (twistedPullbackTwistDown I q q' hq)

/-- The induced morphism of complexes is the identity at `q' = q`. -/
theorem twistDownShortComplexMap_self (q : ℤ) :
    twistDownShortComplexMap I q q le_rfl (S := S) = 𝟙 _ := by
  rw [twistDownShortComplexMap, twistedPullbackTwistDown,
    Stacks.Blowup.twistDownFactorMap_self]
  rfl

/-- The induced morphisms of complexes compose. Both sides are built componentwise out of the
natural transformations, so the law is `Stacks.Blowup.twistDownFactorMap_comp` in each of the
three degrees. -/
theorem twistDownShortComplexMap_comp (q q' q'' : ℤ) (hq'' : q'' ≤ q') (hq : q' ≤ q)
    (h : q'' ≤ q) :
    twistDownShortComplexMap I q q' hq (S := S) ≫ twistDownShortComplexMap I q' q'' hq'' =
      twistDownShortComplexMap I q q'' h := by
  rw [twistDownShortComplexMap, twistDownShortComplexMap, twistDownShortComplexMap,
    twistedPullbackTwistDown, twistedPullbackTwistDown, twistedPullbackTwistDown,
    ← Stacks.Blowup.twistDownFactorMap_comp I q q' q'' hq'' hq h]
  rfl

end ShortComplex

/-! ### The field `Htr` -/

/-- **The field `Htr` of `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`, on the
blowup**: the map `Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ) ⟶ Hⁱ(X, 𝒪_X(q') ⊗ p^*Ñ)` that `𝒪_X(q) ⟶ 𝒪_X(q')`
induces, for any pair of integers `q' ≤ q` and any `A`-module `N`. -/
abbrev blowupHtr (N : ModuleCat.{u} A) (i : ℕ) (q q' : ℤ) (hq : q' ≤ q) :
    blowupHmodTwistedPullback I N i q ⟶ blowupHmodTwistedPullback I N i q' :=
  blowupHmodMap I i ((twistedPullbackTwistDown I q q' hq).app N)

/-- `Htr` is the identity at `q' = q`. -/
theorem blowupHtr_self (N : ModuleCat.{u} A) (i : ℕ) (q : ℤ) :
    blowupHtr I N i q q le_rfl = 𝟙 _ :=
  blowupHmodMap_eq_id I i (NatTrans.congr_app (Stacks.Blowup.twistDownFactorMap_self I q) N)

/-- **`Htr` is functorial.** -/
theorem blowupHtr_comp (N : ModuleCat.{u} A) (i : ℕ) (q q' q'' : ℤ) (hq'' : q'' ≤ q')
    (hq : q' ≤ q) (h : q'' ≤ q) :
    blowupHtr I N i q q' hq ≫ blowupHtr I N i q' q'' hq'' = blowupHtr I N i q q'' h :=
  blowupHmodMap_comp_eq I i
    ((NatTrans.comp_app (twistedPullbackTwistDown I q q' hq)
        (twistedPullbackTwistDown I q' q'' hq'') N).symm.trans
      (NatTrans.congr_app (Stacks.Blowup.twistDownFactorMap_comp I q q' q'' hq'' hq h) N))

/-! ### The field `HGtr` -/

section Image

variable {S : ShortComplex (ModuleCat.{u} A)}

/-- `CategoryTheory.ShortComplex.cyclesMap` depends on the morphism alone, so a morphism of
complexes may be rewritten underneath it; proved by `subst` and proof irrelevance. -/
theorem cyclesMap_congr
    {S₁ S₂ : ShortComplex (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf)}
    {φ ψ : S₁ ⟶ S₂} (h : φ = ψ) :
    ShortComplex.cyclesMap φ = ShortComplex.cyclesMap ψ := by
  subst h
  rfl

/-- **The twisting-down map `𝒢(q) ⟶ 𝒢(q')` of the sheaves themselves**, for `q' ≤ q`: `𝒢` is
`CategoryTheory.ShortComplex.cycles` of the twisted pullback of the presentation
(`Stacks.LocalCohomology.UniformityIII.twistedPullbackImage`), so the map is
`CategoryTheory.ShortComplex.cyclesMap` of the induced morphism of complexes.

The declared type is at the `CategoryTheory.SheafOfModules` spelling on purpose: with the
`AlgebraicGeometry.Scheme.Modules` spelling expected instead, the category of
`CategoryTheory.ShortComplex.cyclesMap` is unified with `(blowupScheme I).Modules`, where
`CategoryTheory.Limits.HasZeroMorphisms` does not synthesize. -/
abbrev twistDownCyclesMap (q q' : ℤ) (hq : q' ≤ q) :
    twistedPullbackImage I q (S := S) ⟶ twistedPullbackImage I q' (S := S) :=
  ShortComplex.cyclesMap (twistDownShortComplexMap I q q' hq (S := S))

/-- The map on `𝒢` is the identity at `q' = q`. -/
theorem twistDownCyclesMap_self (q : ℤ) : twistDownCyclesMap I q q le_rfl (S := S) = 𝟙 _ :=
  (cyclesMap_congr I (twistDownShortComplexMap_self I q (S := S))).trans
    (ShortComplex.cyclesMap_id _)

/-- The maps on `𝒢` compose. -/
theorem twistDownCyclesMap_comp (q q' q'' : ℤ) (hq'' : q'' ≤ q') (hq : q' ≤ q) (h : q'' ≤ q) :
    twistDownCyclesMap I q q' hq (S := S) ≫ twistDownCyclesMap I q' q'' hq'' =
      twistDownCyclesMap I q q'' h :=
  (ShortComplex.cyclesMap_comp _ _).symm.trans
    (cyclesMap_congr I (twistDownShortComplexMap_comp I q q' q'' hq'' hq h (S := S)))

/-- **The field `HGtr` of `Stacks.LocalCohomology.UniformityIII.TwistedModuleSituation`, on the
blowup**: the map `Hⁱ(X, 𝒢(q)) ⟶ Hⁱ(X, 𝒢(q'))` for `q' ≤ q`. -/
abbrev blowupHGtr (i : ℕ) (q q' : ℤ) (hq : q' ≤ q) :
    blowupHmod I i (twistedPullbackImage I q (S := S)) ⟶
      blowupHmod I i (twistedPullbackImage I q' (S := S)) :=
  blowupHmodMap I i (twistDownCyclesMap I q q' hq (S := S))

/-- `HGtr` is the identity at `q' = q`. -/
theorem blowupHGtr_self (i : ℕ) (q : ℤ) : blowupHGtr I i q q le_rfl (S := S) = 𝟙 _ :=
  blowupHmodMap_eq_id I i (twistDownCyclesMap_self I q (S := S))

/-- **The field `HGtr_trans`: `HGtr` is functorial.** The sheaf-level law is
`Stacks.Blowup.twistDownFactorMap_comp`, carried through `cyclesMap` by
`CategoryTheory.ShortComplex.cyclesMap_comp` and then through `Hⁱ(X, -)`. -/
theorem blowupHGtr_comp (i : ℕ) (q q' q'' : ℤ) (hq'' : q'' ≤ q') (hq : q' ≤ q) (h : q'' ≤ q) :
    blowupHGtr I i q q' hq (S := S) ≫ blowupHGtr I i q' q'' hq'' =
      blowupHGtr I i q q'' h :=
  blowupHmodMap_comp_eq I i (twistDownCyclesMap_comp I q q' q'' hq'' hq h (S := S))

/-! ### The field `kernelToImage_tr` -/

/-- **The field `kernelToImage_tr`**: the map `Hⁱ(X, p^*K(q)) ⟶ Hⁱ(X, 𝒢(q))` of the second short
exact sequence is natural in the twist.

At the level of sheaves this is `CategoryTheory.ShortComplex.toCycles_naturality`: the canonical
map to the cycles commutes with `cyclesMap`. -/
theorem toCycles_comp_blowupHGtr (i : ℕ) (q q' : ℤ) (hq : q' ≤ q) :
    blowupHmodMap I i (S.map (twistedPullbackFunctor I q)).toCycles ≫
        blowupHGtr I i q q' hq (S := S) =
      blowupHtr I S.X₁ i q q' hq ≫
        blowupHmodMap I i (S.map (twistedPullbackFunctor I q')).toCycles :=
  (blowupHmodMap_comp_eq I i rfl).trans
    ((blowupHmodMap_congr I i
        (ShortComplex.toCycles_naturality (twistDownShortComplexMap I q q' hq (S := S)))).trans
      (blowupHmodMap_comp_eq I i rfl).symm)

/-! ### The field `pullbackToImage_tr` -/

/-- **The morphism of short exact sequences
`(0 → 𝒢(q) → (𝒪_{Yₙ})^{⊕r}(q) → p^*M(q) → 0) ⟶ (\text{the same at } q')`** that the
twisting-down transformation induces.

Its first component is `cyclesMap`; the square against the inclusion of the cycles is
`CategoryTheory.ShortComplex.cyclesMap_i` and the square against the surjection is the
corresponding square of the induced morphism of twisted-pullback complexes. -/
def twistDownFreeSequenceMap (q q' : ℤ) (hq : q' ≤ q) :
    twistedPullbackFreeSequence I q (S := S) ⟶ twistedPullbackFreeSequence I q' (S := S) where
  τ₁ := twistDownCyclesMap I q q' hq (S := S)
  τ₂ := (twistDownShortComplexMap I q q' hq (S := S)).τ₂
  τ₃ := (twistDownShortComplexMap I q q' hq (S := S)).τ₃
  comm₁₂ := ShortComplex.cyclesMap_i _
  comm₂₃ := (twistDownShortComplexMap I q q' hq (S := S)).comm₂₃

/-- **The field `pullbackToImage_tr`**: the connecting map
`Hⁱ(X, p^*M(q)) ⟶ Hⁱ⁺¹(X, 𝒢(q))` of the first short exact sequence is natural in the twist.

This is the field `CategoryTheory.DeltaFunctor.δ_naturality` of
`Stacks.LocalCohomology.UniformityIII.blowupDeltaMod` at
`Stacks.LocalCohomology.UniformityIII.twistDownFreeSequenceMap`; the two functors of the δ-functor
involved are the right derived functors of `blowupΓmod` by
`Stacks.LocalCohomology.UniformityIII.blowupDeltaMod_functor`, so its two outer maps are `Htr` and
`HGtr`. -/
theorem blowupHtr_comp_δ_free (hS : S.ShortExact) (i : ℕ) (q q' : ℤ) (hq : q' ≤ q) :
    blowupHtr I S.X₃ i q q' hq ≫
        (blowupDeltaMod I).δ (shortExact_twistedPullbackFreeSequence I q' hS) i =
      (blowupDeltaMod I).δ (shortExact_twistedPullbackFreeSequence I q hS) i ≫
        blowupHGtr I (i + 1) q q' hq (S := S) :=
  (blowupDeltaMod I).δ_naturality (shortExact_twistedPullbackFreeSequence I q hS)
    (shortExact_twistedPullbackFreeSequence I q' hS)
    (twistDownFreeSequenceMap I q q' hq) i

end Image

end Stacks.LocalCohomology.UniformityIII

end
