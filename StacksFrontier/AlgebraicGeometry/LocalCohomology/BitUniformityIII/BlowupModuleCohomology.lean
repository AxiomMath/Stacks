module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupModuleSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningVanishingAboveDegree
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapStructureSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of a twisted pullback to the blowup

Let `A` be a commutative Noetherian ring, `I ⊆ A` an ideal and `p : X → Spec(A)` the blowup of
`Spec(A)` in `I`. For an `A`-module `N` this file builds the `A`-modules

`Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)`,  `i : ℕ`, `q : ℤ`,

as the right derived functors of `A`-linear global sections applied to the twisted pullback, and
proves that they are quasi-coherent in the sheaf and vanish above a degree depending only on `X`.

`Stacks.LocalCohomology.UniformityIII.ModuleSituation` carries four such families — `H`,
`Hfree`, `HG` and `HF`, the cohomology of the twists of `p^*M`, `(𝒪_{Yₙ})^{⊕r}`, `𝒢` and `ℱ` in
the proof of [Stacks, Tag 0GAA] — as bare `ModuleCat A`-valued data, together with the three
fields `vanishing_H`, `vanishing_HG` and `vanishing_HF` asserting that each vanishes above the
invariant `d` of the underlying Situation. This file supplies the blowup's own answer to those
families and to those three fields, for an arbitrary `A`-module in place of an
`(A, n, c)`-module.

## What is reused rather than rebuilt

The twisted pullback itself is `Stacks.Blowup.twistedGeometricFactor`, the functor
`N ↦ 𝒪_X(q) ⊗_{𝒪_X} p^*Ñ` of
`StacksFrontier/AlgebraicGeometry/Blowup/TwistedPullbackSections.lean`, which already carries its
additivity (`Stacks.Blowup.additive_twistedGeometricFactor`), its `A`-linearity and its
preservation of arbitrary direct sums
(`Stacks.Blowup.preservesColimitsOfShape_discrete_twistedGeometricFactor`). Nothing of that is
restated here. What is added is its quasi-coherence, the composition with the `A`-linear
cohomology of `BitUniformityIII/BlowupSituation.lean`, and the vanishing.

## Why the vanishing is uniform in the module

`Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH` produces a degree past
which `Hⁱ(X, ℱ)` vanishes for *every* quasi-coherent `ℱ` at once — it is Čech vanishing for a
finite affine open cover of `X`, so the bound depends on `X` alone. It is the same degree that
`blowupSituationOf` takes for its field `d`. Consequently the three vanishing fields of a
`ModuleSituation` built on `blowupSituationOf` need nothing about the module beyond
quasi-coherence of the sheaf whose cohomology is taken, and that is proved here once and for
all: the inverse image of a quasi-coherent module is quasi-coherent ([Stacks, Tag 01BG]) and the
tensor product of two quasi-coherent modules is quasi-coherent ([Stacks, Tag 01CE]).

## What this gives towards `freeIso`

A `ModuleSituation` needs, besides the four families and the vanishing, the comparison
`freeIso` identifying `Hⁱ(X, p^*((A/Iⁿ)^{⊕r})(q))` with `(Fin r → Hⁱ(X, 𝒪_{Yₙ}(q)))`, i.e. with
a finite direct sum of the field `Hdiv` of the underlying Situation. It has two inputs, and both
are settled below up to one affine identification, which
`BitUniformityIII/BlowupFreeCohomology.lean` takes;
`Stacks.LocalCohomology.UniformityIII.blowupFreeIsoSituationOf` there is the field itself.

The second — that cohomology commutes with finite direct sums — is
`blowupHmodTwistedPullbackPiEquiv`.

The first is geometric, and is the substantial one:

`𝒪_X(q) ⊗ p^*((A/Iⁿ)~) ≅ 𝒪_{Yₙ}(q)`,

the identification of the twisted pullback of the `n`-th thickened structure ring with the twist
of the structure sheaf of the `n`-th thickening `Yₙ` of the exceptional divisor. It is not a
restatement of anything already in the library:
`Stacks.LocalCohomology.UniformityIII.thickeningSheaf` is defined in
`BitUniformityIII/BlowupTwists.lean` as the direct image of the structure sheaf of the closed
subscheme cut out by `Stacks.LocalCohomology.UniformityIII.thickeningIdeal`, the `n`-th power of the
inverse image of `I`.

Its *ideal-sheaf* half is `thickeningIdeal_eq_comap`: the thickening is cut
out by the scheme-theoretic inverse image of the ideal sheaf of `Iⁿ`, so `Yₙ` is `p⁻¹(V(Iⁿ))`
scheme-theoretically and not merely a power of the exceptional divisor. Its *module-level* half
is `pullbackPowStructureSheafIso`: `p^*(𝒪_{V(Iⁿ)}) ≅ 𝒪_{Yₙ}`, the base change of a closed
immersion read on structure sheaves, by the general
`Stacks.IdealSheaf.comapStructureSheafIso`.

### The remaining step is affine, and is taken elsewhere

`p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}` as literally stated needs one further step, which contains no geometry and
no blowup: that `𝒪_{V(Iⁿ)}` — the structure sheaf of the subscheme of `powIdealSheaf I n`,
pushed forward to `Spec(A)` — is `AlgebraicGeometry.tilde (ModuleCat.of A (A ⧸ Iⁿ))`. It is
`Stacks.LocalCohomology.tildeQuotientIsoSubschemePushforward` of
`BitUniformityIII/BlowupFreeCohomology.lean`, the join of
`Stacks.LocalCohomology.tildeQuotientIsoPushforward` (`(A/Iⁿ)~ ≅ π_* 𝒪` for
`π : Spec(A/Iⁿ) ⟶ Spec(A)`) with
`Stacks.LocalCohomology.subschemeIsoSpecQuotient_hom_comp_subschemeι` (that `π` and
`(powIdealSheaf I n).subschemeι` are the same closed immersion into `Spec(A)`).

The identification of `𝒪_{Yₙ}` with `𝒪_X/ℐ_{Yₙ}` is *not* among what is left: it is in hand,
from `Stacks.LocalCohomology.UniformityIII.epi_thickeningProj` together with
`Stacks.IdealSheafSequence.divisorIdeal_shortExact` at `thickeningIdeal I n`.
`pullbackPowStructureSheafIso` neither supplies nor needs it — the affine base-change route
reaches `𝒪_{Yₙ}` as a pushforward directly, without presenting it as a quotient of `𝒪_X`.

## Why the direct sums take a proof and not an `inferInstance`

That cohomology commutes with finite direct sums is **not** formal in the way it may appear.
Mathlib's `CategoryTheory.Functor.rightDerived` of an additive functor carries no
`CategoryTheory.Functor.Additive` instance, and
`StacksFrontier/Algebra/Homology/RightDerivedBiprod.lean` proves a different statement, that right
derivation commutes with biproducts *of functors*. What supplies it is
`StacksFrontier/Homology/DerivedIndexing/Basic.lean`: the `ℕ`-indexed right derived functors are the
functors of a cohomological δ-functor ([Stacks, Tag 010Q]), and additivity of each is a field of
`CategoryTheory.DeltaFunctor`. `blowupDeltaMod` is that δ-functor for `blowupΓmod`, so
`additive_blowupHmod` (`BitUniformityIII/BlowupModuleSituation.lean`) is one projection out of
it, and the biproducts follow from `CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullback`:
  `Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` as an `A`-module.
* `Stacks.LocalCohomology.UniformityIII.twistedPullbackCohomologyFunctor`: the same as a functor
  `Mod(A) ⥤ Mod(A)`, which is where its additivity is used.

## Main results

* `Stacks.LocalCohomology.UniformityIII.isQuasicoherent_twistedGeometricFactor_obj`:
  `𝒪_X(q) ⊗ p^*Ñ` is quasi-coherent, for every `A`-module `N` and every twist.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmodTwistedPullback`:
  `Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ) = 0` above the degree of `exists_forall_subsingleton_blowupH`.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmodTwistedPullback_blowupSituationOf`
  and `…_blowupSituation`: the same vanishing stated against the field `d` of the witness, which
  is the form the three vanishing fields of a `ModuleSituation` built on the blowup ask for.
* `Stacks.LocalCohomology.UniformityIII.blowupHmodBiproductIso`: **`Hⁱ(X, -)` commutes with
  finite direct sums of sheaves.**
* `Stacks.LocalCohomology.UniformityIII.blowupHmodTwistedPullbackPiEquiv`:
  **`Hⁱ(X, 𝒪_X(q) ⊗ p^*((N^{⊕r})~)) ≅ (Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ))^{⊕r}`**, the second input to the
  field `freeIso` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation`.
* `Stacks.LocalCohomology.UniformityIII.ofIdealTop_pow`: the ideal sheaf attached to a power of
  an ideal of global functions is that power of the ideal sheaf.
* `Stacks.LocalCohomology.UniformityIII.pullbackPowStructureSheafIso`:
  **`p^*(𝒪_{V(Iⁿ)}) ≅ 𝒪_{Yₙ}`**, the module-level half of the same identification.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Quasi-coherence of the twisted pullback -/

/-- **`𝒪_X(q) ⊗ p^*Ñ` is quasi-coherent**, for every `A`-module `N` and every twist.

The three factors of `Stacks.Blowup.twistedGeometricFactor` each preserve quasi-coherence:
`Ñ` is quasi-coherent on `Spec A`, the inverse image of a quasi-coherent module along an
arbitrary morphism of schemes is quasi-coherent ([Stacks, Tag 01BG]), and the tensor product of
quasi-coherent modules is quasi-coherent ([Stacks, Tag 01CE]), the twist being quasi-coherent by
`Stacks.Blowup.isQuasicoherent_blowUpTwist`. -/
instance isQuasicoherent_twistedGeometricFactor_obj (q : ℤ) (N : ModuleCat.{u} A) :
    ((Stacks.Blowup.twistedGeometricFactor I q).obj N).IsQuasicoherent := by
  have hpull : ((Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).obj
      (AlgebraicGeometry.tilde N)).IsQuasicoherent := inferInstance
  exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj
    (X := Stacks.Blowup.blowUpSpec I) (Stacks.Blowup.blowUpTwist I q) _ inferInstance hpull

/-! ### Its cohomology -/

/-- **`Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` as an `A`-module**: the `i`-th right derived functor of `A`-linear
global sections of the blowup, applied to the twisted pullback of `N`. -/
abbrev blowupHmodTwistedPullback (N : ModuleCat.{u} A) (i : ℕ) (q : ℤ) : ModuleCat.{u} A :=
  blowupHmod I i ((Stacks.Blowup.twistedGeometricFactor I q).obj N)

/-- **`Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ) = 0` above the vanishing degree of the blowup**, for every
`A`-module `N` and every twist.

The degree is the one `exists_forall_subsingleton_blowupH` produces, which depends on `X` alone
and not on the sheaf; the twisted pullback is quasi-coherent, which is all that theorem asks of
it. -/
theorem subsingleton_blowupHmodTwistedPullback [IsNoetherianRing A] (N : ModuleCat.{u} A)
    (i : ℕ) (q : ℤ) (hi : (exists_forall_subsingleton_blowupH I).choose < i) :
    Subsingleton (blowupHmodTwistedPullback I N i q) :=
  subsingleton_blowupHmod I i ((Stacks.Blowup.twistedGeometricFactor I q).obj N)
    ((exists_forall_subsingleton_blowupH I).choose_spec
      ((Stacks.Blowup.twistedGeometricFactor I q).obj N) inferInstance i hi)

/-- **The vanishing stated against the field `d` of the witness.** This is the form the three
fields `vanishing_H`, `vanishing_HG` and `vanishing_HF` of
`Stacks.LocalCohomology.UniformityIII.ModuleSituation` ask for, at a `ModuleSituation` built on
`blowupSituationOf`: the witness takes its `d` to be exactly the degree of
`exists_forall_subsingleton_blowupH`, so no hypothesis on `N` beyond the quasi-coherence that is
automatic is needed. -/
theorem subsingleton_blowupHmodTwistedPullback_blowupSituationOf [IsNoetherianRing A] (q₀ : ℕ)
    (h : IsBaseThreshold I q₀) (N : ModuleCat.{u} A) (i : ℕ) (q : ℤ)
    (hi : (blowupSituationOf I q₀ h).d < i) :
    Subsingleton (blowupHmodTwistedPullback I N i q) :=
  subsingleton_blowupHmodTwistedPullback I N i q hi

/-- The same vanishing at the witness `blowupSituation`, whose threshold is `q(S)`. -/
theorem subsingleton_blowupHmodTwistedPullback_blowupSituation [IsNoetherianRing A]
    (N : ModuleCat.{u} A) (i : ℕ) (q : ℤ) (hi : (blowupSituation I).d < i) :
    Subsingleton (blowupHmodTwistedPullback I N i q) :=
  subsingleton_blowupHmodTwistedPullback I N i q hi

/-! ### Cohomology commutes with finite direct sums -/

/-- Sheaves of `𝒪_X`-modules on the blowup have finite biproducts: the category is abelian, so it
has finite products, and in a preadditive category with a zero object finite products are
biproducts.

This is deliberately *not* an instance: `CategoryTheory.Limits.HasFiniteBiproducts` and
`CategoryTheory.Limits.HasFiniteProducts` already imply one another in Mathlib's instance graph,
and adding this arrow makes instance search for either of them diverge. Introduce it with `letI`
where a biproduct of sheaves is needed. -/
theorem hasFiniteBiproducts_blowupModules :
    HasFiniteBiproducts (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **`Hⁱ(X, ⨁_{j ∈ J} ℱ_j) ≅ ⨁_{j ∈ J} Hⁱ(X, ℱ_j)` for a finite family of sheaves.**

Cohomology of the blowup commutes with finite direct sums. This is not formal: it rests on
`additive_blowupHmod`, and an additive functor preserves finite biproducts
(`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`). It is also not
`StacksFrontier/Algebra/Homology/RightDerivedBiprod.lean`, which proves that right derivation
commutes with biproducts *of functors* — a different statement about a different biproduct.

`HasBiproduct F` is a hypothesis rather than an instance because the `⨁ F` of the statement has
to elaborate; `hasFiniteBiproducts_blowupModules` supplies it for any finite family. -/
noncomputable def blowupHmodBiproductIso (i : ℕ) {J : Type} [Finite J]
    (F : J → _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) [HasBiproduct F] :
    ((blowupΓmod I).rightDerived i).obj (⨁ F) ≅
      ⨁ (fun j => ((blowupΓmod I).rightDerived i).obj (F j)) :=
  ((blowupΓmod I).rightDerived i).mapBiproduct F

/-- `Stacks.Blowup.twistedGeometricFactor` read at the `SheafOfModules` view of the category of
sheaves of modules on the blowup rather than at the `AlgebraicGeometry.Scheme.Modules` view.

The two views are definitionally equal but `AlgebraicGeometry.Scheme.Modules` is a plain
definition with its own `CategoryTheory.Category` and `CategoryTheory.Abelian` instances, so the
addition on a `Hom`-group — and hence `CategoryTheory.Functor.Additive` — is a different
instance on each side and instance search sees through neither. The right derived functors of
`blowupΓmod` are elaborated at the `SheafOfModules` view, so composing with them needs the
twisted pullback there too. -/
abbrev twistedPullbackFunctor (q : ℤ) :
    ModuleCat.{u} A ⥤ _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf :=
  Stacks.Blowup.twistedGeometricFactor I q

/-- Additivity of the twisted pullback transported to the `SheafOfModules` view; the term is
`Stacks.Blowup.additive_twistedGeometricFactor` itself, which typechecks there because the two
views are definitionally equal. -/
instance additive_twistedPullbackFunctor (q : ℤ) : (twistedPullbackFunctor I q).Additive :=
  Stacks.Blowup.additive_twistedGeometricFactor I q

/-- **`N ↦ Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ)` as a functor `Mod(A) ⥤ Mod(A)`**, which is
`blowupHmodTwistedPullback` on objects. -/
abbrev twistedPullbackCohomologyFunctor (i : ℕ) (q : ℤ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  twistedPullbackFunctor I q ⋙ (blowupΓmod I).rightDerived i

/-- **`Hⁱ(X, 𝒪_X(q) ⊗ p^*((N^{⊕r})~)) ≅ (Hⁱ(X, 𝒪_X(q) ⊗ p^*Ñ))^{⊕r}`**, as an `A`-linear
equivalence onto the `r`-fold product.

This is the form the field `freeIso` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation`
asks for: there `N` is `A/Iⁿ`, `r` is the rank of the chosen presentation, and the target is a
function type `Fin r → …` rather than a biproduct.

It is the composite of three isomorphisms: `N^{⊕r}` written as a biproduct in `Mod(A)`, the
preservation of that biproduct by `twistedPullbackCohomologyFunctor` — additive, by
`additive_twistedPullbackFunctor` and `additive_blowupHmod` — and the biproduct in
`Mod(A)` written back as a function type. No biproduct of *sheaves* occurs: both the source and
the target of the composite functor are `Mod(A)`, which is where the two biproducts are
taken. -/
noncomputable def blowupHmodTwistedPullbackPiEquiv (N : ModuleCat.{u} A) (r i : ℕ) (q : ℤ) :
    blowupHmodTwistedPullback I (ModuleCat.of A (Fin r → N)) i q ≃ₗ[A]
      (Fin r → blowupHmodTwistedPullback I N i q) :=
  ((twistedPullbackCohomologyFunctor I i q).mapIso
        (ModuleCat.biproductIsoPi (fun _ : Fin r => N)).symm ≪≫
      (twistedPullbackCohomologyFunctor I i q).mapBiproduct (fun _ : Fin r => N) ≪≫
      ModuleCat.biproductIsoPi _).toLinearEquiv

/-! ### The thickenings are the inverse images of the closed subschemes `V(Iⁿ)` -/

/-- **The ideal sheaf attached to a power is that power of the ideal sheaf.** On each affine open
the ideal of `Scheme.IdealSheafData.ofIdealTop J` is the image of `J` under restriction, and
taking images of ideals along a ring map commutes with powers.

This is the companion of `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_mul`, which Mathlib's
lattice-theoretic API for ideal sheaves does not reach either. -/
theorem ofIdealTop_pow {X : Scheme.{u}} (J : Ideal Γ(X, ⊤)) (n : ℕ) :
    Scheme.IdealSheafData.ofIdealTop (J ^ n) = Scheme.IdealSheafData.ofIdealTop J ^ n :=
  Scheme.IdealSheafData.ext (funext fun _ => by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_pow])

/-- The ideal sheaf of the closed subscheme `V(Iⁿ) ⊆ Spec(A)`. -/
abbrev powIdealSheaf (n : ℕ) : (Spec (CommRingCat.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (I ^ n))

/-- **`p^*(𝒪_{V(Iⁿ)}) ≅ 𝒪_{Yₙ}`**: the inverse image along the blowdown `p : X ⟶ Spec(A)` of the
structure sheaf of the closed subscheme `V(Iⁿ) ⊆ Spec(A)` is the structure sheaf of the `n`-th
thickening `Yₙ` of the exceptional divisor.

This is the **module-level half** of the identification `p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}` that the field
`freeIso` of `Stacks.LocalCohomology.UniformityIII.ModuleSituation` rests on, the ideal-sheaf
half being `thickeningIdeal_eq_comap` of `BitUniformityIII/ThickeningPullback.lean`. It is the
base change of a closed immersion read on structure sheaves,
`Stacks.IdealSheaf.comapStructureSheafIso`, which
holds for an arbitrary morphism — the affineness hypothesis of [Stacks, Tag 02KG] falls on the
closed immersion `V(Iⁿ) ⟶ Spec(A)` and not on `p`, which is essential here since the blowdown is
projective and not flat.

What it is composed with is the ideal-sheaf half: by it the inverse image ideal sheaf
`powIdealSheaf I n |>.comap p` *is* `thickeningIdeal I n`, so the right-hand side of the general
isomorphism is `thickeningSheaf I n` after that one rewrite.

Only one step then separates this from `p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}` as literally stated, and it is
affine and carries no geometry: the identification of `𝒪_{V(Iⁿ)}` — the structure sheaf of the
subscheme of `powIdealSheaf I n`, pushed forward to `Spec(A)` — with
`AlgebraicGeometry.tilde (ModuleCat.of A (A ⧸ Iⁿ))`. That step is
`Stacks.LocalCohomology.tildeQuotientIsoSubschemePushforward`, and composing it with this gives
`Stacks.LocalCohomology.UniformityIII.pullbackTildeQuotientIsoThickeningSheaf`, both in
`BitUniformityIII/BlowupFreeCohomology.lean`. -/
noncomputable def pullbackPowStructureSheafIso (n : ℕ) :
    (Scheme.Modules.pullback (Stacks.Blowup.toSpec I)).obj
        ((Scheme.Modules.pushforward (powIdealSheaf I n).subschemeι).obj
          (Scheme.unitModule (powIdealSheaf I n).subscheme)) ≅ thickeningSheaf I n :=
  Stacks.IdealSheaf.comapStructureSheafIso (Stacks.Blowup.toSpec I) (powIdealSheaf I n) ≪≫
    eqToIso (by rw [← thickeningIdeal_eq_comap]; rfl)

end Stacks.LocalCohomology.UniformityIII

end
