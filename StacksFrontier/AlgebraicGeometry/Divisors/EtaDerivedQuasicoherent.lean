module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
import StacksCore.Tactic.StacksAttribute

/-!
# The derived Berthelot–Ogus décalage preserves quasi-coherent cohomology

Let `X` be a scheme and let `D ⊆ X` be an effective Cartier divisor with ideal sheaf
`I ⊆ 𝒪_X`. The derived décalage `Lη_I : D(𝒪_X) ⟶ D(𝒪_X)` of [Stacks, Tag 0F8Q] sends
`D_QCoh(𝒪_X)` into itself.

The cohomology sheaves of `η_I F^•` are computed by [Stacks, Tag 0F8N]:
`H^n(η_I F^•) ≅ I^{⊗ n} ⊗ (H^n(F^•)/H^n(F^•)[I])`. So the cohomology sheaves of the décalage
depend only on the cohomology sheaves of `F^•`, and each of the three operations involved —
the `I`-torsion subsheaf, the quotient by it, and the twist by an integer power of `I` — stays
inside the quasi-coherent modules. Since an object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)` exactly
when its cohomology sheaves are quasi-coherent, and `Lη_I` is computed on an
`I`-torsion-free representative by `η_I`, this is all that is needed; the terms of the
representative are *not* assumed quasi-coherent, and indeed the flat resolutions which
[Stacks, Tag 0F8Q] uses to produce one have no reason to be.

## Main definitions

* `Stacks.Divisors.Eta.DerivedEta`: the data that [Stacks, Tag 0F8Q] provides for an invertible
  ideal sheaf — an endofunctor of `D(𝒪_X)`, its comparison with the chain-level décalage on
  complexes of `I`-torsion-free modules, and the representability of every object of `D(𝒪_X)`
  by such a complex.

## Main results

* `Stacks.Divisors.Eta.isQuasicoherent_idealPowerAnnihilatorSubsheaf`: the `I`-torsion subsheaf
  `M[I]` of a quasi-coherent module is quasi-coherent.
* `Stacks.Divisors.Eta.isQuasicoherent_homology_etaObj`: if the cohomology sheaves of a complex
  of `I`-torsion-free `𝒪_X`-modules are quasi-coherent, then so are those of its décalage.
* `Stacks.Divisors.Eta.derivedCategoryB_isQuasicoherent_obj`: a functor with the properties
  `DerivedEta` records sends `D_QCoh(𝒪_X)` into itself — at the functor `Lη_I`, the first
  assertion of [Stacks, Tag 0GTV].

## Implementation notes

**Only the first of the two assertions of [Stacks, Tag 0GTV] is proved here**, and for an
arbitrary `E : DerivedEta D`. The tag itself, at the functor `Lη_I` of
`Stacks.Divisors.Eta.derivedEtaData` and with both assertions, is
`Stacks.Divisors.Eta.derivedEta_isQuasicoherent_and_affineComparison` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedBerthelotOgus.lean`. Its second assertion —
that on `X = Spec(A)` with `D = V(f)` the functor `Lη_f` on `D(A)` of More on Algebra,
[Stacks, Tag 0F7R] corresponds to `Lη_I` under the equivalence `D(A) ≌ D_QCoh(𝒪_X)` of
[Stacks, Tag 06Z0] — is assembled from `Stacks.Divisors.Eta.derivedEtaAffineComparison` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedAffineComparison.lean`.

Its chain-level input, the identification `η_I(M̃^•) ≅ (η_f M^•)^~` of sheaves, is
available. The second assertion of [Stacks, Tag 0F8M], `Stacks.Divisors.Eta.etaSectionsIso`,
gives that identification on *sections* over an affine open, and
`Stacks.Divisors.Eta.etaObjTildeIso` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaAffineSheafComparison.lean` promotes it to one of
sheaves along the equivalence between `A`-modules and quasi-coherent `𝒪_{Spec A}`-modules — in
the general form `η_I F^• ≅ (η_f Γ(X, F^•))^~`, for every complex `F^•` of quasi-coherent
`I`-torsion-free modules rather than only for those of the shape `M̃^•`.

That identification is natural in the complex, by
`Stacks.IdealTorsion.Eta.etaSectionsIso_naturality` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaAffineComparisonNatural.lean`, so a natural
isomorphism of functors — rather than a family of isomorphisms of objects — can be assembled
out of it. The *morphism* clause of [Stacks, Tag 0F8Q] is likewise available, although
`DerivedEta` below records the comparison with `η_I` on objects only:
`Stacks.IdealTorsion.Eta.derivedEta_iso`, out of which `Stacks.Divisors.Eta.derivedEtaData`
builds that field, is a natural isomorphism `torsionFreeToDerived ⋙ Lη_I ≅ η_I ⋙ Q` and so
supplies the morphisms too. And `D(A)` is the localization of the complexes of `f`-torsion-free
`A`-modules at the quasi-isomorphisms, by
`Stacks.Eta.DerivedDescent.isLocalization_underlyingComplexCompQ`, which is what lets a natural
isomorphism of functors on `D(A)` be built from one of their restrictions to those complexes.

The input that `M̃^•` be a complex of `I`-torsion-free modules when `M^•` is one of
`f`-torsion-free modules — without which `η_I(M̃^•)` is not even a well-formed term, the
chain-level décalage of a complex of `𝒪_X`-modules being defined only on the `I`-torsion-free
ones — is now available: `Stacks.Divisors.Eta.isIdealTorsionFree_tildeComplex` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaTildeTorsionFree.lean`, out of which
`Stacks.Divisors.Eta.etaObjTildeComplexIso` there reads the chain-level comparison at a complex
of that shape.

**The two models of `D(𝒪_X)` are not an obstacle.**
`Stacks.Divisors.Eta.derivedEtaData` is built at
`CategoryTheory.HasDerivedCategory.standard`, and the equivalence of [Stacks, Tag 06Z0] is
available at that same model —
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`, which exists
precisely so that a consumer at the standard model needs no model comparison. Under
`attribute [local instance 10000] HasDerivedCategory.standard` the composite
`(AlgebraicGeometry.tilde.functor R).mapDerivedCategory ⋙ (derivedEtaData D).functor`
elaborates, so no bridge through `StacksDraft.DerivedModel.modelEquiv` is called for.

**No transport of the module-side décalage along `AlgebraicGeometry.Scheme.ΓSpecIso R` is
needed.** The source takes `X = Spec(A)`
and `f ∈ A = Γ(X, 𝒪_X)`, so the ring to form `η_f` over is `Γ(Spec R, ⊤)` — the one the
generating section lives in, and the one `Stacks.Divisors.Eta.etaObjTildeIso` already uses. The
canonical isomorphism with `R` is absorbed into the sheafification functor instead, as
`Stacks.Divisors.Eta.derivedTildeGamma`. The assembly of the natural isomorphism out of
`CategoryTheory.Localization.liftNatIso`,
`Stacks.Eta.DerivedDescent.isLocalization_underlyingComplexCompQ`,
`CategoryTheory.Functor.mapDerivedCategoryFactors` and the naturality recorded above is
`Stacks.Divisors.Eta.derivedEtaAffineComparison`.

The functor `Lη_I` and the two properties which characterize it are carried as an explicit
hypothesis, bundled as `DerivedEta`. Its three fields are exactly the content of
[Stacks, Tag 0F8Q]: the endofunctor (its additivity is not used below and is therefore not
asked for), the identification `Lη_I(F^•) = η_I(F^•)` for a complex `F^•` of `I`-torsion-free
modules, and — established in the course of the proof of that tag, from the existence of
resolutions with flat terms together with the implication "flat ⇒ `I`-torsion free" — the fact
that every object of `D(𝒪_X)` is represented by such a complex. Only the comparison on
*objects* is asked for; the morphism clause of [Stacks, Tag 0F8Q] plays no role below. No
`@[stacks 0F8Q]` attribute is attached to `DerivedEta`: it is a hypothesis, not a proof of that
tag. What discharges it, unconditionally and for exactly the situation of this file, is
`Stacks.Divisors.Eta.derivedEtaData` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedUnconditional.lean`, which carries
`@[stacks 0F8Q]`: on a scheme the ideal sheaf of an effective Cartier divisor is invertible and
the stalks of `𝒪_X` are local, so the termwise `I`-torsion-free resolutions that
`Stacks.IdealTorsion.Eta.derivedEta` and `Stacks.IdealTorsion.Eta.derivedEta_iso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafDerived.lean` take as a hypothesis are
available rather than assumed, and `derivedEtaData` is those two for a ringed space fed with
them. A complex `F^•` of `I`-torsion-free
modules together with its torsion-freeness is the same thing as a complex of objects of
`Stacks.IdealTorsion.Eta.TorsionFreeModule`, by
`HomologicalComplex.liftObjectProperty`, and `Stacks.IdealTorsion.Eta.etaFunctor` is `etaObj`
of that complex, so `derivedEta_iso` is the `objIso` field; the `exists_...` field is the
resolution hypothesis of that development.

The `I`-torsion subsheaf of a quasi-coherent module is quasi-coherent because it is a kernel:
`idealPowerAnnihilatorIsKernel` of [Stacks, Tag 0F8N] exhibits `I^{⊗ (n+1)} ⊗ M[I]` as the
kernel of `I^{⊗ (n+1)} ⊗ M ⟶ I^{⊗ n} ⊗ M`, and at `n = -1` the twist is `I^{⊗ 0}`, which is
the identity functor; both ends are then quasi-coherent by
`Stacks.Divisors.Eta.isQuasicoherent_idealPowerTerm`, and quasi-coherent modules on a scheme
are closed under kernels.

**No derived category is fixed.** `DerivedEta` and the theorem below take
`[HasDerivedCategory.{w} X.Modules]` as a hypothesis rather than relying on a model in force,
because the two models in play here are different categories and the statement is wanted at
both. `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — the locally small one, a global
instance — is the model at which `D_QCoh(𝒪_X)` is a triangulated subcategory in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasicoherentWeakSerre.lean` and at
which the affine comparison of [Stacks, Tag 06Z0] is stated; but
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafDerived.lean`, which is where `Lη_I`
lives, is written at `CategoryTheory.HasDerivedCategory.standard`. Nothing below needs either
one: `DerivedCategoryB.derivedCategoryB` is a definition at an arbitrary model, and the
closure properties of quasi-coherent modules it is fed are properties of the abelian category
`X.Modules` alone.

Complexes are written at the spelling `CochainComplex X.Modules ℤ` rather than
`CochainComplex (SheafOfModules (structureSheaf X.toRingedSpace.sheaf)) ℤ`: the two are the
same type, but the derived category of the second is not recognized as the derived category of
the first by instance search.

## References

* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0F8N](https://stacks.math.columbia.edu/tag/0F8N)
* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 0F7R](https://stacks.math.columbia.edu/tag/0F7R)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.IdealTorsion (IsIdealTorsionFree idealPowerAnnihilatorSubsheaf)
open Stacks.IdealTorsion.Eta (etaObj etaCohomologyIso idealPowerAnnihilatorIsKernel)

universe w u

namespace Stacks.Divisors.Eta

variable {X : Scheme.{u}}

/-- The `I`-torsion subsheaf `M[I]` of a quasi-coherent `𝒪_X`-module is quasi-coherent. By the
kernel presentation of [Stacks, Tag 0F8N], the twist `I^{⊗ 0} ⊗ M[I]` is the kernel of
`I^{⊗ 0} ⊗ M ⟶ I^{⊗ (-1)} ⊗ M`; both ends are quasi-coherent because an integer power of an
invertible ideal acting on a quasi-coherent module is, and quasi-coherent modules on a scheme
are closed under kernels. -/
theorem isQuasicoherent_idealPowerAnnihilatorSubsheaf (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (M : X.Modules) (hM : M.IsQuasicoherent) :
    (idealPowerAnnihilatorSubsheaf X.toRingedSpace (idealSheafι D) M
      1).toSheafOfModules.IsQuasicoherent := by
  have hI : (idealSheaf D).IsQuasicoherent :=
    isQuasicoherent_of_isInvertible (idealSheaf D) inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
    (@idealPowerAnnihilatorIsKernel X.toRingedSpace (idealSheaf D) (idealSheafι D)
      (isInvertible_idealSheaf D) M (-1))
    (isQuasicoherent_idealPowerTerm (idealSheaf D) hI M hM _)
    (isQuasicoherent_idealPowerTerm (idealSheaf D) hI M hM _)

/-- If every cohomology sheaf of a complex `F^•` of `I`-torsion-free `𝒪_X`-modules is
quasi-coherent, then so is every cohomology sheaf of its décalage `η_I F^•`. The cohomology
sheaf `H^n(η_I F^•)` is `I^{⊗ n} ⊗ (H^n(F^•)/H^n(F^•)[I])` by [Stacks, Tag 0F8N], and each of
the three steps preserves quasi-coherence. No quasi-coherence of the *terms* of `F^•` is
assumed. -/
theorem isQuasicoherent_homology_etaObj (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : CochainComplex X.Modules ℤ)
    (htf : ∀ n : ℤ, IsIdealTorsionFree X.toRingedSpace (idealSheafι D) (F.X n))
    (hH : ∀ n : ℤ, (F.homology n).IsQuasicoherent) (n : ℤ) :
    ((etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) F htf).homology
      n).IsQuasicoherent := by
  have hI : (idealSheaf D).IsQuasicoherent :=
    isQuasicoherent_of_isInvertible (idealSheaf D) inferInstance
  have hcok : (cokernel (idealPowerAnnihilatorSubsheaf X.toRingedSpace (idealSheafι D)
      (F.homology n) 1).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_cokernel _
      (isQuasicoherent_idealPowerAnnihilatorSubsheaf D (F.homology n) (hH n)) (hH n)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (@etaCohomologyIso X.toRingedSpace (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
      (isInvertible_idealSheaf D) F htf n)
    (isQuasicoherent_idealPowerTerm (idealSheaf D) hI _ hcok n)

variable [HasDerivedCategory.{w} X.Modules]

/-- The data that [Stacks, Tag 0F8Q] attaches to an effective Cartier divisor `D ⊆ X` with
ideal sheaf `I`: the derived décalage `Lη_I : D(𝒪_X) ⟶ D(𝒪_X)`, its identification with the
chain-level décalage `η_I` on complexes of `I`-torsion-free `𝒪_X`-modules, and the fact that
every object of `D(𝒪_X)` is represented by such a complex.

The last field is what makes the second one a characterization rather than a vacuous
condition; it is proved in the source from the existence of resolutions with flat terms,
flat modules being `I`-torsion free. -/
structure DerivedEta (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] where
  /-- The endofunctor `Lη_I` of the unbounded derived category of `𝒪_X`-modules. -/
  functor : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules
  /-- On an object represented by a complex of `I`-torsion-free modules, `Lη_I` is the
  chain-level décalage of that complex. -/
  objIso : ∀ (F : CochainComplex X.Modules ℤ)
      (htf : ∀ n : ℤ, IsIdealTorsionFree X.toRingedSpace (idealSheafι D) (F.X n)),
      functor.obj (DerivedCategory.Q.obj F) ≅
        DerivedCategory.Q.obj (etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) F htf)
  /-- Every object of `D(𝒪_X)` is represented by a complex of `I`-torsion-free modules. -/
  exists_isIdealTorsionFree_rep : ∀ K : DerivedCategory X.Modules,
    ∃ (F : CochainComplex X.Modules ℤ)
      (_ : ∀ n : ℤ, IsIdealTorsionFree X.toRingedSpace (idealSheafι D) (F.X n)),
      Nonempty (DerivedCategory.Q.obj F ≅ K)

/-- **A functor with the properties of the derived décalage preserves `D_QCoh`.** Let `X` be a
scheme, let `D ⊆ X` be an effective Cartier divisor with ideal sheaf `I ⊆ 𝒪_X`, and let
`E : DerivedEta D` be an endofunctor of `D(𝒪_X)` which is computed by the chain-level décalage
`η_I` on complexes of `I`-torsion-free modules, at a model of `D(𝒪_X)` in which every object is
represented by such a complex. If every cohomology sheaf of `K` is quasi-coherent, then so is
every cohomology sheaf of `E K`.

At `E = Stacks.Divisors.Eta.derivedEtaData D`, the functor `Lη_I` of [Stacks, Tag 0F8Q], this is
the first assertion of [Stacks, Tag 0GTV]; the tag, both assertions together, is
`Stacks.Divisors.Eta.derivedEta_isQuasicoherent_and_affineComparison`.

The proof represents `K` by a complex `F^•` of `I`-torsion-free modules, reads off that the
cohomology sheaves of `F^•` are quasi-coherent, and applies `isQuasicoherent_homology_etaObj`. -/
theorem derivedCategoryB_isQuasicoherent_obj (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (E : DerivedEta D)
    (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) (E.functor.obj K) := by
  obtain ⟨F, htf, ⟨e⟩⟩ := E.exists_isIdealTorsionFree_rep K
  have hH : ∀ n : ℤ, (F.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app F)
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules n).mapIso e.symm) (hK n))
  intro n
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor X.Modules n).mapIso
        (E.functor.mapIso e.symm ≪≫ E.objIso F htf) ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules n).app _).symm)
    (isQuasicoherent_homology_etaObj D F htf hH n)

end Stacks.Divisors.Eta

end
