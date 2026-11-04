module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineCoherentHomFiniteInjectiveDimension
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedSubcategory
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFiniteCohomology
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare
import StacksCore.Tactic.StacksAttribute

/-!
# `R𝓗om_{𝒪_X}(-, K)` carries `D_Coh(𝒪_X)` into `D_Coh(𝒪_X)`

Let `X` be a locally Noetherian scheme and `K` a dualizing complex on it ([Stacks, Tag 0A87]).
This file proves the second assertion of [Stacks, Tag 0A89]: the duality functor
`D = R𝓗om_{𝒪_X}(-, K)` of
`Stacks.Duality.dualizingDerivedSheafHomFunctor` sends an object of `D_Coh(𝒪_X)` to an object of
`D_Coh(𝒪_X)`, so that it induces a functor

`D : D_Coh(𝒪_X)ᵒᵖ ⥤ D_Coh(𝒪_X)`.

No boundedness is assumed anywhere: `D_Coh(𝒪_X)` is the *unbounded* subcategory of
`Stacks.Duality.CoherentDerivedCategory`.

## Main results

* `Stacks.Duality.isCoherent_homology_derivedSheafHomTilde` — the statement over a Noetherian
  ring: `R𝓗om_{𝒪_{Spec R}}(M̃, ω̃)` has coherent cohomology sheaves for `M` in `D_Coh(R)` and `ω`
  a dualizing complex for `R`.
* `Stacks.Duality.derivedCategoryB_isCoherent_dualizingDerivedSheafHom` reads the statement on a
  locally Noetherian scheme, for a dualizing complex in the second variable, off
  `Stacks.Duality.isCoherent_homology_derivedSheafHom_of_isDualizingComplex` of
  `StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/SchemeCoherentDuality.lean`.
  It is **[Stacks, Tag 0A89]** in the packaged form: `D` preserves `D_Coh(𝒪_X)`.
* `Stacks.Duality.coherentDualizingDerivedSheafHomFunctor` — the functor `D` induces on
  `D_Coh(𝒪_X)`.

## The proof

Over a Noetherian ring `R` it is [Stacks, Tag 0A88] followed by [Stacks, Tag 0G4H]. Tag 0A88,
`AlgebraicGeometry.isIso_affineDerivedTildeHomComparison_of_finite_homology`, identifies

`R𝓗om_{𝒪_{Spec R}}(M̃, ω̃)` with `(R Hom_R(M, ω))~`

for `M` in `D_Coh(R)` — every cohomology module finite, **no boundedness** — and `ω` of finite
injective dimension, which a dualizing complex is by
`Dualizing.IsDualizingComplex.finiteInjectiveDimension`. Tag 0G4H,
`Dualizing.derivedHom_finiteCohomology`, then makes the cohomology modules of `R Hom_R(M, ω)`
finite, and the sheaf associated with a finite module over a Noetherian ring is coherent
([Stacks, Tag 01XZ], here `AlgebraicGeometry.isCoherent_homology_tildeDerived`).

Globally, coherence is local on `X` (`AlgebraicGeometry.Modules.isCoherent_of_restrict`), so it
is enough to work over an affine open `U`; the chain of transports is the one
`AlgebraicGeometry.isCoherent_homology_derivedSheafHom_of_isAffine` uses for
[Stacks, Tag 0D0C] — the derived internal Hom commutes with restriction to `U`
(`Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`, [Stacks, Tag 08DL]) and with the
transport along `U ≅ Spec Γ(X, U)` (`Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso`) — with
two differences. The first argument is recognized as a derived sheafification by
`Stacks.Duality.exists_iso_tilde_of_isCoherent_homology`, the **unbounded** form of the
recognition of [Stacks, Tag 06Z0]. The second argument is not recognized but *given*: it is the
dualizing model of `Stacks.Duality.HasDualizingModelOn`, pushed forward onto `Spec Γ(X, U)` by
`Stacks.Duality.exists_isDualizingComplex_iso_tilde_of_hasDualizingModelOn`. That is what keeps
the finite injective dimension of `ω`, which the recognition would lose.

## Implementation notes

The two spellings of derived internal Hom over a ring meet here. Tag 0A88 is stated at
`StacksDraft.DerivedHom.derivedHomAdjunction`, whose module universe is the ring's own, while
Tag 0G4H is stated at `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, the
universe-polymorphic one; `Dualizing.modelHomIsoDerivedHomAdjunctionOverRing` is the comparison
of the two, and only the object-level half of it is used, since all that crosses is finiteness
of a cohomology module.

The derived category is the standard model, `CategoryTheory.HasDerivedCategory.standard`, at
priority 10000 as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/SchemeCoherentDerivedHom.lean`: it is the
model `Stacks.SheafOfModules.derivedSheafHom` and the two transport isomorphisms are stated at,
and the model sealed inside the body of `Stacks.Duality.HasDualizingModelOn`. The clause-1
registration `Stacks.Duality.mem_coherentDerivedCategory_of_isDualizingComplex` instead carries a
free `[HasDerivedCategory.{w} X.Modules]` binder; the statements below are the standard-model
instances of the same assertions.

## Where the rest of Tag 0A89 lives

The assertion of [Stacks, Tag 0A89] that `D` exchanges `D⁺_Coh(𝒪_X)` and `D⁻_Coh(𝒪_X)` for
quasi-compact `X` is in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDerivedDualityBounded.lean`,
which continues this file.

The assertion that the canonical morphism `id → D ∘ D` of
`Stacks.Duality.dualizingDerivedSheafHomBiduality` is an **isomorphism**, and the two
anti-equivalences that follow formally from it, are in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/CoherentDerivedDualityBiduality.lean`.
The functor the anti-equivalence of `D_Coh(𝒪_X)` is stated at,
`Stacks.Duality.coherentDualizingDerivedSheafHomFunctor`, is the one this file ends with.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
* [Stacks Project, Tag 0G4H](https://stacks.math.columbia.edu/tag/0G4H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHom`,
--   `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`,
--   `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-! ### Over a Noetherian ring -/

variable (R : CommRingCat.{u})

/-- **An object of `D_Coh(𝒪_{Spec R})` is the derived sheafification of an object of
`D_Coh(R)`.** This is [Stacks, Tag 06Z0] in the form the duality statements need: the unbounded
one. The bounded forms are
`AlgebraicGeometry.exists_derivedCategoryBMinus_finite_iso_tilde` and
`AlgebraicGeometry.exists_derivedCategoryBPlus_finite_iso_tilde`; a coherent cohomology sheaf is
quasi-coherent, which is all `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`
asks, and finiteness of the cohomology modules is read back out of coherence of the cohomology
sheaves. -/
theorem exists_iso_tilde_of_isCoherent_homology (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsCoherent) :
    ∃ M : DerivedCategory (ModuleCat.{u} R),
      (∀ n : ℤ, Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj M)) ∧
        Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ E) := by
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E fun n =>
    have := hE n
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E)).1
  refine ⟨M, fun n => ?_, ⟨e⟩⟩
  exact finite_homology_of_isCoherent_homology_tilde R M n
    (isCoherent_of_modulesIso ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e).symm
      (hE n))

/-- **Derived Hom from a coherent complex into a dualizing complex, over a Noetherian ring, has
coherent cohomology sheaves.** For `M` in `D_Coh(R)` — no boundedness — and `ω` a dualizing
complex for `R`, every cohomology sheaf of `R𝓗om_{𝒪_{Spec R}}(M̃, ω̃)` is coherent.

[Stacks, Tag 0A88] identifies that object with `(R Hom_R(M, ω))~`, [Stacks, Tag 0G4H] makes the
cohomology modules of `R Hom_R(M, ω)` finite, and the sheaf associated with a finite module over
a Noetherian ring is coherent. -/
theorem isCoherent_homology_derivedSheafHomTilde [IsNoetherianRing R]
    (M ω : DerivedCategory (ModuleCat.{u} R))
    (hM : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M))
    (hω : Dualizing.IsDualizingComplex ω) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
          (op ((tilde.functor R).mapDerivedCategory.obj M))).obj
            ((tilde.functor R).mapDerivedCategory.obj ω))).IsCoherent := by
  have hfin : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))).hom.obj (op M, ω))) := by
    intro i
    have := Dualizing.derivedHom_finiteCohomology.{u, u} (A := (R : Type u)) M ω hM
      hω.finiteCohomology hω.finiteInjectiveDimension i
    exact Module.Finite.equiv ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (Dualizing.modelHomIsoDerivedHomAdjunctionOverRing (R : Type u) M ω)).toLinearEquiv.symm
  have hiso : IsIso (affineDerivedTildeHomComparison R M ω) :=
    isIso_affineDerivedTildeHomComparison_of_finite_homology R M ω hM hω.finiteInjectiveDimension
  refine isCoherent_of_modulesIso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      (asIso (affineDerivedTildeHomComparison R M ω))) ?_
  exact CoherentAbelian.isCoherent_iff_stacksIsCoherent.mpr
    (isCoherent_homology_tildeDerived R _ n (hfin n))

/-! ### Transport to an affine open -/

/-- **Coherence of all cohomology sheaves passes to the restriction along an open immersion.**
The unbounded form of
`AlgebraicGeometry.derivedCategoryBMinus_isCoherent_restrictFunctor_mapDerivedCategory`. -/
theorem isCoherent_homology_restrictFunctor {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (K : DerivedCategory Y.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor Y.Modules n).obj K).IsCoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K)).IsCoherent :=
  isCoherent_of_modulesIso ((DerivedCategoryB.mapDerivedCategoryHomologyIso
    (Scheme.Modules.restrictFunctor g) n).app K).symm
    (isCoherent_restrict_of_isOpenImmersion g _ (hK n))

/-- **A dualizing model at an affine open, pushed forward onto `Spec Γ(X, U)`.**
`Stacks.Duality.HasDualizingModelOn` presents the model pulled back to `U` along
`U ≅ Spec Γ(X, U)`; one further restriction along the inverse of that isomorphism cancels the
transport, by `Stacks.AffineTilde.tildeIsoSpecCancelIso`, leaving plain derived
sheafification. -/
theorem exists_isDualizingComplex_iso_tilde_of_hasDualizingModelOn
    {X : Scheme.{u}} [IsLocallyNoetherian X] {U : X.Opens} (hU : IsAffineOpen U)
    (K : DerivedCategory X.Modules) (h : HasDualizingModelOn K U hU) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω ∧
      Nonempty ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) ≅
        (tilde.functor Γ(X, U)).mapDerivedCategory.obj ω) := by
  obtain ⟨ω, hω, ⟨e⟩⟩ := h
  exact ⟨ω, hω, ⟨(Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso e ≪≫
    (Stacks.AffineTilde.tildeIsoSpecCancelIso hU).app ω⟩⟩

/-! ### Clause 2 of Tag 0A89 -/

/-- **Stacks Project, Tag 0A89.** `D = R𝓗om_{𝒪_X}(-, K)` carries `D_Coh(𝒪_X)` into
`D_Coh(𝒪_X)`, for `K` a dualizing complex on a locally Noetherian scheme `X`.

This is the second assertion of the lemma, the one the anti-equivalence of `D_Coh(𝒪_X)` is
phrased against. `D_Coh(𝒪_X)` is unbounded: the hypothesis on `L` and the conclusion are both
membership in `DerivedCategoryB.derivedCategoryB (Stacks.Duality.isCoherentSheaf X)`, the
`D_B(A)` construction of [Stacks, Tag 06UP] at coherence, which is what
`Stacks.Duality.CoherentDerivedCategory` is the full subcategory on. -/
@[stacks 0A89 "preservation of coherent objects"]
theorem derivedCategoryB_isCoherent_dualizingDerivedSheafHom
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (L : DerivedCategory X.Modules)
    (hL : DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X) L) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules) (isCoherentSheaf X)
      ((dualizingDerivedSheafHomFunctor X K).obj (op L)) :=
  fun n => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hL n

/-- **The functor `D` induces on `D_Coh(𝒪_X)`**, for `K` a dualizing complex on a locally
Noetherian scheme: `D : D_Coh(𝒪_X)ᵒᵖ ⥤ D_Coh(𝒪_X)`. It lands in the subcategory by
`Stacks.Duality.derivedCategoryB_isCoherent_dualizingDerivedSheafHom`.

This is the scheme-level counterpart of `Dualizing.coherentDualizingDerivedHomFunctor`. -/
def coherentDualizingDerivedSheafHomFunctor (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    (CoherentDerivedCategory X)ᵒᵖ ⥤ CoherentDerivedCategory X where
  obj L := ⟨(dualizingDerivedSheafHomFunctor X K).obj (op L.unop.obj),
    derivedCategoryB_isCoherent_dualizingDerivedSheafHom X hK L.unop.obj L.unop.property⟩
  map f := ⟨(dualizingDerivedSheafHomFunctor X K).map ((ObjectProperty.ι _).map f.unop).op⟩
  map_id _ := by
    ext
    dsimp
    exact (dualizingDerivedSheafHomFunctor X K).map_id _
  map_comp f g := by
    ext
    dsimp
    exact (dualizingDerivedSheafHomFunctor X K).map_comp _ _

end Stacks.Duality

end
