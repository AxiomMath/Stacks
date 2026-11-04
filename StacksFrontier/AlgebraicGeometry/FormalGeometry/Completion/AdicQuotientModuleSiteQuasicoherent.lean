module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealSheafSiteFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientUnitQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal

/-!
# `𝒪/ℐⁿ` is quasi-coherent, on a ringed site and on a locally Noetherian scheme

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals, that is a submodule of the free
rank-one sheaf of modules. `Stacks.Sites.adicQuotientModule ℐ n` is the quotient `𝒪/ℐⁿ`, formed
in `Mod(𝒪)` as the cokernel of the inclusion `ℐⁿ ⊆ 𝒪`. This file proves that **`𝒪/ℐⁿ` is
quasi-coherent whenever `ℐ` is of finite type**, and specialises that to a quasi-coherent sheaf
of ideals of a locally Noetherian scheme read on its small Zariski site.

## Main results

* `Stacks.Sites.idealPow_succ_eq_idealSmul_idealPow` — **`ℐⁿ⁺¹ = ℐ · ℐⁿ`.**
* `Stacks.Sites.presheafIsFiniteType_idealPow` and `Stacks.Sites.isFiniteType_idealPow` — a
  power of a sheaf of ideals of finite type is of finite type.
* `Stacks.Sites.isQuasicoherent_adicQuotientModule` — **`𝒪/ℐⁿ` is quasi-coherent**, for a sheaf
  of ideals of finite type on a ringed site.
* `Stacks.Algebraization.isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule` — the same
  for `ℐ = Stacks.Algebraization.idealSheafSiteSubmodule 𝓘` on a locally Noetherian scheme, with
  no hypothesis beyond local Noetherianity: quasi-coherence of `𝓘` is already carried by
  `AlgebraicGeometry.Scheme.IdealSheafData`.
* `Stacks.Algebraization.isQuasicoherent_homology_adicReductionTower_of_isPseudoCoherent` —
  **the hypothesis `hqc` of the affine adic-tower comparison, discharged**: every cohomology
  sheaf of every term of the adic reduction tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` of a pseudo-coherent `K`
  is quasi-coherent.

## `hqc`

`Algebraization.exists_isIso_comp_limit_sections_homology_adicReductionTower_of_isAffineOpen`
carries three undischarged hypotheses, of which the second, `hqc`, asks exactly that the
cohomology sheaves of the terms of the adic reduction tower be quasi-coherent. Its neighbourhood
records that it reduces to *one* missing lemma, quasi-coherence of the site-level
`Stacks.Sites.adicQuotientModule`; that lemma is proved here, and the reduction is carried out,
so `hqc` is no longer a hypothesis anyone has to supply — only pseudo-coherence of `K` is, and
[Stacks, Tag 0A0K] part (2) assumes it.

The reduction is the one the note describes, and every step of it is already available:
[Stacks, Tag 08DX] part (1) in the hypothesis-taking form
`AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor` splits the tensor into its
two factors; the first is free from pseudo-coherence by [Stacks, Tag 08E5]
(`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`), whose conclusion is
definitionally the `∀ j`-statement wanted; and the second is the quotient placed in degree zero,
whose cohomology is quasi-coherent in every degree by
`Stacks.Duality.derivedCategoryB_singleFunctor_obj_inDegree` applied to the new lemma. Tag 08DX
is available only for a `Scheme`, while the tower is built from
`Stacks.SheafOfModules.derivedTensorProductFunctor` at a `RingedSite`, so the two are crossed by
`AlgebraicGeometry.RingedSite.derivedTensorObjIso`; at the site of opens of a scheme the target
of that isomorphism is the scheme-level derived tensor product on the nose.

## Implementation notes

**Which power this is about, and why the comparison of the two ideal powers is not needed.**
`Stacks.Sites.adicQuotientModule` takes `Stacks.Sites.idealPow`, the sheafification
`Stacks.SheafOfModules.sheafifySubmodule` of the objectwise power `U ↦ ℐ(U)ⁿ`. That is a
different construction from the scheme-level
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, the infimum of the subsheaves bounded
below by `𝓘(U)ⁿ Γ(X, U)` on every affine open, which is what
`Stacks.Algebraization.adicQuotientSystem` and the scheme-level statement
`Stacks.Algebraization.isQuasicoherent_adicQuotientSystem_obj` use; and nothing in the library
identifies the two. The proof below does not go through that identification, and so does not
need it: it stays on the site throughout and never mentions `idealPowerMultiple` except through
the *first* power, which is all `Stacks.Algebraization.idealSheafSiteSubmodule` is built from.

**The route is finite type, not a presentation.**
`Stacks.SheafOfModules.isQuasicoherent_cokernel_toUnit` already says that the quotient of the
sheaf of rings by a *locally generated* submodule is quasi-coherent — the quotient map
`𝒪 ⟶ 𝒪/ℐⁿ` is presented by the single generator `1` with the generators of `ℐⁿ` as relations. So
all that is owed is a family of local generators of `ℐⁿ`, and `SheafOfModules.IsFiniteType`
supplies one. That is where the only new mathematics sits: finite generation has to be
propagated from `ℐ` to `ℐⁿ`, and the sheafification in the definition of
`Stacks.Sites.idealPow` means the propagation is not objectwise.

It is `Stacks.Sites.idealPow_succ_eq_idealSmul_idealPow` that makes the propagation an
induction. `Stacks.Sites.isFiniteType_idealSmul` is the finite-type statement for the product
`ℐ · 𝒩` of a sheaf of ideals with a submodule, and the identity `ℐⁿ⁺¹ = ℐ · ℐⁿ` turns the whole
family of powers into iterated applications of it, so no bookkeeping of degree-`n` monomials in
a generating family of `ℐ` is needed anywhere. Of the two inclusions the identity consists of,
`ℐ · ℐⁿ ⊆ ℐⁿ⁺¹` was already proved — it is `Stacks.Sites.idealSmul_idealPow_le_idealPow_succ`,
and is the half that needs the local description of the sheafification, because a section of
`ℐⁿ` is only locally an `n`-fold product. The other half is objectwise and cheap: a product
`a · b` with `a ∈ ℐ(U)` and `b ∈ ℐ(U)ⁿ` is a scalar multiple of a section of `ℐⁿ`, so it lies in
`ℐ · ℐⁿ`, and `Stacks.Sites.idealPow_le` reduces `ℐⁿ⁺¹ ⊆ ℐ · ℐⁿ` to exactly that.

The base of the induction is `ℐ⁰ = 𝒪`, whose finite generation is
`PresheafOfModules.isFiniteType_unit` — the section `1` generates — read through
`Stacks.Sites.isFiniteType_top`.

**One universe.** `Stacks.SheafOfModules.isQuasicoherent_cokernel_toUnit` is stated for a site
whose object and morphism universes agree with the module universe, so the quotient statement is
proved for `AlgebraicGeometry.RingedSite.{u, u, u}`. That is the shape
`Stacks.SheafOfModules.opensRingedSite` lands in, so the specialisation to a scheme loses
nothing. The powers and the identity between them are proved at independent universes, since
nothing there needs a presentation.

## References

* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ u₁ u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Sites

section Powers

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}

/-- **`ℐⁿ⁺¹ ⊆ ℐ · ℐⁿ`.** A section of the objectwise power `ℐ(U)ⁿ⁺¹` is a sum of products of a
section of `ℐ(U)` with a section of `ℐ(U)ⁿ`, and each such product is a scalar multiple of a
section of `ℐⁿ`; the power `ℐⁿ⁺¹` is the smallest sheaf of ideals containing the objectwise
power, so this objectwise statement suffices. -/
theorem idealPow_succ_le_idealSmul_idealPow (I : IdealSubsheaf O) (n : ℕ) :
    idealPow I (n + 1) ≤ idealSmul I (idealPow I n) :=
  idealPow_le I (n + 1) fun X => by
    rw [pow_succ']
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    exact smul_mem_idealSmul I ha (presheafIdealPow_le_idealPow I n X hb)

/-- **`ℐⁿ⁺¹ = ℐ · ℐⁿ`**, for a sheaf of ideals on a site. The inclusion `ℐ · ℐⁿ ⊆ ℐⁿ⁺¹` is
`Stacks.Sites.idealSmul_idealPow_le_idealPow_succ`. -/
theorem idealPow_succ_eq_idealSmul_idealPow (I : IdealSubsheaf O) (n : ℕ) :
    idealPow I (n + 1) = idealSmul I (idealPow I n) :=
  le_antisymm (idealPow_succ_le_idealSmul_idealPow I n)
    (idealSmul_idealPow_le_idealPow_succ I n)

/-- **Every power of a sheaf of ideals of finite type is of finite type**, in the sectionwise
sense of `PresheafOfModules.IsFiniteType`. The induction is on the exponent, through
`Stacks.Sites.idealPow_succ_eq_idealSmul_idealPow` and the finite-type statement
`Stacks.Sites.isFiniteType_idealSmul` for a product `ℐ · 𝒩`. -/
theorem presheafIsFiniteType_idealPow (I : IdealSubsheaf O)
    (hI : PresheafOfModules.IsFiniteType J I.toPresheafOfModules) :
    ∀ n : ℕ, PresheafOfModules.IsFiniteType J (idealPow I n).toPresheafOfModules
  | 0 => by
      rw [idealPow_zero]
      exact isFiniteType_top (PresheafOfModules.isFiniteType_unit _)
  | n + 1 => by
      rw [idealPow_succ_eq_idealSmul_idealPow]
      exact isFiniteType_idealSmul I _ hI (presheafIsFiniteType_idealPow I hI n)

end Powers

section Quotient

variable {X : RingedSite.{u, u, u}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : X.C, HasSheafify (X.J.over Y) AddCommGrpCat.{u}]
  [∀ Y : X.C, (X.J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts X.C] (I : IdealSubsheaf.{u, u, u} X.O)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts X.C] in
/-- **Every power of a sheaf of ideals of finite type is of finite type**, in Mathlib's sense. -/
theorem isFiniteType_idealPow
    (hI : PresheafOfModules.IsFiniteType X.J I.toPresheafOfModules) (n : ℕ) :
    (idealPow I n).toSheafOfModules.IsFiniteType :=
  _root_.SheafOfModules.isFiniteType_of_presheaf_isFiniteType _
    (presheafIsFiniteType_idealPow I hI n)

/-- **`𝒪/ℐⁿ` is quasi-coherent**, for a sheaf of ideals of finite type on a ringed site.

`Stacks.Sites.adicQuotientModule ℐ n` is the cokernel of `ℐⁿ ⟶ 𝒪`, so
`Stacks.SheafOfModules.isQuasicoherent_cokernel_toUnit` applies to any family of local
generators of `ℐⁿ`, and `Stacks.Sites.isFiniteType_idealPow` provides one. -/
theorem isQuasicoherent_adicQuotientModule
    (hI : PresheafOfModules.IsFiniteType X.J I.toPresheafOfModules) (n : ℕ) :
    (adicQuotientModule I n).IsQuasicoherent := by
  obtain ⟨σ, -⟩ := (isFiniteType_idealPow I hI n).exists_localGeneratorsData
  exact Stacks.SheafOfModules.isQuasicoherent_cokernel_toUnit (idealPow I n).ι σ

end Quotient

end Stacks.Sites

namespace Stacks.Algebraization

variable {Y : Scheme.{u}} (I : Y.IdealSheafData) [IsLocallyNoetherian Y]

/-- **`𝒪_X/ℐⁿ` is quasi-coherent**, for a quasi-coherent sheaf of ideals `𝓘` of a locally
Noetherian scheme read on its small Zariski ringed site by
`Stacks.Algebraization.idealSheafSiteSubmodule`.

This is the site-level statement, about `Stacks.Sites.adicQuotientModule`, which the
scheme-level `Stacks.Algebraization.isQuasicoherent_adicQuotientSystem_obj` does not give: the
two are about different models of the power of a sheaf of ideals. -/
theorem isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule (n : ℕ) :
    (Stacks.Sites.adicQuotientModule
      (X := Stacks.SheafOfModules.opensRingedSite Y.sheaf)
      (idealSheafSiteSubmodule I) n).IsQuasicoherent :=
  Stacks.Sites.isQuasicoherent_adicQuotientModule _
    (presheaf_isFiniteType_idealSheafSiteSubmodule I) n

/-- `Stacks.Algebraization.isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule` with the
quotient read in `AlgebraicGeometry.Scheme.Modules`, which is the spelling the hypotheses of the
affine adic-tower comparison are written at. The two spellings of the sheaf of rings are
definitionally but not syntactically equal, so the ascription is named here once. -/
theorem isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule' (n : ℕ) :
    ((Stacks.Sites.adicQuotientModule
      (X := Stacks.SheafOfModules.opensRingedSite Y.sheaf)
      (idealSheafSiteSubmodule I) n : Y.Modules)).IsQuasicoherent :=
  isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule I n

/-! ### The hypothesis `hqc` of the affine adic-tower comparison -/

variable (K : DerivedCategory Y.Modules)

/-- **Every cohomology sheaf of every term of the adic reduction tower is quasi-coherent**, as
soon as every cohomology sheaf of `K` is.

[Stacks, Tag 08DX] part (1) splits the tensor product `K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`; the quotient placed in
degree zero has quasi-coherent cohomology by
`Stacks.Algebraization.isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule`. Tag 08DX is
available for a scheme, while the tower is built from the derived tensor product of the ringed
site, so `AlgebraicGeometry.RingedSite.derivedTensorObjIso` crosses the two. -/
theorem isQuasicoherent_homology_adicReductionTower
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor Y.Modules j).obj K).IsQuasicoherent)
    (n : ℕᵒᵖ) (p : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules p).obj
      ((AlgebraicGeometry.RingedSite.adicReductionTower
        (Stacks.SheafOfModules.opensRingedSite Y.sheaf)
        (idealSheafSiteSubmodule I) K).obj n)).IsQuasicoherent := by
  set L : DerivedCategory Y.Modules :=
    (DerivedCategory.singleFunctor Y.Modules 0).obj
      (Stacks.Sites.adicQuotientModule
        (X := Stacks.SheafOfModules.opensRingedSite Y.sheaf)
        (idealSheafSiteSubmodule I) (n.unop + 1)) with hL
  have e : (AlgebraicGeometry.RingedSite.adicReductionTower
        (Stacks.SheafOfModules.opensRingedSite Y.sheaf)
        (idealSheafSiteSubmodule I) K).obj n ≅
      ((AlgebraicGeometry.TorFormula.derivedTensor Y).obj K).obj L :=
    AlgebraicGeometry.RingedSite.derivedTensorObjIso
      (Stacks.SheafOfModules.opensRingedSite Y.sheaf) K L
  have hLqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor Y.Modules j).obj L).IsQuasicoherent :=
    fun j => Stacks.Duality.derivedCategoryB_singleFunctor_obj_inDegree _
      (isQuasicoherent_adicQuotientModule_idealSheafSiteSubmodule' I (n.unop + 1)) 0 j
  exact Stacks.Descent.isQuasicoherent_of_iso
    ((DerivedCategory.homologyFunctor Y.Modules p).mapIso e).symm
    (AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor Y K L hK hLqc p)

/-- **The hypothesis `hqc` of
`exists_isIso_comp_limit_sections_homology_adicReductionTower_of_isAffineOpen`,
discharged for a pseudo-coherent object.**

Quasi-coherence of the cohomology sheaves of `K` is free from pseudo-coherence by
[Stacks, Tag 08E5], so a pseudo-coherent `K` — which is what [Stacks, Tag 0A0K] part (2) assumes
— needs nothing further. -/
theorem isQuasicoherent_homology_adicReductionTower_of_isPseudoCoherent
    (hK : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) K) (n : ℕᵒᵖ) (p : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules p).obj
      ((AlgebraicGeometry.RingedSite.adicReductionTower
        (Stacks.SheafOfModules.opensRingedSite Y.sheaf)
        (idealSheafSiteSubmodule I) K).obj n)).IsQuasicoherent :=
  isQuasicoherent_homology_adicReductionTower I K
    (AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent Y K hK) n p

end Stacks.Algebraization

end
