module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FinitenessDepthCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatLocalBaseCanonicalExtension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementCohomologyModule
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.DerivedSectionsOverBase
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Serre.CohenMacaulay
public import StacksFrontier.RingTheory.LocalCohomology.PrincipalQuotientFiniteness
public import StacksFrontier.RingTheory.Depth.LocalizationLocallyFree
public import StacksFrontier.RingTheory.Module.LocallyFree.LocalizationAwayRestrict
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.CohenMacaulayRegular
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.TildeStalkPrime
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.LocalCohomology.QuotientLocallyFreeFiniteness

/-!
# The finiteness of `H⁰(U, F₁)` and `H¹(U, F₁)` in the presence of a dualizing complex

Fix a Noetherian ring `A` with ideals `I ⊆ 𝔞`, and write `X = Spec A`, `Y = V(I)`, `Z = V(𝔞)` and
`U = X ∖ Z`. Let `(F_n)` be a coherent `I`-adic system on `U`. Assume that `A` has a dualizing
complex. Then `H⁰(U, F₁)` and `H¹(U, F₁)` are finite `A`-modules if and only if

  `depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2`

for every `y ∈ U ∩ Y` and every `z ∈ Z ∩ closure{y}`. This holds for example if `F₁` is a finite
locally free `𝒪_{U ∩ Y}`-module, `Y` is `(S₂)`, and `codim(Z', Y') ≥ 3` for every pair of
irreducible components `Y'` of `Y` and `Z'` of `Z` with `Z' ⊆ Y'`. This is Stacks 0EJT.

## Main results

* `Stacks.Algebraization.finite_lowDegreeCohomology_iff_depthDimension_of_isDualizingComplex` —
  **Stacks 0EJT**: both assertions of the remark, stated on the stalks of `F₁` and on its pullback
  to `U ∩ Y`.
* `Stacks.Algebraization.depth_stalk_eq_depth_localizedModule_of_iso` — for `F₁ ≅ M̃|_U`, the
  depth of the stalk `F_{1,y}` over `𝒪_{U,y}` is the depth of `M_𝔭` over `A_𝔭`.
* `Stacks.Algebraization.intersectionUYι` — the closed immersion `U ∩ Y ⟶ U`.
* `Stacks.Algebraization.hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two_of_iso` — the
  equivalence, for a finite `A`-module `M` with `M̃|_U ≅ F₁`.
* `Stacks.Algebraization.hasDepthDimensionAt_two_of_hasLocallyFreeCodimensionThreeCondition` —
  the sufficient condition gives the inequality.
* `Stacks.Algebraization.formalFibersHavePropertySk_of_isDualizingComplex` — the formal fibres of
  the local rings of a ring with a dualizing complex satisfy `(Sₖ)` for every `k`.
* `Stacks.Algebraization.finite_cohomologyOverBase_iff_finite_complementCohomologyBase` — for
  `G ≅ M̃|_U`, the `A`-module `H^p(U, G)` is finite exactly when the cohomology over `U` of `M̃` on
  `X` is.

## Implementation notes

The registered statement speaks of the stalks `F_{1,y}` of `F₁` at the points `y` of `U` with
`I ⊆ 𝔭_y` (the points of `U ∩ Y`), their depth over `𝒪_{U,y}`, and the primes `𝔮 ⊇ 𝔞 + 𝔭_y` (the
points of `Z ∩ closure{y}`), with `dim(𝒪_{closure{y}, z})` the height of the image of `𝔮` in
`A ⧸ 𝔭_y`. The proof passes to a finite `A`-module `M` with `I M = 0` and `F₁ ≅ M̃|_U`, the first
term of a finite module model of `(F_n)` (Stacks 0DXT), where the stalk at `y` is `M_{𝔭_y}` and
the inequality is `Stacks.Algebraization.HasDepthDimensionAt` at `2`; a point of `U` outside `Y`
has `M_𝔭 = 0`, of infinite depth.

The equivalence is the criterion of Stacks 0BJY at `n = 2`, as recorded by
`Stacks.Algebraization.hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two`; what is supplied
here are the inputs of that statement.

* A dualizing complex makes the formal fibres of the local rings Gorenstein (Stacks 0AWY), hence
  Cohen–Macaulay (Stacks 0DW8), hence `(S₂)`.
* `H⁰(U, F₁)` and `H¹(U, F₁)` of `Stacks.Algebraization.HasFiniteLowDegreeCohomology` are the right
  derived functors of global sections on the open subscheme `U`, read over `A`; for the sheaf
  `M̃|_U` these are `Stacks.LocalCohomologySequence.complementCohomologyBase`, the derived
  functors of sections over `U` of sheaves on `X`, by
  `Stacks.LocalCohomology.complementSheafCohomologyTildeIso` (Stacks 01E1). The two readings of
  `H^p(U, -)` over `A`, through `U ⟶ Spec A` in one step and through `Γ(Spec A, 𝒪)` in two, are
  the same module, `Stacks.Algebraization.cohomologyOverBaseLinearEquivComplementSheafCohomology`.

For the sufficient condition, "`F₁` is a finite locally free `𝒪_{U ∩ Y}`-module" says that the
pullback of `F₁` along the closed immersion `U ∩ Y ⟶ U` is finite locally free. The module `M`
above, killed by `I`, is an `A ⧸ I`-module `N`, and that pullback is `Ñ|_{U ∩ Y}`
(`Stacks.Algebraization.pullbackIntersectionUYιTildeIso`, through Stacks 01I9), so `N` satisfies
`Stacks.Algebraization.HasLocallyFreeCodimensionThreeCondition`. The proof is then the source's: at
`y ∈ U ∩ Y` the stalk is free over `𝒪_{Y,y}`, so its depth is at least `depth(𝒪_{Y,y})`, which
`(S₂)` bounds below by `min(2, dim 𝒪_{Y,y})`. The ring `A ⧸ I` is universally catenary
(Stacks 0A80) and `(S₂)`, so its local rings are equidimensional (Stacks 0FIW) and heights add:
`dim 𝒪_{Y,z} = dim 𝒪_{Y,y} + dim 𝒪_{closure{y}, z}`, by
`Stacks.LocalCohomology.height_eq_height_add_height_map_quotientMk`. The codimension condition,
applied to a component `Z' ∋ z` of `Z` and a component `Y' ⊇ Z'` of `Y`, gives
`dim 𝒪_{Y,z} ≥ 3`. Since `dim 𝒪_{closure{y}, z} ≥ 1`, the two bounds give the inequality.

## References

* [Stacks Project, Tag 0EJT](https://stacks.math.columbia.edu/tag/0EJT)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY)
* [Stacks Project, Tag 0FIW](https://stacks.math.columbia.edu/tag/0FIW)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DXT](https://stacks.math.columbia.edu/tag/0DXT)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.LocalCohomologySequence

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

/-- **The formal fibres of a ring with a dualizing complex satisfy `(Sₖ)`.** Every localization of
`A` at a prime again has a dualizing complex (Stacks 0A7G), so its formal fibres are Gorenstein
(Stacks 0AWY), hence Cohen–Macaulay (Stacks 0DW8), hence `(Sₖ)` for every `k`. -/
theorem formalFibersHavePropertySk_of_isDualizingComplex {A : Type u} [CommRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsDualizingComplex K) (q : PrimeSpectrum A) (k : ℕ) :
    Stacks.LocalCohomology.FormalFibersHavePropertySk (Localization.AtPrime q.asIdeal) k := by
  intro p hp
  obtain ⟨hN, hG⟩ := Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex
    (Localization.AtPrime q.asIdeal) _
    (Dualizing.isDualizingComplex_localizationAtPrime.{u, u} K hK q) p
  exact ⟨hN, @propertySkRing_of_isCohenMacaulayRing _ _ hN
    (@Dualizing.IsGorensteinRing.isCohenMacaulayRing _ _ hN hG) k⟩

variable (S : AlgebraizationSituation.{u})

/-- **The two readings of `H^p(U, G)` over `A` agree.** For a sheaf of modules `G` on `U`, the
cohomology `Stacks.LocalCohomology.cohomologyOverBase` (scalars restricted along `U ⟶ Spec A` in
one step) and `Stacks.LocalCohomology.complementSheafCohomology` (scalars restricted through
`Γ(Spec A, 𝒪)`) are the same right derived functor module with the same `A`-action. -/
def cohomologyOverBaseLinearEquivComplementSheafCohomology (G : S.U.toScheme.Modules) (p : ℕ) :
    Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι G p ≃ₗ[S.A]
      (Stacks.LocalCohomology.complementSheafCohomology S.A S.a p).obj G where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    let X0 : ModuleCat.{u} Γ(S.U.toScheme, ⊤) :=
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections S.U.toScheme).rightDerived p).obj G
    refine (ModuleCat.restrictScalars.smul_def (Stacks.LocalCohomology.baseScalars S.A S.U.ι)
      (M := X0) a x).trans ?_
    rw [baseScalars_eq_scalarMap]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Finiteness of `H^p(U, G)` for `G ≅ M̃|_U`.** The `A`-module `H^p(U, G)` is finite exactly
when the cohomology over `U` of `M̃` on `X`,
`Stacks.LocalCohomologySequence.complementCohomologyBase`, is finite. -/
theorem finite_cohomologyOverBase_iff_finite_complementCohomologyBase
    (M : ModuleCat.{u} (CommRingCat.of S.A)) (G : S.U.toScheme.Modules)
    (e : G ≅ (tilde M).restrict S.U.ι) (p : ℕ) :
    Module.Finite S.A (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι G p) ↔
      Module.Finite S.A (complementCohomologyBase (A := CommRingCat.of S.A) S.a M p) := by
  let e₁ := Stacks.LocalCohomology.cohomologyOverBaseLinearEquivOfIso.{u, u} S.A S.U.ι e p
  let e₂ := cohomologyOverBaseLinearEquivComplementSheafCohomology S ((tilde M).restrict S.U.ι) p
  let e₃ := (Stacks.LocalCohomology.complementSheafCohomologyTildeIso S.A S.a M p).toLinearEquiv
  let E := e₁.trans (e₂.trans e₃)
  exact ⟨fun _ => Module.Finite.equiv E, fun _ => Module.Finite.equiv E.symm⟩

/-- The global sections of `F₁` read over `A` through `U ⟶ Spec A`, as in
`Stacks.LocalCohomology.sectionsOverBase`, are the first term of
`Stacks.Algebraization.globalSectionsSystem`. -/
def globalSectionsSystemZeroLinearEquiv (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    (Stacks.LocalCohomology.sectionsOverBase.{u, u} S.A S.U.ι).obj (F.obj.obj (op 0)) ≃ₗ[S.A]
      (globalSectionsSystem S F).obj (op 0) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    refine (ModuleCat.restrictScalars.smul_def (Stacks.LocalCohomology.baseScalars S.A S.U.ι)
      a x).trans ?_
    rw [baseScalars_eq_scalarMap]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Finiteness of `H⁰(U, F₁)` for `F₁ ≅ M̃|_U`.** The module of sections of `F₁` over `U` is a
finite `A`-module exactly when `complementCohomologyBase` of `M` in degree `0` is. -/
theorem finite_globalSectionsSystem_zero_iff_finite_complementCohomologyBase
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (M : ModuleCat.{u} (CommRingCat.of S.A)) (e : F.obj.obj (op 0) ≅ (tilde M).restrict S.U.ι) :
    Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) ↔
      Module.Finite S.A (complementCohomologyBase (A := CommRingCat.of S.A) S.a M 0) := by
  obtain ⟨e₀⟩ := Stacks.LocalCohomology.nonempty_cohomologyOverBase_zero_iso_sections S.A S.U.ι
    (F.obj.obj (op 0))
  let E := e₀.toLinearEquiv.trans (globalSectionsSystemZeroLinearEquiv S F)
  refine Iff.trans ⟨fun _ => Module.Finite.equiv E.symm, fun _ => Module.Finite.equiv E⟩ ?_
  exact finite_cohomologyOverBase_iff_finite_complementCohomologyBase S M _ e 0

/-- **The equivalence of Stacks 0EJT.** Assume `A` has a dualizing complex and let `M` be a finite
`A`-module with `F₁ ≅ M̃|_U`. Then `H⁰(U, F₁)` and `H¹(U, F₁)` are finite `A`-modules if and only
if `depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2` for all `y ∈ U ∩ Y` and `z ∈ Z ∩ closure{y}`. -/
theorem hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two_of_iso
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (M : ModuleCat.{u} (CommRingCat.of S.A)) [Module.Finite S.A M]
    (e : F.obj.obj (op 0) ≅ (tilde M).restrict S.U.ι)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K) :
    HasFiniteLowDegreeCohomology S F ↔ HasDepthDimensionAt S M 2 :=
  hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two S F M inferInstance ⟨K, hK⟩
    (fun _ q => formalFibersHavePropertySk_of_isDualizingComplex K hK q 2)
    (finite_globalSectionsSystem_zero_iff_finite_complementCohomologyBase S F M e)
    (finite_cohomologyOverBase_iff_finite_complementCohomologyBase S M _ e 1)

section SufficientCondition

open IsLocalRing

/-- An additive bijection from a module over a localization `Aₚ` of `A` to a module over a ring
`B` receiving `Aₚ` by `f` is semilinear over `f` as soon as it is so on the image of `A`: an
element of `Aₚ` is a fraction `r / s`, and `s` acts invertibly on both sides. -/
theorem smul_eq_of_isLocalization_ringHom {A : Type*} [CommRing A] {q : Submonoid A}
    {Ap : Type*} [CommRing Ap] [Algebra A Ap] [IsLocalization q Ap] {B : Type*} [CommRing B]
    {M : Type*} [AddCommGroup M] [Module Ap M] {P : Type*} [AddCommGroup P] [Module B P]
    (f : Ap →+* B) (e : M ≃+ P)
    (he : ∀ (a : A) (m : M), e (algebraMap A Ap a • m) = f (algebraMap A Ap a) • e m)
    (x : Ap) (m : M) : e (x • m) = f x • e m := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q x
  have hs : IsUnit (f (algebraMap A Ap s)) := (IsLocalization.map_units Ap s).map f
  have hx : algebraMap A Ap s * IsLocalization.mk' Ap r s = algebraMap A Ap r :=
    IsLocalization.mk'_spec' Ap r s
  refine hs.smul_left_cancel.mp ?_
  rw [← he, ← mul_smul, hx, he, smul_smul, ← map_mul, hx]

/-- **Depth of a localization of a module over a quotient ring.** Let `N` be an `A ⧸ J`-module,
`P` a prime of `A ⧸ J` and `p` its contraction to `A`. The depth of `N_p` over `A_p`, for `N`
viewed as an `A`-module, is the depth of `N_P` over `(A ⧸ J)_P`: the two localizations of `N`
agree, and `A_p → (A ⧸ J)_P` is surjective. -/
theorem depth_localizedModule_comap_quotientMk {A : Type u} [CommRing A] (J : Ideal A)
    (N : ModuleCat.{u} (A ⧸ J)) (P : Ideal (A ⧸ J)) [P.IsPrime] (p : Ideal A) [p.IsPrime]
    (hp : P.comap (Ideal.Quotient.mk J) = p) :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N)) =
      Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl (N : Type u)) := by
  subst hp
  let : Module A (N : Type u) := Module.compHom _ (Ideal.Quotient.mk J)
  have : IsScalarTower A (A ⧸ J) (N : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have htower : IsScalarTower A (A ⧸ J) (LocalizedModule P.primeCompl (N : Type u)) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      rw [Algebra.algebraMap_eq_smul_one]
      exact OreLocalization.smul_one_smul a x
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (A ⧸ J)
      (P.comap (Ideal.Quotient.mk J)).primeCompl)
      (LocalizedModule.mkLinearMap P.primeCompl (N : Type u)) := by
    have hsub : Algebra.algebraMapSubmonoid (A ⧸ J)
        (P.comap (Ideal.Quotient.mk J)).primeCompl = P.primeCompl := by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨?_, fun hx ↦ ⟨y, hx, rfl⟩⟩
      rintro ⟨z, hz, hzy⟩ hmem
      have hzz : Ideal.Quotient.mk J z = Ideal.Quotient.mk J y := hzy
      exact hz (show Ideal.Quotient.mk J z ∈ P by rwa [hzz])
    rw [hsub]
    infer_instance
  have := IsLocalizedModule.restrictScalars (A := A ⧸ J)
    (P.comap (Ideal.Quotient.mk J)).primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl (N : Type u))
  let E := IsLocalizedModule.linearEquiv (P.comap (Ideal.Quotient.mk J)).primeCompl
    (LocalizedModule.mkLinearMap (P.comap (Ideal.Quotient.mk J)).primeCompl (N : Type u))
    ((LocalizedModule.mkLinearMap P.primeCompl (N : Type u)).restrictScalars A)
  set Ap := Localization.AtPrime (P.comap (Ideal.Quotient.mk J))
  set B := Localization.AtPrime P
  have : IsLocalization.AtPrime (Ap ⧸ J.map (algebraMap A Ap)) P :=
    isLocalization_atPrime_quotient _ Ap J P rfl
  let σ := IsLocalization.algEquiv P.primeCompl (Ap ⧸ J.map (algebraMap A Ap)) B
  let f : Ap →+* B := σ.toRingHom.comp (Ideal.Quotient.mk _)
  have hfs : Function.Surjective f := σ.surjective.comp Ideal.Quotient.mk_surjective
  have hfA : ∀ a : A, f (algebraMap A Ap a) = algebraMap (A ⧸ J) B (Ideal.Quotient.mk J a) :=
    fun a ↦ σ.commutes (Ideal.Quotient.mk J a)
  have hl : ∀ (x : Ap) (m : LocalizedModule (P.comap (Ideal.Quotient.mk J)).primeCompl
      (N : Type u)), E.toAddEquiv (x • m) = f x • E.toAddEquiv m := by
    refine smul_eq_of_isLocalization_ringHom (q := (P.comap (Ideal.Quotient.mk J)).primeCompl)
      f E.toAddEquiv fun a m ↦ ?_
    rw [hfA, algebraMap_smul, algebraMap_smul B]
    show E (a • m) = _
    rw [E.map_smul]
    exact (algebraMap_smul (A ⧸ J) a (E m)).symm
  refine (Stacks.CohenMacaulay.BaseFieldExtension.depth_eq_depth_map hfs (maximalIdeal Ap)
    E.toAddEquiv hl).trans ?_
  rw [IsLocalRing.map_maximalIdeal_of_surjective f hfs]

/-- For ideals `I ≤ p` and `q` of `A`, the height of the image of `q` in `(A ⧸ I) ⧸ (p/I)` is the
height of its image in `A ⧸ p`, through `(A ⧸ I) ⧸ (p/I) ≅ A ⧸ p`. -/
theorem height_map_quotientMk_map_quotientMk {A : Type*} [CommRing A] {I p : Ideal A}
    (hIp : I ≤ p) (q : Ideal A) :
    ((q.map (Ideal.Quotient.mk I)).map
        (Ideal.Quotient.mk (p.map (Ideal.Quotient.mk I)))).height =
      (q.map (Ideal.Quotient.mk p)).height := by
  have hcomp : (((DoubleQuot.quotQuotEquivQuotOfLE hIp) :
        ((A ⧸ I) ⧸ p.map (Ideal.Quotient.mk I)) →+* A ⧸ p).comp
      (Ideal.Quotient.mk (p.map (Ideal.Quotient.mk I)))).comp (Ideal.Quotient.mk I) =
        Ideal.Quotient.mk p := by
    ext x
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hIp
  have hmapeq : Ideal.map ((DoubleQuot.quotQuotEquivQuotOfLE hIp) :
        ((A ⧸ I) ⧸ p.map (Ideal.Quotient.mk I)) →+* A ⧸ p)
      ((q.map (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk (p.map (Ideal.Quotient.mk I)))) =
      q.map (Ideal.Quotient.mk p) := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  rw [← RingEquiv.height_map (DoubleQuot.quotQuotEquivQuotOfLE hIp)]
  exact congrArg Ideal.height hmapeq

/-- If every element of `I` kills `M` and the localization of `M` at a prime `p` is nontrivial,
then `I ≤ p`. -/
private theorem le_of_nontrivial_localizedModule_of_forall_smul_eq_zero {A : Type u} [CommRing A]
    {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (hM : ∀ s ∈ I, ∀ m : M, s • m = 0)
    (p : Ideal A) [p.IsPrime] (hnt : Nontrivial (LocalizedModule p.primeCompl M)) : I ≤ p := by
  by_contra h
  obtain ⟨s, hsI, hsp⟩ := Set.not_subset.mp h
  refine (not_nontrivial_iff_subsingleton.mpr ⟨fun x y ↦ ?_⟩) hnt
  have hz : ∀ z : LocalizedModule p.primeCompl M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m t =>
      rw [← LocalizedModule.zero_mk (1 : p.primeCompl)]
      refine LocalizedModule.mk_eq.mpr ⟨⟨s, hsp⟩, ?_⟩
      simp only [one_smul, smul_zero]
      exact hM s hsI m
  rw [hz x, hz y]

/-- The image of a prime containing `I` in `A ⧸ I` is prime. -/
private theorem isPrime_map_quotientMk {A : Type*} [CommRing A] {I p : Ideal A} [p.IsPrime]
    (hIp : I ≤ p) : (p.map (Ideal.Quotient.mk I)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- For primes `I ⊆ 𝔭 ⊆ 𝔮` of `A` with `A ⧸ I` universally catenary and `(S₂)`, the height of the
image of `𝔭` in `A ⧸ I` plus the height of the image of `𝔮` in `A ⧸ 𝔭` is the height of the image
of `𝔮` in `A ⧸ I`. -/
private theorem height_map_add_height_map_eq (hcat : Ring.IsUniversallyCatenary (S.A ⧸ S.I))
    (hS₂ : PropertySkRing (S.A ⧸ S.I) 2) {p q : Ideal S.A} [p.IsPrime] [q.IsPrime]
    (hIp : S.I ≤ p) (hpq : p ≤ q) :
    (p.map (Ideal.Quotient.mk S.I)).height + (q.map (Ideal.Quotient.mk p)).height =
      (q.map (Ideal.Quotient.mk S.I)).height := by
  have := isPrime_map_quotientMk hIp
  have := isPrime_map_quotientMk (hIp.trans hpq)
  rw [Stacks.LocalCohomology.height_eq_height_add_height_map_quotientMk (S.A ⧸ S.I) hcat hS₂
    (p.map (Ideal.Quotient.mk S.I)) (q.map (Ideal.Quotient.mk S.I)) (Ideal.map_mono hpq),
    height_map_quotientMk_map_quotientMk hIp]

/-- **The codimension bound of Stacks 0EJT.** If `A ⧸ I` is universally catenary and `(S₂)`, and
`codim(Z', Y') ≥ 3` for all irreducible components `Z' ⊆ Y'` of `Z` and `Y`, then for primes
`I ⊆ 𝔭 ⊆ 𝔮` with `𝔞 ⊆ 𝔮` the height of the image of `𝔭` in `A ⧸ I` plus the height of the image
of `𝔮` in `A ⧸ 𝔭` is at least `3`. -/
private theorem three_le_height_add_height_of_codimThree
    (hcat : Ring.IsUniversallyCatenary (S.A ⧸ S.I)) (hS₂ : PropertySkRing (S.A ⧸ S.I) 2)
    (hcodim : ∀ p ∈ S.I.minimalPrimes, ∀ q ∈ S.a.minimalPrimes, p ≤ q →
      3 ≤ (q.map (Ideal.Quotient.mk p)).height)
    {p q : Ideal S.A} [p.IsPrime] [q.IsPrime] (hIp : S.I ≤ p) (hpq : p ≤ q) (hqa : S.a ≤ q) :
    3 ≤ (p.map (Ideal.Quotient.mk S.I)).height + (q.map (Ideal.Quotient.mk p)).height := by
  rw [height_map_add_height_map_eq S hcat hS₂ hIp hpq]
  obtain ⟨z, hz, hzq⟩ := Ideal.exists_minimalPrimes_le (I := S.a) (J := q) hqa
  have : z.IsPrime := hz.1.1
  have hIz : S.I ≤ z := S.I_le_a.trans hz.1.2
  obtain ⟨p₀, hp₀, hp₀z⟩ := Ideal.exists_minimalPrimes_le (I := S.I) (J := z) hIz
  have : p₀.IsPrime := hp₀.1.1
  calc (3 : ℕ∞) ≤ (z.map (Ideal.Quotient.mk p₀)).height := hcodim p₀ hp₀ z hz hp₀z
    _ ≤ (z.map (Ideal.Quotient.mk S.I)).height :=
        le_add_self.trans_eq (height_map_add_height_map_eq S hcat hS₂ hp₀.1.2 hp₀z)
    _ ≤ (q.map (Ideal.Quotient.mk S.I)).height := Ideal.height_mono (Ideal.map_mono hzq)

/-- In `ℕ∞`, if `min 2 b ≤ a`, `1 ≤ c` and `3 ≤ b + c`, then `2 < a + c`. -/
private theorem two_lt_add_of_min_two_le {a b c : ℕ∞} (ha : min 2 b ≤ a) (hc : 1 ≤ c)
    (h : 3 ≤ b + c) : 2 < a + c := by
  refine lt_of_lt_of_le ?_ (add_le_add ha le_rfl)
  rcases le_total 2 b with h2 | h2
  · rw [min_eq_left h2]
    calc (2 : ℕ∞) < 2 + 1 := by norm_num
      _ ≤ 2 + c := add_le_add le_rfl hc
  · rw [min_eq_right h2]
    exact lt_of_lt_of_le (by norm_num) h

/-- **The sufficient condition of Stacks 0EJT.** Assume `A` has a dualizing complex. Let `N` be a
finite `A ⧸ I`-module such that `Ñ` is finite locally free on `U ∩ Y`, let `Y = Spec(A ⧸ I)` be
`(S₂)`, and let `codim(Z', Y') ≥ 3` for every pair of irreducible components `Y'` of `Y` and `Z'`
of `Z` with `Z' ⊆ Y'`. Then `depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2` for all `y ∈ U ∩ Y` and
`z ∈ Z ∩ closure{y}`, where `F₁` is the restriction to `U` of the sheaf associated to `N` viewed as
an `A`-module. -/
theorem hasDepthDimensionAt_two_of_hasLocallyFreeCodimensionThreeCondition
    (N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I))) [Module.Finite (S.A ⧸ S.I) N]
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcond : HasLocallyFreeCodimensionThreeCondition S N) :
    HasDepthDimensionAt S ((ModuleCat.restrictScalars (Ideal.Quotient.mk S.I)).obj N) 2 := by
  obtain ⟨hfree, hS₂, hcodim⟩ := hcond
  intro p q hpa hqa hpq hnt
  -- the support of `F₁` lies in `Y`
  have hIp : S.I ≤ p.asIdeal := by
    refine le_of_nontrivial_localizedModule_of_forall_smul_eq_zero (fun s hs m ↦ ?_) p.asIdeal hnt
    show Ideal.Quotient.mk S.I s • (m : (N : Type u)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs, zero_smul]
  set R := S.A ⧸ S.I
  set P : Ideal R := p.asIdeal.map (Ideal.Quotient.mk S.I) with hPdef
  have hPprime : P.IsPrime := isPrime_map_quotientMk hIp
  have hPcomap : P.comap (Ideal.Quotient.mk S.I) = p.asIdeal := by
    rwa [hPdef, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left]
  rw [depth_localizedModule_comap_quotientMk S.I N P p.asIdeal hPcomap]
  -- `F₁` is free at `y`
  obtain ⟨a₀, ha₀a, ha₀p⟩ := Set.not_subset.mp hpa
  have hfP : Ideal.Quotient.mk S.I a₀ ∉ P := fun h ↦ ha₀p (by rwa [← hPcomap])
  have hloc :=
    Module.isFiniteLocallyFree_localization_away_of_mem_of_isFiniteLocallyFree_zeroLocusCompl
    (A := CommRingCat.of R) (S.a.map (Ideal.Quotient.mk S.I)) N hfree
    (Ideal.Quotient.mk S.I a₀) (Ideal.mem_map_of_mem _ ha₀a)
  have hNfree := Module.free_localizedModule_of_isFiniteLocallyFree_away (A := R) (N : Type u)
    (Ideal.Quotient.mk S.I a₀) hloc ⟨P, hPprime⟩ hfP
  have hdepthfree := AlgebraicGeometry.depth_le_depth_of_free
    (maximalIdeal (Localization.AtPrime P)) (LocalizedModule P.primeCompl (N : Type u))
  rw [← ringDepth_eq_depth_maximalIdeal] at hdepthfree
  -- Serre's condition at `y`
  have hS := hS₂ P
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)] at hS
  simp only [WithBot.unbotD_coe, Nat.cast_ofNat] at hS
  have hdepth : min (2 : ℕ∞) P.height ≤ Module.depth (Localization.AtPrime P)
      (maximalIdeal (Localization.AtPrime P)) (LocalizedModule P.primeCompl (N : Type u)) :=
    hS.trans hdepthfree
  -- the codimension bound
  have hcatR : Ring.IsUniversallyCatenary R :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective
      (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK)
  -- `dim(𝒪_{closure{y}, z}) ≥ 1`
  have hne : p.asIdeal ≠ q.asIdeal := fun h ↦ hpa (h ▸ hqa)
  have : IsDomain (S.A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  have hd1 : (1 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
    refine Order.one_le_iff_ne_zero.mpr fun h0 ↦ ?_
    have hbot := Ideal.height_eq_zero_iff_eq_bot.mp h0
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hbot
    exact hne (le_antisymm hpq hbot)
  rw [show ((2 : ℕ) : ℕ∞) = (2 : ℕ∞) by norm_num]
  exact two_lt_add_of_min_two_le hdepth hd1
    (three_le_height_add_height_of_codimThree S hcatR hS₂ hcodim hIp hpq hqa)

end SufficientCondition

/-! ### Stalks, and the locus `U ∩ Y` -/

section Stalks

open IsLocalRing

/-- **The depth of a stalk of `F ≅ M̃|_U`.** At a point `y` of `U` over the prime `𝔭`, the depth of
the stalk `F_y` over `𝒪_{U,y}` is the depth of `M_𝔭` over `A_𝔭`. -/
theorem depth_stalk_eq_depth_localizedModule_of_iso_restrict (G : S.U.toScheme.Modules)
    (M : ModuleCat.{u} (CommRingCat.of S.A)) (e : G ≅ (tilde M).restrict S.U.ι)
    (y : S.U.toScheme) (p : PrimeSpectrum S.A) (hp : underlyingPrime S y = p) :
    Module.depth (S.U.toScheme.presheaf.stalk y) (maximalIdeal (S.U.toScheme.presheaf.stalk y))
        (G.presheaf.stalk y) =
      Module.depth (Localization.AtPrime p.asIdeal) (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := by
  subst hp
  rw [Scheme.Modules.depth_stalk_congr e y]
  exact (Scheme.Modules.depth_stalk_restrict S.U.ι (tilde M) y).trans
    (depth_stalk_tilde_eq_depth_localizedModule (R := CommRingCat.of S.A) M
      (S.U.ι.base y) (underlyingPrime S y) rfl)

/-- A module killed by `I` has zero localization at every prime not containing `I`. -/
theorem le_of_nontrivial_localizedModule_of_smul_top_eq_bot {A : Type u} [CommRing A]
    {I : Ideal A} {M : Type u} [AddCommGroup M] [Module A M] (hM : I • (⊤ : Submodule A M) = ⊥)
    (p : Ideal A) [p.IsPrime] (hnt : Nontrivial (LocalizedModule p.primeCompl M)) : I ≤ p := by
  refine le_of_nontrivial_localizedModule_of_forall_smul_eq_zero (fun s hs m ↦ ?_) p hnt
  have hmem : s • m ∈ I • (⊤ : Submodule A M) := Submodule.smul_mem_smul hs trivial
  rwa [hM, Submodule.mem_bot] at hmem

/-- **`F₁` is the restriction of the sheaf of a finite module killed by `I`.** The first term of
a finite module model of `(F_n)` (Stacks 0DXT) is a finite `A`-module `M` with `I M = 0` and
`F₁ ≅ M̃|_U`. -/
theorem exists_finite_smul_eq_bot_iso_restrict_tilde
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    ∃ M : ModuleCat.{u} (CommRingCat.of S.A), Module.Finite S.A M ∧
      S.I • (⊤ : Submodule S.A M) = ⊥ ∧
        Nonempty (F.obj.obj (op 0) ≅ (tilde M).restrict S.U.ι) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_finiteModuleModel S F
  refine ⟨M.obj (op 0), hM.1 0, by simpa using hM.2.1 0, ⟨?_⟩⟩
  exact ((ObjectProperty.ι _).mapIso e).symm.app (op 0) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback S.U.ι).app
      ((tilde.functor (CommRingCat.of S.A)).obj (M.obj (op 0)))).symm

/-- The open `U ∩ Y` of `Y = Spec(A ⧸ I)`: the complement of the vanishing locus of the image of
`𝔞`. -/
abbrev intersectionUY : (Spec (CommRingCat.of (S.A ⧸ S.I))).Opens :=
  zeroLocusCompl (A := CommRingCat.of (S.A ⧸ S.I)) (S.a.map (Ideal.Quotient.mk S.I))

/-- `U ∩ Y` maps into `U` under the closed immersion `Y ⟶ X`. -/
theorem intersectionUY_le_preimage : intersectionUY S ≤ S.Yι ⁻¹ᵁ S.U := by
  intro x hx
  show S.Yι.base x ∈ (PrimeSpectrum.zeroLocus (S.a : Set S.A))ᶜ
  intro hz
  exact hx fun b hb ↦ Ideal.map_le_iff_le_comap.mpr hz hb

/-- **The closed immersion `U ∩ Y ⟶ U`**, the restriction of `Y ⟶ X` over `U`. -/
def intersectionUYι : (intersectionUY S).toScheme ⟶ S.U.toScheme :=
  S.Yι.resLE S.U (intersectionUY S) (intersectionUY_le_preimage S)

/-- For a finite `A`-module `M` killed by `I`, read as an `A ⧸ I`-module `N`, the pullback of
`M̃|_U` to `U ∩ Y` is `Ñ|_{U ∩ Y}`. -/
def pullbackIntersectionUYιTildeIso (N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I))) :
    (Scheme.Modules.pullback (intersectionUYι S)).obj
        ((tilde ((ModuleCat.restrictScalars (Ideal.Quotient.mk S.I)).obj N)).restrict S.U.ι) ≅
      (tilde N).restrict (intersectionUY S).ι :=
  let M := (ModuleCat.restrictScalars (Ideal.Quotient.mk S.I)).obj N
  (Scheme.Modules.pullback (intersectionUYι S)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback S.U.ι).app (tilde M)) ≪≫
    (Scheme.Modules.pullbackComp (intersectionUYι S) S.U.ι).app (tilde M) ≪≫
    (Scheme.Modules.pullbackCongr (show intersectionUYι S ≫ S.U.ι = (intersectionUY S).ι ≫ S.Yι
      from Scheme.Hom.resLE_comp_ι _ _)).app (tilde M) ≪≫
    ((Scheme.Modules.pullbackComp (intersectionUY S).ι S.Yι).app (tilde M)).symm ≪≫
    (Scheme.Modules.pullback (intersectionUY S).ι).mapIso
      ((AlgebraicGeometry.pullbackTildeIso (CommRingCat.of S.A) (CommRingCat.of (S.A ⧸ S.I))
          (CommRingCat.ofHom (Ideal.Quotient.mk S.I))).app M ≪≫
        (tilde.functor (CommRingCat.of (S.A ⧸ S.I))).mapIso
          (@asIso _ _ _ _ ((ModuleCat.extendRestrictScalarsAdj
              (Ideal.Quotient.mk S.I)).counit.app N)
            (Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app _
              Ideal.Quotient.mk_surjective N))) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (intersectionUY S).ι).app (tilde N)).symm

/-- **The depth–dimension inequality, read on stalks.** For a finite `A`-module `M` killed by `I`
with `F₁ ≅ M̃|_U`, the inequality `HasDepthDimensionAt S M 2` says exactly that
`depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2` for every point `y ∈ U ∩ Y` and every `z ∈ Z` in
the closure of `y`, the depth being that of the stalk of `F₁` at `y` over `𝒪_{U,y}`. -/
theorem hasDepthDimensionAt_two_iff_forall_depth_stalk (G : S.U.toScheme.Modules)
    (M : ModuleCat.{u} (CommRingCat.of S.A)) (hM : S.I • (⊤ : Submodule S.A M) = ⊥)
    (e : G ≅ (tilde M).restrict S.U.ι) :
    HasDepthDimensionAt S M 2 ↔
      ∀ y : S.U.toScheme, S.I ≤ (underlyingPrime S y).asIdeal →
        ∀ q : PrimeSpectrum S.A, S.a ≤ q.asIdeal → (underlyingPrime S y).asIdeal ≤ q.asIdeal →
          (2 : ℕ∞) < Module.depth (S.U.toScheme.presheaf.stalk y)
              (maximalIdeal (S.U.toScheme.presheaf.stalk y)) (G.presheaf.stalk y) +
            (q.asIdeal.map (Ideal.Quotient.mk (underlyingPrime S y).asIdeal)).height := by
  have hcast : ((2 : ℕ) : ℕ∞) = (2 : ℕ∞) := by norm_num
  refine ⟨fun h y hI q hqa hpq ↦ ?_, fun h p q hpa hqa hpq hnt ↦ ?_⟩
  · have hya : ¬ S.a ≤ (underlyingPrime S y).asIdeal := y.2
    rw [depth_stalk_eq_depth_localizedModule_of_iso_restrict S G M e y _ rfl]
    rcases subsingleton_or_nontrivial
        (LocalizedModule (underlyingPrime S y).asIdeal.primeCompl M) with hsub | hnt
    · rw [Module.depth_eq_top_of_subsingleton, top_add]
      exact ENat.coe_lt_top 2
    · have := h _ q hya hqa hpq hnt
      rwa [hcast] at this
  · have hI := le_of_nontrivial_localizedModule_of_smul_top_eq_bot hM p.asIdeal hnt
    let y : S.U.toScheme := ⟨p, hpa⟩
    have hy : underlyingPrime S y = p := rfl
    have := h y (hy ▸ hI) q hqa (hy ▸ hpq)
    rw [depth_stalk_eq_depth_localizedModule_of_iso_restrict S G M e y p hy] at this
    rwa [hcast]

end Stalks

/-- **Stacks Project, Tag 0EJT.** In Situation 0EHC, let `(F_n)` be a coherent `I`-adic system on
`U = Spec A ∖ V(𝔞)`, as in Stacks 0EJS, and assume `A` has a dualizing complex.

* `H⁰(U, F₁)` and `H¹(U, F₁)` are finite `A`-modules if and only if
  `depth(F_{1,y}) + dim(𝒪_{closure{y}, z}) > 2` for all `y ∈ U ∩ Y` and `z ∈ Z ∩ closure{y}`.
  The depth is that of the stalk of `F₁` at `y` over `𝒪_{U,y}`; the point `z` is a prime `𝔮` of
  `A` containing `𝔞` and the prime `𝔭` of `y`, and `dim(𝒪_{closure{y}, z})` is the height of the
  image of `𝔮` in `A ⧸ 𝔭`.
* This holds if `F₁` is a finite locally free `𝒪_{U ∩ Y}`-module, that is its pullback along the
  closed immersion `U ∩ Y ⟶ U` is finite locally free, `Y = Spec(A ⧸ I)` is `(S₂)`, and
  `codim(Z', Y') ≥ 3` for every pair of irreducible components `Y'` of `Y` and `Z'` of `Z` with
  `Z' ⊆ Y'`. The components of `Y` and `Z` are the minimal primes of `I` and of `𝔞`, `Z' ⊆ Y'`
  is the inclusion of those primes, and `codim(Z', Y')` is the height of the image of the prime
  of `Z'` in the quotient by the prime of `Y'`. -/
@[stacks 0EJT "the equivalence and the sufficient condition"]
theorem finite_lowDegreeCohomology_iff_depthDimension_of_isDualizingComplex
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K) :
    (HasFiniteLowDegreeCohomology S F ↔
      ∀ y : S.U.toScheme, S.I ≤ (underlyingPrime S y).asIdeal →
        ∀ q : PrimeSpectrum S.A, S.a ≤ q.asIdeal → (underlyingPrime S y).asIdeal ≤ q.asIdeal →
          (2 : ℕ∞) < Module.depth (S.U.toScheme.presheaf.stalk y)
              (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk y))
              ((F.obj.obj (op 0)).presheaf.stalk y) +
            (q.asIdeal.map (Ideal.Quotient.mk (underlyingPrime S y).asIdeal)).height) ∧
      (Scheme.Modules.IsFiniteLocallyFree
          ((Scheme.Modules.pullback (intersectionUYι S)).obj (F.obj.obj (op 0))) →
        PropertySkRing (S.A ⧸ S.I) 2 →
        (∀ p ∈ S.I.minimalPrimes, ∀ q ∈ S.a.minimalPrimes, p ≤ q →
          3 ≤ (q.map (Ideal.Quotient.mk p)).height) →
        HasFiniteLowDegreeCohomology S F ∧
          ∀ y : S.U.toScheme, S.I ≤ (underlyingPrime S y).asIdeal →
            ∀ q : PrimeSpectrum S.A, S.a ≤ q.asIdeal → (underlyingPrime S y).asIdeal ≤ q.asIdeal →
              (2 : ℕ∞) < Module.depth (S.U.toScheme.presheaf.stalk y)
                  (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk y))
                  ((F.obj.obj (op 0)).presheaf.stalk y) +
                (q.asIdeal.map (Ideal.Quotient.mk (underlyingPrime S y).asIdeal)).height) := by
  obtain ⟨M, hMfin, hMI, ⟨e⟩⟩ := exists_finite_smul_eq_bot_iso_restrict_tilde S F
  have hequiv : HasFiniteLowDegreeCohomology S F ↔ _ :=
    (hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two_of_iso S F M e K hK).trans
      (hasDepthDimensionAt_two_iff_forall_depth_stalk S _ M hMI e)
  refine ⟨hequiv, fun hlf hS₂ hcodim ↦ ?_⟩
  -- `M`, killed by `I`, is a finite `A ⧸ I`-module `N`
  have htors : Module.IsTorsionBySet S.A M (S.I : Set S.A) := by
    intro x a
    have hmem : (a : S.A) • x ∈ S.I • (⊤ : Submodule S.A M) :=
      Submodule.smul_mem_smul a.2 trivial
    rwa [hMI, Submodule.mem_bot] at hmem
  let : Module (S.A ⧸ S.I) M := htors.module
  let N : ModuleCat.{u} (CommRingCat.of (S.A ⧸ S.I)) := ModuleCat.of (S.A ⧸ S.I) M
  have : Module.Finite (S.A ⧸ S.I) N := Module.Finite.of_restrictScalars_finite S.A (S.A ⧸ S.I) M
  let eN : (ModuleCat.restrictScalars (Ideal.Quotient.mk S.I)).obj N ≅ M :=
    LinearEquiv.toModuleIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  let e' : F.obj.obj (op 0) ≅
      (tilde ((ModuleCat.restrictScalars (Ideal.Quotient.mk S.I)).obj N)).restrict S.U.ι :=
    e ≪≫ (Scheme.Modules.restrictFunctor S.U.ι).mapIso
      ((tilde.functor (CommRingCat.of S.A)).mapIso eN.symm)
  -- the three conditions on `N`
  have hcond : HasLocallyFreeCodimensionThreeCondition S N :=
    ⟨Scheme.Modules.IsFiniteLocallyFree.of_iso
      ((Scheme.Modules.pullback (intersectionUYι S)).mapIso e' ≪≫
        pullbackIntersectionUYιTildeIso S N) hlf, hS₂, hcodim⟩
  have : Module.Finite S.A ((ModuleCat.restrictScalars (Ideal.Quotient.mk S.I)).obj N) :=
    (Stacks.LocalCohomology.finite_restrictScalars_quotient_iff S.I N).mpr this
  have hfin := (hasFiniteLowDegreeCohomology_iff_hasDepthDimensionAt_two_of_iso S F _ e' K hK).mpr
    (hasDepthDimensionAt_two_of_hasLocallyFreeCodimensionThreeCondition S N K hK hcond)
  exact ⟨hfin, hequiv.mp hfin⟩

end Stacks.Algebraization
