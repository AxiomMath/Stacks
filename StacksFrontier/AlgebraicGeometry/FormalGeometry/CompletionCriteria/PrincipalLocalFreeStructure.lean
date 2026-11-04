module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.Algebra.Module.RingEquivTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerDirectSum
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.BaseQuotientLocalFreeness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.FirstTermStalkFreeness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenCohomologyGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisorHypotheses

/-!
# The local structure of the sections of an adic system away from the closed point

Fix an algebraization situation (Stacks 0EHC) whose ring `A` is Noetherian local with `𝔞 = 𝔪`,
and let `(ℱₙ)` be a coherent `I`-adic system on `U = X ∖ V(𝔪)` with `I = (f)` and with every term
finite locally free over the infinitesimal neighbourhood it is annihilated by — conditions (1),
(3) and (4) of [Stacks, Tag 0DXU]. Write `Mₙ = H⁰(U, ℱₙ)` for the `A`-module of sections.

This file computes the localization `(Mₙ)_𝔮` at a prime `𝔮 ∈ V(f)` other than `𝔪`. Such a prime
is a point `y` of `U`, and the content of conditions (3) and (4) there is that the stalk of `ℱₙ`
at `y` is a free `𝒪_{U,y}/f^(n+1)`-module of finite rank, while the transition `ℱₙ ⟶ ℱ₀` is
surjective on stalks with kernel `f·ℱ_{n,y}`. Since `(Mₙ~)|_U ≅ ℱₙ` naturally in `n`
([Stacks, Tag 0EIR]), the two statements transport to `(Mₙ)_𝔮` and to the localized transition
map. This is the local input to the last step of the proof of [Stacks, Tag 0DXU], where local
duality over `A_𝔮` is applied to `(Mₙ)_𝔮`.

## Main definitions

* `Stacks.Algebraization.tildeRestrictStalkMap` — the `A`-linear map `M → stalk_y((M~)|_U)`
  taking `m` to the germ at `y` of the global section it determines. It is a localization of `M`
  at the prime under `y` (`Stacks.Algebraization.isLocalizedModule_tildeRestrictStalkMap`) and is
  natural in `M` (`Stacks.Algebraization.tildeRestrictStalkMap_naturality`), which is what the
  per-module isomorphism
  `Stacks.Algebraization.exists_addEquiv_localizedModule_stalk_restrict_tilde` cannot provide.
* `Stacks.Algebraization.localizedModuleStalkEquiv` — the resulting canonical identification of
  `stalk_y((M~)|_U)` with the localized module `M_𝔭`.
* `Stacks.Algebraization.globalSectionsStalkLocalizedAddEquiv` — the identification of the stalk
  of `ℱₙ` at `y` with `(Mₙ)_𝔭`, carrying the transition maps along.

## Main results

* `Stacks.Algebraization.free_stalk_of_isFiniteLocallyFreeAdic` — the local content of condition
  (4) at the term `ℱₙ` itself rather than at an ideal-power quotient of `ℱ_(n+1)`: the stalk of
  `ℱₙ` at a point of `U` is free over `𝒪_{U,y}/ℐ_y^(n+1)`. At `n = 0` this is
  `Stacks.Algebraization.free_stalk_zero_of_isFiniteLocallyFreeAdic`.
* `Stacks.Algebraization.exists_linearEquiv_quotSMulTop_localizedModule_globalSectionsSystem` —
  **the first conclusion**: `(Mₙ)_𝔮` is `(B/f^(n+1)B)^r` for some `r`, where `B = A_𝔮`.
* `Stacks.Algebraization.surjective_and_ker_localizedModule_map_globalSectionsSystem` — **the
  second conclusion**: the localized transition map `(Mₙ)_𝔮 ⟶ (M₀)_𝔮` is surjective with kernel
  `f·(Mₙ)_𝔮`.

The last two are read off the corresponding statements at a point of `U`, in the namespace
`Stacks.Algebraization`,
`exists_linearEquiv_quotSMulTop_localizedModule_globalSectionsSystem_at_point` and
`surjective_and_ker_localizedModule_map_globalSectionsSystem_at_point`, which do not need `A` to
be local.

## Implementation notes

The nonzerodivisor hypothesis (1) of the source plays no role here: freeness of the stalk comes
from condition (4) alone, and the surjectivity and the kernel of the transition map are part of
the definition of a coherent adic system
(`Stacks.Algebraization.surjective_stalk_transition`,
`Stacks.Algebraization.ker_stalk_transition_zero`). So neither statement below takes `f` to be a
nonzerodivisor.

Everything is proved first at a point `y` of `U` and then read at a prime `𝔮` of `A`: a prime
with `𝔮 ≠ 𝔪` does not contain `𝔞 = 𝔪`, so it is the prime under a point of `U`
(`Stacks.Algebraization.exists_point_underlyingPrime`), and `Stacks.Algebraization.underlyingPrime`
of that point is `𝔮` on the nose, so the point-level statement substitutes into the prime-level
one.

The three `local instance`s make the local ring of `U` at `y` an `A`-algebra through
`Stacks.Algebraization.baseToPointStalk` and the stalk of an `𝒪_U`-module an `A`-module through
it. They are local because neither structure is canonical: the same stalk carries the `A`-action
of every point lying over the same prime.

`Stacks.Algebraization.mem_smul_top_iff_of_semilinearEquiv` repeats, for two modules related by a
semilinear additive isomorphism, what `mem_smul_top_iff_of_ringEquiv`
(`StacksFrontier/RingTheory/Flat/HenselianFlatFiniteColimit.lean`) says for one module carrying two
actions; neither form follows from the other without the transport the other form is being used
for.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper Stacks.AlgebraicGeometry.OpenStalkExactness
open scoped AlgebraicGeometry Pointwise

universe u

namespace Stacks.Algebraization

/-! ### Annihilation and ideal multiples across a semilinear isomorphism -/

section Semilinear

variable {R R' : Type*} [CommRing R] [CommRing R'] (ε : R ≃+* R')
  {I : Ideal R} {I' : Ideal R'} (hI : Ideal.map (ε : R →+* R') I = I')
  {P L : Type*} [AddCommGroup P] [Module R P] [AddCommGroup L] [Module R' L]
  (G : P ≃+ L) (hG : ∀ (r : R) (p : P), G (r • p) = ε r • G p)

include hI hG

/-- **Membership in `I·P` is unchanged by a semilinear isomorphism.** If `ε : R ≃+* R'` carries
`I` to `I'` and `G : P ≃+ L` is semilinear over `ε`, then `p` lies in `I·P` exactly when `G p`
lies in `I'·L`. -/
theorem mem_smul_top_iff_of_semilinearEquiv (p : P) :
    p ∈ I • (⊤ : Submodule R P) ↔ G p ∈ I' • (⊤ : Submodule R' L) := by
  have hmem : ∀ r : R, r ∈ I ↔ ε r ∈ I' := by
    intro r
    refine ⟨fun hr => hI ▸ Ideal.mem_map_of_mem _ hr, fun hr => ?_⟩
    obtain ⟨s, hs, hse⟩ := (Ideal.mem_map_iff_of_surjective (ε : R →+* R')
      ε.surjective).mp (hI ▸ hr : ε r ∈ Ideal.map (ε : R →+* R') I)
    exact ε.injective (hse : ε s = ε r) ▸ hs
  have hGsymm : ∀ (r' : R') (l : L), G.symm (r' • l) = ε.symm r' • G.symm l := fun r' l =>
    G.injective (by rw [G.apply_symm_apply, hG, ε.apply_symm_apply, G.apply_symm_apply])
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · refine Submodule.smul_induction_on (p := fun z => G z ∈ I' • (⊤ : Submodule R' L)) hp
      (fun r hr m _ => ?_) fun _ _ h₁ h₂ => by rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    rw [hG]
    exact Submodule.smul_mem_smul ((hmem r).mp hr) Submodule.mem_top
  · have key : ∀ l ∈ I' • (⊤ : Submodule R' L), G.symm l ∈ I • (⊤ : Submodule R P) := by
      intro l hl
      refine Submodule.smul_induction_on (p := fun z => G.symm z ∈ I • (⊤ : Submodule R P)) hl
        (fun r' hr' m _ => ?_) fun _ _ h₁ h₂ => by rw [map_add]; exact Submodule.add_mem _ h₁ h₂
      rw [hGsymm]
      refine Submodule.smul_mem_smul ((hmem _).mpr ?_) Submodule.mem_top
      rwa [ε.apply_symm_apply]
    simpa only [G.symm_apply_apply] using key (G p) hp

/-- **Annihilation by an ideal transports along a semilinear isomorphism.** -/
theorem smul_top_eq_bot_of_semilinearEquiv (h : I • (⊤ : Submodule R P) = ⊥) :
    I' • (⊤ : Submodule R' L) = ⊥ := by
  refine le_antisymm (fun l hl => ?_) bot_le
  have h1 : G (G.symm l) ∈ I' • (⊤ : Submodule R' L) := by rwa [G.apply_symm_apply]
  have h2 := (mem_smul_top_iff_of_semilinearEquiv ε hI G hG (G.symm l)).mpr h1
  rw [h, Submodule.mem_bot] at h2
  have h3 : l = G (G.symm l) := (G.apply_symm_apply l).symm
  rw [h3, h2, map_zero]
  exact Submodule.zero_mem _

end Semilinear

/-! ### Free modules modulo a principal ideal -/

section QuotSMulTop

variable {R : Type*} [CommRing R]

/-- **Reducing a finite free module modulo `a` gives a finite free module over `R/(a)`.** -/
def quotSMulTopPiEquiv (a : R) (r : ℕ) :
    QuotSMulTop a (Fin r → R) ≃ₗ[R] (Fin r → R ⧸ Ideal.span {a}) :=
  (QuotSMulTop.equivQuotTensor a (Fin r → R)).trans
    (TensorProduct.piScalarRight R R (R ⧸ Ideal.span {a}) (Fin r))

/-- **A module annihilated by `(a)` whose reduction modulo `(a)` is finite free is a reduction of
a finite free module.** Here the reduction is the module itself, `(a)` annihilating it, so the
conclusion says it is `(R/(a))^r` read as an `R`-module. -/
theorem exists_linearEquiv_quotSMulTop_of_free (a : R) (hunit : ¬ IsUnit a)
    {L : Type*} [AddCommGroup L] [Module R L]
    (hbot : Ideal.span {a} • (⊤ : Submodule R L) = ⊥)
    (hfree : Module.Free (R ⧸ Ideal.span {a})
      (L ⧸ (Ideal.span {a} • ⊤ : Submodule R L)))
    (hfin : Module.Finite (R ⧸ Ideal.span {a})
      (L ⧸ (Ideal.span {a} • ⊤ : Submodule R L))) :
    ∃ r : ℕ, Nonempty (L ≃ₗ[R] QuotSMulTop a (Fin r → R)) := by
  classical
  have := hfree
  have := hfin
  have : Nontrivial (R ⧸ Ideal.span {a}) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R ⧸ Ideal.span {a})
    (M := L ⧸ (Ideal.span {a} • ⊤ : Submodule R L))
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  have e₁ : L ≃ₗ[R] (L ⧸ (Ideal.span {a} • ⊤ : Submodule R L)) :=
    (Submodule.quotEquivOfEqBot _ hbot).symm
  have e₂ : (L ⧸ (Ideal.span {a} • ⊤ : Submodule R L)) ≃ₗ[R ⧸ Ideal.span {a}]
      (Fin (Fintype.card ι) → (R ⧸ Ideal.span {a})) :=
    (b.reindex (Fintype.equivFin ι)).equivFun
  have e₃ : (L ⧸ (Ideal.span {a} • ⊤ : Submodule R L)) ≃ₗ[R]
      (Fin (Fintype.card ι) → (R ⧸ Ideal.span {a})) := e₂.restrictScalars R
  exact ⟨Fintype.card ι, ⟨e₁.trans (e₃.trans (quotSMulTopPiEquiv a (Fintype.card ι)).symm)⟩⟩

end QuotSMulTop

/-! ### The germ of a global section, naturally in the module -/

section Point

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme)

/-- The local ring of `U` at `y` is an `A`-algebra through
`Stacks.Algebraization.baseToPointStalk`. -/
local instance algebraBaseToPointStalk : Algebra S.A ↑(S.U.toScheme.presheaf.stalk y) :=
  (baseToPointStalk S y).toAlgebra

/-- The stalk at `y` of an `𝒪_U`-module is an `A`-module through the local ring of `U` at `y`. -/
local instance moduleBaseStalk (N : S.U.toScheme.Modules) :
    Module S.A ((modulesStalkFunctor S.U.toScheme y).obj N : Type u) :=
  Module.compHom _ (algebraMap S.A ↑(S.U.toScheme.presheaf.stalk y))

/-- The `A`-action on the stalk of an `𝒪_U`-module is the one through the local ring. -/
local instance isScalarTowerBaseStalk (N : S.U.toScheme.Modules) :
    IsScalarTower S.A ↑(S.U.toScheme.presheaf.stalk y)
      ((modulesStalkFunctor S.U.toScheme y).obj N : Type u) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

variable (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
  (M : ModuleCat.{u} (CommRingCat.of S.A))

/-- **The stalk comparison for the restriction of `M~` to `U`**, as an additive isomorphism from
the stalk of `M~` at the prime under `y`. It is
`Stacks.AlgebraicGeometry.OpenStalkExactness.restrictStalkInv`, which is an isomorphism because
restriction along an open immersion does not change stalks. -/
def tildeRestrictStalkAddEquiv :
    ↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf S.A (M : Type u)).presheaf
          (underlyingPrime S y)) ≃+
      ((modulesStalkFunctor S.U.toScheme y).obj ((restrictedTildeFunctor S).obj M) : Type u) :=
  haveI := isIso_restrictStalkInv S.U.ι (AlgebraicGeometry.tilde M) y
  AddEquiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (restrictStalkInv S.U.ι (AlgebraicGeometry.tilde M) y))

/-- The stalk comparison is `A`-linear: the image of `r ∈ A` in the stalk of `Spec A` acts on the
one side and its image in the local ring of `U` acts on the other
(`Stacks.Algebraization.stalkMap_algebraMap_specStalk`). -/
theorem tildeRestrictStalkAddEquiv_smul (r : S.A)
    (n : ↑(TopCat.Presheaf.stalk
      (AlgebraicGeometry.moduleStructurePresheaf S.A (M : Type u)).presheaf
        (underlyingPrime S y))) :
    tildeRestrictStalkAddEquiv S y M (r • n) = r • tildeRestrictStalkAddEquiv S y M n := by
  have h1 : tildeRestrictStalkAddEquiv S y M (r • n)
      = tildeRestrictStalkAddEquiv S y M
        (algebraMap S.A
          ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk
            (underlyingPrime S y)) r • n) := by
    rw [IsScalarTower.algebraMap_smul]
  have h2 := restrictStalkInv_smul S.U.ι (AlgebraicGeometry.tilde M) y
    (algebraMap S.A
      ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk
        (underlyingPrime S y)) r) n
  rw [stalkMap_algebraMap_specStalk] at h2
  exact (h1.trans h2).trans rfl

/-- `Stacks.Algebraization.tildeRestrictStalkAddEquiv` as an isomorphism of `A`-modules. -/
def tildeRestrictStalkEquiv :
    ↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf S.A (M : Type u)).presheaf
          (underlyingPrime S y)) ≃ₗ[S.A]
      ((modulesStalkFunctor S.U.toScheme y).obj ((restrictedTildeFunctor S).obj M) : Type u) :=
  { (tildeRestrictStalkAddEquiv S y M).toEquiv with
    map_add' := (tildeRestrictStalkAddEquiv S y M).map_add
    map_smul' := tildeRestrictStalkAddEquiv_smul S y M }

/-- **The germ at `y` of the global section of `(M~)|_U` determined by an element of `M`.** -/
def tildeRestrictStalkMap :
    M →ₗ[S.A] ((modulesStalkFunctor S.U.toScheme y).obj
      ((restrictedTildeFunctor S).obj M) : Type u) :=
  (tildeRestrictStalkEquiv S y M).toLinearMap ∘ₗ
    AlgebraicGeometry.StructureSheaf.toStalkₗ S.A (M : Type u) (underlyingPrime S y)

/-- **The germ map is a localization of `M` at the prime under `y`**: it is the localization map
`M → (M~)_𝔭` of `AlgebraicGeometry.StructureSheaf.toStalkₗ` followed by an isomorphism. -/
instance isLocalizedModule_tildeRestrictStalkMap :
    IsLocalizedModule (underlyingPrime S y).asIdeal.primeCompl (tildeRestrictStalkMap S y M) :=
  IsLocalizedModule.of_linearEquiv (underlyingPrime S y).asIdeal.primeCompl
    (AlgebraicGeometry.StructureSheaf.toStalkₗ S.A (M : Type u) (underlyingPrime S y))
    (tildeRestrictStalkEquiv S y M)

/-- The germ map is the germ over `⊤` of the section of `(M~)|_U` attached to `m`, which over `U`
is the section of `M~` attached to `m`. -/
theorem tildeRestrictStalkMap_apply (m : M) :
    tildeRestrictStalkMap S y M m
      = (((restrictedTildeFunctor S).obj M).presheaf.germ ⊤ y trivial)
          (AlgebraicGeometry.StructureSheaf.toOpenₗ S.A (M : Type u)
            (S.U.ι ''ᵁ (⊤ : S.U.toScheme.Opens)) m) := by
  have h1 := TopCat.Presheaf.germ_res_apply (AlgebraicGeometry.tilde M).presheaf
    (homOfLE (le_top : (S.U.ι ''ᵁ (⊤ : S.U.toScheme.Opens)) ≤ ⊤)) (underlyingPrime S y)
    ⟨y, trivial, rfl⟩ (AlgebraicGeometry.StructureSheaf.toOpenₗ S.A (M : Type u) ⊤ m)
  refine Eq.trans ?_ (restrictStalkInv_germ S.U.ι (AlgebraicGeometry.tilde M) y
    (U := (⊤ : S.U.toScheme.Opens)) trivial ⟨y, trivial, rfl⟩
    (AlgebraicGeometry.StructureSheaf.toOpenₗ S.A (M : Type u) _ m))
  exact congrArg (fun z => restrictStalkInv S.U.ι (AlgebraicGeometry.tilde M) y z) h1.symm

/-- **The germ map is natural in the module.** This is what makes the identification of the stalk
with a localization compatible with maps of modules, and it is the reason for naming the map
instead of quantifying over it existentially as
`Stacks.Algebraization.exists_addEquiv_localizedModule_stalk_restrict_tilde` does. -/
theorem tildeRestrictStalkMap_naturality {M N : ModuleCat.{u} (CommRingCat.of S.A)}
    (φ : M ⟶ N) (m : M) :
    ((modulesStalkFunctor S.U.toScheme y).map ((restrictedTildeFunctor S).map φ))
        (tildeRestrictStalkMap S y M m) = tildeRestrictStalkMap S y N (φ m) := by
  have e3 := Stacks.Algebraization.modulesStalkFunctor_map_germ
    ((restrictedTildeFunctor S).map φ) y (⊤ : S.U.toScheme.Opens) trivial
    (AlgebraicGeometry.StructureSheaf.toOpenₗ S.A (M : Type u)
      (S.U.ι ''ᵁ (⊤ : S.U.toScheme.Opens)) m)
  rw [tildeRestrictStalkMap_apply, tildeRestrictStalkMap_apply]
  refine e3.trans (congrArg
    (fun z => (((restrictedTildeFunctor S).obj N).presheaf.germ ⊤ y trivial) z) ?_)
  exact ConcreteCategory.congr_hom (AlgebraicGeometry.tilde.toOpen_map_app φ _) m

/-! ### The stalk of `(M~)|_U` as the localized module -/

/-- The local ring of `U` at `y` is a localization of `A` at the prime under `y`. -/
local instance isLocalization_underlyingPrime_pointStalk :
    IsLocalization (underlyingPrime S y).asIdeal.primeCompl
      ↑(S.U.toScheme.presheaf.stalk y) := by
  refine (IsLocalization.isLocalization_iff_of_algEquiv _
    (AlgEquiv.ofRingEquiv (f := (pointStalkRingEquiv S y).symm) ?_)).mp inferInstance
  intro r
  exact (RingEquiv.symm_apply_eq _).mpr (congrArg
    (fun t : S.A →+* Localization.AtPrime (underlyingPrime S y).asIdeal => t r)
    (pointStalkRingEquiv_comp_baseToPointStalk S y)).symm

/-- The canonical comparison of the two models of the localization of `A` at the prime under `y`
is `Stacks.Algebraization.pointStalkRingEquiv`: both agree on the image of `A`. -/
theorem isLocalizationAlgEquiv_apply_eq_pointStalkRingEquiv
    (a : ↑(S.U.toScheme.presheaf.stalk y)) :
    (IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
        ↑(S.U.toScheme.presheaf.stalk y)
        (Localization.AtPrime (underlyingPrime S y).asIdeal)) a = pointStalkRingEquiv S y a := by
  have h : ((IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
        ↑(S.U.toScheme.presheaf.stalk y)
        (Localization.AtPrime (underlyingPrime S y).asIdeal)).toRingEquiv :
          ↑(S.U.toScheme.presheaf.stalk y) →+*
            Localization.AtPrime (underlyingPrime S y).asIdeal)
      = ((pointStalkRingEquiv S y) : ↑(S.U.toScheme.presheaf.stalk y) →+*
          Localization.AtPrime (underlyingPrime S y).asIdeal) := by
    refine IsLocalization.ringHom_ext (underlyingPrime S y).asIdeal.primeCompl ?_
    ext r
    exact ((IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
      ↑(S.U.toScheme.presheaf.stalk y)
      (Localization.AtPrime (underlyingPrime S y).asIdeal)).commutes r).trans
      (congrArg (fun t : S.A →+* Localization.AtPrime (underlyingPrime S y).asIdeal => t r)
        (pointStalkRingEquiv_comp_baseToPointStalk S y)).symm
  exact congrArg (fun t : ↑(S.U.toScheme.presheaf.stalk y) →+*
    Localization.AtPrime (underlyingPrime S y).asIdeal => t a) h

/-- **The stalk at `y` of the restriction of `M~` to `U` is the localization of `M` at the prime
under `y`**, canonically: both are models of that localization, the first through
`Stacks.Algebraization.tildeRestrictStalkMap` and the second through
`ModuleCat.localizedModuleMkLinearMap`. -/
def localizedModuleStalkEquiv :
    ((modulesStalkFunctor S.U.toScheme y).obj ((restrictedTildeFunctor S).obj M) : Type u)
      ≃ₗ[S.A] (M.localizedModule (underlyingPrime S y).asIdeal.primeCompl : Type u) :=
  IsLocalizedModule.linearEquiv (underlyingPrime S y).asIdeal.primeCompl
    (tildeRestrictStalkMap S y M)
    (M.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl)

/-- The identification of the stalk with the localized module is semilinear over
`Stacks.Algebraization.pointStalkRingEquiv`: it is `A`-linear, and two `A`-linear maps out of a
localization agree once they agree on the image of `A`
(`IsLocalizedModule.linearMap_ext`). -/
theorem localizedModuleStalkEquiv_smul (ρ : ↑(S.U.toScheme.presheaf.stalk y))
    (z : ((modulesStalkFunctor S.U.toScheme y).obj
      ((restrictedTildeFunctor S).obj M) : Type u)) :
    localizedModuleStalkEquiv S y M (ρ • z)
      = pointStalkRingEquiv S y ρ • localizedModuleStalkEquiv S y M z := by
  have key : ((localizedModuleStalkEquiv S y M).toLinearMap ∘ₗ
        (LinearMap.toSpanSingleton ↑(S.U.toScheme.presheaf.stalk y) _ z).restrictScalars S.A)
      = ((LinearMap.toSpanSingleton (Localization.AtPrime (underlyingPrime S y).asIdeal)
            (M.localizedModule (underlyingPrime S y).asIdeal.primeCompl : Type u)
            (localizedModuleStalkEquiv S y M z)).restrictScalars S.A) ∘ₗ
        (IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
          ↑(S.U.toScheme.presheaf.stalk y)
          (Localization.AtPrime (underlyingPrime S y).asIdeal)).toLinearEquiv.toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (underlyingPrime S y).asIdeal.primeCompl
      (Algebra.linearMap S.A ↑(S.U.toScheme.presheaf.stalk y))
      (M.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl) ?_
    ext
    simp [LinearMap.toSpanSingleton, Algebra.linearMap]
  refine Eq.trans (congrArg (fun k : ↑(S.U.toScheme.presheaf.stalk y) →ₗ[S.A]
    (M.localizedModule (underlyingPrime S y).asIdeal.primeCompl : Type u) => k ρ) key) ?_
  exact congrArg (fun t => t • localizedModuleStalkEquiv S y M z)
    (isLocalizationAlgEquiv_apply_eq_pointStalkRingEquiv S y ρ)

/-- The identification of the stalk with the localized module takes the germ of a global section
to its class in the localized module. -/
theorem localizedModuleStalkEquiv_apply (m : M) :
    localizedModuleStalkEquiv S y M (tildeRestrictStalkMap S y M m)
      = M.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl m :=
  IsLocalizedModule.linearEquiv_apply (underlyingPrime S y).asIdeal.primeCompl
    (tildeRestrictStalkMap S y M)
    (M.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl) m

/-- **The identification of the stalk with the localized module is natural in the module.** -/
theorem localizedModuleStalkEquiv_naturality {M N : ModuleCat.{u} (CommRingCat.of S.A)}
    (φ : M ⟶ N) (z : ((modulesStalkFunctor S.U.toScheme y).obj
      ((restrictedTildeFunctor S).obj M) : Type u)) :
    localizedModuleStalkEquiv S y N
        (((modulesStalkFunctor S.U.toScheme y).map ((restrictedTildeFunctor S).map φ)) z)
      = (ModuleCat.localizedModuleMap.{u} (underlyingPrime S y).asIdeal.primeCompl φ).hom
        (localizedModuleStalkEquiv S y M z) := by
  have key : (localizedModuleStalkEquiv S y N).toLinearMap ∘ₗ
        (((modulesStalkFunctor S.U.toScheme y).map
          ((restrictedTildeFunctor S).map φ)).hom.restrictScalars S.A)
      = ((ModuleCat.localizedModuleMap.{u}
            (underlyingPrime S y).asIdeal.primeCompl φ).hom.restrictScalars S.A) ∘ₗ
        (localizedModuleStalkEquiv S y M).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (underlyingPrime S y).asIdeal.primeCompl
      (tildeRestrictStalkMap S y M)
      (N.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl) ?_
    refine LinearMap.ext fun m => ?_
    have h3 := IsLocalizedModule.map_apply (underlyingPrime S y).asIdeal.primeCompl
      (M.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl)
      (N.localizedModuleMkLinearMap (underlyingPrime S y).asIdeal.primeCompl) φ.hom m
    show localizedModuleStalkEquiv S y N
        (((modulesStalkFunctor S.U.toScheme y).map ((restrictedTildeFunctor S).map φ))
          (tildeRestrictStalkMap S y M m))
      = (ModuleCat.localizedModuleMap.{u}
          (underlyingPrime S y).asIdeal.primeCompl φ).hom
        (localizedModuleStalkEquiv S y M (tildeRestrictStalkMap S y M m))
    rw [tildeRestrictStalkMap_naturality, localizedModuleStalkEquiv_apply,
      localizedModuleStalkEquiv_apply]
    exact h3.symm
  exact (congrArg (fun k : ((modulesStalkFunctor S.U.toScheme y).obj
    ((restrictedTildeFunctor S).obj M) : Type u) →ₗ[S.A]
    (N.localizedModule (underlyingPrime S y).asIdeal.primeCompl : Type u) => k z) key)

/-! ### The stalk of a term of the system -/

/-- **The stalk of `ℱ_(n+1)` at `y` modulo `ℐ_y^(n+1)` is the stalk of `ℱₙ`.** A term of a
coherent adic system is the quotient of the next term by `ℐ^(n+1)`
(`Stacks.Coherent.IsCoherentAdicSystem.quotientIso`), and the stalk of such a quotient is the
quotient of the stalk (`Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv`). -/
def stalkIdealPowerQuotientEquiv (n : ℕ) :
    (((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))) : Type u) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1)))))))
      ≃ₗ[S.U.toScheme.presheaf.stalk y]
      ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) : Type u) :=
  haveI : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
  (idealPowerQuotientStalkLinearEquiv (idealOnOpen S) (n + 1) (F.obj.obj (op (n + 1))) y).trans
    ((modulesStalkFunctor S.U.toScheme y).mapIso (C := S.U.toScheme.Modules)
      (F.property.quotientIso n)).toLinearEquiv

/-- **`ℐ_y^(n+1)` annihilates the stalk of `ℱₙ` at `y`.** The stalk is a quotient of the stalk of
`ℱ_(n+1)` by `ℐ_y^(n+1)` times it, and such a quotient is annihilated by that ideal. -/
theorem stalk_pow_smul_top_eq_bot (n : ℕ) :
    IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
        (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
          ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)))) = ⊥ := by
  refine ideal_smul_top_eq_bot_of_linearEquiv _ (stalkIdealPowerQuotientEquiv S y F n) ?_
  refine le_antisymm (Submodule.smul_le.2 fun r hr z _ => ?_) bot_le
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.mem_bot _).mpr
    ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr Submodule.mem_top))

/-- **The stalk of `ℱₙ` at a point of `U` is free over `𝒪_{U,y}/ℐ_y^(n+1)`**, under condition (4)
of [Stacks, Tag 0DXU]: that condition gives the freeness of the stalk of `ℱ_(n+1)` modulo
`ℐ_y^(n+1)` (`Stacks.Algebraization.free_stalk_quotient_of_isFiniteLocallyFreeAdic`), and that
quotient is the stalk of `ℱₙ`.

Off the support of the ideal the stalk ideal is the unit ideal and the quotient is zero, so
nothing is required there. This is
`Stacks.Algebraization.free_stalk_zero_of_isFiniteLocallyFreeAdic` at a general index. -/
theorem free_stalk_of_isFiniteLocallyFreeAdic
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F) (n : ℕ) :
    Module.Free
      (S.U.toScheme.presheaf.stalk y ⧸ IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1))
      ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)))))) := by
  by_cases hy : y ∈ (idealOnOpen S).support
  · have h0 := free_stalk_quotient_of_isFiniteLocallyFreeAdic S F hfree n hy
    have hZq := free_quotient_smul_top_of_free
      (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1))
      (Z := ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))))))))
    exact free_quotient_of_linearEquiv _ (stalkIdealPowerQuotientEquiv S y F n)
  · have htop : IdealSheafData.stalk (idealOnOpen S) y = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support (idealOnOpen S) y).mpr hy
    rw [htop, Ideal.top_pow]
    have hsub : ((⊤ : Ideal ↑(S.U.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
          ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n))))) = ⊤ :=
      Submodule.top_smul _
    have := Submodule.Quotient.subsingleton_iff.mpr hsub
    infer_instance

/-! ### The localized sections of the system at a point of `U` -/

/-- **The stalk at `y` of `(Mₙ~)|_U` is the stalk of `ℱₙ`**, by [Stacks, Tag 0EIR] in the form
`Stacks.Algebraization.globalSectionsRestrictedTildeSystemIso`. -/
def globalSectionsRestrictedTildeStalkEquiv (n : ℕ) :
    ((modulesStalkFunctor S.U.toScheme y).obj
        ((restrictedTildeFunctor S).obj ((globalSectionsSystem S F).obj (op n))) : Type u)
      ≃ₗ[S.U.toScheme.presheaf.stalk y]
      ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) : Type u) :=
  ((modulesStalkFunctor S.U.toScheme y).mapIso (C := S.U.toScheme.Modules)
    ((globalSectionsRestrictedTildeSystemIso S F).app (op n))).toLinearEquiv

/-- The comparison `stalk_y((Mₙ~)|_U) ≅ ℱ_{n,y}` is the stalk of the comparison of sheaves. -/
theorem globalSectionsRestrictedTildeStalkEquiv_apply (n : ℕ)
    (z : ((modulesStalkFunctor S.U.toScheme y).obj
      ((restrictedTildeFunctor S).obj ((globalSectionsSystem S F).obj (op n))) : Type u)) :
    globalSectionsRestrictedTildeStalkEquiv S y F n z
      = ((modulesStalkFunctor S.U.toScheme y).map (C := S.U.toScheme.Modules)
          ((globalSectionsRestrictedTildeSystemIso S F).hom.app (op n))) z := rfl

/-- The comparison `stalk_y((Mₙ~)|_U) ≅ ℱ_{n,y}` carries the transition map of the system of
sections to the transition map of the system of sheaves: the comparison is a natural
isomorphism. -/
theorem globalSectionsRestrictedTildeStalkEquiv_naturality (n : ℕ)
    (z : ((modulesStalkFunctor S.U.toScheme y).obj
      ((restrictedTildeFunctor S).obj ((globalSectionsSystem S F).obj (op n))) : Type u)) :
    globalSectionsRestrictedTildeStalkEquiv S y F 0
        (((modulesStalkFunctor S.U.toScheme y).map ((restrictedTildeFunctor S).map
          ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op))) z)
      = ((modulesStalkFunctor S.U.toScheme y).map (F.obj.map (homOfLE (Nat.zero_le n)).op))
          (globalSectionsRestrictedTildeStalkEquiv S y F n z) := by
  have hnat := (globalSectionsRestrictedTildeSystemIso S F).hom.naturality
    (homOfLE (Nat.zero_le n)).op
  rw [Functor.comp_map] at hnat
  have h2 := congrArg (fun k => (modulesStalkFunctor S.U.toScheme y).map
    (C := S.U.toScheme.Modules) k) hnat
  rw [Functor.map_comp, Functor.map_comp] at h2
  have h3 := ConcreteCategory.congr_hom h2 z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h3
  rw [globalSectionsRestrictedTildeStalkEquiv_apply,
    globalSectionsRestrictedTildeStalkEquiv_apply]
  exact h3

/-- **The stalk of `ℱₙ` at `y` is the localization of `Mₙ = H⁰(U, ℱₙ)` at the prime under `y`**,
as an additive isomorphism; it is semilinear over `Stacks.Algebraization.pointStalkRingEquiv`
(`Stacks.Algebraization.globalSectionsStalkLocalizedAddEquiv_smul`) and compatible with the
transition maps (`Stacks.Algebraization.globalSectionsStalkLocalizedAddEquiv_transition`). -/
def globalSectionsStalkLocalizedAddEquiv (n : ℕ) :
    ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) : Type u) ≃+
      ((((globalSectionsSystem S F).obj (op n)).localizedModule
        (underlyingPrime S y).asIdeal.primeCompl : Type u)) :=
  (globalSectionsRestrictedTildeStalkEquiv S y F n).toAddEquiv.symm.trans
    (localizedModuleStalkEquiv S y ((globalSectionsSystem S F).obj (op n))).toAddEquiv

/-- The identification of the stalk of `ℱₙ` with `(Mₙ)_𝔭` is the comparison of sheaves on stalks
followed by the identification of the stalk of `(Mₙ~)|_U` with the localized module. -/
theorem globalSectionsStalkLocalizedAddEquiv_apply (n : ℕ)
    (w : ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) : Type u)) :
    globalSectionsStalkLocalizedAddEquiv S y F n w
      = localizedModuleStalkEquiv S y ((globalSectionsSystem S F).obj (op n))
          ((globalSectionsRestrictedTildeStalkEquiv S y F n).symm w) := rfl

/-- The identification of the stalk of `ℱₙ` with `(Mₙ)_𝔭` is semilinear over the identification
of the local ring of `U` at `y` with `A_𝔭`. -/
theorem globalSectionsStalkLocalizedAddEquiv_smul (n : ℕ)
    (ρ : ↑(S.U.toScheme.presheaf.stalk y))
    (w : ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) : Type u)) :
    globalSectionsStalkLocalizedAddEquiv S y F n (ρ • w)
      = pointStalkRingEquiv S y ρ • globalSectionsStalkLocalizedAddEquiv S y F n w := by
  rw [globalSectionsStalkLocalizedAddEquiv_apply, globalSectionsStalkLocalizedAddEquiv_apply,
    map_smul]
  exact localizedModuleStalkEquiv_smul S y ((globalSectionsSystem S F).obj (op n)) ρ _

/-- **The identification of the stalk of `ℱₙ` with `(Mₙ)_𝔭` carries the transition map of the
system to the localized transition map of the sections.** -/
theorem globalSectionsStalkLocalizedAddEquiv_transition (n : ℕ)
    (w : ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op n)) : Type u)) :
    (ModuleCat.localizedModuleMap.{u} (underlyingPrime S y).asIdeal.primeCompl
          ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom
        (globalSectionsStalkLocalizedAddEquiv S y F n w)
      = globalSectionsStalkLocalizedAddEquiv S y F 0
          (((modulesStalkFunctor S.U.toScheme y).map
            (F.obj.map (homOfLE (Nat.zero_le n)).op)) w) := by
  rw [globalSectionsStalkLocalizedAddEquiv_apply, globalSectionsStalkLocalizedAddEquiv_apply,
    ← localizedModuleStalkEquiv_naturality]
  refine congrArg (localizedModuleStalkEquiv S y ((globalSectionsSystem S F).obj (op 0))) ?_
  refine ((globalSectionsRestrictedTildeStalkEquiv S y F 0).eq_symm_apply).mpr ?_
  rw [globalSectionsRestrictedTildeStalkEquiv_naturality, LinearEquiv.apply_symm_apply]

/-! ### The two conclusions at a point of `U` -/

/-- The ideal `ℐ_y = (f)` of the local ring of `U` at `y` maps onto `(f)` in `A_𝔭`. -/
private theorem map_pointStalkRingEquiv_stalk (f : S.A) (hI : S.I = Ideal.span {f}) :
    Ideal.map ((pointStalkRingEquiv S y) : ↑(S.U.toScheme.presheaf.stalk y) →+*
        Localization.AtPrime (underlyingPrime S y).asIdeal)
        (IdealSheafData.stalk (idealOnOpen S) y)
      = Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f} := by
  rw [stalk_idealOnOpen_eq_span_of_ideal_eq_span S f hI y, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun z => Ideal.span {z}) (congrArg
    (fun t : S.A →+* Localization.AtPrime (underlyingPrime S y).asIdeal => t f)
    (pointStalkRingEquiv_comp_baseToPointStalk S y))

/-- **The localization of `Mₙ = H⁰(U, ℱₙ)` at a prime of `V(f)` other than `𝔪` is
`(A_𝔭/f^(n+1))^r`.** -/
theorem exists_linearEquiv_quotSMulTop_localizedModule_globalSectionsSystem_at_point
    (f : S.A) (hI : S.I = Ideal.span {f})
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F)
    (hfy : f ∈ (underlyingPrime S y).asIdeal) (n : ℕ) :
    ∃ r : ℕ, Nonempty
      ((((globalSectionsSystem S F).obj (op n)).localizedModule
            (underlyingPrime S y).asIdeal.primeCompl : Type u)
          ≃ₗ[Localization.AtPrime (underlyingPrime S y).asIdeal]
        QuotSMulTop
          (algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f ^ (n + 1))
          (Fin r → Localization.AtPrime (underlyingPrime S y).asIdeal)) := by
  have hmap : Ideal.map
        ((pointStalkRingEquiv S y) : ↑(S.U.toScheme.presheaf.stalk y) →+*
          Localization.AtPrime (underlyingPrime S y).asIdeal)
        (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1))
      = Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f
          ^ (n + 1)} := by
    rw [Ideal.map_pow, map_pointStalkRingEquiv_stalk S y f hI, Ideal.span_singleton_pow]
  have hGsmul := globalSectionsStalkLocalizedAddEquiv_smul S y F n
  have hbot := smul_top_eq_bot_of_semilinearEquiv (pointStalkRingEquiv S y) hmap
    (globalSectionsStalkLocalizedAddEquiv S y F n) hGsmul (stalk_pow_smul_top_eq_bot S y F n)
  have hfreestalk := free_stalk_of_isFiniteLocallyFreeAdic S y F hfree n
  have hfreeq := free_quotient_of_ringEquiv (pointStalkRingEquiv S y) hmap
    (globalSectionsStalkLocalizedAddEquiv S y F n) hGsmul
  have hfinstalk := finite_stalk_coherentAdicSystem_obj F y n
  have hfinL : Module.Finite (Localization.AtPrime (underlyingPrime S y).asIdeal)
      ((((globalSectionsSystem S F).obj (op n)).localizedModule
        (underlyingPrime S y).asIdeal.primeCompl : Type u)) :=
    Module.Finite.of_semilinearEquiv (pointStalkRingEquiv S y).symm
      (globalSectionsStalkLocalizedAddEquiv S y F n).symm
      (fun b l => (globalSectionsStalkLocalizedAddEquiv S y F n).injective (by
        rw [AddEquiv.apply_symm_apply, hGsmul, RingEquiv.apply_symm_apply,
          AddEquiv.apply_symm_apply]))
  have hfinq : Module.Finite
      (Localization.AtPrime (underlyingPrime S y).asIdeal ⧸
        Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f
          ^ (n + 1)})
      ((((globalSectionsSystem S F).obj (op n)).localizedModule
            (underlyingPrime S y).asIdeal.primeCompl : Type u) ⧸
        (Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f
            ^ (n + 1)} •
          (⊤ : Submodule (Localization.AtPrime (underlyingPrime S y).asIdeal)
            ((((globalSectionsSystem S F).obj (op n)).localizedModule
              (underlyingPrime S y).asIdeal.primeCompl : Type u))))) :=
    Module.Finite.of_restrictScalars_finite
      (Localization.AtPrime (underlyingPrime S y).asIdeal) _ _
  have hunit : ¬ IsUnit (algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f
      ^ (n + 1)) := by
    have hmem : algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f
        ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (underlyingPrime S y).asIdeal) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (underlyingPrime S y).asIdeal f).mpr hfy
    have hnu : ¬ IsUnit (algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f) :=
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    exact fun h => hnu ((isUnit_pow_iff (Nat.succ_ne_zero n)).mp h)
  exact exists_linearEquiv_quotSMulTop_of_free _ hunit hbot hfreeq hfinq

/-- **The localized transition map `(Mₙ)_𝔭 ⟶ (M₀)_𝔭` is surjective with kernel `f·(Mₙ)_𝔭`**, at a
point `y` of `U`. On stalks the transition map of a coherent adic system is surjective
(`Stacks.Algebraization.surjective_stalk_transition`) with kernel `ℐ_y` times the stalk
(`Stacks.Algebraization.ker_stalk_transition_zero`), and `ℐ_y = (f)`. -/
theorem surjective_and_ker_localizedModule_map_globalSectionsSystem_at_point
    (f : S.A) (hI : S.I = Ideal.span {f}) (n : ℕ) :
    Function.Surjective
        (ModuleCat.localizedModuleMap.{u} (underlyingPrime S y).asIdeal.primeCompl
          ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom ∧
      LinearMap.ker
          (ModuleCat.localizedModuleMap.{u} (underlyingPrime S y).asIdeal.primeCompl
            ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom =
        algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f •
          (⊤ : Submodule (Localization.AtPrime (underlyingPrime S y).asIdeal)
            ((((globalSectionsSystem S F).obj (op n)).localizedModule
              (underlyingPrime S y).asIdeal.primeCompl : Type u))) := by
  have hmap := map_pointStalkRingEquiv_stalk S y f hI
  have hGsmul := globalSectionsStalkLocalizedAddEquiv_smul S y F n
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨w₀, hw₀⟩ := (globalSectionsStalkLocalizedAddEquiv S y F 0).surjective z
    obtain ⟨v, hv⟩ := surjective_stalk_transition F y (Nat.zero_le n) w₀
    refine ⟨globalSectionsStalkLocalizedAddEquiv S y F n v, ?_⟩
    rw [globalSectionsStalkLocalizedAddEquiv_transition, hv, hw₀]
  · rw [← Submodule.ideal_span_singleton_smul]
    refine Submodule.ext fun z => ?_
    obtain ⟨w, rfl⟩ := (globalSectionsStalkLocalizedAddEquiv S y F n).surjective z
    have h1 : (globalSectionsStalkLocalizedAddEquiv S y F n w ∈
          LinearMap.ker
            (ModuleCat.localizedModuleMap.{u} (underlyingPrime S y).asIdeal.primeCompl
              ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom)
        ↔ ((modulesStalkFunctor S.U.toScheme y).map
            (F.obj.map (homOfLE (Nat.zero_le n)).op)) w = 0 := by
      rw [LinearMap.mem_ker, globalSectionsStalkLocalizedAddEquiv_transition]
      exact ⟨fun h => (globalSectionsStalkLocalizedAddEquiv S y F 0).injective
          (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    rw [h1, ← mem_smul_top_iff_of_semilinearEquiv (pointStalkRingEquiv S y) hmap
      (globalSectionsStalkLocalizedAddEquiv S y F n) hGsmul w,
      ← ker_stalk_transition_zero F y n]
    exact LinearMap.mem_ker.symm

end Point

/-! ### The two conclusions at a prime of `A` -/

section Prime

variable (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **A prime other than the maximal ideal does not contain `𝔞`**, when `𝔞 = 𝔪`: a prime
containing the maximal ideal and not the unit ideal *is* the maximal ideal. So such a prime is
the prime under a point of `U = X ∖ V(𝔞)`. -/
theorem not_a_le_of_ne_maximalIdeal (ha : S.a = IsLocalRing.maximalIdeal S.A) (q : Ideal S.A)
    [hq : q.IsPrime] (hqm : q ≠ IsLocalRing.maximalIdeal S.A) : ¬ (S.a ≤ q) := by
  rw [ha]
  intro hle
  exact hqm ((IsLocalRing.maximalIdeal.isMaximal S.A).eq_of_le hq.ne_top hle).symm

/-- **Stacks Project, Tag 0DXU (the local structure of `Mₙ` away from the closed point).** Let
`A` be Noetherian local with `𝔞 = 𝔪`, let `(ℱₙ)` be a coherent `I`-adic system on
`U = X ∖ V(𝔪)` with `I = (f)` whose terms are finite locally free over the infinitesimal
neighbourhoods — conditions (1), (3) and (4) of the source — and write `Mₙ = H⁰(U, ℱₙ)`. Then for
every prime `𝔮` containing `f` and different from `𝔪` the localization `(Mₙ)_𝔮` is a finite free
module over `A_𝔮/f^(n+1)A_𝔮`, read as an `A_𝔮`-module.

The prime is a point `y` of `U` (`Stacks.Algebraization.exists_point_underlyingPrime`); the stalk
of `ℱₙ` there is free over `𝒪_{U,y}/ℐ_y^(n+1)` of finite rank by condition (4)
(`Stacks.Algebraization.free_stalk_of_isFiniteLocallyFreeAdic`), and
`Stacks.Algebraization.globalSectionsStalkLocalizedAddEquiv` identifies that stalk with
`(Mₙ)_𝔮`. -/
theorem exists_linearEquiv_quotSMulTop_localizedModule_globalSectionsSystem
    (ha : S.a = IsLocalRing.maximalIdeal S.A) (f : S.A) (hI : S.I = Ideal.span {f})
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F) (q : Ideal S.A) [q.IsPrime]
    (hfq : f ∈ q) (hqm : q ≠ IsLocalRing.maximalIdeal S.A) (n : ℕ) :
    ∃ r : ℕ, Nonempty
      ((((globalSectionsSystem S F).obj (op n)).localizedModule q.primeCompl : Type u)
          ≃ₗ[Localization.AtPrime q]
        QuotSMulTop (algebraMap S.A (Localization.AtPrime q) f ^ (n + 1))
          (Fin r → Localization.AtPrime q)) := by
  obtain ⟨y, hy⟩ := exists_point_underlyingPrime S q (not_a_le_of_ne_maximalIdeal S ha q hqm)
  subst hy
  exact exists_linearEquiv_quotSMulTop_localizedModule_globalSectionsSystem_at_point S y F f hI
    hfree hfq n

/-- **Stacks Project, Tag 0DXU (the transition map of the sections away from the closed point).**
In the situation above, the localization at `𝔮` of the transition map `Mₙ ⟶ M₀` is surjective
with kernel `f·(Mₙ)_𝔮`.

On stalks at the point `y` of `U` under `𝔮` the transition map of a coherent adic system is
surjective (`Stacks.Algebraization.surjective_stalk_transition`) with kernel `ℐ_y` times the
stalk (`Stacks.Algebraization.ker_stalk_transition_zero`), and `ℐ_y` is generated by the image of
`f`. Neither statement uses condition (4) or the nonzerodivisor hypothesis. -/
theorem surjective_and_ker_localizedModule_map_globalSectionsSystem
    (ha : S.a = IsLocalRing.maximalIdeal S.A) (f : S.A) (hI : S.I = Ideal.span {f})
    (q : Ideal S.A) [q.IsPrime] (hqm : q ≠ IsLocalRing.maximalIdeal S.A) (n : ℕ) :
    Function.Surjective ((ModuleCat.localizedModuleFunctor.{u} q.primeCompl).map
          ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom ∧
      LinearMap.ker ((ModuleCat.localizedModuleFunctor.{u} q.primeCompl).map
            ((globalSectionsSystem S F).map (homOfLE (Nat.zero_le n)).op)).hom =
        algebraMap S.A (Localization.AtPrime q) f •
          (⊤ : Submodule (Localization.AtPrime q)
            ((((globalSectionsSystem S F).obj (op n)).localizedModule q.primeCompl :
              Type u))) := by
  obtain ⟨y, hy⟩ := exists_point_underlyingPrime S q (not_a_le_of_ne_maximalIdeal S ha q hqm)
  subst hy
  exact surjective_and_ker_localizedModule_map_globalSectionsSystem_at_point S y F f hI n

end Prime

end Stacks.Algebraization

end
