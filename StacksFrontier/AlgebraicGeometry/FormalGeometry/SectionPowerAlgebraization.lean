module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LocalCohomologyAnnihilatorInputs
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctionsHigher
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerTower

/-!
# Algebraization along the infinitesimal neighbourhoods of a zero scheme

Let `P` be a scheme with an invertible module `L`, let `s` be a global section of `L`, let `Q`
be the zero scheme of `s` and let `Qₙ` be its `n`-th infinitesimal neighbourhood. For a
quasi-coherent `𝓕` on `P` with restrictions `𝓕ₙ` to `Qₙ` there is the comparison map

`Hⁱ(P, 𝓕) ⟶ lim Hⁱ(Qₙ, 𝓕ₙ)`

of `Stacks.Algebraization.zeroSchemeComparison`. [Stacks, Tag 0EL1] asserts that it is an
isomorphism in every degree `i < σ` as soon as

`depth(𝓕_p) + dim({p}‾) > σ`

at every point `p` of `P` outside `Q`. That proposition, for `P` proper over a field `k`, `L`
ample and `𝓕` coherent, is `Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/LefschetzZeroSchemeComparison.lean`, proved through
Čech complexes of the section ring. This file keeps the earlier route through local cohomology
on the punctured cone, whose last step is a transport lemma with the geometric inputs taken as
hypotheses.

## The route, and what is taken as hypotheses

The source's proof passes to the cone: with `A = ⨁_{m ≥ 0} Γ(P, L^m)` the section ring,
`U ⊆ Spec A` the punctured cone and `M` a finite `A`-module with `𝓕|_U = M̃|_U`, the comparison
map above becomes the comparison map `Hⁱ(U, M̃) ⟶ limₙ Hⁱ(U, (M/fⁿM)̃)` of [Stacks, Tag 0EKM],
for `f ∈ A₁` the image of `s`. The bijectivity of the latter is
`Stacks.Algebraization.HigherComplementTower.bijective_toTowerSections`, whose input is the
annihilation of `H^k_{V(I)}(M)` by a power of `f` for every `k ≤ σ + 1`.

This file discharges that annihilation input from the geometric depth–dimension bound. The
chain is the source's: the bound on `P` is carried to the bound `> σ + 1` on `Spec A` by the
fibre dichotomy of the punctured cone
(`Stacks.Algebraization.lt_depthAddRelativeDim_of_fibreSplitting`); Faltings' annihilator theorem
[Stacks, Tag 0EFC] turns that into an ideal `J` annihilating the local cohomology, with
`V(J) ⊆ V(I)`; and since `f ∈ I` some power of `f` lies in `J`.

The transport lemma `isIso_zeroSchemeComparison_of_depthAddDim_gt` takes three inputs as
explicit hypotheses.

* **The fibre dichotomy `hsplit`.** A point of `U` over `p ∈ P` is either the generic point of
  the fibre of `π|_U`, where the depth is `depth(𝓕_p)` and the dimension `dim({p}‾) + 1`, or a
  closed point of it, where the depth is `depth(𝓕_p) + 1` and the dimension `dim({p}‾)`. This
  rests on `π|_U` being smooth of relative dimension one, which is not in the library.
* **The section ring data.** The ring enters as an abstract Noetherian `k`-algebra `A` of finite
  type together with a finite module `M`. The lemma also asks `A` to be `f`-adically complete.
  A finite type algebra over a field is a Jacobson ring, so its Jacobson radical is its
  nilradical, while `f`-adic completeness puts `f` in the Jacobson radical
  (`IsAdicComplete.le_jacobson_bot`): the hypotheses together force `f` to be nilpotent. The
  source's passage to the completion `A'` is therefore not what these hypotheses describe, and
  the lemma does not apply to the section ring of a non-nilpotent `s`.
* **The algebraization square.** That the geometric comparison map *is* the comparison map of
  [Stacks, Tag 0EKM] under the graded decomposition of [Stacks, Tag 0EKH] is carried as a
  commuting square with bijective vertical maps. This is the only place where the two sides are
  compared, and it is where the base-change square of
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjAndSpecBaseChange.lean` would be consumed.

## Main definitions

* `Stacks.Algebraization.sheafDepthAt` — the depth `depth(𝓕_p)` of a module on a scheme at a
  point, that is the depth of its stalk over the local ring.
* `Stacks.Algebraization.dimClosureAt` — the dimension `dim({p}‾)` of the closure of a point.

## Main results

* `Stacks.Algebraization.exists_pow_smul_localCohomologyModule_eq_zero_of_fibreSplitting` — the
  annihilation claim: the depth–dimension bound on the base annihilates `H^k_{V(I)}(M)` by a
  power of `f` for every `k ≤ σ + 1`.
* `Stacks.Algebraization.bijective_toTowerSections_of_fibreSplitting` — hence the comparison map
  of [Stacks, Tag 0EKM] is bijective in every degree `i < σ`.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_of_depthAddDim_gt` — transport of that
  bijectivity to the geometric comparison map along a commuting square. [Stacks, Tag 0EL1] itself
  is `Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper`.

## Implementation notes

The depth of a module on a scheme at a point needs the `𝒪_{X,x}`-module structure on the stalk,
which instance search does not find through the `Scheme.Modules` wrapper; it is supplied by
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`, exactly as
`Stacks.ModuleStalk.stalkModule` and
`Stacks.AlgebraicGeometry.AssociatedPointsMono.stalkModule` do.

The ideal `I` is abstract, playing the role of the irrelevant ideal `A₊` so that
`Spec A ∖ V(I)` is the punctured cone and `V(I)` is the finite set of closed points `Z`; the
hypotheses only use `f ∈ I` and a finite generating family of `I`, which is what both
[Stacks, Tag 0EFC] and [Stacks, Tag 0EKM] consume.

The two supports of [Stacks, Tag 0EFC] are taken equal, both being `V(I)`: the source's claim is
about `H^i_Z(M)` and the annihilating ideal is wanted supported in `Z` as well, which is what
makes `f` — vanishing on `Z` because `f ∈ A₊` — a power of an element of it.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EKM](https://stacks.math.columbia.edu/tag/0EKM)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EKH](https://stacks.math.columbia.edu/tag/0EKH)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The depth and the dimension at a point -/

/-- The depth `depth(𝓕_x)` of a module on a scheme at a point: the depth of its stalk over the
local ring of the scheme at that point, along the maximal ideal. This is the quantity of
[Stacks, Tag 0341] part (1), which `AlgebraicGeometry.SheafHasDepthAt` compares against a
natural number. -/
def sheafDepthAt {X : Scheme.{u}} (F : X.Modules) (x : X) : ℕ∞ :=
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (F.presheaf.stalk x)

/-- The dimension `dim({x}‾)` of the closure of a point of a scheme. -/
def dimClosureAt (X : Scheme.{u}) (x : X) : WithBot ℕ∞ :=
  topologicalKrullDim (closure ({x} : Set X))

/-! ### The annihilation claim -/

/-- **The annihilation claim of [Stacks, Tag 0EL1].** Let `A` be a Noetherian algebra of finite
type over a field, `M` a finite `A`-module, `I` an ideal and `f ∈ I`. If the depth and the
relative dimension of `M` at a prime outside `V(I)` are those of a base point with one extra
unit distributed between them — the fibre dichotomy of the punctured cone — and the base
satisfies `depth + dim > σ`, then a single power of `f` annihilates `H^k_{V(I)}(M)` in every
degree `k ≤ σ + 1`.

Faltings' annihilator theorem [Stacks, Tag 0EFC], in the form
`Stacks.Algebraization.exists_ideal_le_annihilator_localCohomology_of_fibreSplitting_finiteType`,
produces an ideal `J` with `V(J) ⊆ V(I)` annihilating those modules; since `f ∈ I` the closed
set `V(I)` lies in `V(f)`, so `f` lies in the radical of `J` and some `f ^ c` lies in `J`. -/
theorem exists_pow_smul_localCohomologyModule_eq_zero_of_fibreSplitting
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I.FG) (f : A) (hf : f ∈ I)
    {P : Type u} (proj : PrimeSpectrum A → P)
    (baseDepth : P → ℕ∞) (baseDim : P → WithBot ℕ∞) (σ : ℕ)
    (hsplit : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      ∀ q : PrimeSpectrum A, q ∈ PrimeSpectrum.zeroLocus (I : Set A) →
      p.asIdeal ≤ q.asIdeal →
      (localizedDepth A M p = baseDepth (proj p) ∧
          relativeDimAt A p q = baseDim (proj p) + 1) ∨
        (localizedDepth A M p = baseDepth (proj p) + 1 ∧
          relativeDimAt A p q = baseDim (proj p)))
    (hbase : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      enatToEInt (baseDepth (proj p)) + krullDimToEInt (baseDim (proj p)) > ((σ : ℤ) : EInt)) :
    ∃ c : ℕ, ∀ j : ℤ, j ≤ (σ : ℤ) + 1 →
      ∀ x : Stacks.LocalCohomology.localCohomologyModule A I hI (ModuleCat.of A M) j,
        f ^ c • x = 0 := by
  have hT : StableUnderSpecialization (PrimeSpectrum.zeroLocus (I : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  obtain ⟨J, hJT', hJann⟩ :=
    exists_ideal_le_annihilator_localCohomology_of_fibreSplitting_finiteType
      k A M (PrimeSpectrum.zeroLocus (I : Set A)) (PrimeSpectrum.zeroLocus (I : Set A))
      le_rfl hT hT proj baseDepth baseDim (σ : ℤ) (Int.natCast_nonneg σ) hsplit hbase
  have hsub : PrimeSpectrum.zeroLocus (J : Set A)
      ⊆ PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A) := by
    refine hJT'.trans ?_
    rw [PrimeSpectrum.zeroLocus_span]
    exact PrimeSpectrum.zeroLocus_anti_mono (by simpa using hf)
  obtain ⟨c, hc⟩ : f ∈ J.radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J (Ideal.span {f})).mp hsub
      (Ideal.mem_span_singleton_self f)
  refine ⟨c, fun j hj x => ?_⟩
  have e := Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule
    A I hI (ModuleCat.of A M) j
  have hx := Module.mem_annihilator.mp (hJann j hj hc) (e.inv x)
  simpa only [map_smul, map_zero, ← ConcreteCategory.comp_apply, e.inv_hom_id,
    ConcreteCategory.id_apply] using congrArg (fun y => e.hom y) hx

/-- **The algebraic half of [Stacks, Tag 0EL1].** With the annihilation claim discharged from the
depth–dimension bound, the comparison map `Hⁱ(U, M̃) ⟶ limₙ Hⁱ(U, (M/fⁿM)̃)` of
[Stacks, Tag 0EKM] is bijective in every degree `i < σ`. -/
theorem bijective_toTowerSections_of_fibreSplitting
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I.FG) {r : ℕ} (fam : Fin r → A)
    (hfam : Ideal.span (Set.range fam) = I) (f : A) (hf : f ∈ I)
    [IsAdicComplete (Ideal.span {f}) A]
    {P : Type u} (proj : PrimeSpectrum A → P)
    (baseDepth : P → ℕ∞) (baseDim : P → WithBot ℕ∞) (σ : ℕ)
    (hsplit : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      ∀ q : PrimeSpectrum A, q ∈ PrimeSpectrum.zeroLocus (I : Set A) →
      p.asIdeal ≤ q.asIdeal →
      (localizedDepth A M p = baseDepth (proj p) ∧
          relativeDimAt A p q = baseDim (proj p) + 1) ∨
        (localizedDepth A M p = baseDepth (proj p) + 1 ∧
          relativeDimAt A p q = baseDim (proj p)))
    (hbase : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      enatToEInt (baseDepth (proj p)) + krullDimToEInt (baseDim (proj p)) > ((σ : ℤ) : EInt))
    (i : ℕ) (hi : i < σ) :
    Function.Bijective
      (HigherComplementTower.toTowerSections fam f (ModuleCat.of A M) (i : ℤ)) := by
  obtain ⟨c, hc⟩ := exists_pow_smul_localCohomologyModule_eq_zero_of_fibreSplitting
    k A M I hI f hf proj baseDepth baseDim σ hsplit hbase
  exact HigherComplementTower.bijective_toTowerSections hI fam hfam f hf (ModuleCat.of A M) σ
    (fun j hj => ⟨c, hc (j : ℤ) (by exact_mod_cast hj)⟩) i hi

/-! ### Stacks 0EL1 -/

/-- Transport of the bijectivity of the comparison map of [Stacks, Tag 0EKM] to the geometric
comparison map `Hⁱ(P, 𝓕) ⟶ lim Hⁱ(Qₙ, 𝓕ₙ)` of a zero scheme, for `P` a scheme, `L` an invertible
module, `s ∈ Γ(P, L)` and `𝓕` quasi-coherent, under `depth(𝓕_p) + dim({p}‾) > σ` off `Q = Z(s)`
(`hdepth`). The cone inputs are hypotheses: the fibre dichotomy `hsplit` with `hproj`, a
Noetherian `k`-algebra `A` of finite type which is `f`-adically complete with a finite module `M`,
and the square `halg` identifying the geometric comparison map with the algebraic one.

A finite type `k`-algebra is Jacobson and `f`-adic completeness puts `f` in its Jacobson radical,
so these hypotheses force `f` to be nilpotent in `A`; the lemma is not a form of
[Stacks, Tag 0EL1]. That proposition, for `P` proper over `k`, `L` ample and `𝓕` coherent, is
`Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper`. -/
theorem isIso_zeroSchemeComparison_of_depthAddDim_gt
    (k : Type u) [Field k] (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (σ : ℕ)
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      enatToEInt (sheafDepthAt F x) + krullDimToEInt (dimClosureAt X x) > ((σ : ℤ) : EInt))
    (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I.FG) {r : ℕ} (fam : Fin r → A)
    (hfam : Ideal.span (Set.range fam) = I) (f : A) (hf : f ∈ I)
    [IsAdicComplete (Ideal.span {f}) A]
    (proj : PrimeSpectrum A → X)
    (hproj : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      proj p ∉ ((zeroScheme X L s).support : Set X))
    (hsplit : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      ∀ q : PrimeSpectrum A, q ∈ PrimeSpectrum.zeroLocus (I : Set A) →
      p.asIdeal ≤ q.asIdeal →
      (localizedDepth A M p = sheafDepthAt F (proj p) ∧
          relativeDimAt A p q = dimClosureAt X (proj p) + 1) ∨
        (localizedDepth A M p = sheafDepthAt F (proj p) + 1 ∧
          relativeDimAt A p q = dimClosureAt X (proj p)))
    (halg : ∀ i : ℕ, i < σ →
      ∃ (e₁ : Hgroup X.ringCatSheaf ⊤ i F ≃+
          (complementCohomologyFunctor fam (i : ℤ)).obj (ModuleCat.of A M))
        (e₂ : ↥(limit (IdealTower.cohomologyTower (zeroSchemeTowerIdeal X L s)
            (zeroSchemeTowerIdeal_succ_le X L s) F i)) ≃+
          ↥(Stacks.ProZero.towerSections
            (HigherComplementTower.quotientCohomologyTower fam f (ModuleCat.of A M) (i : ℤ))
            (HigherComplementTower.quotientCohomologyTransition fam f (ModuleCat.of A M)
              (i : ℤ)))),
          ∀ x : Hgroup X.ringCatSheaf ⊤ i F,
            e₂ (zeroSchemeComparison X L s F i x) =
              HigherComplementTower.toTowerSections fam f (ModuleCat.of A M) (i : ℤ) (e₁ x))
    (i : ℕ) (hi : i < σ) :
    IsIso (zeroSchemeComparison X L s F i) := by
  obtain ⟨e₁, e₂, hsq⟩ := halg i hi
  have hbij := bijective_toTowerSections_of_fibreSplitting k A M I hI fam hfam f hf
    proj (sheafDepthAt F) (dimClosureAt X) σ hsplit (fun p hp => hdepth (proj p) (hproj p hp))
    i hi
  have hfun : (fun x => (zeroSchemeComparison X L s F i) x) =
      e₂.symm ∘ (HigherComplementTower.toTowerSections fam f (ModuleCat.of A M) (i : ℤ)) ∘ e₁ := by
    funext x
    exact (e₂.symm_apply_apply _).symm.trans (congrArg e₂.symm (hsq x))
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  have : Function.Bijective
      (e₂.symm ∘ (HigherComplementTower.toTowerSections fam f (ModuleCat.of A M) (i : ℤ)) ∘ e₁) :=
    e₂.symm.bijective.comp (hbij.comp e₁.bijective)
  rw [← hfun] at this
  exact this

end Stacks.Algebraization

end
