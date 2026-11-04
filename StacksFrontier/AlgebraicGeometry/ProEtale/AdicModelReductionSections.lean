module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LocallyConstantValues
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleDerivedSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocallyConstantAdicModel
public import StacksFrontier.AlgebraicGeometry.ProEtale.QuasiCompactFinalObject
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenPoint
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ConstantReductionsMittagLeffler
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.AdicReductionSections
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.AdicCompletionModel
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Module.AdicSystem.RowReductionHomology
public import StacksFrontier.Topology.Sheaves.Modules.StalkKFlat
import StacksCore.Tactic.StacksAttribute

/-!
# The adic model of a complex with constant reductions, and Mittag-Leffler for its sections

Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K`
an object of `D_cons(X, Λ)`, the constructibility read through the derived reduction
(`AlgebraicGeometry.ProEtale.IsConstructibleViaDerivedReduction`), such that every reduction
`K ⊗_Λ^L Λ/Iⁿ` is isomorphic to a complex of constant sheaves of `Λ/Iⁿ`-modules. This file
produces a bounded above complex of finite free `Λ^∧`-modules carrying the reductions of `K`,
and from it Stacks 09C5: the inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` is Mittag-Leffler.

The inverse system is `AlgebraicGeometry.ProEtale.derivedReductionSectionsSystem` of
`StacksFrontier/AlgebraicGeometry/ProEtale/WeaklyContractible/ConstantReductionsMittagLeffler.lean`,
applied to `K` read in the derived category of sheaves of `Λ`-modules through
`AlgebraicGeometry.ProEtale.derivedModuleEquiv`. The same tag is also registered, with the
constructibility condition `IsConstructibleDerivedSheaf` and the reductions taken along chosen
derived base changes, on
`AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_derivedReductionSectionsSystem`
(`StacksFrontier/AlgebraicGeometry/ProEtale/ConstructibleReductionSections.lean`).

## Main results

* `AlgebraicGeometry.ProEtale.isZero_of_isZero_constantSheaf`: on a nonempty scheme, a module
  whose constant sheaf on `X_proét` vanishes is zero.
* `AlgebraicGeometry.ProEtale.isPseudoCoherent_of_hasConstructibleCohomology_constantSheaf`:
  an object `E` of `D(R)`, `R` Noetherian, whose constant complex on a nonempty scheme is
  bounded above with constructible cohomology sheaves is pseudo-coherent.
* `AlgebraicGeometry.ProEtale.exists_isBoundedAboveFiniteFree_reduction_iso`: the adic model,
  a bounded above complex of finite free `Λ^∧`-modules with the reductions of `K`.
* `isMittagLefflerCategorical_derivedReductionSectionsSystem_of_isConstructibleViaDerivedReduction`
  (in `AlgebraicGeometry.ProEtale`): Stacks 09C5; on a weakly contractible affine scheme, the
  inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` is Mittag-Leffler when every reduction of `K` is
  constant.

## Implementation notes

The hypothesis of 09C5, that `K ⊗_Λ^L Λ/Iⁿ` is isomorphic to a complex of constant sheaves of
`Λ/Iⁿ`-modules, is taken in the form in which the source's proof uses it:
`K ⊗_Λ^L Λ/Iⁿ ≅ \underline{E_n}` in `D(X_proét, Λ/Iⁿ)` for an object `E_n` of `D(Λ/Iⁿ)`, the
constant sheaf functor being exact and so inducing a functor of derived categories.

The source's proof uses 09C3 and Stacks 0658 to see that `E_1` is perfect, Stacks 09BE and
Stacks 09AW to produce a finite complex `M^•` of finite projective `Λ^∧`-modules with
`M^•/IⁿM^• ≅ E_n` compatibly with chosen transition maps, and the Tor spectral sequence with
Stacks 0911 for the Mittag-Leffler property of `n ↦ H⁰(M^•/IⁿM^•)`. The proof here is
arranged differently, and needs neither 09C3 nor perfectness:

* `E_n` is the reduction `Λ/Iⁿ ⊗_Λ N` of the fibre `N` of a K-flat representative `P` of `K`
  at a point of `X_proét` (`Stacks.ModuleSheaf.nonempty_iso_extendScalars_sheafFiber`);
* `E_1` is pseudo-coherent, by Stacks 066E: its cohomology modules are finite because their
  constant sheaves are constructible, and it is bounded above because `K ⊗_Λ^L Λ/I` has finite
  Tor amplitude;
* Stacks 0CQF, applied to the tower of the reductions of `N`, produces a bounded above complex
  `F` of finite free `Λ^∧`-modules with `F/Iⁿ F ≅ E_n` in `D(Λ/Iⁿ)` for every `n ≥ 1`;
* the system `j ↦ H⁰(X, \underline{F} ⊗^L Λ^∧/Iʲ) = H⁰(X, \underline{H⁰(F/IʲF)})` is
  Mittag-Leffler, since sections over `X` are exact and the cohomology of the adic reductions
  of a complex of finite modules over a Noetherian ring is Mittag-Leffler by the Artin–Rees
  lemma; this replaces the Tor spectral sequence and Stacks 0911;
* for each `n` the isomorphism of the `n`-th reductions of `P` and `\underline{F}`, which need
  not be compatible with the transition maps, identifies the truncations of the two sections
  systems to the indices `j ≤ n`, and the Mittag-Leffler condition depends only on such
  truncations (`Stacks.ModuleSheaf.isMittagLefflerCategorical_reductionSections_of_adicModel`).
  This is the source's observation about triples of indices `n > m > k`.

Over the empty scheme every term of the system vanishes.

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

section ConstantValues

variable {X : Scheme.{u}} [Nonempty X] {R : Type (max (u + 1) w)} [CommRing R]

/-- On a nonempty scheme `X`, a module whose constant sheaf on `X_proét` is zero is zero: an
isomorphism `\underline{0} ≅ \underline{M}` yields a surjection `0 → M`. -/
theorem isZero_of_isZero_constantSheaf (M : ModuleCat.{max (u + 1) w} R)
    (h : IsZero ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)).obj M)) :
    IsZero M := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)
  obtain ⟨ψ, hψ⟩ := Stacks.ConstantSheaf.exists_surjective_of_constantSheaf_iso
    (Scheme.ProEt.topology X)
    ⟨Scheme.ProEt.mk (𝟙 X),
      Scheme.ProEt.bot_notMem_topology_of_nonempty (V := Scheme.ProEt.mk (𝟙 X)) x⟩
    (ModuleCat.of R PUnit) M ((c.map_isZero (ModuleCat.isZero_of_subsingleton _)).iso h)
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := hψ a
  obtain ⟨b, rfl⟩ := hψ b
  rw [Subsingleton.elim a b]

/-- **A complex of constant sheaves with constructible bounded above cohomology comes from a
pseudo-coherent complex.** Let `X` be a nonempty scheme, `R` a Noetherian ring and `E` an object
of `D(R)` such that `\underline{E}` is bounded above and has constructible cohomology sheaves on
`X_proét`. Then `E` is pseudo-coherent: `\underline{Hⁱ(E)} = Hⁱ(\underline{E})` is constructible,
so `Hⁱ(E)` is finite, and it vanishes with `Hⁱ(\underline{E})`; Stacks 066E concludes. -/
theorem isPseudoCoherent_of_hasConstructibleCohomology_constantSheaf [IsNoetherianRing R]
    (E : DerivedCategory (ModuleCat.{max (u + 1) w} R)) (b : ℤ)
    (hb : ((constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} R)).mapDerivedCategory.obj E).IsLE b)
    (hE : HasConstructibleModuleSheafCohomology.{u, w} X R ((constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} R)).mapDerivedCategory.obj E)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent E := by
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)
  let e : ∀ i, (DerivedCategory.homologyFunctor _ i).obj (c.mapDerivedCategory.obj E) ≅
      c.obj ((DerivedCategory.homologyFunctor _ i).obj E) := fun i =>
    (c.mapDerivedCategoryHomologyIso i).app E
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology E 0
    R).2.1).2 ⟨⟨b, fun i hi => ?_⟩, fun i => ?_⟩
  · exact isZero_of_isZero_constantSheaf _
      ((DerivedCategory.isZero_of_isLE _ b i hi).of_iso (e i).symm)
  · exact finite_of_isConstructibleModuleSheaf'_constantSheaf R _
      (ObjectProperty.prop_of_iso _ (e i) (hE i))

end ConstantValues

section Reduction

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)
  [IsNoetherianRing Λ]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  CochainComplex.braidedCategory Stacks.ModuleSheaf.derivedMonoidal

/-- **The adic model of a K-flat representative.** Let `X` be a nonempty weakly contractible
affine scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K` a constructible object of
`D(X_proét, Λ)` all of whose reductions `K ⊗_Λ^L Λ/Iⁿ` are isomorphic to complexes of constant
sheaves `\underline{E_n}`. For a K-flat complex `P` representing `K`, there is a bounded above
complex `F` of finite free modules over the completion `Λ^∧` such that for every `n ≥ 1` the
reductions `Λ/Iⁿ ⊗_Λ P` and `Λ/Iⁿ ⊗_{Λ^∧} \underline{F}` are isomorphic in `D(X_proét, Λ/Iⁿ)`.

Indeed `E_n` is the reduction `Λ/Iⁿ ⊗_Λ N` of the fibre `N` of `P` at a point of `X_proét`;
`E_1` is pseudo-coherent, its constant complex having constructible bounded above cohomology;
and Stacks 0CQF, applied to the tower of the reductions of `N`, produces `F`. The isomorphisms
need not be compatible as `n` varies. -/
theorem exists_isBoundedAboveFiniteFree_reduction_iso [IsAffine X] [Nonempty X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hconstant : ∀ n : ℕ, ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n)),
      Nonempty ((derivedReduction.{u, w} X Λ (I ^ n)).obj K ≅
        (constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n))).mapDerivedCategory.obj E))
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P) :
    ∃ F : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ,
      StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree F ∧ ∀ n : ℕ,
        Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
          DerivedCategory.Q.obj
            (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
              (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((constantSheaf (Scheme.ProEt.topology X)
                (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj F))) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let J := Scheme.ProEt.topology X
  let Φ := Scheme.ProEt.clopenPoint hX x
  let N := ((Stacks.ModuleSheaf.moduleSheafFiber Λ Φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hN : ∀ n : ℕ, CochainComplex.KFlat.{max (u + 1) w, max (u + 1) w}
      (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) := fun n =>
    kFlat_baseChange _ _
      ((CochainComplex.kFlat_iff_kFlatBifunctor N).2 (Stacks.ModuleSheaf.kFlat_sheafFiber Φ hP))
  have hE : ∀ n : ℕ, ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
      Nonempty ((derivedReduction.{u, w} X Λ (I ^ (n + 1))).obj K ≅
        (constantSheaf J (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))).mapDerivedCategory.obj E) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) := fun n => by
    obtain ⟨E, ⟨e₀⟩⟩ := hconstant (n + 1)
    exact ⟨E, ⟨e₀⟩, Stacks.ModuleSheaf.nonempty_iso_extendScalars_sheafFiber Φ _ hP E
      ((Stacks.ModuleSheaf.derivedExtendScalars J _).mapIso eP ≪≫ e₀)⟩
  have hN₀ : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)) := by
    obtain ⟨E, ⟨e₀⟩, ⟨e₁⟩⟩ := hE 0
    obtain ⟨a, b, hab⟩ := exists_hasTorAmplitude_derivedReduction_pow X Λ I hK
    have hb := ((hab (0 + 1)).isGE_isLE).2
    exact (isPseudoCoherent_of_hasConstructibleCohomology_constantSheaf E b
      (by have := hb; exact DerivedCategory.TStructure.t.isLE_of_iso e₀ b)
      (fun i => ObjectProperty.prop_of_iso _ ((DerivedCategory.homologyFunctor _ i).mapIso e₀)
        (hasConstructibleCohomology_derivedReduction_pow X Λ I hK (0 + 1) i))).ofIso e₁
  obtain ⟨F, hF, hFN⟩ :=
    StacksDraft.DerivedInverseLimit.exists_isBoundedAboveFiniteFree_adicCompletion_iso I N hN hN₀
  refine ⟨F, hF, fun n => ?_⟩
  obtain ⟨E, ⟨e₀⟩, ⟨e₁⟩⟩ := hE n
  obtain ⟨e₂⟩ := hFN n
  let f := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  let cS := constantSheaf J (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))
  have : (ModuleCat.extendScalars.{max (u + 1) w, max (u + 1) w, max (u + 1) w} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max (u + 1) w} f).left_adjoint_additive
  exact ⟨(Stacks.ModuleSheaf.derivedExtendScalarsObjIso J _ hP).symm ≪≫
    (Stacks.ModuleSheaf.derivedExtendScalars J _).mapIso eP ≪≫ e₀ ≪≫
    cS.mapDerivedCategory.mapIso (e₁ ≪≫ e₂.symm) ≪≫ cS.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (Stacks.ModuleSheaf.extendScalarsConstantSheafIso J f).symm (ComplexShape.up ℤ)).app F ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app F).symm)⟩

/-- **Stacks 09C5.** Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring,
`I ⊆ Λ` an ideal and `K` an object of `D_cons(X, Λ)` such that every reduction
`K ⊗_Λ^L Λ/Iⁿ` is isomorphic, in `D(X_proét, Λ/Iⁿ)`, to a complex of constant sheaves of
`Λ/Iⁿ`-modules. Then the inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` of `Λ`-modules satisfies the
Mittag-Leffler condition.

The conclusion is the Mittag-Leffler condition of Stacks Tag 02N0 for the system
`derivedReductionSectionsSystem X Λ I K'`, `K'` being `K` read in the derived category of sheaves
of `Λ`-modules; its terms are the sections modules `H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` and its transition maps
are induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`. Constructibility is
`AlgebraicGeometry.ProEtale.IsConstructibleViaDerivedReduction`, and the reductions are
`AlgebraicGeometry.ProEtale.derivedReduction`.

The proof: for a K-flat representative `P` of `K`,
`AlgebraicGeometry.ProEtale.exists_isBoundedAboveFiniteFree_reduction_iso` gives a bounded
above complex `F` of finite free `Λ^∧`-modules whose constant complex has, levelwise, the
reductions of `P`; the sections system of the reductions of `\underline{F}` is
`j ↦ Γ(X, \underline{H⁰(F/IʲF)})`, which is Mittag-Leffler by the Artin–Rees lemma
(`AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_constantComplexReductionSections`), and
`Stacks.ModuleSheaf.isMittagLefflerCategorical_reductionSections_of_adicModel` transports the
condition. Over the empty scheme every term of the system vanishes. -/
@[stacks 09C5 "the Mittag-Leffler condition for the inverse system n ↦ H^0(X, K ⊗_Λ^L Λ/I^n) \
of sections modules, with its canonical transition maps; the hypothesis that each reduction is \
a complex of constant sheaves is read, as in the source's proof, as K ⊗_Λ^L Λ/I^n ≅ \
\\underline{E_n} for an object E_n of D(Λ/I^n)"]
theorem
    isMittagLefflerCategorical_derivedReductionSectionsSystem_of_isConstructibleViaDerivedReduction
    [IsAffine X] (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hconstant : ∀ n : ℕ, ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n)),
      Nonempty ((derivedReduction.{u, w} X Λ (I ^ n)).obj K ≅
        (constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n))).mapDerivedCategory.obj E)) :
    IsMittagLefflerCategorical (derivedReductionSectionsSystem X Λ I
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)) := by
  rcases isEmpty_or_nonempty X with hXe | hXne
  · exact isMittagLefflerCategorical_of_forall_exists_range_eq _ fun i =>
      ⟨i, le_rfl, fun k _ => by
        have : Subsingleton ((derivedReductionSectionsSystem X Λ I
            ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)).obj (op i)) :=
          subsingleton_sheafSections_terminal_of_isEmpty _
        exact Subsingleton.elim _ _⟩
  let J := Scheme.ProEt.topology X
  let K' := (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K
  obtain ⟨P, p, hP, hp⟩ :=
    Stacks.ModuleSheaf.exists_kFlat_quasiIso (DerivedCategory.Q.objPreimage K')
  let eP : DerivedCategory.Q.obj P ≅ K' :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K'
  obtain ⟨F, hF, hψ⟩ := exists_isBoundedAboveFiniteFree_reduction_iso X Λ I hX K hK hconstant eP hP
  let A := AdicCompletion I Λ
  let cA := constantSheaf J (ModuleCat.{max (u + 1) w} A)
  let W := (cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  obtain ⟨b, hb⟩ := hF.upperBound
  have : CochainComplex.IsStrictlyLE W b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun k hk => cA.map_isZero (F.isZero_of_isStrictlyLE b k hk)
  have hW : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (Sheaf J (ModuleCat.{max (u + 1) w} A))) W :=
    Stacks.ModuleSheaf.kFlat_of_isStrictlyLE W b fun n => by
      have := (hF.finiteFree n).2
      exact Stacks.ModuleSheaf.sheafifiedFree_constantSheaf_obj J (F.X n)
  exact Stacks.ModuleSheaf.isMittagLefflerCategorical_reductionSections_of_adicModel I
    (IsNoetherian.noetherian I) (⊤_ X.ProEt) eP
    (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hP)
    (fun n => CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _
      (Stacks.ModuleSheaf.kFlat_extendScalars J _ hP))
    (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hW)
    (fun n => CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _
      (Stacks.ModuleSheaf.kFlat_extendScalars J _ hW))
    (fun n => (hψ n).some)
    (isMittagLefflerCategorical_constantComplexReductionSections hX A (I.map (algebraMap Λ A)) F
      (fun n => (hF.finiteFree n).1) (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hW)
      (algebraMap Λ A))

end Reduction

end AlgebraicGeometry.ProEtale

end
