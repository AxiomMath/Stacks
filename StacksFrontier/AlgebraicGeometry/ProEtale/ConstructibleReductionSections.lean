module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedReductionComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocallyConstantAdicModel
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ConstantReductionsMittagLeffler
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.Homology.PseudoCoherent.Coherent
import StacksCore.Tactic.StacksAttribute

/-!
# Mittag-Leffler for the sections of the reductions of a constructible complex

Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K`
an object of `D_cons(X, Λ)` (Stacks 09C1). Stacks 09C5 says that if every reduction
`K ⊗_Λ^L Λ/Iⁿ` is isomorphic in `D(X_proét, Λ/Iⁿ)` to a complex of constant sheaves of
`Λ/Iⁿ`-modules, then the inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` satisfies the Mittag-Leffler
condition. This file proves it.

The proof follows the source's, with two steps arranged differently:

* the reduction `E_1` is pseudo-coherent: its cohomology modules are finite because their
  constant sheaves are constructible
  (`AlgebraicGeometry.ProEtale.finite_of_isConstructibleModuleSheaf'_constantSheaf`), and it is
  bounded above because `K ⊗_Λ^L Λ/I` locally has finite Tor dimension
  (`AlgebraicGeometry.ProEtale.exists_isZero_homology_of_locallyHasFiniteTorDimension`); in the
  source this is where perfectness of `E_1` (Stacks 0658) enters;
* the compatible complex `M^•` of finite projective `Λ^∧`-modules of Stacks 09AW is replaced by
  a bounded above complex `F` of finite free `Λ^∧`-modules with `F/IⁿF ≅ E_n` (Stacks 0CQF), the
  `E_n` being identified through the fibre of a K-flat representative of `K` at a point of
  `X_proét`; and the Tor spectral sequence with Stacks 0911 is replaced by the Artin–Rees lemma
  for the cohomology of the adic reductions of `F`. The comparison of the triples of indices
  `n > m > k` is the source's. See
  `StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ConstantReductionsMittagLeffler`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_isZero_homology_of_locallyHasFiniteTorDimension`: a locally
  finite Tor dimensional constant complex is bounded above.
* `AlgebraicGeometry.ProEtale.isPseudoCoherent_of_isConstructibleDerivedSheaf`: the reduction
  modulo `I` of a constructible complex with constant reduction is pseudo-coherent.
* `AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_derivedReductionSectionsSystem`:
  **Stacks 09C5**.

## Implementation notes

`D(X_proét, Λ)` is `AlgebraicGeometry.ProEtale.DerivedSheaves`, the derived category of sheaves of
modules over the constant coefficient ring sheaf, in which `D_cons(X, Λ)` and the derived base
changes `- ⊗_Λ^L Λ/Iⁿ` (Stacks 0DIZ) are formulated. The derived tensor product of sheaves of
`Λ`-modules is constructed on the equivalent derived category of sheaves of `Λ`-modules, so the
inverse system of the conclusion is read there, through
`AlgebraicGeometry.ProEtale.derivedCoefficientModuleSheafEquivalence`; its `n`-th term is the
degree-zero cohomology of `K ⊗_Λ^L \underline{Λ/Iⁿ}` over `X`, as a `Λ`-module, and its
transition maps are induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`. Every derived base change is
computed by K-flat representatives
(`AlgebraicGeometry.ProEtale.nonempty_derivedCoefficientModuleSheafEquivalence_baseChange_iso`),
which is what connects the hypothesis to that system.

The coefficient ring lies in the universe `max (u + 1) w` of the module sections, which contains
the universe of the objects of `X_proét`; every ring is isomorphic to one in such a universe. This
is the universe in which the tensor product of sheaves of modules, and with it the derived
tensor product, is constructed.

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
* [Stacks Project, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
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

section Bounded

variable {X : Scheme.{u}} (R : Type (max (u + 1) w)) [CommRing R]

attribute [local instance] Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat

/-- The homology in degree `i` of an object `L` of `D(X_proét, R)` whose image in the derived
category of sheaves of `R`-modules is a constant complex, read as sheaves of `R`-modules, is the
constant sheaf of the homology of that complex. -/
private def homologyConstantIso (L : DerivedSheaves.{u, max (u + 1) w, w} X R)
    (E : DerivedCategory (ModuleCat.{max (u + 1) w} R))
    (e : (derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X R).functor.obj L ≅
      (constantDerivedFunctor X R).obj E) (i : ℤ) :
    (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X R).obj
        ((DerivedCategory.homologyFunctor _ i).obj L) ≅
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)).obj
        ((DerivedCategory.homologyFunctor _ i).obj E) :=
  let c' := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)
  have : PreservesFiniteColimits c' := Stacks.ModuleSheaf.preservesFiniteColimits_constantSheaf _ R
  have : PreservesFiniteLimits c' := Stacks.ModuleSheaf.preservesFiniteLimits_constantSheaf _ R
  have : c'.Additive := Functor.additive_of_preserves_binary_products _
  ((toCoefficientModuleSheaf.{u, max (u + 1) w, w} X R).mapDerivedCategoryHomologyIso i).app L
      |>.symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫ (c'.mapDerivedCategoryHomologyIso i).app E

/-- **A locally finite Tor dimensional constant complex is bounded above.** On a nonempty scheme
`X`, if an object `L` of `D(X_proét, R)` locally has finite Tor dimension and is, read as an
object of the derived category of sheaves of `R`-modules, the constant complex of an object `E`
of `D(R)`, then the cohomology of `E` vanishes in all large degrees: on a nonempty member `W`
of a covering on which `L` has Tor amplitude in `[a, b]`, the cohomology sheaves of `L` above
`b` vanish, and the sections over `W` of the constant sheaf of a module contain that module. -/
theorem exists_isZero_homology_of_locallyHasFiniteTorDimension [Nonempty X]
    (D : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, w} X R).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w, max (u + 1) w + 1}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, w} X R).over U))
    (L : DerivedSheaves.{u, max (u + 1) w, w} X R)
    (hL : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, max (u + 1) w, w} X R) D L)
    (E : DerivedCategory (ModuleCat.{max (u + 1) w} R))
    (e : (derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X R).functor.obj L ≅
      (constantDerivedFunctor X R).obj E) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) w} R) i).obj E) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let J := Scheme.ProEt.topology X
  obtain ⟨S, hS, hSV⟩ := hL (Scheme.ProEt.mk (𝟙 X))
  obtain ⟨V, g, hg, ⟨y, -⟩⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hS
    (show (Scheme.ProEt.mk (𝟙 X)).left from x)
  obtain ⟨W, h, f, hf, -⟩ := hg
  obtain ⟨a, b, hab⟩ := hSV f hf
  have hW : (⊥ : Sieve W) ∉ J W := Scheme.ProEt.bot_notMem_topology_of_nonempty (h.left y)
  refine ⟨b, fun i hi => ?_⟩
  let O := Stacks.SheafOfModules.Tensor.ringSheaf
    (constantCoefficientRingedSite.{u, max (u + 1) w, w} X R).O
  let F := SheafOfModules.overFunctor.{max (u + 1) w} O W
  have : PreservesFiniteLimits F :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
  have : PreservesFiniteColimits F :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have hle : (F.mapDerivedCategory.obj L).IsLE b :=
    Stacks.SheafOfModules.DerivedTensorProduct.isLE_of_hasTorAmplitude (D W) _ hab
  have h1 := DerivedCategory.isZero_of_isLE (F.mapDerivedCategory.obj L) b i hi
  let M := (DerivedCategory.homologyFunctor _ i).obj L
  have h2 : IsZero (F.obj M) := h1.of_iso ((F.mapDerivedCategoryHomologyIso i).app L).symm
  have h3 : Subsingleton ((SheafOfModules.evaluation _ (op (Over.mk (𝟙 W)))).obj (F.obj M)) :=
    ModuleCat.isZero_iff_subsingleton.1
      ((SheafOfModules.evaluation _ (op (Over.mk (𝟙 W)))).map_isZero h2)
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) w} R) i).obj E
  let b' := toCoefficientModuleSheaf.{u, max (u + 1) w, w} X R
  let c' := constantSheaf J (ModuleCat.{max (u + 1) w} R)
  let φ := ((sheafSections J (ModuleCat.{max (u + 1) w} R)).obj (op W)).mapIso
    (homologyConstantIso R L E e i)
  have h4 : Subsingleton (((sheafSections J (ModuleCat.{max (u + 1) w} R)).obj (op W)).obj
      (b'.obj M)) := h3
  have h5 : Subsingleton (((sheafSections J (ModuleCat.{max (u + 1) w} R)).obj (op W)).obj
      (c'.obj N)) := φ.toLinearEquiv.toEquiv.symm.subsingleton
  have h5' : Subsingleton ((sheafify J ((Functor.const X.ProEtᵒᵖ).obj N)).obj (op W)) := h5
  have h6 : Subsingleton N :=
    (Stacks.ConstantSheaf.injective_toSheafify_const_app J N W hW).subsingleton
  exact ModuleCat.isZero_iff_subsingleton.2 h6

end Bounded

section Constant

variable (X : Scheme.{u}) (R : Type (max (u + 1) w)) [CommRing R]

/-- The constant sheaf of a coefficient module, read over the constant coefficient ring sheaf, is
additive in the module. -/
instance constantSheafOverCoefficients_additive :
    (constantSheafOverCoefficients.{u, max (u + 1) w, w} X R).Additive := by
  unfold constantSheafOverCoefficients
  infer_instance

/-- A complex of constant sheaves of `R`-modules, built over the constant coefficient ring sheaf,
read as a complex of sheaves of `R`-modules in the derived category, is the constant complex. -/
def derivedCoefficientModuleSheafEquivalenceConstantIso
    (E : CochainComplex (ModuleCat.{max (u + 1) w} R) ℤ) :
    (derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X R).functor.obj
        (DerivedCategory.Q.obj (((constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{max (u + 1) w} R) ⋙
            moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w}
              X R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E)) ≅
      (constantDerivedFunctor X R).obj (DerivedCategory.Q.obj E) :=
  let c := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)
  have : PreservesFiniteColimits c := Stacks.ModuleSheaf.preservesFiniteColimits_constantSheaf _ R
  have : PreservesFiniteLimits c := Stacks.ModuleSheaf.preservesFiniteLimits_constantSheaf _ R
  have : c.Additive := Functor.additive_of_preserves_binary_products _
  (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X R).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app _ ≪≫
        (NatIso.mapHomologicalComplex
          (Functor.isoWhiskerLeft c (constantCoefficientsUnitIso.{u, max (u + 1) w, w} X R).symm ≪≫
            c.rightUnitor) (ComplexShape.up ℤ)).app E) ≪≫
    (c.mapDerivedCategoryFactors.app E).symm

end Constant

section Statement

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] [IsNoetherianRing Λ]
  (I : Ideal Λ)

/-- **The reduction modulo `I` of a constructible complex with constant reduction is
pseudo-coherent.** On a nonempty scheme `X`, let `K` be an object of `D_cons(X, Λ)` whose
reduction `K ⊗_Λ^L Λ/I` is the constant complex of an object `E` of `D(Λ/I)`. Then `E` is
pseudo-coherent: its cohomology modules are finite because their constant sheaves are
constructible, and it is bounded above because `K ⊗_Λ^L Λ/I` locally has finite Tor dimension;
Stacks 066E concludes. -/
theorem isPseudoCoherent_of_isConstructibleDerivedSheaf [Nonempty X]
    (T : DerivedReduction.{u, max (u + 1) w, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w,
          max (u + 1) w + 1}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ I)).over U))
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleDerivedSheaf.{u, max (u + 1) w, w} X Λ I T D K)
    (E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I)))
    (e : (Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
        (Ideal.Quotient.mk I)).obj
          ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj K) ≅
      (constantDerivedFunctor X (Λ ⧸ I)).obj E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent E := by
  obtain ⟨eT⟩ := nonempty_derivedCoefficientModuleSheafEquivalence_baseChange_iso X Λ I T K
  let c := eT ≪≫ e
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_locallyHasFiniteTorDimension (Λ ⧸ I) D _
    hK.2.2 E c
  have hfin : ∀ i : ℤ, Module.Finite (Λ ⧸ I)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) w} (Λ ⧸ I)) i).obj E) := by
    intro i
    let ι := homologyConstantIso (Λ ⧸ I) (T.baseChange.obj K) E c i
    exact finite_of_isConstructibleModuleSheaf'_constantSheaf.{u, max (u + 1) w, w} (Λ ⧸ I) _
      (ObjectProperty.prop_of_iso _ ι (hK.2.1 i))
  exact ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology E 0
    (Λ ⧸ I)).2.1).2 ⟨⟨b, hb⟩, fun i => hfin i⟩

/-- **Mittag-Leffler for the sections of the reductions of a constructible complex.** Let `X` be
a weakly contractible affine scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K` an object of
`D_cons(X, Λ)` such that every derived extension of scalars `K ⊗_Λ^L Λ/Iⁿ⁺¹` of `K`, read as an
object of the derived category of sheaves of `Λ`-modules, is the constant complex of an object
of `D(Λ/Iⁿ⁺¹)`. Then the inverse system `n ↦ H⁰(X, K ⊗_Λ^L \underline{Λ/Iⁿ})` is
Mittag-Leffler. -/
theorem isMittagLefflerCategorical_derivedReductionSectionsSystem_of_derivedExtendScalars
    [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (T : DerivedReduction.{u, max (u + 1) w, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w,
          max (u + 1) w + 1}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ I)).over U))
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleDerivedSheaf.{u, max (u + 1) w, w} X Λ I T D K)
    (hconstant : ∀ n : ℕ,
      ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
        Nonempty ((Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
          (Ideal.Quotient.mk (I ^ (n + 1)))).obj
            ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj K) ≅
          (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E)) :
    IsMittagLefflerCategorical (derivedReductionSectionsSystem X Λ I
      ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj K)) := by
  let J := Scheme.ProEt.topology X
  let K' := (derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj K
  obtain ⟨P, p, hP, hp⟩ :=
    Stacks.ModuleSheaf.exists_kFlat_quasiIso (DerivedCategory.Q.objPreimage K')
  let eP : DerivedCategory.Q.obj P ≅ K' :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K'
  have hconst : ∀ n : ℕ, ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
      Nonempty ((Stacks.ModuleSheaf.derivedExtendScalars J
          (Ideal.Quotient.mk (I ^ (n + 1)))).obj K' ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E) ∧
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars J
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E) := fun n => by
    obtain ⟨E, ⟨e⟩⟩ := hconstant n
    exact ⟨E, ⟨e⟩, ⟨(Stacks.ModuleSheaf.derivedExtendScalarsObjIso J _ hP).symm ≪≫
      (Stacks.ModuleSheaf.derivedExtendScalars J _).mapIso eP ≪≫ e⟩⟩
  have key : ∀ 𝔟 : Ideal Λ, 𝔟 = I → Nonempty X →
      ∀ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ 𝔟)),
      Nonempty ((Stacks.ModuleSheaf.derivedExtendScalars J (Ideal.Quotient.mk 𝔟)).obj K' ≅
        (constantDerivedFunctor X (Λ ⧸ 𝔟)).obj E) →
      StacksDraft.PseudoCoherence.IsPseudoCoherent E := by
    rintro 𝔟 rfl hXne E ⟨e⟩
    exact isPseudoCoherent_of_isConstructibleDerivedSheaf 𝔟 T D K hK E e
  refine isMittagLefflerCategorical_reductionSections_of_constant hX I eP hP
    (fun n => (hconst n).imp fun _ h => h.2)
    fun hXne => ?_
  obtain ⟨E, ⟨e⟩, h⟩ := hconst 0
  exact ⟨E, key (I ^ (0 + 1)) (pow_one I) hXne E ⟨e⟩, h⟩

omit [IsNoetherianRing Λ] in
/-- The hypothesis of Stacks 09C5, that the reductions `K ⊗_Λ^L Λ/Iⁿ` are complexes of constant
sheaves, read in the derived category of sheaves of `Λ/Iⁿ`-modules with the derived extension of
scalars computed by K-flat representatives. -/
theorem exists_derivedExtendScalars_iso_constantDerivedFunctor
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (Tn : ∀ n : ℕ, DerivedReduction.{u, max (u + 1) w, w} X Λ (I ^ n))
    (hconstant : ∀ n : ℕ, 1 ≤ n →
      ∃ E : CochainComplex (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n)) ℤ,
        Nonempty ((Tn n).baseChange.obj K ≅ DerivedCategory.Q.obj
          (((constantSheafOverCoefficients.{u, max (u + 1) w, w}
            X (Λ ⧸ I ^ n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E))) (n : ℕ) :
    ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
      Nonempty ((Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
        (Ideal.Quotient.mk (I ^ (n + 1)))).obj
          ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj K) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E) := by
  obtain ⟨E, ⟨e⟩⟩ := hconstant (n + 1) (by omega)
  obtain ⟨eT⟩ := nonempty_derivedCoefficientModuleSheafEquivalence_baseChange_iso X Λ
    (I ^ (n + 1)) (Tn (n + 1)) K
  exact ⟨DerivedCategory.Q.obj E, ⟨eT.symm ≪≫
    (derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X
      (Λ ⧸ I ^ (n + 1))).functor.mapIso e ≪≫
    derivedCoefficientModuleSheafEquivalenceConstantIso X (Λ ⧸ I ^ (n + 1)) E⟩⟩

/-- **Stacks 09C5.** Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring,
`I ⊆ Λ` an ideal and `K` an object of `D_cons(X, Λ)` such that for every `n ≥ 1` the reduction
`K ⊗_Λ^L \underline{Λ/Iⁿ}` is isomorphic in `D(X_proét, Λ/Iⁿ)` to a complex of constant sheaves
of `Λ/Iⁿ`-modules. Then the inverse system `n ↦ H⁰(X, K ⊗_Λ^L Λ/Iⁿ)` of `Λ`-modules satisfies the
Mittag-Leffler condition.

The reductions in the hypothesis are taken with derived base changes `Tn n` along
`Λ → Λ/Iⁿ` (any two of which are canonically isomorphic), and a complex of constant sheaves is
the constant sheaf functor applied to a complex `E` of `Λ/Iⁿ`-modules. The inverse system of the
conclusion is `AlgebraicGeometry.ProEtale.derivedReductionSectionsSystem`: degree-zero cohomology
and sections over `X` of the derived tensor products of `K` with the constant sheaves
`\underline{Λ/Iⁿ}`, whose transition maps are induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`; here `K`
is read in the derived category of sheaves of `Λ`-modules, where the derived tensor product is
constructed, through the constant coefficients equivalence.

"A complex of constant sheaves" is read, with the first sentence of the source's proof, as the
constant complex of a complex of `Λ/Iⁿ`-modules; with constant terms and arbitrary differentials
(`AlgebraicGeometry.ProEtale.IsConstantSheafComplexModel`) the statement fails, see
`StacksFrontier/AlgebraicGeometry/ProEtale/LocallyConstantAdicModel.lean`. -/
@[stacks 09C5 "the Mittag-Leffler condition for the inverse system n ↦ H^0(X, K ⊗_Λ^L Λ/I^n) \
with its canonical transition maps induced by Λ/I^(n+1) → Λ/I^n; a complex of constant sheaves \
is read, as in the first sentence of the source's proof, as the constant complex of a complex \
of Λ/I^n-modules"]
theorem isMittagLefflerCategorical_derivedReductionSectionsSystem [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (T : DerivedReduction.{u, max (u + 1) w, w} X Λ I)
    (D : ∀ U : (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ I)).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w,
          max (u + 1) w + 1}
        ((constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ I)).over U))
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleDerivedSheaf.{u, max (u + 1) w, w} X Λ I T D K)
    (Tn : ∀ n : ℕ, DerivedReduction.{u, max (u + 1) w, w} X Λ (I ^ n))
    (hconstant : ∀ n : ℕ, 1 ≤ n →
      ∃ E : CochainComplex (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ n)) ℤ,
        Nonempty ((Tn n).baseChange.obj K ≅ DerivedCategory.Q.obj
          (((constantSheafOverCoefficients.{u, max (u + 1) w, w}
            X (Λ ⧸ I ^ n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E))) :
    IsMittagLefflerCategorical (derivedReductionSectionsSystem X Λ I
      ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj K)) := by
  exact isMittagLefflerCategorical_derivedReductionSectionsSystem_of_derivedExtendScalars.{u, w}
    I hX T D K hK (exists_derivedExtendScalars_iso_constantDerivedFunctor.{u, w} I K Tn hconstant)

end Statement

end AlgebraicGeometry.ProEtale

end
