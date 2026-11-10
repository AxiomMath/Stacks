module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.QuotientTilde
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionChartUnit
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections

/-!
# The ideal-power quotient of the structure sheaf on the complement of a closed subset

Let `A` be a commutative ring, let `𝔞 ⊆ A` be an ideal, let `f ∈ A` and let
`U = Spec(A) ∖ V(𝔞)`. The affine identification
`Stacks.Algebraization.exists_specUnitQuotient_iso` of `𝒪_{Spec A} / (f)ⁿ 𝒪_{Spec A}` with the
sheaf associated to `A / (f)ⁿ` is transported here along the open immersion `ι : U ⟶ Spec A`:

`𝒪_U / ((f)𝒪_U)ⁿ 𝒪_U ≅ (A / (f)ⁿ)~|_U`,

compatibly with the quotient projections out of the structure sheaf and with the maps that lower
the exponent.

## Main definitions

* `Stacks.Algebraization.complementTildeModule` — the restriction to `U` of the sheaf associated
  to an `A`-module, which is `Stacks.LocalCohomology.complementTilde`.
* `Stacks.Algebraization.complementUnitModuleIso` — the restriction of `𝒪_{Spec A}` to `U` is
  `𝒪_U`, which is `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.
* `Stacks.Algebraization.specPrincipalQuotientπ` and
  `Stacks.Algebraization.specPrincipalQuotientDrop` — the quotient projection
  `𝒪_{Spec A} ⟶ (A / (f)ⁿ)~` and the exponent-lowering map `(A / (f)ᵐ)~ ⟶ (A / (f)ⁿ)~`.

## Main results

* `Stacks.Algebraization.exists_complementUnitQuotient_iso` — **`𝒪_U / ((f)𝒪_U)ⁿ 𝒪_U` is the
  restriction to `U` of the sheaf associated to `A / (f)ⁿ`**, compatibly with the quotient
  projections.
* `Stacks.Algebraization.idealPowerQuotientDrop_comp_complementUnitQuotient_iso` — **the same
  family of isomorphisms is compatible with lowering the exponent.**
* `Stacks.Algebraization.pullbackUnitIso_inv_comp_restrictFunctorIsoPullback_inv_app` — the
  comparison of the inverse image with the restriction, at the structure sheaf.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (a : Ideal A) (f : A) (n : ℕ)

/-- The restriction to `U = Spec(A) ∖ V(𝔞)` of the sheaf associated to an `A`-module, as an
object of `U.Modules` and with the associated sheaf written as `AlgebraicGeometry.tilde`. It is
`Stacks.LocalCohomology.complementTilde` (`Stacks.Algebraization.complementTildeModule_eq`). -/
public abbrev complementTildeModule (M : ModuleCat.{u} A) :
    (complementZeroLocus A a : Scheme).Modules :=
  (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj (tilde M)

/-- The restriction to `U` of the sheaf associated to `M` is `M̃|_U`. -/
public theorem complementTildeModule_eq (M : ModuleCat.{u} A) :
    complementTildeModule A a M = complementTilde A a M :=
  rfl

/-- The restriction of `𝒪_{Spec A}` to `U = Spec(A) ∖ V(𝔞)` is `𝒪_U`. This is
`Stacks.LocalCohomology.complementTildeRingIsoUnit`, with both of its sides written in
`U.Modules`. -/
public abbrev complementUnitModuleIso :
    (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).obj
        (Spec (CommRingCat.of A)).unitModule ≅
      (complementZeroLocus A a : Scheme).unitModule :=
  complementTildeRingIsoUnit A a

/-- The quotient projection `𝒪_{Spec A} ⟶ (A / (f)ⁿ)~`, with its source written as the structure
sheaf of `Spec A` and its target as `AlgebraicGeometry.tilde`. -/
public abbrev specPrincipalQuotientπ :
    (Spec (CommRingCat.of A)).unitModule ⟶
      tilde (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ n : Ideal A))) :=
  (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (Submodule.mkQ (Ideal.span {f} ^ n : Ideal A)))

/-- **At the structure sheaf the comparison of the inverse image with the restriction along an
open immersion is the identification `ι^* 𝒪_{Spec A} ≅ 𝒪_U`.** -/
public theorem pullbackUnitIso_inv_comp_restrictFunctorIsoPullback_inv_app :
    (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback (complementZeroLocus A a).ι).inv.app
          (Spec (CommRingCat.of A)).unitModule =
      (complementUnitModuleIso A a).inv := by
  have h1 : (Scheme.Modules.restrictFunctorIsoPullback (complementZeroLocus A a).ι).inv.app
        (Spec (CommRingCat.of A)).unitModule ≫ (complementUnitModuleIso A a).hom =
      (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).hom :=
    restrictFunctorIsoPullback_inv_app_unit_comp_restrictUnitIso' (complementZeroLocus A a).ι
  rw [(Iso.eq_comp_inv _).2 h1, Iso.inv_hom_id_assoc]

/-- **The quotient of the structure sheaf of `U = Spec(A) ∖ V(𝔞)` by the `n`-th power of the
ideal sheaf `f 𝒪_U` is the restriction to `U` of the sheaf associated to `A / (f)ⁿ`**, compatibly
with the quotient projections out of the structure sheaf. -/
public theorem exists_complementUnitQuotient_iso :
    ∃ e : idealPowerQuotient (complementPrincipalIdealSheaf A a f) n
            (complementZeroLocus A a : Scheme).unitModule ≅
          complementTildeModule A a (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ n : Ideal A))),
      unitIdealPowerQuotientπ (complementPrincipalIdealSheaf A a f) n ≫ e.hom =
        (complementUnitModuleIso A a).inv ≫
          (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
            (specPrincipalQuotientπ A f n) := by
  rw [complementPrincipalIdealSheaf_eq_comap]
  obtain ⟨e₀, he₀⟩ := exists_specUnitQuotient_iso A (Ideal.span {f}) n
  obtain ⟨e₁, he₁⟩ := Stacks.Coherent.exists_functor_idealPowerQuotient_iso
    (Scheme.Modules.pullback (complementZeroLocus A a).ι) (specIdealSheaf A (Ideal.span {f}))
    ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι) n
    (Spec (CommRingCat.of A)).unitModule
    (fun {N} φ => pullback_idealPowerMultiple_comp_eq_zero_iff (complementZeroLocus A a).ι
      (specIdealSheaf A (Ideal.span {f})) n (Spec (CommRingCat.of A)).unitModule φ)
  have hiso : IsIso (idealPowerQuotientMap
      ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι)
      ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι) n n le_rfl
      (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).inv) :=
    isIso_idealPowerQuotientMap _ n
      (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).symm
  refine ⟨asIso (idealPowerQuotientMap
        ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι)
        ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι) n n le_rfl
        (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).inv) ≪≫ e₁.symm ≪≫
      (Scheme.Modules.pullback (complementZeroLocus A a).ι).mapIso e₀ ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (complementZeroLocus A a).ι).app
        (tilde (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ n : Ideal A))))).symm, ?_⟩
  have hπ := idealPowerQuotientMap_π
    ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι)
    ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι) n n le_rfl
    (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).inv
  have he₁' : cokernel.π (C := (complementZeroLocus A a : Scheme).Modules)
          (idealPowerMultiple ((specIdealSheaf A (Ideal.span {f})).comap
            (complementZeroLocus A a).ι) n
            ((Scheme.Modules.pullback (complementZeroLocus A a).ι).obj
              (Spec (CommRingCat.of A)).unitModule)).ι ≫ e₁.inv =
      (Scheme.Modules.pullback (complementZeroLocus A a).ι).map
        (cokernel.π (C := (Spec (CommRingCat.of A)).Modules)
          (idealPowerMultiple (specIdealSheaf A (Ideal.span {f})) n
            (Spec (CommRingCat.of A)).unitModule).ι) :=
    (Iso.comp_inv_eq e₁).mpr he₁.symm
  have he₀' : cokernel.π (C := (Spec (CommRingCat.of A)).Modules)
          (idealPowerMultiple (specIdealSheaf A (Ideal.span {f})) n
            (Spec (CommRingCat.of A)).unitModule).ι ≫ e₀.hom =
      specPrincipalQuotientπ A f n := he₀
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback
    (complementZeroLocus A a).ι).inv.naturality (specPrincipalQuotientπ A f n)
  change unitIdealPowerQuotientπ ((specIdealSheaf A (Ideal.span {f})).comap
        (complementZeroLocus A a).ι) n ≫
      (idealPowerQuotientMap
          ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι)
          ((specIdealSheaf A (Ideal.span {f})).comap (complementZeroLocus A a).ι) n n le_rfl
          (Scheme.Modules.pullbackUnitIso (complementZeroLocus A a).ι).inv ≫
        e₁.inv ≫
          (Scheme.Modules.pullback (complementZeroLocus A a).ι).map e₀.hom ≫
            (Scheme.Modules.restrictFunctorIsoPullback (complementZeroLocus A a).ι).inv.app
              (tilde (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ n : Ideal A))))) = _
  rw [reassoc_of% hπ, reassoc_of% he₁', ← Category.assoc
      ((Scheme.Modules.pullback (complementZeroLocus A a).ι).map
        (cokernel.π (C := (Spec (CommRingCat.of A)).Modules)
          (idealPowerMultiple (specIdealSheaf A (Ideal.span {f})) n
            (Spec (CommRingCat.of A)).unitModule).ι)),
    ← Functor.map_comp, he₀', hnat, ← Category.assoc,
    pullbackUnitIso_inv_comp_restrictFunctorIsoPullback_inv_app]

/-- The exponent-lowering map `(A / (f)ᵐ)~ ⟶ (A / (f)ⁿ)~` for `n ≤ m`, induced by the projection
`A / (f)ᵐ ⟶ A / (f)ⁿ`. -/
public abbrev specPrincipalQuotientDrop {m n : ℕ} (h : n ≤ m) :
    tilde (R := CommRingCat.of A) (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ m : Ideal A))) ⟶
      tilde (R := CommRingCat.of A) (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ n : Ideal A))) :=
  (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom
    (Submodule.mapQ (Ideal.span {f} ^ m : Ideal A) (Ideal.span {f} ^ n : Ideal A)
      LinearMap.id (by
        rw [Submodule.comap_id]
        exact Ideal.pow_le_pow_right h)))

/-- Lowering the exponent takes the one quotient projection out of `𝒪_{Spec A}` to the other. -/
public theorem specPrincipalQuotientπ_comp_drop {m n : ℕ} (h : n ≤ m) :
    specPrincipalQuotientπ A f m ≫ specPrincipalQuotientDrop A f h =
      specPrincipalQuotientπ A f n :=
  ((tilde.functor (CommRingCat.of A)).map_comp _ _).symm.trans
    (congrArg (tilde.functor (CommRingCat.of A)).map
      (ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)))

/-- **The identifications of `Stacks.Algebraization.exists_complementUnitQuotient_iso` are
compatible with lowering the exponent**: for `n ≤ m` the map
`𝒪_U / ((f)𝒪_U)ᵐ 𝒪_U ⟶ 𝒪_U / ((f)𝒪_U)ⁿ 𝒪_U` corresponds to the restriction to `U` of the sheaf
map induced by `A / (f)ᵐ ⟶ A / (f)ⁿ`. -/
public theorem idealPowerQuotientDrop_comp_complementUnitQuotient_iso {m n : ℕ} (h : n ≤ m)
    (em : idealPowerQuotient (complementPrincipalIdealSheaf A a f) m
          (complementZeroLocus A a : Scheme).unitModule ≅
        complementTildeModule A a (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ m : Ideal A))))
    (en : idealPowerQuotient (complementPrincipalIdealSheaf A a f) n
          (complementZeroLocus A a : Scheme).unitModule ≅
        complementTildeModule A a (ModuleCat.of A (A ⧸ (Ideal.span {f} ^ n : Ideal A))))
    (hem : unitIdealPowerQuotientπ (complementPrincipalIdealSheaf A a f) m ≫ em.hom =
      (complementUnitModuleIso A a).inv ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          (specPrincipalQuotientπ A f m))
    (hen : unitIdealPowerQuotientπ (complementPrincipalIdealSheaf A a f) n ≫ en.hom =
      (complementUnitModuleIso A a).inv ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          (specPrincipalQuotientπ A f n)) :
    idealPowerQuotientDrop (complementPrincipalIdealSheaf A a f) h
          (complementZeroLocus A a : Scheme).unitModule ≫ en.hom =
      em.hom ≫ (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
        (specPrincipalQuotientDrop A f h) := by
  have hdrop : (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          (specPrincipalQuotientπ A f m) ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
          (specPrincipalQuotientDrop A f h) =
      (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
        (specPrincipalQuotientπ A f n) :=
    ((Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.restrictFunctor (complementZeroLocus A a).ι).map
        (specPrincipalQuotientπ_comp_drop A f h))
  refine (cancel_epi (unitIdealPowerQuotientπ (complementPrincipalIdealSheaf A a f) m)).1 ?_
  rw [idealPowerQuotientDrop_π_assoc, hen, reassoc_of% hem, hdrop]

end Stacks.Algebraization

end
