module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.QuotientTildeComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.UnitGenerated

/-!
# The completion of the structure sheaf on the complement of a closed subset

Let `B` be a Noetherian ring, let `𝔟 ⊆ B` be an ideal, let `g ∈ B` and let
`U = Spec(B) ∖ V(𝔟)`. Two towers of quotients of the structure sheaf of `U` by the powers of
`g` occur in this library:

* the completion of `𝒪_U` along `g 𝒪_U` in the sense of Stacks 0880, whose `n`-th term is
  `𝒪_U / (g 𝒪_U)ⁿ⁺¹ 𝒪_U` (`Stacks.Algebraization.completionFunctor`);
* the tower of Stacks 0EII, whose `n`-th term is the sheaf associated to `B / gⁿB` restricted to
  `U` (`Stacks.Algebraization.ComplementTower.quotientModule`).

This file identifies them, termwise and compatibly with the quotient projections out of the
structure sheaf and with the transition maps. It is the transport of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/QuotientTildeComplement.lean`
read at the indexing of Stacks 0880 and at the quotient modules Stacks 0EII uses.

## Main definitions

* `Stacks.Algebraization.principalQuotientModuleIso` — `B / (g)ⁿ` is the `n`-th quotient module
  of the tower of Stacks 0EII.
* `Stacks.Algebraization.complementCompletionTermIso` — **the `n`-th term of the completion of
  `𝒪_U` is the restriction to `U` of the sheaf associated to `B / gⁿ⁺¹B`.**

## Main results

* `Stacks.Algebraization.completionProjection_comp_complementCompletionTermIso` — the
  identification carries the projection of the completion to the quotient projection of
  Stacks 0EII.
* `Stacks.Algebraization.complementCompletionTermIso_transition` — the identification carries the
  transition maps of the completion to the transition maps of the tower of Stacks 0EII.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` and `SheafOfModules X.ringCatSheaf` are two presentations of
one category, definitionally equal but not interchangeable: a goal that mentions
`(Stacks.Algebraization.unitCoherentModule X).obj`, whose declared type is the second, is not
type-correct at `implicit` transparency, so `rw` and `simp` cannot build a motive for it and
neither can instance search find the zero morphisms, the cokernel epimorphisms or
`CategoryTheory.IsIso` of an `CategoryTheory.eqToHom` of that category. Both proofs here are
therefore assembled in term mode from `CategoryTheory.Category.assoc` and `congrArg`, with the
epimorphism and isomorphism instances supplied by hand, exactly as
`Stacks.Algebraization.bijective_completionFunctor_map_iff_bijective_comp` is.

The index shift between the two towers is
`Stacks.Algebraization.completionFunctor_obj`, an equality of objects; it enters through
`CategoryTheory.eqToHom`, and the cancellation of that `eqToHom` against the one inside
`Stacks.Algebraization.completionProjection` is the first step of each proof.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (B : Type u) [CommRing B] (b : Ideal B) (g : B) (n : ℕ)

/-- **`B / (g)ⁿ` is the `n`-th quotient module of the tower of Stacks 0EII.** The two differ
only in the spelling of the submodule divided out: `(g)ⁿ` as an ideal of `B` on one side and
`(g)ⁿ · B` as a submodule of `B` on the other. -/
public def principalQuotientModuleIso :
    ModuleCat.of B (B ⧸ (Ideal.span {g} ^ n : Ideal B)) ≅
      ComplementTower.quotientModule B g (ModuleCat.of B B) n :=
  LinearEquiv.toModuleIso
    (Submodule.quotEquivOfEq ((Ideal.span {g} ^ n : Ideal B) : Submodule B B)
      ((Ideal.span {g} ^ n : Ideal B) • (⊤ : Submodule B B)) (by simp))

/-- The identification carries the quotient projection to the quotient projection. -/
public theorem mkQ_comp_principalQuotientModuleIso :
    ModuleCat.ofHom (Submodule.mkQ (Ideal.span {g} ^ n : Ideal B)) ≫
        (principalQuotientModuleIso B g n).hom =
      ComplementTower.quotientMap B g (ModuleCat.of B B) n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The identification carries the exponent-lowering map to the transition map of the tower. -/
public theorem principalQuotientModuleIso_comp_quotientTransition :
    (principalQuotientModuleIso B g (n + 1)).hom ≫
        ComplementTower.quotientTransition B g (ModuleCat.of B B) n =
      ModuleCat.ofHom (Submodule.mapQ (Ideal.span {g} ^ (n + 1) : Ideal B)
          (Ideal.span {g} ^ n : Ideal B) LinearMap.id (by
            rw [Submodule.comap_id]
            exact Ideal.pow_le_pow_right (Nat.le_succ n))) ≫
        (principalQuotientModuleIso B g n).hom :=
  ModuleCat.hom_ext (LinearMap.ext fun z => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl)

section Sheaf

/-- Restricting the tilde of a composite of module maps to the complement composes. -/
private theorem restrict_tilde_map_comp {M N P : ModuleCat B} (f : M ⟶ N) (k : N ⟶ P)
    (h : M ⟶ P) (hfk : f ≫ k = h) :
    (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
        ((tilde.functor (CommRingCat.of B)).map f) ≫
      (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
        ((tilde.functor (CommRingCat.of B)).map k) =
    (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
      ((tilde.functor (CommRingCat.of B)).map h) :=
  ((Functor.map_comp _ _ _).symm.trans (congrArg _ ((Functor.map_comp _ _ _).symm.trans
    (congrArg _ hfk))))

variable [IsNoetherianRing B]

/-- The `n`-th term of the completion of `𝒪_U` along `f 𝒪_U` is the restriction to `U` of the
sheaf associated to the `(n+1)`-st term of the quotient tower of Stacks 0EII. -/
public def complementCompletionTermIso :
    ((completionFunctor (complementZeroLocus B b : Scheme)
          (complementPrincipalIdealSheaf B b g)).obj
        (unitCoherentModule (complementZeroLocus B b : Scheme))).obj.obj (op n) ≅
      (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).obj
        (tilde (ComplementTower.quotientModule B g (ModuleCat.of B B) (n + 1))) :=
  eqToIso (completionFunctor_obj _ _ _ n) ≪≫
    (exists_complementUnitQuotient_iso B b g (n + 1)).choose ≪≫
      (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).mapIso
        ((tilde.functor (CommRingCat.of B)).mapIso (principalQuotientModuleIso B g (n + 1)))

/-- **The identification carries the projection of the completion to the quotient projection of
Stacks 0EII.** Composing the projection of `𝒪_U` onto the `n`-th term of its completion with
`Stacks.Algebraization.complementCompletionTermIso` gives the restriction to `U` of the quotient
projection `B~ ⟶ (B / gⁿ⁺¹B)~`, read on `𝒪_U` through
`Stacks.Algebraization.complementUnitModuleIso`. -/
public theorem completionProjection_comp_complementCompletionTermIso :
    completionProjection (complementZeroLocus B b : Scheme)
          (complementPrincipalIdealSheaf B b g)
          (unitCoherentModule (complementZeroLocus B b : Scheme)) n ≫
        (complementCompletionTermIso B b g n).hom =
      (complementUnitModuleIso B b).inv ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
          ((tilde.functor (CommRingCat.of B)).map
            (ComplementTower.quotientMap B g (ModuleCat.of B B) (n + 1))) := by
  have hc := (exists_complementUnitQuotient_iso B b g (n + 1)).choose_spec
  have hmod := restrict_tilde_map_comp B b _ _ _ (mkQ_comp_principalQuotientModuleIso B g (n + 1))
  have hpi : completionProjection (complementZeroLocus B b : Scheme)
          (complementPrincipalIdealSheaf B b g)
          (unitCoherentModule (complementZeroLocus B b : Scheme)) n ≫
        eqToHom (completionFunctor_obj (complementZeroLocus B b : Scheme)
          (complementPrincipalIdealSheaf B b g)
          (unitCoherentModule (complementZeroLocus B b : Scheme)) n) =
      cokernel.π (C := (complementZeroLocus B b : Scheme).Modules)
        (idealPowerMultiple (complementPrincipalIdealSheaf B b g) (n + 1)
          (unitCoherentModule (complementZeroLocus B b : Scheme)).obj).ι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => cokernel.π (C := (complementZeroLocus B b : Scheme).Modules)
            (idealPowerMultiple (complementPrincipalIdealSheaf B b g) (n + 1)
              (unitCoherentModule (complementZeroLocus B b : Scheme)).obj).ι ≫ k)
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
  have key : unitIdealPowerQuotientπ (complementPrincipalIdealSheaf B b g) (n + 1) ≫
        ((exists_complementUnitQuotient_iso B b g (n + 1)).choose.hom ≫
          (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
            ((tilde.functor (CommRingCat.of B)).map
              (principalQuotientModuleIso B g (n + 1)).hom)) =
      (complementUnitModuleIso B b).inv ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
          ((tilde.functor (CommRingCat.of B)).map
            (ComplementTower.quotientMap B g (ModuleCat.of B B) (n + 1))) := by
    rw [reassoc_of% hc]
    exact congrArg _ hmod
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫
      ((exists_complementUnitQuotient_iso B b g (n + 1)).choose.hom ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
          ((tilde.functor (CommRingCat.of B)).map
            (principalQuotientModuleIso B g (n + 1)).hom))) hpi).trans key)

/-- **The identification carries the transition maps of the completion to the transition maps of
the tower of Stacks 0EII.** Under `Stacks.Algebraization.complementCompletionTermIso`, the
transition map from the `(n+1)`-st to the `n`-th term of the completion of `𝒪_U` is the
restriction to `U` of the map `(B / gⁿ⁺²B)~ ⟶ (B / gⁿ⁺¹B)~` induced by the transition map of the
quotient tower. -/
public theorem complementCompletionTermIso_transition :
    ((completionFunctor (complementZeroLocus B b : Scheme)
            (complementPrincipalIdealSheaf B b g)).obj
          (unitCoherentModule (complementZeroLocus B b : Scheme))).obj.map
          (homOfLE (Nat.le_succ n)).op ≫
        (complementCompletionTermIso B b g n).hom =
      (complementCompletionTermIso B b g (n + 1)).hom ≫
        (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
          ((tilde.functor (CommRingCat.of B)).map
            (ComplementTower.quotientTransition B g (ModuleCat.of B B) (n + 1))) := by
  have hiso : IsIso (eqToHom (completionFunctor_obj (complementZeroLocus B b : Scheme)
      (complementPrincipalIdealSheaf B b g)
      (unitCoherentModule (complementZeroLocus B b : Scheme)) (n + 1)).symm) :=
    (eqToIso (completionFunctor_obj (complementZeroLocus B b : Scheme)
      (complementPrincipalIdealSheaf B b g)
      (unitCoherentModule (complementZeroLocus B b : Scheme)) (n + 1)).symm).isIso_hom
  have hepi0 : Epi (eqToHom (completionFunctor_obj (complementZeroLocus B b : Scheme)
      (complementPrincipalIdealSheaf B b g)
      (unitCoherentModule (complementZeroLocus B b : Scheme)) (n + 1)).symm) :=
    IsIso.epi_of_iso _
  have hepi : Epi (completionProjection (complementZeroLocus B b : Scheme)
      (complementPrincipalIdealSheaf B b g)
      (unitCoherentModule (complementZeroLocus B b : Scheme)) (n + 1)) := by
    show Epi (cokernel.π (C := (complementZeroLocus B b : Scheme).Modules)
        (idealPowerMultiple (complementPrincipalIdealSheaf B b g) (n + 1 + 1)
          (unitCoherentModule (complementZeroLocus B b : Scheme)).obj).ι ≫
      eqToHom (completionFunctor_obj (complementZeroLocus B b : Scheme)
        (complementPrincipalIdealSheaf B b g)
        (unitCoherentModule (complementZeroLocus B b : Scheme)) (n + 1)).symm)
    have := epi_cokernel_π_submodule_ι
      (idealPowerMultiple (complementPrincipalIdealSheaf B b g) (n + 1 + 1)
        (unitCoherentModule (complementZeroLocus B b : Scheme)).obj)
    exact epi_comp _ _
  refine (cancel_epi (completionProjection (complementZeroLocus B b : Scheme)
    (complementPrincipalIdealSheaf B b g)
    (unitCoherentModule (complementZeroLocus B b : Scheme)) (n + 1))).1 ?_
  have hmod0 := restrict_tilde_map_comp B b _ _ _
    (quotientMap_comp_quotientTransition (A := B) (f := g) (ModuleCat.of B B) (n + 1))
  have hL2 := congrArg (fun k => k ≫ (complementCompletionTermIso B b g n).hom)
    (completionProjection_transition (complementZeroLocus B b : Scheme)
      (complementPrincipalIdealSheaf B b g)
      (unitCoherentModule (complementZeroLocus B b : Scheme)) n)
  have hR2 := congrArg (fun k => k ≫
      (Scheme.Modules.restrictFunctor (complementZeroLocus B b).ι).map
        ((tilde.functor (CommRingCat.of B)).map
          (ComplementTower.quotientTransition B g (ModuleCat.of B B) (n + 1))))
    (completionProjection_comp_complementCompletionTermIso B b g (n + 1))
  have hR4 := congrArg (fun k => (complementUnitModuleIso B b).inv ≫ k) hmod0
  exact ((Category.assoc _ _ _).symm.trans (hL2.trans
      (completionProjection_comp_complementCompletionTermIso B b g n))).trans
    (((hR4.symm.trans (Category.assoc _ _ _).symm).trans hR2.symm).trans
      (Category.assoc _ _ _))

end Sheaf

end Stacks.Algebraization

end
