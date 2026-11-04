module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.AffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.QuotientTowerFormalFunctions
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryB.InverseLimitAsDerivedLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Formal sections for a principal ideal on a scheme

Let `A` be a ring, let `f ∈ A`, let `X` be a scheme over `A` and let `ℱ` be a quasi-coherent
`𝒪_X`-module whose `f`-power torsion stabilizes. The tower of quotients `ℱ/f^(n+1)ℱ` consists of
quasi-coherent modules and its transition maps are surjective on affine sections, so the ordinary
inverse limit `lim ℱ/f^(n+1)ℱ` is already a derived limit of the tower. Consequently the nine-term
diagram of formal functions for a principal ideal may be read off at that ordinary limit: a derived
limit of the `f`-power Koszul tower is isomorphic to `lim ℱ/f^(n+1)ℱ`, and for every `p` the middle
column of the diagram is the short exact sequence

`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`.

## Main definitions

* `Stacks.Algebraization.PrincipalQuotientTower.mulF`: multiplication by the image of `f` on a
  sheaf of `𝒪_X`-modules.
* `Stacks.Algebraization.PrincipalQuotientTower.quotientTower`: the inverse system
  `n ↦ ℱ/f^(n+1)ℱ` of sheaves of `𝒪_X`-modules.
* `Stacks.Algebraization.PrincipalQuotientTower.quotientTowerSingleIso`: the quotient tower in
  degree zero is the inverse system `Csys` of the derived category.

## Main results

* `Stacks.Algebraization.PrincipalQuotientTower.isDerivedLimit_single_limit_Csys`: for `ℱ`
  quasi-coherent the ordinary limit `lim ℱ/f^(n+1)ℱ`, placed in degree zero, is a derived limit of
  the tower of quotients.
* `PrincipalQuotientTower.exists_shortExact_homology_derivedSections_limit_quotientTower`: the
  middle column of the diagram of formal functions at that ordinary limit, together with the
  identification of a derived limit of the `f`-power Koszul tower with `lim ℱ/f^(n+1)ℱ`.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
* [Stacks Project, Tag 0H3E](https://stacks.math.columbia.edu/tag/0H3E)
* [Stacks Project, Tag 0BKS](https://stacks.math.columbia.edu/tag/0BKS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open Opposite TopologicalSpace
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open RingedSpaceModuleAdjunction
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open Stacks.Cohomology.DerivedSectionsOverBase (baseSmul derivedSectionsOver)
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)
open Stacks.Cohomology.QuotientTowerFormalFunctions
  (exists_shortExact_homology_derivedSections_quotientTower)
open Stacks.InverseSystems.EndIterate (iterate iterate_zero iterate_succ iterate_succ' iterate_add)

universe u

namespace Stacks.Algebraization.PrincipalQuotientTower

attribute [local instance] HasDerivedCategory.standard

/-- Being a derived limit is transported along an isomorphism of inverse systems. -/
private lemma isDerivedLimit_of_natIso {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (E E' : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ E.obj ⟨n⟩] [HasProduct fun n : ℕ ↦ E'.obj ⟨n⟩]
    (e : E ≅ E') (K : D) (hK : IsDerivedLimit E K) : IsDerivedLimit E' K := by
  obtain ⟨a, b, hT⟩ := hK
  let P := ∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩
  let P' := ∏ᶜ fun n : ℕ ↦ E'.obj ⟨n⟩
  let de : Discrete.functor (fun n : ℕ ↦ E.obj ⟨n⟩) ≅
      Discrete.functor (fun n : ℕ ↦ E'.obj ⟨n⟩) := Discrete.natIso fun n ↦ e.app ⟨n.as⟩
  let pe : P ≅ P' := HasLimit.isoOfNatIso de
  have peπ (n : ℕ) : pe.hom ≫ Pi.π (fun n : ℕ ↦ E'.obj ⟨n⟩) n =
      Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n ≫ (e.app ⟨n⟩).hom :=
    HasLimit.isoOfNatIso_hom_π de (Discrete.mk n)
  let d : P ⟶ P := Pi.lift fun n : ℕ ↦ Pi.π _ n - Pi.π _ (n + 1) ≫
    E.map (homOfLE (Nat.le_succ n)).op
  let d' : P' ⟶ P' := Pi.lift fun n : ℕ ↦ Pi.π _ n - Pi.π _ (n + 1) ≫
    E'.map (homOfLE (Nat.le_succ n)).op
  have hd : d ≫ pe.hom = pe.hom ≫ d' := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    dsimp only [d, d']
    rw [Category.assoc, peπ, ← Category.assoc, Pi.lift_π, Preadditive.sub_comp]
    simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub]
    congr 1
    · rw [peπ]
    · have hn : E.map (homOfLE (Nat.le_succ n)).op ≫ (e.app ⟨n⟩).hom =
          (e.app ⟨n + 1⟩).hom ≫ E'.map (homOfLE (Nat.le_succ n)).op := e.hom.naturality _
      rw [hn, ← Category.assoc pe.hom, peπ, Category.assoc]
  refine ⟨a ≫ pe.hom, pe.inv ≫ b, ?_⟩
  refine isomorphic_distinguished (Triangle.mk a d b) hT _
    (Triangle.isoMk _ _ (Iso.refl _) pe.symm pe.symm ?_ ?_ ?_)
  · dsimp only [Triangle.mk]; simp
  · dsimp only [Triangle.mk, Iso.symm_hom]
    simpa using (congrArg (fun u ↦ pe.inv ≫ u ≫ pe.inv) hd).symm
  · dsimp only [Triangle.mk]; simp

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.toRingedSpace.carrier)))
  (f : A) (ℱ : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- **Multiplication by `f`.** The endomorphism of a sheaf of `𝒪_X`-modules given by the action of
the image of `f ∈ A` in `Γ(X, 𝒪_X)`. -/
abbrev mulF : ℱ ⟶ ℱ := (baseSmul X.toRingedSpace ρ f).app ℱ

/-- **The quotient tower of `ℱ` at `f`.** The inverse system `n ↦ ℱ/f^(n+1)ℱ` of sheaves of
`𝒪_X`-modules, whose transition maps are the canonical surjections. -/
def quotientTower : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Functor.ofOpSequence
    (X := fun n ↦ cokernel (iterate (mulF X ρ f ℱ) (n + 1)))
    (fun n ↦ cokernel.map (iterate (mulF X ρ f ℱ) (n + 2)) (iterate (mulF X ρ f ℱ) (n + 1))
      (mulF X ρ f ℱ) (𝟙 _) (by rw [Category.comp_id, ← iterate_succ]))

/-- The quotient tower, read as an inverse system of modules on the scheme `X`. -/
abbrev quotientTowerModules : ℕᵒᵖ ⥤ X.Modules := quotientTower X ρ f ℱ

/-- The transition map out of level `n + 1` of the quotient tower is the map
`ℱ/f^(n+2)ℱ ⟶ ℱ/f^(n+1)ℱ` induced by the identity of `ℱ`. -/
lemma quotientTower_map_succ (n : ℕ) :
    (quotientTower X ρ f ℱ).map (homOfLE (Nat.le_succ n)).op =
      cokernel.map (iterate (mulF X ρ f ℱ) (n + 2)) (iterate (mulF X ρ f ℱ) (n + 1))
        (mulF X ρ f ℱ) (𝟙 _) (by rw [Category.comp_id, ← iterate_succ]) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The quotient tower in degree zero and the inverse system `Csys` have the same transition maps
between consecutive levels. -/
lemma singleFunctor_map_quotientTower_succ (n : ℕ) :
    (quotientTower X ρ f ℱ ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).map
        (homOfLE (Nat.le_succ n)).op =
    (Csys (mulF X ρ f ℱ)).map (homOfLE (Nat.le_succ n)).op := by
  change (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).map
      ((quotientTower X ρ f ℱ).map (homOfLE (Nat.le_succ n)).op) = _
  rw [quotientTower_map_succ, show (Csys (mulF X ρ f ℱ)).map (homOfLE (Nat.le_succ n)).op =
    Ctrans (mulF X ρ f ℱ) n from Functor.ofOpSequence_map_homOfLE_succ _ n]
  rfl

/-- The quotient tower `n ↦ ℱ/f^(n+1)ℱ`, placed in cohomological degree zero, is the inverse
system `Csys` of cokernels of the powers of multiplication by `f` in the derived category. -/
def quotientTowerSingleIso :
    quotientTower X ρ f ℱ ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ≅ Csys (mulF X ρ f ℱ) := by
  let τ : quotientTower X ρ f ℱ ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0 ⟶ Csys (mulF X ρ f ℱ) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) fun n ↦ (Category.comp_id _).trans
      ((singleFunctor_map_quotientTower_succ X ρ f ℱ n).trans (Category.id_comp _).symm)
  haveI : ∀ n : ℕᵒᵖ, IsIso (τ.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  haveI : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

section Quasicoherent

variable (hℱ : (ℱ : X.Modules).IsQuasicoherent)

include hℱ in
/-- Each term of the quotient tower is quasi-coherent. -/
lemma isQuasicoherent_quotientTower_obj (n : ℕᵒᵖ) :
    ((quotientTower X ρ f ℱ).obj n : X.Modules).IsQuasicoherent :=
  @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel X ℱ ℱ
    (iterate (mulF X ρ f ℱ) (n.unop + 1)) hℱ hℱ

/-- The transition maps of the quotient tower are epimorphisms. -/
lemma epi_quotientTower_map_succ (n : ℕ) :
    Epi ((quotientTower X ρ f ℱ).map (homOfLE (Nat.le_succ n)).op) := by
  rw [quotientTower_map_succ]
  have hfac : cokernel.π (iterate (mulF X ρ f ℱ) (n + 2)) ≫
      cokernel.map (iterate (mulF X ρ f ℱ) (n + 2)) (iterate (mulF X ρ f ℱ) (n + 1))
        (mulF X ρ f ℱ) (𝟙 _) (by rw [Category.comp_id, ← iterate_succ]) =
      cokernel.π (iterate (mulF X ρ f ℱ) (n + 1)) := by simp
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ coequalizer.π_epi hfac

include hℱ in
/-- On an affine open the transition maps of the quotient tower are surjective on sections. -/
lemma surjective_quotientTowerModules_map_succ_app (U : X.affineOpens) (n : ℕ) :
    Function.Surjective
      ((((quotientTowerModules X ρ f ℱ).map (homOfLE (Nat.le_succ n)).op).app U.1).hom) :=
  @Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen X _ _
    (isQuasicoherent_quotientTower_obj X ρ f ℱ hℱ (op (Nat.succ n)))
    (isQuasicoherent_quotientTower_obj X ρ f ℱ hℱ (op n))
    ((quotientTowerModules X ρ f ℱ).map (homOfLE (Nat.le_succ n)).op)
    (epi_quotientTower_map_succ X ρ f ℱ n) U

include hℱ in
/-- The ordinary limit `lim ℱ/f^(n+1)ℱ`, placed in degree zero, is a derived limit of the quotient
tower in degree zero. -/
theorem isDerivedLimit_single_limit_quotientTower :
    ∃ h : HasProduct (fun n : ℕ ↦ (quotientTower X ρ f ℱ ⋙
        DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
        _ _ _ _ _ _ (quotientTower X ρ f ℱ ⋙
          DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0) h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
          (limit (quotientTower X ρ f ℱ))) :=
  Stacks.Cohomology.SpaceInverseLimits.isDerivedLimit_single_limit_of_isBasis X.toRingedSpace
    (quotientTower X ρ f ℱ) X.affineOpens X.isBasis_affineOpens
    (fun U hU n p hp ↦ @Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X
      ((quotientTowerModules X ρ f ℱ).obj ⟨n⟩)
      (isQuasicoherent_quotientTower_obj X ρ f ℱ hℱ ⟨n⟩) U hU p hp)
    (fun U hU ↦ Stacks.Cohomology.SpaceInverseLimits.epi_inverseLimitDifference_of_surjective _
      (fun n ↦ surjective_quotientTowerModules_map_succ_app X ρ f ℱ hℱ ⟨U, hU⟩ n))

include hℱ in
/-- The ordinary limit `lim ℱ/f^(n+1)ℱ`, in degree zero, is a derived limit of the inverse
system of the quotients `ℱ/f^(n+1)ℱ` in the derived category. -/
theorem isDerivedLimit_single_limit_Csys :
    ∃ h : HasProduct (fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
        _ _ _ _ _ _ (Csys (mulF X ρ f ℱ)) h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
          (limit (quotientTower X ρ f ℱ))) := by
  obtain ⟨h, hlim⟩ := isDerivedLimit_single_limit_quotientTower X ρ f ℱ hℱ
  have h' : HasProduct (fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩) := h
  exact ⟨h', isDerivedLimit_of_natIso _ _ (quotientTowerSingleIso X ρ f ℱ) _ hlim⟩

include hℱ in
/-- **Formal sections for a principal ideal on a scheme: the middle column of the diagram.**
Let `A` be a ring, `f ∈ A`, let `X` be a scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let `ℱ`
be a quasi-coherent `𝒪_X`-module whose `f`-power torsion stabilizes. Let `E^` be a derived limit
of the `f`-power Koszul tower `ℱ ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)`. Then `E^` is isomorphic to the
ordinary inverse limit `lim ℱ/f^(n+1)ℱ`, and for every `p` the cohomology of
`RΓ(X, lim ℱ/f^(n+1)ℱ)` over `A` sits in a short exact sequence

`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`,

whose inclusion descends the connecting morphism of the Milnor triangle and whose projection is
characterized by the limit projections, and whose outer terms are isomorphic to the outer terms of
the corresponding sequence for the Koszul tower. -/
@[stacks 0BLD "the middle column of the diagram, for a quasi-coherent module on a scheme: the \
short exact sequence `0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0` at \
the ordinary limit, together with the isomorphism of a derived limit of the f-power Koszul tower \
with `lim ℱ/fⁿℱ`. The displayed equality `RΓ(X, lim ℱ/fⁿℱ) = RΓ(X, ℱ)^∧` and the remaining rows \
and columns of the diagram are not covered"]
theorem exists_shortExact_homology_derivedSections_limit_quotientTower
    (hstab : Stabilizes (mulF X ρ f ℱ))
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Csys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    (Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hEhat : IsDerivedLimit (Ksys (mulF X ρ f ℱ)) Ehat) :
    let Fhat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
        (limit (quotientTower X ρ f ℱ))
    let F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      Csys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ
    let G : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    Nonempty (Ehat ≅ Fhat) ∧
      ∃ (a : (derivedSectionsOver X.toRingedSpace ρ).obj Fhat ⟶ ∏ᶜ Y)
        (b : (∏ᶜ Y) ⟶ ((derivedSectionsOver X.toRingedSpace ρ).obj Fhat)⟦(1 : ℤ)⟧),
        let T := Triangle.mk a d b
        T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
          ∀ p : ℤ,
            let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) p
            let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1)
            let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
            let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
            let P : ModuleCat.{u} A :=
              ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
            let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
                Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                  shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
            ∃ (e : H₁.obj (∏ᶜ Y) ≅ P)
              (i : cokernel δ ⟶ H.obj ((derivedSectionsOver X.toRingedSpace ρ).obj Fhat))
              (q : H.obj ((derivedSectionsOver X.toRingedSpace ρ).obj Fhat) ⟶
                limit homologySystem)
              (w : i ≫ q = 0),
              e.hom = piComparison H₁ Y ∧
                cokernel.π δ ≫ i = e.inv ≫
                  DerivedCategory.HomologySequence.δ T (p - 1) p ∧
                (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                  H.map a ≫ H.map (Pi.π Y n)) ∧
                (ShortComplex.mk i q w).ShortExact ∧
                Nonempty (limit homologySystem ≅ limit (G ⋙ H)) ∧
                Nonempty (cokernel δ ≅
                  CompletionSequences.firstDerivedLimit A (G ⋙ H₁)) := by
  obtain ⟨_, hlim⟩ := isDerivedLimit_single_limit_Csys X ρ f ℱ hℱ
  exact exists_shortExact_homology_derivedSections_quotientTower X.toRingedSpace ρ f ℱ hstab
    _ Ehat hlim hEhat

end Quasicoherent

end Stacks.Algebraization.PrincipalQuotientTower

end
