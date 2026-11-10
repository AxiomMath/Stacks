module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional

/-!
# Base change of a proper direct image of sheaves of modules, in degree zero

Let
```
Z' --g'--> Z
|i'        |i
v          v
X' --g---> X
```
be a cartesian square of schemes with `i` proper and `Λ` a commutative ring. The base change map
`g^{-1} i_* M ⟶ i'_* g'^{-1} M` of `Stacks.EtaleCohomology.etaleModuleBaseChange` is an
isomorphism for every sheaf `M` of `Λ`-modules on `Z_étale`: this is
[Stacks, Tag 0A3U] (proper base change in degree zero), which holds for every sheaf of sets and
hence for every abelian sheaf (`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isProper`),
transported to sheaves of modules along the forgetful functor exactly as for integral morphisms
(`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isIntegralHom`).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isIso_smallEtaleBaseChangeAb`: the
  module base change map is invertible as soon as the abelian one is.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isProper`: [Stacks, Tag 0A3U] for
  sheaves of modules.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper`: the case of
  the base change to an extension field of a proper morphism over a field.

## References

* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

variable {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X) (g' : Z' ⟶ Z)

/-- Direct image commutes with forgetting the module structure, on the nose. -/
private def directImageForgetIso {S T : Scheme.{u}} (k : T ⟶ S) :
    etaleModuleDirectImage.{u, 0} Λ k ⋙ etaleModuleUnderlyingAbelian (X := S) Λ ≅
      etaleModuleUnderlyingAbelian (X := T) Λ ⋙ smallEtalePushforwardAb k :=
  Iso.refl _

/-- **The module base change map is invertible when the abelian one is.** For a cartesian square
`i' ≫ g = g' ≫ i`, if the abelian comparison `g^{-1} i_* ⟶ i'_* g'^{-1}` of
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is an isomorphism, so is the base change map of
sheaves of `Λ`-modules: both are mates of the identification of the two composite direct images,
and the forgetful functor to abelian sheaves reflects isomorphisms. -/
theorem isIso_etaleModuleBaseChange_of_isIso_smallEtaleBaseChangeAb (sq : IsPullback i' g' g i)
    (hAb : IsIso (smallEtaleBaseChangeAb g i i' g' sq.w)) :
    IsIso (etaleModuleBaseChange Λ i i' g g' sq.w) := by
  have : ∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := fun Z =>
    ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology
  have : ∀ Z : Scheme.{u}, Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := fun Z =>
    ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology
  rw [show smallEtaleBaseChangeAb g i i' g' sq.w = _ from
    Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm _ _ _ _ _] at hAb
  have hhom : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (ab : A ⟶ C) (hab : ab = a ≫ b),
      (etaleAbelianDirectImageCompIso'.{u, 0} a b ab hab).hom =
        (etaleAbelianDirectImageCompIso'.{u, 0} a b (a ≫ b) rfl).hom ≫
          eqToHom (congrArg (fun m : A ⟶ C => etaleAbelianDirectImage.{u, 0} m) hab.symm) := by
    intro A B C a b ab hab
    subst hab
    simp
  have hcell : (smallEtalePushforwardAbCompIso g' i ≪≫
      eqToIso (congrArg smallEtalePushforwardAb sq.w.symm) ≪≫
        (smallEtalePushforwardAbCompIso i' g).symm).hom =
      (etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv := by
    rw [hhom, etaleAbelianDirectImageCompIso'_rfl, etaleAbelianDirectImageCompIso'_rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
    rfl
  rw [hcell] at hAb
  set T := TwoSquare.mk (smallEtalePushforwardAb g') (smallEtalePushforwardAb i')
    (smallEtalePushforwardAb i) (smallEtalePushforwardAb g)
    ((etaleAbelianDirectImageCompIso'.{u, 0} g' i (i' ≫ g) sq.w).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, 0} i' g (i' ≫ g) rfl).inv)
  have : IsIso
      ((mateEquiv (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)).symm T) := hAb
  have hmate : ∀ {A B : Scheme.{u}} (f : A ⟶ B),
      mateEquiv (etaleModuleInverseImageAdj.{u, 0} Λ f) (smallEtaleAdjunctionAb f)
        (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange f) B.smallEtaleTopology
          A.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) =
      coefficientPushforwardTwoSquare (smallEtaleBaseChange f) B.smallEtaleTopology
        A.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    fun _ => Equiv.apply_symm_apply _ _
  rw [etaleModuleBaseChange_eq_mateEquiv_symm]
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (etaleModuleInverseImageAdj.{u, 0} Λ g') (etaleModuleInverseImageAdj.{u, 0} Λ g)
    (smallEtaleAdjunctionAb g') (smallEtaleAdjunctionAb g)
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g') Z.smallEtaleTopology
      Z'.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
      X'.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
    (directImageForgetIso Λ i).hom (directImageForgetIso Λ i').inv _ T ?_
  rw [hmate g', hmate g]
  refine NatTrans.ext (funext fun M => ?_)
  refine Sheaf.hom_ext ?_
  refine NatTrans.ext (funext fun U => ?_)
  rfl

/-- **[Stacks, Tag 0A3U] for sheaves of modules.** For a cartesian square `i' ≫ g = g' ≫ i` with
`i` proper, the base change map `g^{-1} i_* ⟶ i'_* g'^{-1}` of sheaves of `Λ`-modules is an
isomorphism. -/
theorem isIso_etaleModuleBaseChange_of_isProper (sq : IsPullback i' g' g i) [IsProper i] :
    IsIso (etaleModuleBaseChange Λ i i' g g' sq.w) :=
  isIso_etaleModuleBaseChange_of_isIso_smallEtaleBaseChangeAb Λ i i' g g' sq
    (isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange g i i' g' sq.w
      (isIso_etaleAbelianBaseChange_of_isProper i g g' i' sq.flip))

section FieldBaseChange

open Stacks.Frobenius

variable {k : Type u} [Field k] {Zk Yk : Over (Spec (.of k))} (i : Zk ⟶ Yk)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The base change map to `k̄` along a proper morphism over `k` is an isomorphism.** -/
theorem isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper [IsProper i.left] :
    IsIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Yk kbar)
      (fieldBaseChangeProj Zk kbar) (fieldBaseChangeMap_comp_fst i kbar)) :=
  isIso_etaleModuleBaseChange_of_isProper Λ i.left (fieldBaseChangeMap i kbar)
    (fieldBaseChangeProj Yk kbar) (fieldBaseChangeProj Zk kbar)
    (isPullback_fieldBaseChangeMap i kbar)

/-- The base change to `k̄` of a proper morphism over `k` is proper. -/
theorem isProper_fieldBaseChangeMap [IsProper i.left] : IsProper (fieldBaseChangeMap i kbar) :=
  MorphismProperty.of_isPullback (isPullback_fieldBaseChangeMap i kbar).flip ‹_›

end FieldBaseChange

end Stacks.EtaleCohomology

end
