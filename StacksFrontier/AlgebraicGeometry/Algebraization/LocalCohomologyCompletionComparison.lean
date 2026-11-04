module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.CechReflection
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Composition
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.DerivedHomCompletionTorsion
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.ExtendedCech

/-!
# Completed local cohomology: enlarging the ideal, and derived Hom from local cohomology

Let `A` be a commutative ring, let `I = (f₁, …, f_r)` and `J` be ideals of `A`, write `(-)^∧` for
derived `I`-adic completion and `RΓ_{V(K)}` for local cohomology with support in `V(K)`. This
file gives two identifications of `RΓ_{V(J)}(-)^∧` from the proof of [Stacks, Tag 0EFH]: the
natural isomorphism `RΓ_{V(J)}(-)^∧ ≅ RΓ_{V(J + I)}(-)^∧`, and `K^∧ ≅ RHom_A(RΓ_{V(I)}(A), K)`,
which for `K = RΓ_{V(J)}(M)` reads `RΓ_{V(J)}(M)^∧ ≅ RHom_A(RΓ_{V(I)}(A), RΓ_{V(J)}(M))`.

## Main definitions

* `Stacks.Algebraization.derivedCompletionLocalCohomologyCounitIso`: the natural isomorphism
  `RΓ_{V(I)}(-)^∧ ≅ (-)^∧`.
* `Stacks.Algebraization.derivedCompletionLocalCohomologySupIso`: the natural isomorphism
  `RΓ_{V(J)}(-)^∧ ≅ RΓ_{V(J + I)}(-)^∧`.
* `Stacks.Algebraization.derivedCompletionLocalCohomologySupIsoOfEq`: the same for any ideal
  equal to `J + I`.
* `Stacks.Algebraization.derivedCompletionIsoDerivedHomLocalCohomology`: the isomorphism
  `K^∧ ≅ RHom_A(RΓ_{V(I)}(A), K)`.
* `Stacks.Algebraization.derivedCompletionIsoDerivedHomDerivedPowerTorsion`: over a Noetherian
  ring, the isomorphism `K^∧ ≅ RHom_A(RΓ_I(A), K)` with derived `I`-power torsion of the ring.
* `Stacks.Algebraization.derivedCompletionLocalCohomologyIsoDerivedHomSup`: the isomorphism
  `RΓ_{V(J)}(K)^∧ ≅ RHom_A(RΓ_{V(I)}(A), RΓ_{V(J + I)}(K))`.

## Main results

* `Stacks.Algebraization.isIso_derivedCompletionFunctor_map_localCohomologyCounit`: derived
  `I`-adic completion inverts the counit `RΓ_{V(I)}(L) ⟶ L` of Tag 0A6Q.

## Implementation notes

Derived `I`-adic completion is `DerivedCompletion.derivedCompletionFunctor A f`, the derived Hom
out of the extended alternating Čech complex of a finite family `f` generating `I`; the
generating family, rather than the ideal, is the argument, and the module universe equals the
ring universe. Local cohomology is the support-indexed model `Dualizing.localCohomologyFunctor` of
Tag 0A6Q, valued in the objects with power-torsion cohomology; the inclusion of that subcategory
is written out in the statements.

## References

* [Stacks Project, Tag 0EFH](https://stacks.math.columbia.edu/tag/0EFH), the two identifications
  opening the proof.
* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
* [Stacks Project, Tag 091V](https://stacks.math.columbia.edu/tag/091V)
* [Stacks Project, Tag 0956](https://stacks.math.columbia.edu/tag/0956)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### Derived completion inverts the local-cohomology counit -/

/-- **Stacks 0A6W in the Čech model of derived completion.** For a finite family `f` generating
`I`, derived `I`-adic completion carries the counit `RΓ_{V(I)}(L) ⟶ L` of Tag 0A6Q to an
isomorphism. -/
theorem isIso_derivedCompletionFunctor_map_localCohomologyCounit (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((DerivedCompletion.derivedCompletionFunctor A f).map
      ((Dualizing.localCohomologyAdjunction A I hI).counit.app L)) := by
  let F := DerivedCompletion.derivedCompletionFunctor A f
  let ε := DerivedCompletion.derivedCompletionUnit A f
  have hε := DerivedCompletion.derivedCompletion_isReflection A f
  have hFc : ∀ X, Dualizing.derivedCompleteProperty A I (F.obj X) := fun X => by
    rw [← hf]
    exact hε.1 X
  have hb : ∀ X E, Dualizing.derivedCompleteProperty A I E →
      Function.Bijective (fun g : F.obj X ⟶ E ↦ ε.app X ≫ g) := fun X E hE =>
    hε.2 X E (by rw [hf]; exact hE)
  exact Dualizing.isIso_derivedCompletion_map_localCohomologyCounit A I hI
    ((Dualizing.derivedCompleteProperty A I).lift F hFc)
    (Dualizing.reflectionAdjunctionOfUniversal
      (Dualizing.derivedCompleteProperty A I) F ε hFc hb) L

/-- **Stacks 0A6W as a natural isomorphism in the Čech model.** Derived `I`-adic completion of
`RΓ_{V(I)}(-)` is derived `I`-adic completion: the counit of Tag 0A6Q becomes invertible. -/
def derivedCompletionLocalCohomologyCounitIso (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    (Dualizing.localCohomologyFunctor.{u, u} A I hI ⋙
          (Dualizing.derivedPowerTorsionProperty A I hI).ι) ⋙
        DerivedCompletion.derivedCompletionFunctor A f ≅
      DerivedCompletion.derivedCompletionFunctor A f := by
  refine NatIso.ofComponents (fun L => @asIso _ _ _ _ _
    (isIso_derivedCompletionFunctor_map_localCohomologyCounit A I hI f hf L)) ?_
  intro L L' g
  have h := congrArg (DerivedCompletion.derivedCompletionFunctor A f).map
    ((Dualizing.localCohomologyAdjunction A I hI).counit.naturality g)
  rwa [Functor.map_comp, Functor.map_comp] at h

/-! ### Enlarging the ideal under derived completion -/

/-- For ideals `I` and `J` of `A` with `I` generated by the finite family `f`, derived `I`-adic
completion does not distinguish `RΓ_{V(J)}` from `RΓ_{V(J + I)}`: there is a natural isomorphism
`RΓ_{V(J)}(-)^∧ ≅ RΓ_{V(J + I)}(-)^∧`. -/
@[stacks 0EFH "the first identification of the proof: `RΓ_J(-)^∧ = RΓ_{I+J}(-)^∧`, which is
what lets `J` be replaced by `I + J`"]
def derivedCompletionLocalCohomologySupIso (A : Type u) [CommRing A] (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    Dualizing.localCohomologyFunctor.{u, u} A J hJ ⋙
        (Dualizing.derivedPowerTorsionProperty A J hJ).ι ⋙
          DerivedCompletion.derivedCompletionFunctor A f ≅
      Dualizing.localCohomologyFunctor.{u, u} A (J + I) (Submodule.FG.sup hJ hI) ⋙
        (Dualizing.derivedPowerTorsionProperty A (J + I) (Submodule.FG.sup hJ hI)).ι ⋙
          DerivedCompletion.derivedCompletionFunctor A f :=
  Functor.isoWhiskerLeft
      (Dualizing.localCohomologyFunctor.{u, u} A J hJ ⋙
        (Dualizing.derivedPowerTorsionProperty A J hJ).ι)
      (derivedCompletionLocalCohomologyCounitIso A I hI f hf).symm ≪≫
    Functor.isoWhiskerRight (Dualizing.localCohomologyCompIso.{u, u} A J I hJ hI)
      ((Dualizing.derivedPowerTorsionProperty A (J + I) (Submodule.FG.sup hJ hI)).ι ⋙
        DerivedCompletion.derivedCompletionFunctor A f)

/-- The natural isomorphism `RΓ_{V(J)}(-)^∧ ≅ RΓ_{V(S)}(-)^∧` of
`derivedCompletionLocalCohomologySupIso`, for an ideal `S` equal to `J + I`. -/
def derivedCompletionLocalCohomologySupIsoOfEq (A : Type u) [CommRing A] (I J S : Ideal A)
    (hI : I.FG) (hJ : J.FG) (hS : S.FG) (hSJI : S = J + I) {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    Dualizing.localCohomologyFunctor.{u, u} A J hJ ⋙
        (Dualizing.derivedPowerTorsionProperty A J hJ).ι ⋙
          DerivedCompletion.derivedCompletionFunctor A f ≅
      Dualizing.localCohomologyFunctor.{u, u} A S hS ⋙
        (Dualizing.derivedPowerTorsionProperty A S hS).ι ⋙
          DerivedCompletion.derivedCompletionFunctor A f := by
  subst hSJI
  exact derivedCompletionLocalCohomologySupIso A I J hI hJ f hf

/-! ### Derived completion as derived Hom from local cohomology of the ring -/

/-- For a finite family `f` generating `I`, derived `I`-adic completion is derived Hom out of the
local cohomology `RΓ_{V(I)}(A)` of the ring: `K^∧ ≅ RHom_A(RΓ_{V(I)}(A), K)`. -/
@[stacks 0EFH "the second identification of the proof: derived `I`-adic completion is `RHom`
out of `RΓ_{V(I)}(A)`"]
def derivedCompletionIsoDerivedHomLocalCohomology (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCompletion.derivedCompletionFunctor A f).obj K ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((Stacks.LocalCohomology.localCohomologyOnModules.{u, u} A I hI).obj
          (ModuleCat.of A A)), K) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
    (Iso.prod ((Stacks.LocalCohomology.localCohomologyIsoCech.{u} f I hI hf).app
      (ModuleCat.of A A)).op (Iso.refl K))

/-- Over a Noetherian ring derived `I`-adic completion is derived Hom out of derived `I`-power
torsion of the ring: `K^∧ ≅ RHom_A(RΓ_I(A), K)`. -/
@[stacks 0EFH "the second identification of the proof, written with `RΓ_I(A)` over a
Noetherian ring"]
def derivedCompletionIsoDerivedHomDerivedPowerTorsion (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCompletion.derivedCompletionFunctor A f).obj K ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op (Stacks.LocalCohomology.derivedPowerTorsionObj.{u, u} A I
          (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of A A)), K) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
    (Iso.prod (Stacks.LocalCohomology.extendedCechComparison.{u, u} A I f hf
      (ModuleCat.of A A)).1.1.op (Iso.refl K))

/-- For ideals `I` and `J` of `A` with `I` generated by the finite family `f`, the derived
`I`-adic completion of `RΓ_{V(J)}(K)` is `RHom_A(RΓ_{V(I)}(A), RΓ_{V(J + I)}(K))`. -/
@[stacks 0EFH "the two identifications of the first paragraph of the proof, composed into the
form the truncation reduction consumes"]
def derivedCompletionLocalCohomologyIsoDerivedHomSup (A : Type u) [CommRing A] (I J : Ideal A)
    (hI : I.FG) (hJ : J.FG) {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCompletion.derivedCompletionFunctor A f).obj
        ((Dualizing.derivedPowerTorsionProperty A J hJ).ι.obj
          ((Dualizing.localCohomologyFunctor.{u, u} A J hJ).obj K)) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((Stacks.LocalCohomology.localCohomologyOnModules.{u, u} A I hI).obj
            (ModuleCat.of A A)),
          (Dualizing.derivedPowerTorsionProperty A (J + I) (Submodule.FG.sup hJ hI)).ι.obj
            ((Dualizing.localCohomologyFunctor.{u, u} A (J + I)
              (Submodule.FG.sup hJ hI)).obj K)) :=
  (derivedCompletionLocalCohomologySupIso A I J hI hJ f hf).app K ≪≫
    derivedCompletionIsoDerivedHomLocalCohomology A I hI f hf _

end Stacks.Algebraization

end
