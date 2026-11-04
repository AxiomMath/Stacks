module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalExcision
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartConverse
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedIsoOpenImmersionCover

/-!
# The diagonal condition is local on the diagonal open

Let `W` be a diagonal open of `f : X ⟶ S`, with diagonal `Δ : X ⟶ W`, and let `(K, ξ)` be a pair
as in Stacks 0E2T. Both `Δ_*𝒪_X` and `R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W) = Δ_* R ℰom(𝒪_X, -)`
(Stacks 0A77) are supported on `Δ(X)`, so their derived pullbacks to an open missing `Δ(X)`
vanish. Hence the map `Δ_*𝒪_X ⟶ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)` defined by `ξ` is an isomorphism
as soon as its derived pullbacks along a family of open immersions whose images cover `Δ(X)` are.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isZero_derivedPullback_pushforward`: vanishing off
  the diagonal.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_of_cover`: the local criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- A module on a scheme all of whose stalks vanish is zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalk {Y : Scheme.{u}}
    (M : Y.Modules)
    (h : ∀ y : Y, IsZero (TopCat.Presheaf.stalk (X := Y.toRingedSpace.carrier) M.val.presheaf y)) :
    IsZero M := by
  have : IsIso (0 : M ⟶ M) := Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _
    fun y => isIso_of_source_target_iso_zero _ (h y).isoZero (h y).isoZero
  exact ((isIsoZero_iff_source_target_isZero _ _).1 this).1

/-- An object of a derived category all of whose cohomology objects vanish is zero. -/
theorem _root_.CategoryTheory.DerivedCategory.isZero_of_isZero_homology {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] (T : DerivedCategory C)
    (h : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj T)) : IsZero T := by
  have : IsIso (0 : T ⟶ T) := (DerivedCategory.isIso_iff (C := C) _).2 fun n =>
    isIso_of_source_target_iso_zero _ (h n).isoZero (h n).isoZero
  exact ((isIsoZero_iff_source_target_isZero _ _).1 this).1

/-- **Derived pushforwards along `Δ` vanish off the diagonal.** The derived pullback of `Δ_*T` to
an open whose image misses `Δ(X)` is zero. -/
theorem isZero_derivedPullback_pushforward {Z : Scheme.{u}} (c : Z ⟶ D.W) [IsOpenImmersion c]
    (hc : ∀ z : Z, c.base z ∉ Set.range D.diag.base) (T : DerivedCategory X.Modules) :
    IsZero ((derivedPullback c.toLRSHom.toShHom).obj
      ((RingedSpaceModuleAdjunction.modulePushforward
        D.diagQuotient.i).mapDerivedCategory.obj T)) := by
  refine IsZero.of_iso ?_ ((Scheme.Modules.derivedRestrictIsoDerivedPullback c).app _).symm
  refine DerivedCategory.isZero_of_isZero_homology _ fun n => ?_
  refine IsZero.of_iso ?_ ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (Scheme.Modules.restrictFunctor c) n).app _)
  refine IsZero.of_iso ?_ ((Scheme.Modules.restrictFunctor c).mapIso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i) n).app T))
  refine Scheme.Modules.isZero_of_isZero_stalk _ fun z => ?_
  exact IsZero.of_iso (@AddCommGrpCat.isZero_of_subsingleton _
    (subsingleton_stalk_pushforward_of_notMemRange' D.diag
      ((DerivedCategory.homologyFunctor X.Modules n).obj T) (c.base z) (hc z)))
    ((Scheme.Modules.restrictStalkNatIso c z).app _)

/-- `R SheafHom(Δ_*𝒪_X, L)` is `Δ_* R ℰom(𝒪_X, L)` (Stacks 0A77). -/
def derivedSheafHomDiagonalObjectIso (L : DerivedCategory D.W.Modules) :
    ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj L ≅
      (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).mapDerivedCategory.obj
        (D.diagQuotient.derivedSheafHomExactSupport.obj L) :=
  (((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).mapIso D.diagonalObjectIso.op).app L).symm ≪≫
    (D.diagQuotient.derivedSheafHomExactSupportPushforwardNatIso.app L).symm

/-- **The diagonal condition is local on the diagonal open.** If the derived pullbacks of the map
`Δ_*𝒪_X ⟶ R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W)` defined by `ξ` along a family of open immersions whose
images cover `Δ(X)` are isomorphisms, then so is that map. -/
theorem isIso_diagonalAction_of_cover (K : DerivedCategory X.Modules)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) {I : Type*} {Z : I → Scheme.{u}}
    (j : ∀ i, Z i ⟶ D.W) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ x : X, ∃ i, D.diag.base x ∈ Set.range (j i).base)
    (h : ∀ i, IsIso ((derivedPullback (j i).toLRSHom.toShHom).map (D.diagonalAction K ξ))) :
    IsIso (D.diagonalAction K ξ) := by
  let C : D.W.Opens :=
    ⟨(Set.range D.diag.base)ᶜ, D.diag.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let Z' : Option I → Scheme.{u} := fun o => o.elim C.toScheme Z
  let j' : ∀ o, Z' o ⟶ D.W := fun o => match o with
    | none => C.ι
    | some i => j i
  have : ∀ o, IsOpenImmersion (j' o) := fun o => match o with
    | none => inferInstanceAs (IsOpenImmersion C.ι)
    | some i => inferInstanceAs (IsOpenImmersion (j i))
  refine Scheme.Modules.isIso_of_isIso_derivedPullback_openImmersion _ j' (fun y => ?_)
    (fun o => ?_)
  · by_cases hy : y ∈ Set.range D.diag.base
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨i, hi⟩ := hj x
      exact ⟨some i, hi⟩
    · exact ⟨none, ⟨⟨y, hy⟩, rfl⟩⟩
  · match o with
    | none =>
      have hC : ∀ z : C.toScheme, C.ι.base z ∉ Set.range D.diag.base := fun z => z.2
      have h₁ := D.isZero_derivedPullback_pushforward C.ι hC (structureSingle X)
      have h₂ := D.isZero_derivedPullback_pushforward C.ι hC
        (D.diagQuotient.derivedSheafHomExactSupport.obj (D.derivedPullbackProj K))
      exact isIso_of_source_target_iso_zero _
        ((derivedPullback C.ι.toLRSHom.toShHom).mapIso D.diagonalObjectIso ≪≫ h₁.isoZero)
        ((derivedPullback C.ι.toLRSHom.toShHom).mapIso
          (D.derivedSheafHomDiagonalObjectIso _) ≪≫ h₂.isoZero)
    | some i => exact h i

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
