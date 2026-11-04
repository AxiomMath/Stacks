module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentInternalHomSmallOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a finite locally free module on a ringed site is finite locally free

Let `X` be a ringed site and let `M` be an `𝒪_X`-module which is finite locally free in the
sense of Stacks 03DL(2). Then the dual `M^∨ = 𝓗om_{𝒪_X}(M, 𝒪_X)` is finite locally free too
(Stacks 0FA7).

## Main definitions

* `Stacks.SheafOfModules.moduleULiftSectionsEquiv`: the sections of a universe lift of a sheaf
  of modules are the sections of the module, linearly and naturally.
* `AlgebraicGeometry.RingedSite.freeIsoPiUnit`: the free module on `ULift (Fin n)` over a slice
  is the product of `n` copies of the structure sheaf of that slice.

## Main results

* `Stacks.SheafOfModules.isFiniteFree_moduleULift` and
  `Stacks.SheafOfModules.isFiniteFree_of_moduleULift`: finite freeness in the sense of
  Stacks 03DE(2) is unchanged by a universe lift of the sections, in both directions, and
  `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_moduleULift_iff` is the same for
  Stacks 03DL(2).
* `AlgebraicGeometry.RingedSite.isFiniteFree_over_internalHomSheaf_unit`: over an object on
  which `M` is finite free, the restriction of `𝓗om_{𝒪_X}(M, 𝒪_X)` is finite free.
* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOnSite_internalHomSheaf_unit`: **the dual of
  a finite locally free module on a ringed site is finite locally free**, for
  `AlgebraicGeometry.RingedSite.internalHomSheaf`, whose sections live in `max u v w`.
* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOnSite_internalHomSheafSmall_unit`: the same
  for `AlgebraicGeometry.RingedSite.internalHomSheafSmall`, the dual read at the module universe
  of the coefficient rings on an essentially small site.

## References

* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m t

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **The sections of a universe lift of a sheaf of modules are the sections of the module**, as
a linear equivalence over the sections of the ring sheaf: the lift is `ULift` objectwise. -/
def moduleULiftSectionsEquiv (A : _root_.SheafOfModules.{m} R) (U : Cᵒᵖ) :
    (A.val.obj U : Type m) ≃ₗ[R.obj.obj U]
      (((moduleULift.{t, m} R).obj A).val.obj U : Type (max m t)) where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Finite freeness survives a universe lift of the sections.** -/
theorem isFiniteFree_moduleULift {A : _root_.SheafOfModules.{m} R}
    (hA : _root_.SheafOfModules.IsFiniteFree R A) :
    _root_.SheafOfModules.IsFiniteFree R ((moduleULift.{t, m} R).obj A) := by
  obtain ⟨n, P, ι, hc, e, he⟩ := hA
  exact ⟨n, P, ι, hc, fun U ↦ (e U).trans (moduleULiftSectionsEquiv.{_, _, _, _, t} A U),
    fun f x ↦ congrArg ULift.up (he f x)⟩

/-- **Finite freeness descends along a universe lift of the sections**, the converse of
`Stacks.SheafOfModules.isFiniteFree_moduleULift`. -/
theorem isFiniteFree_of_moduleULift {A : _root_.SheafOfModules.{m} R}
    (hA : _root_.SheafOfModules.IsFiniteFree R ((moduleULift.{t, m} R).obj A)) :
    _root_.SheafOfModules.IsFiniteFree R A := by
  obtain ⟨n, P, ι, hc, e, he⟩ := hA
  exact ⟨n, P, ι, hc, fun U ↦ (e U).trans (moduleULiftSectionsEquiv.{_, _, _, _, t} A U).symm,
    fun f x ↦ congrArg ULift.down (he f x)⟩

/-- **Finite local freeness in the sense of Stacks 03DL(2) is unchanged by a universe lift of the
sections.** -/
theorem isFiniteLocallyFreeOnSite_moduleULift_iff (A : _root_.SheafOfModules.{m} R) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite ((moduleULift.{t, m} R).obj A) ↔
      _root_.SheafOfModules.IsFiniteLocallyFreeOnSite A := by
  refine ⟨fun h U ↦ ?_, fun h U ↦ ?_⟩ <;> obtain ⟨I, V, f, hf, hV⟩ := h U
  · exact ⟨I, V, f, hf, fun i ↦ isFiniteFree_of_moduleULift.{_, _, _, _, t} (hV i)⟩
  · exact ⟨I, V, f, hf, fun i ↦ isFiniteFree_moduleULift.{_, _, _, _, t} (hV i)⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The free module on `ULift (Fin n)` over a slice of a ringed site is the product of `n`
copies of the structure sheaf of that slice.** -/
noncomputable def freeIsoPiUnit (W : X.C) (n : ℕ) :
    _root_.SheafOfModules.free
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) (ULift.{w} (Fin n)) ≅
      ∏ᶜ (fun _ : Fin n =>
        _root_.SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) := by
  classical
  letI : HasFiniteLimits
      (_root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    _root_.SheafOfModules.Finite.hasFiniteLimits _
  letI : HasBiproduct (fun _ : Fin n =>
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    HasBiproduct.of_hasProduct _
  exact (Stacks.Sheaves.QcohTypeComparison.isColimitFreeCofanFin
        (R₁ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) n).coconePointUniqueUpToIso
      (coproductIsCoproduct _) ≪≫
    (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _

/-- **Over an object on which `M` is finite free, the restriction of the dual
`𝓗om_{𝒪_X}(M, 𝒪_X)` is finite free.** -/
theorem isFiniteFree_over_internalHomSheaf_unit
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : X.C)
    (hW : _root_.SheafOfModules.IsFiniteFree
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) (M.over W)) :
    _root_.SheafOfModules.IsFiniteFree
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
      ((internalHomSheaf X M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).over W) := by
  classical
  obtain ⟨n, ι, ⟨hc⟩⟩ :=
    (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) (M.over W)).1 hW
  have : PreservesColimitsOfShape (Discrete (ULift.{w} (Fin n)))
      (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    Stacks.SheafOfModules.preservesColimitsOfShape_moduleULift
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) (ULift.{w} (Fin n))
  have : PreservesColimitsOfShape (Discrete (Fin n))
      (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift.{w, 0})) _
  have hcL : IsColimit (Cofan.mk
      ((Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj (M.over W))
      (fun i ↦ (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).map (ι i))) :=
    Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk (M.over W) ι) (isColimitOfPreserves _ hc)
  have eP : internalHomSheaf (X.over W)
        ((Stacks.SheafOfModules.moduleULift.{max u v w, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj (M.over W))
        ((Stacks.SheafOfModules.moduleULift.{max u v w, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))) ≅
      ∏ᶜ (fun _ : Fin n =>
        (Stacks.SheafOfModules.moduleULift.{max u v w, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))) :=
    (isLimitInternalHomSheafFan.{max u v, v, w, w} (X.over W) _ _
        hcL).conePointUniqueUpToIso (productIsProduct _) ≪≫
      Pi.mapIso (fun _ ↦ internalHomSheafULiftUnitIso (X.over W) _)
  have : PreservesFiniteLimits
      (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  have eL : ∏ᶜ (fun _ : Fin n =>
        (Stacks.SheafOfModules.moduleULift.{max u v w, w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))) ≅
      (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj
          (_root_.SheafOfModules.free
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
            (ULift.{w} (Fin n))) :=
    (PreservesProduct.iso _ (fun _ : Fin n =>
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))).symm ≪≫
      Functor.mapIso _ (freeIsoPiUnit X W n).symm
  exact Stacks.SheafOfModules.Intrinsic.isFiniteFree_of_iso
    (internalHomSheafOverIso.{u, v, w, w} X W M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≪≫
      (internalHomSheafULiftIso (X.over W) (M.over W)
        (_root_.SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))).symm ≪≫ eP ≪≫ eL).symm
    (Stacks.SheafOfModules.isFiniteFree_moduleULift.{_, _, _, _, max u v w}
      (Stacks.Sheaves.QcohTypeComparison.isFiniteFree_free_ulift
        (R₁ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) n))

/-- **Stacks 0FA7 on a ringed site: the dual of a finite locally free module is finite locally
free.** Here the dual is `AlgebraicGeometry.RingedSite.internalHomSheaf X M 𝒪_X`, whose
sections live in `max u v w`. -/
theorem isFiniteLocallyFreeOnSite_internalHomSheaf_unit
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      (internalHomSheaf X M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hM U
  exact ⟨I, V, f, hf, fun i ↦ isFiniteFree_over_internalHomSheaf_unit X M (V i) (hV i)⟩

/-- **Stacks 0FA7 on an essentially small ringed site, at the module universe of the coefficient
rings.** The dual `AlgebraicGeometry.RingedSite.internalHomSheafSmall X M 𝒪_X` of a finite
locally free module is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_internalHomSheafSmall_unit [EssentiallySmall.{w} X.C]
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      (internalHomSheafSmall X M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_moduleULift_iff.{_, _, _, _, max u v} _).1
    (Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso
      (internalHomSheafSmallIso X M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm
      (isFiniteLocallyFreeOnSite_internalHomSheaf_unit X M hM))

end AlgebraicGeometry.RingedSite

end
