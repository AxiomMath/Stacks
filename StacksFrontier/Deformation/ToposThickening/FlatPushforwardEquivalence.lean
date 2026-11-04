module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.PullbackModuleFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesHomEq
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction

/-!
# Flatness of a direct image along an equivalence of topoi

Let `i : Sh(C) ⟶ Sh(D)` be a morphism of topoi whose direct image on sheaves of sets is an
equivalence, let `𝒜` be a sheaf of commutative rings on `C` and let `ℳ` be an `𝒜`-module. Then
`i_*ℳ` is flat over `i_*𝒜` if and only if `ℳ` is flat over `𝒜`. This is how the flatness over
the base of a quotient on `X_T` is read on the thickening `X_{T'}`, whose small étale topos is
equivalent to that of `X_T`, in the deformation theory of quotients (Stacks 0CZU, 0CZV).

## Main results

* `Deformation.ToposThickening.isFlat_pushforwardModuleFunctor_iff`: flatness of the direct
  image along an equivalence of topoi.
* `Deformation.ToposThickening.isFlatOverBase_pushforward_iff`: the same for
  `Deformation.ToposThickening.IsFlatOverBase`.

## Implementation notes

The proof reads `(Sh(C), 𝒜) ⟶ (Sh(D), i_*𝒜)` as a morphism of ringed topoi with identity
structure map, so that flatness is invariant under its pullback
(`AlgebraicGeometry.RingedToposHom.isFlat_iff_pullbackModules`), and the direct image, being
fully faithful, has the pullback as a left inverse.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u v' u' w vS uS wS

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The morphism of ringed topoi `(Sh(C), 𝒜) ⟶ (Sh(D), i_*𝒜)` with identity structure map. -/
noncomputable abbrev pushforwardRingToposHom (i : RingedToposHom X Y)
    (A : Sheaf X.J CommRingCat.{w}) :
    RingedToposHom (reshape X A) (reshape Y ((pushforwardCommRingFunctor i.toToposHom).obj A)) where
  toToposHom := i.toToposHom
  fSharp := 𝟙 _

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The direct image of modules along `pushforwardRingToposHom i A` is, by definition, the direct
image of modules along the underlying morphism of topoi of `i`. -/
theorem pushforwardRingToposHom_pushforwardModules (i : RingedToposHom X Y)
    (A : Sheaf X.J CommRingCat.{w}) :
    (pushforwardRingToposHom i A).pushforwardModules =
      pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf A) := rfl

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Flatness of a direct image along an equivalence of topoi.** If the direct image of
sheaves of sets along `i` is an equivalence, an `𝒜`-module `ℳ` is flat if and only if `i_*ℳ` is
flat over `i_*𝒜`. -/
theorem isFlat_pushforwardModuleFunctor_iff (i : RingedToposHom X Y)
    [i.toToposHom.pushforward.IsEquivalence] (A : Sheaf X.J CommRingCat.{w})
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf A)) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := (pushforwardCommRingFunctor i.toToposHom).obj A)
        ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf A)).obj M) ↔
      AlgebraicGeometry.SheafOfModules.IsFlat (O := A) M := by
  have : (pushforwardRingToposHom i A).toToposHom.pushforward.IsEquivalence :=
    inferInstanceAs i.toToposHom.pushforward.IsEquivalence
  have : IsIso (pushforwardRingToposHom i A).fSharp := inferInstanceAs (IsIso (𝟙 _))
  have adj := (pushforwardRingToposHom i A).pullbackAdjPushforwardModulesViaComparison
  have : (pushforwardRingToposHom i A).pushforwardModules.Full := by
    rw [pushforwardRingToposHom_pushforwardModules]
    exact Stacks.Sheaves.ToposPushforward.full_pushforwardModuleFunctor _ _
  have : (pushforwardRingToposHom i A).pushforwardModules.Faithful := by
    rw [pushforwardRingToposHom_pushforwardModules]
    exact Stacks.Sheaves.ToposPushforward.faithful_pushforwardModuleFunctor _ _
  have e : ((pushforwardRingToposHom i A).toModulesHom.pullbackModules).obj
      ((pushforwardRingToposHom i A).pushforwardModules.obj M) ≅ M := by
    rw [← (pushforwardRingToposHom i A).toRingedToposModulesHom_eq_toModulesHom]
    exact asIso (adj.counit.app M)
  refine ((pushforwardRingToposHom i A).isFlat_iff_pullbackModules
    ((pushforwardRingToposHom i A).pushforwardModules.obj M)).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ e h
  · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ e.symm h

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Flatness over the base of a module pushed forward along an equivalence of topoi.** If the
direct image of sheaves of sets along `i` is an equivalence, `i_*𝒬` is flat over `i_*f⁻¹O_ℬ`
(`Deformation.ToposThickening.IsFlatOverBase`) if and only if `𝒬` is flat over `f⁻¹O_ℬ`. -/
theorem isFlatOverBase_pushforward_iff {S : RingedTopos.{vS, uS, wS}}
    [S.J.HasSheafCompose (forget RingCat.{wS})]
    [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
    (i : RingedToposHom X Y) [i.toToposHom.pushforward.IsEquivalence] (f : RingedToposHom X S)
    (Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsFlatOverBase i f ((pushforwardModuleFunctor i.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj Q) ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            f.fSharpInverseImage)).obj Q) := by
  have hring : (sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
      ((pushforwardCommRingFunctor i.toToposHom).map f.fSharpInverseImage) =
        Stacks.Sheaves.ToposPullback.pullbackRingSheafMap Y.J i.toToposHom.pushforward
          ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage) :=
    Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap _ _ _
  have e := Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso Y.J
    i.toToposHom.pushforward
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map f.fSharpInverseImage) Q
  unfold IsFlatOverBase
  rw [hring]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (isFlat_pushforwardModuleFunctor_iff i _ _).1
      (Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ e h)
  · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _ e.symm
      ((isFlat_pushforwardModuleFunctor_iff i _ _).2 h)

end Deformation.ToposThickening

end
