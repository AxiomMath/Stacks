module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeDualOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# The dual of a finite locally free module of rank `r` on a ringed site has rank `r`

Let `X` be a ringed site and `M` an `𝒪_X`-module which is finite locally free of rank `r`: on a
covering of every object, `M` restricts to a coproduct of `r` copies of the structure sheaf (the
rank clause of Stacks 0409). Then the dual `M^∨ = 𝓗om_{𝒪_X}(M, 𝒪_X)` is finite locally free of
rank `r`: on each such member the restriction of the dual is `𝓗om(𝒪^{⊕ r}, 𝒪) = 𝒪^r`, which is
again a coproduct of `r` copies of the structure sheaf. This refines Stacks 0FA7, which records
only the finite local freeness of the dual.

## Main definitions

* `AlgebraicGeometry.RingedSite.internalHomSheafUnitOverIsoFree`: over an object on which `M` is
  a coproduct of `n` copies of the structure sheaf, the restriction of the dual is the universe
  lift of the free module on `n` generators.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_internalHomSheafSmall_unit`: **the dual
  of a module of rank `r` has rank `r`**, on a ringed site of the shape of a small étale site,
  the dual being taken at the module universe of the structure sheaf.

## Implementation notes

The comparison is the one of
`AlgebraicGeometry.RingedSite.isFiniteFree_over_internalHomSheaf_unit`, kept as an isomorphism so
that the number of generators is not forgotten. The small dual is compared with it through the
universe lift of its sections, which is fully faithful; this is why the second statement is made
for `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, where that lift and the one of the comparison
raise to the same universe.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Over an object on which `M` is a coproduct of `n` copies of the structure sheaf, the
restriction of the dual `𝓗om_{𝒪_X}(M, 𝒪_X)` is the universe lift of the free module on `n`
generators. -/
def internalHomSheafUnitOverIsoFree
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : X.C)
    {n : ℕ} (ι : Fin n → (_root_.SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) ⟶ M.over W))
    (hc : IsColimit (Cofan.mk (M.over W) ι)) :
    (internalHomSheaf X M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).over W ≅
      (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)).obj
          (_root_.SheafOfModules.free
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) (ULift.{w} (Fin n))) := by
  classical
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
  have : PreservesFiniteLimits
      (Stacks.SheafOfModules.moduleULift.{max u v w, w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  let eP : internalHomSheaf (X.over W)
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
  let eL : ∏ᶜ (fun _ : Fin n =>
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
  exact internalHomSheafOverIso.{u, v, w, w} X W M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≪≫
      (internalHomSheafULiftIso (X.over W) (M.over W)
        (_root_.SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))).symm ≪≫ eP ≪≫ eL

/-- **The dual of a finite locally free module of rank `r` has rank `r`**, on a ringed site of
the shape of a small étale site, the dual being
`AlgebraicGeometry.RingedSite.internalHomSheafSmall X M 𝒪_X` at the module universe of the
structure sheaf. On a member of a covering on which `M` is a coproduct of `r` copies of the
structure sheaf, so is the restriction of the dual
(`AlgebraicGeometry.RingedSite.internalHomSheafUnitOverIsoFree`). -/
theorem isFiniteLocallyFreeOfRank_internalHomSheafSmall_unit (Y : RingedSite.{u + 1, u, u})
    [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{u}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify Y.J AddCommGrpCat.{u + 1}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [EssentiallySmall.{u} Y.C]
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) {r : ℕ}
    (hM : IsFiniteLocallyFreeOfRank Y M r) :
    IsFiniteLocallyFreeOfRank Y
      (internalHomSheafSmall Y M
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) r := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hM U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨ι, ⟨hc⟩⟩ := hV i
  let e : (Stacks.SheafOfModules.moduleULift.{u + 1, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (V i))).obj
        ((internalHomSheafSmall Y M
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).over (V i)) ≅
      (Stacks.SheafOfModules.moduleULift.{u + 1, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (V i))).obj
          (_root_.SheafOfModules.free
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (V i)) (ULift.{u} (Fin r))) :=
    (SheafOfModules.overFunctor _ (V i)).mapIso
        (internalHomSheafSmallIso Y M
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≪≫
      internalHomSheafUnitOverIsoFree Y M (V i) ι hc
  let e' := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (V i))).preimageIso e
  exact ⟨fun j => (_root_.SheafOfModules.freeCofan
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (V i)) (ULift.{u} (Fin r))).inj
        (Equiv.ulift.symm j) ≫ e'.symm.hom,
    ⟨(Stacks.Sheaves.QcohTypeComparison.isColimitFreeCofanFin
      (R₁ := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (V i)) r).ofIsoColimit
        (Cofan.ext e'.symm (fun _ => rfl))⟩⟩

end AlgebraicGeometry.RingedSite

end
