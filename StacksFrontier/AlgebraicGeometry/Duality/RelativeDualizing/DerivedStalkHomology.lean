module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# Stalks of the cohomology sheaves of a dualizing complex

Let `X` be a locally Noetherian scheme and `K` a dualizing complex on `X` with associated dimension
function `δ` ([Stacks, Tag 0AWF], `Stacks.Duality.associatedShiftFunction`). The derived stalk
`ω^•_{X,x}` of `K` at `x`, shifted by `-δ(x)`, is a normalized dualizing complex over `𝒪_{X,x}`,
and since taking stalks is exact the stalk at `x` of the cohomology sheaf `H^i(K)` is
`H^i(ω^•_{X,x}) = H^{i + δ(x)}(ω^•_{X,x}⟦-δ(x)⟧)`. The bounds of [Stacks, Tag 0A7U] for a
normalized dualizing complex over a local ring of dimension `d` then say that this stalk vanishes
for `i + δ(x) < -d`, and that for `i + δ(x) = -d` it is the canonical module of `𝒪_{X,x}`. This
file records these facts, together with two comparisons for stalks of sheaves of modules on a
scheme.

## Main results

* `Stacks.Duality.stalkHomologyIso` — the stalk of `H^i(K)` is the cohomology of the derived stalk
  of any complex representing `K`.
* `Stacks.Duality.isZero_of_subsingleton_modulesStalkFunctor` — a sheaf of modules all of whose
  stalks vanish is zero.
* `Stacks.Duality.stalkLinearEquivModulesStalkFunctor` — the two `𝒪_{X,x}`-module structures on the
  stalk of a sheaf of modules, the one of `AlgebraicGeometry.SheafHasPropertySk` and the one of
  `Stacks.Duality.modulesStalkFunctor`, agree.
* `Stacks.Duality.stalk_homology_of_isDualizingComplex` — the vanishing and the canonical module
  above.

## Implementation notes

The stalk functor `Stacks.Duality.modulesStalkFunctor` is exact
(`Stacks.Duality.modulesStalkFunctor_preservesFiniteLimits` and its colimit companion), so it
preserves homology, and the comparison of `Stacks.Duality.stalkHomologyIso` is the one of
`CategoryTheory.ShortComplex.mapHomologyIso`, read through `DerivedCategory.homologyFunctorFactors`
on both sides. The two module structures on a stalk have the same underlying abelian group, the
colimit of the sections, and are characterised by the action of sections on germs
(`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul` and
`Stacks.Duality.schemeStalkModuleFunctor_germ_smul`), so the identity is linear.

The derived categories of modules over rings are at `CategoryTheory.HasDerivedCategory.standard`,
which `Dualizing.IsNormalizedDualizingComplex` forces; `D(𝒪_X)` is an instance argument.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Duality

section StalkHomology

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- The stalk at `x` of the cohomology sheaf `H^i(K)` is the cohomology of the derived stalk of any
complex representing `K`: the stalk functor is exact. -/
def stalkHomologyIso (x : X) {K : DerivedCategory X.Modules} (E : CochainComplex X.Modules ℤ)
    (e : DerivedCategory.Q.obj E ≅ K) (i : ℤ) :
    (modulesStalkFunctor x).obj ((DerivedCategory.homologyFunctor X.Modules i).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
        (derivedStalkOfComplex x E) :=
  (modulesStalkFunctor x).mapIso
      ((DerivedCategory.homologyFunctor X.Modules i).mapIso e.symm ≪≫
        (DerivedCategory.homologyFunctorFactors X.Modules i).app E) ≪≫
    ((E.sc i).mapHomologyIso (modulesStalkFunctor x)).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (X.presheaf.stalk x)) i).app
      (((schemeStalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)).symm

end StalkHomology

/-- A sheaf of modules on a scheme all of whose stalks vanish is zero. -/
theorem isZero_of_subsingleton_modulesStalkFunctor {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, Subsingleton ((modulesStalkFunctor x).obj M)) : IsZero M :=
  Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero X.ringCatSheaf M
    fun x => by
      have : Subsingleton ↑(TopCat.Presheaf.stalk M.val.presheaf x) := h x
      exact AddCommGrpCat.isZero_of_subsingleton _

/-- The `𝒪_{X,x}`-module structure on the stalk of a sheaf of modules used by
`AlgebraicGeometry.SheafHasPropertySk` agrees with the one of `Stacks.Duality.modulesStalkFunctor`:
both are characterised by the action of sections on germs. -/
theorem modulesStalkFunctor_smul_eq {X : Scheme.{u}} (M : X.Modules) (x : X)
    (r : X.presheaf.stalk x)
    (m : ↑(TopCat.Presheaf.stalk
      (SheafOfModules.val (R := structureSheafRing X.toRingedSpace) M).presheaf x)) :
    (show (modulesStalkFunctor x).obj M from r • m) =
      r • (show (modulesStalkFunctor x).obj M from m) := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (SheafOfModules.val (R := structureSheafRing X.toRingedSpace) M).presheaf m
  let W : X.Opens := U ⊓ V
  have hW : x ∈ W := ⟨hxU, hxV⟩
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left : W ⟶ U) x hW a,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right : W ⟶ V) x hW n]
  exact (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X.toRingedSpace
    (SheafOfModules.val (R := structureSheafRing X.toRingedSpace) M) x W hW _ _).symm.trans
    (schemeStalkModuleFunctor_germ_smul x M W hW _ _)

/-- The stalk of a sheaf of modules with the module structure of
`AlgebraicGeometry.SheafHasPropertySk` is linearly equivalent to its image under
`Stacks.Duality.modulesStalkFunctor`. -/
def stalkLinearEquivModulesStalkFunctor {X : Scheme.{u}} (M : X.Modules) (x : X) :
    ↑(TopCat.Presheaf.stalk
      (SheafOfModules.val (R := structureSheafRing X.toRingedSpace) M).presheaf x) ≃ₗ[
        X.presheaf.stalk x] (modulesStalkFunctor x).obj M where
  toFun a := a
  invFun a := a
  map_add' _ _ := rfl
  map_smul' r m := modulesStalkFunctor_smul_eq M x r m
  left_inv _ := rfl
  right_inv _ := rfl

section Pointwise

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **The cohomology sheaves of a dualizing complex at a point.** Let `K` be a dualizing complex
with associated dimension function `δ`, let `x ∈ X`, and let `m` and `d` be integers with
`dim 𝒪_{X,x} = d = m - δ(x)`. Then the stalk of `H^i(K)` at `x` vanishes for `i < -m`, and the
stalk of `H^{-m}(K)` at `x` is the canonical module `H^{-d}(L)` of a normalized dualizing complex
`L` over `𝒪_{X,x}`. -/
theorem stalk_homology_of_isDualizingComplex {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) (m : ℤ) (d : ℕ)
    (hd : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞))
    (hdm : (d : ℤ) = m - associatedShiftFunction K x) :
    (∀ i < -m, Subsingleton
      ((modulesStalkFunctor x).obj ((DerivedCategory.homologyFunctor X.Modules i).obj K))) ∧
    ∃ L : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)),
      _root_.Dualizing.IsNormalizedDualizingComplex.{u, u} L ∧
        Nonempty ((modulesStalkFunctor x).obj
            ((DerivedCategory.homologyFunctor X.Modules (-m)).obj K) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) (-(d : ℤ))).obj
            L) := by
  set a := associatedShiftFunction K x with ha
  let E := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hL := ((isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK).2.1
    x E ⟨e⟩ a).mpr rfl
  set L := (derivedStalkOfComplex x E)⟦-a⟧ with hLdef
  have hshift : ∀ i j : ℤ, -a + j = i →
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) j).obj L ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          (derivedStalkOfComplex x E)) := fun i j h =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).shiftIso
      (-a) j i h).app _
  refine ⟨fun i hi => ?_, L, hL, ⟨stalkHomologyIso x E e (-m) ≪≫
    (hshift (-m) (-(d : ℤ)) (by omega)).symm⟩⟩
  have hzero := _root_.Dualizing.isZero_homology_of_lt_neg_ringKrullDim L hL d hd (a + i)
    (by omega)
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((hzero.of_iso (hshift i (a + i) (by omega)).symm).of_iso (stalkHomologyIso x E e i))

end Pointwise

end Stacks.Duality

end
