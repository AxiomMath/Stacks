module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SliceRestrictionDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealLocal
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The derived-completeness condition across a covering family and across an iterated slice

Let `(C, O)` be a ringed site. The predicate
`AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999] tests a complex `K`
object by object: for every object `U` and every section `f` of the sheaf of ideals over `U` it
asks that the Milnor difference `1 - f*shift` be invertible on the countable product of copies
of `K|_U` in `D(O_U)`. [Stacks, Tag 0A0F] says that restriction to a localized ringed site
preserves that condition; see `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete_overIdeal`.

This file proves two properties of the Milnor condition.

1. *Across a covering family.* The Milnor condition at a global section descends from the
   members of a family covering the final object of the site, not merely from the family of
   all objects of the site.
2. *Across an iterated slice.* For an object `U` and an object `W` of the slice over `U`, the
   condition on the iterated slice `(𝒞/U)/W` and the condition on the slice `𝒞/W.left` imply
   each other.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_of_coversTop_isDerivedCompleteAt_over`: the
  Milnor condition `T(K, f) = 0` descends from the members of a covering family, which is
  `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_of_forall_isDerivedCompleteAt_over` with
  the family of *all* objects of the site replaced by one covering the final object.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_of_isDerivedCompleteAt_iteratedSlice`: the
  Milnor condition on the iterated slice gives the Milnor condition on the slice. This is the
  converse of the transport inside
  `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete`, and it is available for the same
  reason: the comparison functor is one half of an equivalence, so it reflects isomorphisms as
  well as preserving them.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_iteratedSlice_of_isDerivedCompleteAt`: the
  other direction, which is the transport that `restrict_isDerivedComplete` performs, isolated
  from the sheaf of ideals so that it applies at one object and one section.

## Implementation notes

All three statements keep to the spelling of the predicate of [Stacks, Tag 0999]: the scalar is
`Stacks.SheafOfModules.terminalSectionToEnd` at the terminal object of the slice, written
`AlgebraicGeometry.RingedSite.overTerminalSmul` for a global section, and the sheaf of rings is
`((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U` rather than
`(Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)`. The two spellings are the same sheaf of
rings but instance search does not pass between them.

The two iterated-slice statements write their scalars with an explicit ascription to
`CategoryTheory.CatCenter`. Without it the elaborator takes the scalar ring to be the declared
type of `Stacks.SheafOfModules.terminalSectionToEnd`, an endomorphism monoid of the identity
functor, and the search for `CommSemiring` on that exceeds the instance budget; with the
ascription the `CommRing` instance of the centre applies at once. The transport itself is
performed on `Stacks.SheafOfModules.InternalHom.sliceModulesEquiv`, the iterated-slice
equivalence of categories of sheaves of modules, whose induced functor on derived categories is
an equivalence by `Stacks.Injectives.mapDerivedCategory_isEquivalence`; the scalar match is
`AlgebraicGeometry.RingedSite.sliceModulesEquiv_functor_map_terminalSectionToEnd`, and the
countable products are preserved because that functor is a right adjoint.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section Descent

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance] linearCatCenterRingSheaf
  isMulCommutative_ringSheaf_over linearCatCenterOver

/-- **The descent of derived completeness from a covering family.** If `T(K|_{V i}, f|_{V i})`
vanishes for every member of a family `V : ι → 𝒞` covering the final object of the site, then
`T(K, f)` vanishes on the site itself. -/
theorem isDerivedCompleteAt_of_coversTop_isDerivedCompleteAt_over
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (hc : ∀ i, IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (V i)).mapDerivedCategory.obj K)
      (overTerminalSmul X h (V i))) :
    IsDerivedCompleteAt K (awaySmul X h) := by
  rw [isDerivedCompleteAt_iff_isIso]
  refine Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory hV _ fun i => ?_
  have hprod := preservesProductsOfShape_nat_overFunctor_mapDerivedCategory X (V i)
  have hpi : IsIso (piComparison
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (V i)).mapDerivedCategory
      (fun _ : ℕ ↦ K)) := inferInstance
  have hiso : IsIso (oneSubSmulShift
      ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (V i)).mapDerivedCategory.obj K)
      (overTerminalSmul X h (V i))) := hc i
  have h1 : IsIso (piComparison
        (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (V i)).mapDerivedCategory
          (fun _ : ℕ ↦ K) ≫
      oneSubSmulShift
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (V i)).mapDerivedCategory.obj K)
        (overTerminalSmul X h (V i))) := inferInstance
  rw [← oneSubSmulShift_map_comp_piComparison
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (V i)).mapDerivedCategory
    (mapDerivedCategory_map_awaySmul_smul_id X h (V i) K)] at h1
  rw [show (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (V i)).mapDerivedCategory.map
        (oneSubSmulShift K (awaySmul X h)) =
      ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (V i)).mapDerivedCategory.map
          (oneSubSmulShift K (awaySmul X h)) ≫
        piComparison
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (V i)).mapDerivedCategory
          (fun _ : ℕ ↦ K)) ≫
        inv (piComparison
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (V i)).mapDerivedCategory
          (fun _ : ℕ ↦ K)) by simp]
  infer_instance

end Descent

section Iterated

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
  isMulCommutative_ringSheaf_obj'

/-- Sheaves of modules on a slice site are linear over the centre of their own category, which
is the linear structure the derived-completeness predicate of [Stacks, Tag 0999] uses. This is
`AlgebraicGeometry.RingedSite.linearCatCenterOver` at the second spelling of the base. -/
abbrev linearCatCenterOverLeft (X : RingedSite.{u, u, u}) (W : X.C) :
    Linear (CatCenter (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W)))
      (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W)) :=
  Linear.ofRingMorphism (RingHom.id _)

/-- The same linear structure on the second spelling of an iterated slice. -/
abbrev linearCatCenterIterated (X : RingedSite.{u, u, u}) (U : X.C) (W : Over U) :
    Linear (CatCenter (SheafOfModules.{u}
        ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)))
      (SheafOfModules.{u} ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)) :=
  Linear.ofRingMorphism (RingHom.id _)

attribute [local instance] linearCatCenterOverLeft linearCatCenterIterated

variable (X : RingedSite.{u, u, u}) (U : X.C) (W : Over U)

/-- The derived category of sheaves of modules on the slice `𝒞/W.left` has countable
products. -/
local instance hasProductsSlice :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left))) :=
  hasProductsOfShape_nat_derivedCategory_over.{u, u, u} X W.left

/-- The derived category of sheaves of modules on the iterated slice `(𝒞/U)/W` has countable
products. -/
local instance hasProductsIteratedSlice :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u}
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W))) :=
  hasProductsOfShape_nat_derivedCategory_over.{u, u, u} (X.over U) W

/-- The Milnor condition on the slice `𝒞/W.left` and on the iterated slice `(𝒞/U)/W` at the same
section are equivalent. -/
private theorem isDerivedCompleteAt_iff_iteratedSlice
    (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op W.left))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left).mapDerivedCategory.obj K)
      (show CatCenter (SheafOfModules.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)) from
        Stacks.SheafOfModules.terminalSectionToEnd
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)
          (Over.mk (𝟙 W.left)) Over.mkIdTerminal g) ↔
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K))
      (show CatCenter (SheafOfModules.{u}
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)) from
        Stacks.SheafOfModules.terminalSectionToEnd
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)
          (Over.mk (𝟙 W)) Over.mkIdTerminal g) := by
  let E := Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, u, u, u} X U W
  let Φ := E.functor
  have hΦadd : Φ.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{u}
      (F := (Over.iteratedSliceEquiv W).functor) (𝟙 _)).Additive
  let := hΦadd
  have hΦeq : Φ.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  let := hΦeq
  have hΨadd : E.inverse.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{u}
      (F := (Over.iteratedSliceEquiv W).inverse) (𝟙 _)).Additive
  let := hΨadd
  have hΦlim : PreservesFiniteLimits Φ := inferInstance
  let := hΦlim
  have hΦcolim : PreservesFiniteColimits Φ := inferInstance
  let := hΦcolim
  have hpl : PreservesLimitsOfShape (Discrete ℕ) Φ.mapDerivedCategory := by
    have adjD : E.inverse.mapDerivedCategory ⊣ Φ.mapDerivedCategory :=
      CategoryTheory.Adjunction.mapDerivedCategory E.symm.toAdjunction
    have := adjD.rightAdjoint_preservesLimits
    infer_instance
  let := hpl
  have hΦD : Φ.mapDerivedCategory.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence Φ
  let := hΦD
  set aL := Stacks.SheafOfModules.terminalSectionToEnd
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)
    (Over.mk (𝟙 W.left)) Over.mkIdTerminal g with haL
  set aW := Stacks.SheafOfModules.terminalSectionToEnd
    ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)
    (Over.mk (𝟙 W)) Over.mkIdTerminal g with haW
  have hmap : ∀ M : SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left),
      Φ.map (aL.app M) = aW.app (Φ.obj M) :=
    sliceModulesEquiv_functor_map_terminalSectionToEnd X U W g
  have hsmulD : ∀ L : DerivedCategory (SheafOfModules.{u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)),
      Φ.mapDerivedCategory.map (aL • 𝟙 L) = aW • 𝟙 (Φ.mapDerivedCategory.obj L) :=
    fun L => Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id
      Φ aL aW
      (fun Z => Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex Φ aL aW
        (fun M => (congrArg Φ.map (Category.comp_id (aL.app M))).trans
          ((hmap M).trans (Category.comp_id (aW.app (Φ.obj M))).symm))
        (ComplexShape.up ℤ) Z) L
  let i₁ := Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left) Φ
  let i₂ := Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
    (SheafOfModules.overFunctor.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W)
  set N := (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left).mapDerivedCategory.obj K
  have e := AlgebraicGeometry.RingedSite.isDerivedCompleteAt_iff_of_iso
    ((i₁.app K).symm ≪≫ i₂.app K) aW
  refine ⟨fun h => e.mp (isDerivedCompleteAt_map_of_smul_id Φ.mapDerivedCategory (hsmulD N) h),
    fun hK => ?_⟩
  have hK' : IsDerivedCompleteAt (Φ.mapDerivedCategory.obj N) aW := e.mpr hK
  rw [isDerivedCompleteAt_iff_isIso] at hK' ⊢
  have hpi : IsIso (piComparison Φ.mapDerivedCategory (fun _ : ℕ ↦ N)) := inferInstance
  have h1 : IsIso (piComparison Φ.mapDerivedCategory (fun _ : ℕ ↦ N) ≫
      oneSubSmulShift (Φ.mapDerivedCategory.obj N) aW) := inferInstance
  rw [← oneSubSmulShift_map_comp_piComparison Φ.mapDerivedCategory (hsmulD N)] at h1
  have h2 : IsIso (Φ.mapDerivedCategory.map (oneSubSmulShift N aL)) :=
    IsIso.of_isIso_comp_right _ (piComparison Φ.mapDerivedCategory (fun _ : ℕ ↦ N))
  exact isIso_of_reflects_iso (oneSubSmulShift N aL) Φ.mapDerivedCategory

/-- **The Milnor condition on the iterated slice gives the Milnor condition on the slice.** Let
`U` be an object of `𝒞`, let `W` be an object of `𝒞/U` and let `g` be a section of `𝒪` over
`W.left`. If the restriction of `K` to the iterated slice `(𝒞/U)/W` is derived complete at `g`,
then so is its restriction to the slice `𝒞/W.left`. -/
theorem isDerivedCompleteAt_of_isDerivedCompleteAt_iteratedSlice
    (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op W.left))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K))
      (show CatCenter (SheafOfModules.{u}
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)) from
        Stacks.SheafOfModules.terminalSectionToEnd
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)
          (Over.mk (𝟙 W)) Over.mkIdTerminal g)) :
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left).mapDerivedCategory.obj K)
      (show CatCenter (SheafOfModules.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)) from
        Stacks.SheafOfModules.terminalSectionToEnd
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)
          (Over.mk (𝟙 W.left)) Over.mkIdTerminal g) := by
  exact (isDerivedCompleteAt_iff_iteratedSlice X U W g K).mpr hK

/-- **The Milnor condition on the slice gives the Milnor condition on the iterated slice.** Let
`U` be an object of `𝒞`, let `W` be an object of `𝒞/U` and let `g` be a section of `𝒪` over
`W.left`. If the restriction of `K` to the slice `𝒞/W.left` is derived complete at `g`, then so
is its restriction to the iterated slice `(𝒞/U)/W`. -/
theorem isDerivedCompleteAt_iteratedSlice_of_isDerivedCompleteAt
    (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op W.left))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) W.left).mapDerivedCategory.obj K)
      (show CatCenter (SheafOfModules.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)) from
        Stacks.SheafOfModules.terminalSectionToEnd
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over W.left)
          (Over.mk (𝟙 W.left)) Over.mkIdTerminal g)) :
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K))
      (show CatCenter (SheafOfModules.{u}
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)) from
        Stacks.SheafOfModules.terminalSectionToEnd
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)
          (Over.mk (𝟙 W)) Over.mkIdTerminal g) := by
  exact (isDerivedCompleteAt_iff_iteratedSlice X U W g K).mp hK

end Iterated

end AlgebraicGeometry.RingedSite

end
