module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Critère de platitude par fibres for a morphism of schemes

The fibrewise criterion for flatness and the relative flat locus are stated in this library for a
quasi-coherent module on the source; this file reads both off at the structure sheaf, which is the
form in which the Stacks Project states them for a morphism.

Let `f : X ⟶ Y` be a morphism of schemes over a base, written as `g : Y ⟶ S` (or `pY : Y ⟶ S`),
so that `X` lies over `S` through `f ≫ g`.

* If `S`, `X`, `Y` are locally Noetherian, `X` is flat over `S` and every induced morphism on
  fibres `X_s ⟶ Y_s` is flat, then `f` is flat; if `f` is moreover surjective, then `Y` is flat
  over `S`.
* If `X` is locally of finite presentation and flat over `S` and `Y` is locally of finite type
  over `S`, then the locus of points of `X` at which `f` is flat is open, and its formation
  commutes with an arbitrary base change `S' ⟶ S`.

## Main results

* `AlgebraicGeometry.flat_of_flat_fiberHom` and
  `AlgebraicGeometry.flat_of_flat_fiberHom_of_surjective` are the two conclusions of the
  Noetherian fibrewise criterion.
* `AlgebraicGeometry.isOpen_setOf_isFlatAt_of_locallyOfFinitePresentation_comp` is openness of
  the relative flat locus of `f`.
* `AlgebraicGeometry.setOf_isFlatAt_baseChange` identifies that locus after an arbitrary base
  change with the preimage of the original one.

## Implementation notes

The structure sheaf enters as `SheafOfModules.unit X.ringCatSheaf`, the free module of rank one.
Three facts turn a statement about modules into a statement about the morphism:
`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`, which says that relative flatness of the
structure sheaf at a point is flatness of the morphism there;
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, which identifies the pullback of the
structure sheaf with the structure sheaf, so that the fibrewise and base-changed conditions are
again about morphisms; and `AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso`, which carries
relative flatness across that identification.

Openness of the flat locus is stated without the flatness of `X` over `S` that the source
assumes: the two finiteness hypotheses make `f` itself locally of finite presentation, so it is
`AlgebraicGeometry.isOpen_setOf_isFlatAt` (Tag 0399) for `f`. The base-change identification does
use the flatness.

The nonvanishing hypothesis of the Noetherian fibrewise criterion is discharged from
`Stacks.SheafOfModules.unitStalkLinearEquiv`: the stalk of the structure sheaf as a module over
itself is free of rank one over the local ring, which is nontrivial.

## References

* [Stacks Project, Tag 039D](https://stacks.math.columbia.edu/tag/039D)
* [Stacks Project, Tag 05VK](https://stacks.math.columbia.edu/tag/05VK)
* [Stacks Project, Tag 039B](https://stacks.math.columbia.edu/tag/039B)
* [Stacks Project, Tag 05VJ](https://stacks.math.columbia.edu/tag/05VJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a scheme, as a module over itself, is of finite presentation. -/
private theorem unit_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  inferInstance

/-- The stalk of the structure sheaf, viewed as a module over itself, is nonzero: it is free of
rank one over the local ring at the point. -/
theorem exists_ne_zero_unitStalk (X : Scheme.{u}) (x : X) :
    ∃ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x, a ≠ 0 := by
  refine ⟨Stacks.SheafOfModules.unitStalkLinearEquiv X.toSheafedSpace x 1, fun h => ?_⟩
  exact one_ne_zero ((Stacks.SheafOfModules.unitStalkLinearEquiv X.toSheafedSpace x).injective
    (h.trans (map_zero _).symm))

/-- The structure sheaf of `X` is flat over the base of a flat morphism `h : X ⟶ S`. -/
private theorem isFlatOver_unit_of_flat {X S : Scheme.{u}} (h : X ⟶ S) [Flat h] :
    IsFlatOver h.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) :=
  fun x => (isFlatOverAt_unit_iff_isFlatAt h x).mpr (Flat.stalkMap h x)

/-- The relative flatness of the structure sheaf of `X` on the fibre of `X ⟶ S`, read off from
flatness of the induced morphism of fibres. -/
private theorem isFlatOverAt_modulePullback_unit_fiber {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (x : X) (hfib : Flat (Stacks.Flatness.fiberHom f g (g (f x)))) :
    IsFlatOverAt (Stacks.Flatness.fiberHom f g (g (f x))).toLRSHom.toShHom
      ((modulePullback ((f ≫ g).fiberι (g (f x))).toLRSHom.toShHom).obj
        (SheafOfModules.unit X.ringCatSheaf)) ((f ≫ g).asFiber x) := by
  exact (isFlatOverAt_iff_of_moduleIso _
    (modulePullbackObjUnitIso ((f ≫ g).fiberι (g (f x))).toLRSHom.toShHom) _).mpr <|
      (isFlatOverAt_unit_iff_isFlatAt (Stacks.Flatness.fiberHom f g (g (f x)))
        ((f ≫ g).asFiber x)).mpr (Flat.stalkMap _ _)

/-- The pointwise content of the Noetherian fibrewise criterion for the structure sheaf: at every
point of `X` the intermediate scheme is flat over the base and `f` is flat. -/
private theorem flat_stalkMap_and_flat_stalkMap_of_flat_fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [Flat (f ≫ g)] (hfib : ∀ s : S, Flat (Stacks.Flatness.fiberHom f g s)) (x : X) :
    (g.stalkMap (f x)).hom.Flat ∧ (f.stalkMap x).hom.Flat := by
  let F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
    SheafOfModules.unit X.ringCatSheaf
  have _ : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have hc := Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have _ : Stacks.SheafOfModules.IsCoherent F :=
    { isFiniteType := hc.isFiniteType
      kernel_isFiniteType := fun U I hI φ => hc.kernel_isFiniteType U I hI φ }
  obtain ⟨hY, hX⟩ := (Stacks.Flatness.isFlatOverBaseAndFiberAt_iff_of_isLocallyNoetherian
    f g F x (exists_ne_zero_unitStalk X x)).mp
      ⟨isFlatOver_unit_of_flat (f ≫ g) x,
        isFlatOverAt_modulePullback_unit_fiber f g x (hfib (g (f x)))⟩
  exact ⟨hY, (isFlatOverAt_unit_iff_isFlatAt f x).mp hX⟩

/-- **Stacks Project, Tag 039D.** Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, given
by `g : Y ⟶ S`. If `S`, `X`, `Y` are locally Noetherian, `X` is flat over `S` and every induced
morphism of fibres `X_s ⟶ Y_s` is flat, then `f` is flat. -/
@[stacks 039D "flatness of the morphism"]
public theorem flat_of_flat_fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat (f ≫ g)]
    (hfib : ∀ s : S, Flat (Stacks.Flatness.fiberHom f g s)) :
    Flat f :=
  Flat.of_stalkMap f fun x =>
    (flat_stalkMap_and_flat_stalkMap_of_flat_fiberHom f g hfib x).2

/-- **Stacks Project, Tag 039D.** In the situation of
`AlgebraicGeometry.flat_of_flat_fiberHom`, if `f` is in addition surjective then `Y` is flat over
the base. -/
@[stacks 039D "flatness of the intermediate scheme over the base"]
public theorem flat_of_flat_fiberHom_of_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat (f ≫ g)]
    [Surjective f] (hfib : ∀ s : S, Flat (Stacks.Flatness.fiberHom f g s)) :
    Flat g :=
  Flat.of_stalkMap g fun y => by
    obtain ⟨x, rfl⟩ := f.surjective y
    exact (flat_stalkMap_and_flat_stalkMap_of_flat_fiberHom f g hfib x).1

/-- **Stacks Project, Tag 05VK (open locus).** For a morphism `f : X ⟶ Y` of schemes over a base
with `X` locally of finite presentation over the base and `Y` locally of finite type over it, the
locus of points of `X` at which `f` is flat is open.

Flatness of `X` over the base, which the source assumes, is not needed here: the two finiteness
hypotheses already make `f` locally of finite presentation, so Tag 0399 applies to `f` itself. -/
@[stacks 05VK "open locus",
  sga "3 VIB 1.3" "partial",
  sga "3 X 4.4" "partial",
  sga "3 XV 7.2" "partial"]
public theorem isOpen_setOf_isFlatAt_of_locallyOfFinitePresentation_comp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (pY : Y ⟶ S) [LocallyOfFinitePresentation (f ≫ pY)] [LocallyOfFiniteType pY] :
    IsOpen {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f pY
  isOpen_setOf_isFlatAt f

/-- **Stacks Project, Tag 05VK (base change).** For a morphism `f : X ⟶ Y` of schemes over a base
`S` with `X` locally of finite presentation and flat over `S` and `Y` locally of finite type over
`S`, the locus of points at which `f` is flat commutes with an arbitrary base change `S' ⟶ S`:
the corresponding locus upstairs is the preimage of the original one. -/
@[stacks 05VK "base change",
  ega "IV 20.5.7" "more general",
  sga "3 VIB 2.5" "flatness clause",
  sga "3 XV 7.2" "partial"]
public theorem setOf_isFlatAt_baseChange {X Y S S' X' Y' : Scheme.{u}} {f : X ⟶ Y} {pY : Y ⟶ S}
    {g : S' ⟶ S} {qY : Y' ⟶ Y} {pY' : Y' ⟶ S'} {qX : X' ⟶ X} {f' : X' ⟶ Y'}
    (hY : IsPullback qY pY' pY g) (hX : IsPullback qX f' f qY)
    [LocallyOfFinitePresentation (f ≫ pY)] [LocallyOfFiniteType pY] [Flat (f ≫ pY)] :
    {x' : X' | IsFlatAt f'.toLRSHom.toShHom x'} =
      qX ⁻¹' {x : X | IsFlatAt f.toLRSHom.toShHom x} := by
  let F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
    SheafOfModules.unit X.ringCatSheaf
  have _ : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have _ : F.IsFinitePresentation := unit_isFinitePresentation X
  have hL : {x' : X' | IsFlatOverAt f'.toLRSHom.toShHom
        ((modulePullback qX.toLRSHom.toShHom).obj F) x'} =
      {x' : X' | IsFlatAt f'.toLRSHom.toShHom x'} :=
    Set.ext fun x' => (isFlatOverAt_iff_of_moduleIso f'.toLRSHom.toShHom
      (modulePullbackObjUnitIso qX.toLRSHom.toShHom) x').trans
        (isFlatOverAt_unit_iff_isFlatAt f' x')
  have hR : {x : X | IsFlatOverAt f.toLRSHom.toShHom F x} =
      {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
    Set.ext fun x => isFlatOverAt_unit_iff_isFlatAt f x
  rw [← hL, ← hR]
  exact setOf_isFlatOverAt_modulePullback_of_isFlatOver hY hX F (isFlatOver_unit_of_flat (f ≫ pY))

end AlgebraicGeometry

end
