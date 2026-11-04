module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekStructureSheafRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlatCharts
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The Tor amplitude of `f_new^! 𝒪_Y` over `Y`

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a flat morphism of schemes of finite type
over `S`, not necessarily separated, all of whose fibres have dimension at most `d`. With `f^!`
replaced by `f_new^!` ([Stacks, Tag 0BV9]), the second assertion of [Stacks, Tag 0BV6] holds:
`f_new^! 𝒪_Y` has Tor amplitude in `[-d, 0]` as an object of `D(X, f^{-1}𝒪_Y)`.

Tor amplitude in a fixed interval is local on `(X, f^{-1}𝒪_Y)`
(`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top`). On an affine open `V ⊆ X`
the open subspace of `(X, f^{-1}𝒪_Y)` cut out by `V` is `(V, (V → Y)^{-1}𝒪_Y)`
(`AlgebraicGeometry.Scheme.Hom.inverseImageOpenMap`), derived restriction of scalars commutes
with restriction to `V`, the restriction of `f_new^! 𝒪_Y` is `(V → Y)^! 𝒪_Y`
(`Stacks.Duality.NormalizedOnOpens.newShriekStructureSheafRestrictIso`), and the library's
[Stacks, Tag 0BV6] for the morphism `V → Y` of `FTS_Y`, whose fibres embed in those of `f`,
gives the bound there.

## Main results

* `Stacks.Duality.topologicalKrullDim_fiber_comp_ι_le`: the fibres of `V → Y` are no bigger than
  those of `f`.
* `Stacks.Duality.NormalizedOnOpens.upperShriekStdStructureIso`: `(V → Y)^! 𝒪_Y` at the
  standard model through the comparison of models.
* `Stacks.Duality.NormalizedOnOpens.hasTorAmplitude_derivedScalarRestriction_newShriek`

## References

* [Stacks Project, Tag 0BV9](https://stacks.math.columbia.edu/tag/0BV9)
* [Stacks Project, Tag 0BV6](https://stacks.math.columbia.edu/tag/0BV6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison pull plusCoh_le_qcoh)

/-- **The fibres of `V → Y` embed in those of `f`**: for an open `V ⊆ X`, the dimension of a
fibre of `V → Y` is at most that of the corresponding fibre of `f`. -/
theorem topologicalKrullDim_fiber_comp_ι_le {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (y : Y) : topologicalKrullDim ((V.ι ≫ f).fiber y) ≤ topologicalKrullDim (f.fiber y) := by
  rw [((V.ι ≫ f).fiberHomeo y).isHomeomorph.topologicalKrullDim_eq,
    (f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  let r : ((V.ι ≫ f) ⁻¹' {y}) → (f ⁻¹' {y}) := fun z => ⟨V.ι z.1, by simpa using z.2⟩
  have hr : Topology.IsInducing r :=
    Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (V.ι.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal)
  exact hr.topologicalKrullDim_le

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel.{u, u} S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

/-- `𝒪_Y` read back from the standard model is `𝒪_Y`, by the counit of the comparison of
models. -/
def structureStdComparisonIso (Y : Scheme.{u}) [IsLocallyNoetherian Y] :
    (⟨(comparison Y).functor.obj (structureStd Y),
        plusCoh_le_qcoh _ (plusCoh_structureStd Y)⟩ : quasiCoherentDerivedCategory Y) ≅
      DerivedPushforward.derivedStructureSheaf Y :=
  ObjectProperty.isoMk _
    ((comparison Y).counitIso.app (DerivedPushforward.derivedStructureSheaf Y).obj)

/-- `(V → Y)^! 𝒪_Y` read at the standard model through the comparison of models is
`(V → Y)^! 𝒪_Y`. -/
def upperShriekStdStructureIso (V : X.Opens) (hV : IsShriekable (V.ι ≫ f)) :
    haveI := hq.source_noetherian
    (UpperShriekDuality.upperShriekStd (ftsHomSelf hV) (c _ hV)).obj
        ⟨structureStd Y, plusCoh_structureStd Y⟩ ≅
      (comparison (ftsOf (V.ι ≫ f) hV.separatedFiniteType).left).inverse.obj
        (relativeDualizingComplexObj (ftsHomSelf hV) (c _ hV)) :=
  haveI := hq.source_noetherian
  (comparison (ftsOf (V.ι ≫ f) hV.separatedFiniteType).left).inverse.mapIso
    ((ObjectProperty.ι _).mapIso
      ((upperShriek (ftsHomSelf hV) (c _ hV)).mapIso (structureStdComparisonIso Y)))

include hpe hωS in
/-- **The second assertion of [Stacks, Tag 0BV6] for `f_new^!`.** For a flat morphism
`f : X ⟶ Y` of schemes of finite type over the base of [Stacks, Tag 0AU4], not necessarily
separated, all of whose fibres have dimension at most `d`, `f_new^! 𝒪_Y` has Tor amplitude in
`[-d, 0]` as an object of `D(X, f^{-1}𝒪_Y)`. -/
theorem hasTorAmplitude_derivedScalarRestriction_newShriek [Flat f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    letI := HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
    letI := HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u} (RingedSpace.inverseImage Y.toRingedSpace f.base))
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
      (RingedSpace.inverseImage Y.toRingedSpace f.base)
      ((Scheme.Hom.derivedScalarRestriction f).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y))
      (-(d : ℤ)) 0 := by
  let std : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
    fun C _ _ => HasDerivedCategory.standard C
  have := hq.source_noetherian
  let Xinv := RingedSpace.inverseImage Y.toRingedSpace f.base
  let W : X.affineOpens → Opens Xinv.carrier := fun V => V.1
  refine Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_iSup_eq_top (X := Xinv) _ _ _ W
    (iSup_affineOpens_eq_top X) fun V => ?_
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2
  have : Flat (ftsHomSelf hsh).left := inferInstanceAs (Flat (V.1.ι ≫ f))
  -- the restriction of `f_new^! 𝒪_Y` to `V`
  let e : (pull V.1.ι).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y) ≅
      (comparison (ftsOf (V.1.ι ≫ f) hsh.separatedFiniteType).left).inverse.obj
        (relativeDualizingComplexObj (ftsHomSelf hsh) (c _ hsh)) :=
    newShriekStructureSheafRestrictIso c 𝒦X 𝒦Y hpe hωS V.1 hsh ≪≫
      upperShriekStdStructureIso c (hq := hq) V.1 hsh
  let j := Scheme.Hom.inverseImageOpenMap f V.1.ι
  have hrange : Set.range (Xinv.ofRestrict (W V).isOpenEmbedding).hom.base ⊆
      Set.range j.hom.base := by
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  let σ := RingedSpace.openImmersionLift j (Xinv.ofRestrict (W V).isOpenEmbedding) hrange
  have hV : Stacks.Cohomology.TorAmplitude.HasTorAmplitude _
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j).obj
        ((Scheme.Hom.derivedScalarRestriction f).obj (newShriekStructureSheaf c f 𝒦X 𝒦Y)))
      (-(d : ℤ)) 0 :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso
      (hasTorAmplitude_derivedScalarRestriction_upperShriek (ftsHomSelf hsh) (c _ hsh) d
        fun y => (topologicalKrullDim_fiber_comp_ι_le f V.1 y).trans (hd y))
      ((Scheme.Hom.derivedScalarRestrictionOpenImmersionIso f V.1.ι _).symm ≪≫
        (Scheme.Hom.derivedScalarRestriction (V.1.ι ≫ f)).mapIso e)
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso
    (Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback σ _ _ _ hV)
    ((RingedSpace.derivedRestrictModulesIsoDerivedPullback Xinv (W V)).app _ ≪≫
      ((Stacks.Cohomology.TorAmplitude.derivedPullbackFactorIso σ j _
        (RingedSpace.openImmersionLift_fac _ _ _)).app _).symm)

end NormalizedOnOpens

end Stacks.Duality

end
