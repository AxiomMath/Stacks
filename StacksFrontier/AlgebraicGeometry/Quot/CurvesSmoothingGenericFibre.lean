module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.GeometricFibresDirectImage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LocalConstancy
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreConnectedness
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentFlattening
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothDense
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic fibre of a family of curves over `k⟦t⟧`

Let `g : Y ⟶ Spec k⟦t⟧` be proper, flat and of finite presentation, with smooth generic fibre
and special fibre `X ⟶ Spec k` geometrically connected and geometrically reduced. The space
`Spec k⟦t⟧` has two points, the generic point and the closed point, so every fibre of `g` is
geometrically reduced; the number of geometric connected components of the fibres is then
locally constant (Stacks 0E0N), hence constant on the connected space `Spec k⟦t⟧`, and the generic
fibre is geometrically connected. By Stacks 0E0L the generic fibre has `f_*𝒪 = 𝒪`, universally.
If moreover `X` has dimension at most one and `H⁰(X, 𝒪_X) = k`, the Euler characteristic of the
structure sheaf of the fibres, which is locally constant (Stacks 0B9T) and equals `1 - genus` on a
curve with constant global functions, shows that the generic fibre has the genus of `X`; the
fibre over the closed point is compared with `X` by extension of the residue field (Stacks 0BY9).

## Main definitions

* `AlgebraicGeometry.PowerSeriesFamily.genericPoint` and
  `AlgebraicGeometry.PowerSeriesFamily.specialPoint`: the generic point of `Spec k⟦t⟧` and the
  closed immersion of its closed point.

## Main results

* `AlgebraicGeometry.PowerSeriesFamily.geometricallyConnected_genericFibre`: the generic fibre is
  geometrically connected.
* `AlgebraicGeometry.PowerSeriesFamily.isIso_c_genericFibre`: `f_*𝒪 = 𝒪` universally on the
  generic fibre.
* `AlgebraicGeometry.PowerSeriesFamily.genus_genericFibre_eq`: the generic fibre has the genus of
  the special fibre.

## References

* [Stacks Project, Tag 0E0N](https://stacks.math.columbia.edu/tag/0E0N)
* [Stacks Project, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace PowerSeriesFamily

variable {k : Type u} [Field k]

/-- The generic point of `Spec k⟦t⟧`. -/
abbrev genericPoint (k : Type u) [Field k] : Spec (.of (PowerSeries k)) :=
  (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))

/-- The closed immersion `Spec k ⟶ Spec k⟦t⟧` of the closed point. -/
abbrev specialPoint (k : Type u) [Field k] :
    Spec (.of k) ⟶ Spec (.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))

/-- `Spec k⟦t⟧` has two points, the generic point and the closed point. -/
theorem eq_genericPoint_or_eq_specialPoint (y : Spec (.of (PowerSeries k))) :
    y = genericPoint k ∨ y = (specialPoint k).base (IsLocalRing.closedPoint k) := by
  by_cases h : y.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext h)
  · right
    have hy : y.asIdeal.IsMaximal := y.isPrime.isMaximal h
    have hz : ((specialPoint k).base (IsLocalRing.closedPoint k)).asIdeal =
        Ideal.comap (PowerSeries.constantCoeff (R := k)) (IsLocalRing.maximalIdeal k) := rfl
    have h2 : ((specialPoint k).base (IsLocalRing.closedPoint k)).asIdeal.IsMaximal := by
      rw [hz]
      exact Ideal.comap_isMaximal_of_surjective _ fun a => ⟨PowerSeries.C a, by simp⟩
    apply PrimeSpectrum.ext
    rw [IsLocalRing.eq_maximalIdeal hy, IsLocalRing.eq_maximalIdeal h2]

/-- Geometric reducedness of a fibre of the right-hand vertical map of a cartesian square passes to
the corresponding fibre of the left-hand vertical map, which is its base change along an
extension of residue fields. -/
theorem geometricallyReduced_of_pullback_fiber
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y)
    (hc : GeometricallyReduced (b.fiberToSpecResidueField y)) :
    GeometricallyReduced (f.fiberToSpecResidueField (g y)) := by
  let : Algebra (Z.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback h y
  have e : Arrow.mk (b.fiberToSpecResidueField y) ≅
      Arrow.mk (pullback.snd (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))) :=
    Arrow.isoMk' _ _ hpb.isoPullback (Iso.refl _)
      (hpb.isoPullback_hom_snd.trans (Category.comp_id _).symm)
  have hc' : GeometricallyReduced
      (pullback.snd (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))) := by
    rw [GeometricallyReduced.eq_geometrically] at hc ⊢
    exact (MorphismProperty.arrow_mk_iso_iff
      (P := geometrically IsReduced) e).1 hc
  exact (geometricallyReduced_iff_baseChange_fieldExtension
    (Z.residueField (g y)) (Y.residueField y)
    (f.fiberToSpecResidueField (g y))).mpr hc'

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of (PowerSeries k)))
  {X : Scheme.{u}} {a : X ⟶ Y} (f : X ⟶ Spec (.of k))
  (h : IsPullback a f g (specialPoint k))

include h in
/-- **The fibres of a family over `k⟦t⟧` with smooth generic fibre and geometrically reduced
special fibre are geometrically reduced.** -/
theorem geometricallyReduced_of_smooth_genericFibre
    [Smooth (g.fiberToSpecResidueField (genericPoint k))] [GeometricallyReduced f] :
    GeometricallyReduced g := by
  refine ConnectedComponentSection.geometricallyReduced_of_fibers g fun y => ?_
  rcases eq_genericPoint_or_eq_specialPoint y with rfl | rfl
  · exact geometricallyReduced_of_smooth _
  · exact geometricallyReduced_of_pullback_fiber h _
      (inferInstanceAs (GeometricallyReduced
        (pullback.snd f ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k)))))

include h in
/-- **The generic fibre of a family over `k⟦t⟧` is geometrically connected** when the family is
proper, flat and of finite presentation with geometrically reduced fibres and its special fibre
is geometrically connected: the number of geometric connected components of the fibres is
locally constant (Stacks 0E0N) on the connected space `Spec k⟦t⟧`, and it is one at the closed
point. -/
@[ega "IV 15.5.9" "(ii), special case"]
theorem geometricallyConnected_genericFibre [IsProper g] [Flat g] [LocallyOfFinitePresentation g]
    [Smooth (g.fiberToSpecResidueField (genericPoint k))] [GeometricallyReduced f]
    [GeometricallyConnected f] :
    GeometricallyConnected (g.fiberToSpecResidueField (genericPoint k)) := by
  have := geometricallyReduced_of_smooth_genericFibre g f h
  have hlc := isLocallyConstant_numGeometricConnectedComponents g
    (fun K _ _ s => (geometricallyReduced_iff_forall_isAlgClosed g).1 inferInstance K s)
  have hs : numGeometricConnectedComponents g ((specialPoint k).base (IsLocalRing.closedPoint k))
      = 1 :=
    (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one g _).1
      (ConnectedComponentSection.geometricallyConnected_of_pullback_fiber h _
        (inferInstanceAs (GeometricallyConnected
          (pullback.snd f ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k))))))
  rw [geometricallyConnected_iff_numGeometricConnectedComponents_eq_one,
    hlc.apply_eq_of_preconnectedSpace _ ((specialPoint k).base (IsLocalRing.closedPoint k)), hs]

open ProperFlatFibreEulerCharacteristic in
/-- The Euler characteristic of the structure sheaf of a proper scheme of dimension at most one
over a field is `h⁰ - g`. -/
theorem eulerSum_unit_eq_finrank_sub_genus {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsProper c] (hdim : topologicalKrullDim C ≤ 1) :
    eulerSum K c (SheafOfModules.unit C.ringCatSheaf) =
      (Module.finrank K (cohomologyOverField K c (SheafOfModules.unit C.ringCatSheaf) 0) : ℤ) -
        (genus c : ℤ) := by
  have hs := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero K c
    (SheafOfModules.unit C.ringCatSheaf)
    (fun m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le K c _ (d := 1)
      (by exact_mod_cast hdim) (by omega))
  have hg : (genus c : ℤ) = (Module.finrank K
      (cohomologyOverField K c (SheafOfModules.unit C.ringCatSheaf) 1) : ℤ) := by
    rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField K c 1).toLinearEquiv.finrank_eq]
  rwa [hg]

include h in
open ProperFlatFibreEulerCharacteristic in
/-- **The genus of the generic fibre of a family over `k⟦t⟧` is that of its special fibre**, for
a proper flat family of finite presentation whose special fibre has dimension at most one, and
both of whose fibres have only constant global functions: the Euler characteristic of the
structure sheaf of the fibres is locally constant (Stacks 0B9T) on the connected space
`Spec k⟦t⟧`, it is `1 - g` on a fibre with `H⁰ = κ`, and cohomology over a field commutes with
extension of the field (Stacks 0BY9). -/
theorem genus_genericFibre_eq [IsProper g] [Flat g] [LocallyOfFinitePresentation g] [IsProper f]
    (hdimX : topologicalKrullDim X ≤ 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    [IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of (PowerSeries k))).residueField
      (genericPoint k)))).inv ≫ (g.fiberToSpecResidueField (genericPoint k)).appTop)] :
    genus (g.fiberToSpecResidueField (genericPoint k)) = genus f := by
  obtain ⟨hOfp, hOflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible g
    (SheafOfModules.unit Y.ringCatSheaf) (Stacks.SheafOfModules.isInvertible_unit _ _)
  have hfp : FinitePresentation g :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  have hlc := isLocallyConstant_fibreEulerCharacteristic g hfp _ hOfp hOflat
  have hdimy : ∀ y, topologicalKrullDim (g.fiber y) ≤ 1 := fun y =>
    (fiberDimension_le_one_of_specialFibre f hdimX g h.isoPullback h.isoPullback_hom_snd y).trans
      (by simp)
  have hχ : ∀ y, fibreEulerCharacteristic g (SheafOfModules.unit Y.ringCatSheaf) y =
      (Module.finrank ((Spec (.of (PowerSeries k))).residueField y)
        (cohomologyOverField ((Spec (.of (PowerSeries k))).residueField y)
          (g.fiberToSpecResidueField y)
        (SheafOfModules.unit (g.fiber y).ringCatSheaf) 0) : ℤ) -
        (genus (g.fiberToSpecResidueField y) : ℤ) := fun y =>
    (eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso (g.fiberι y))).trans
      (eulerSum_unit_eq_finrank_sub_genus _ (hdimy y))
  let x := (Scheme.SpecToEquivOfField k _ (specialPoint k)).1
  let ψ := (Scheme.SpecToEquivOfField k _ (specialPoint k)).2
  have hφ : specialPoint k = Spec.map ψ ≫ (Spec (.of (PowerSeries k))).fromSpecResidueField x :=
    ((Scheme.SpecToEquivOfField k _).symm_apply_apply (specialPoint k)).symm
  let : Algebra ((Spec (.of (PowerSeries k))).residueField x) k := ψ.hom.toAlgebra
  have hψ : Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of (PowerSeries k))).residueField x)
      k)) = Spec.map ψ := rfl
  have hright := IsPullback.of_hasPullback g ((Spec (.of (PowerSeries k))).fromSpecResidueField x)
  let l : X ⟶ g.fiber x := pullback.lift a (f ≫ Spec.map ψ) (by rw [h.w, hφ, Category.assoc])
  have hbig : IsPullback (l ≫ g.fiberι x) f g
      (Spec.map ψ ≫ (Spec (.of (PowerSeries k))).fromSpecResidueField x) := by
    have hl : l ≫ g.fiberι x = a := pullback.lift_fst _ _ _
    rw [hl, ← hφ]
    exact h
  have hleft : IsPullback l f (g.fiberToSpecResidueField x) (Spec.map ψ) :=
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) hright
  rw [← hψ] at hleft
  have hgx : genus f = genus (g.fiberToSpecResidueField x) :=
    genus_baseChange ((Spec (.of (PowerSeries k))).residueField x) k l f _ hleft
  have h0x : Module.finrank ((Spec (.of (PowerSeries k))).residueField x)
      (cohomologyOverField ((Spec (.of (PowerSeries k))).residueField x)
        (g.fiberToSpecResidueField x)
      (SheafOfModules.unit (g.fiber x).ringCatSheaf) 0) = 1 := by
    have e₁ := finrank_cohomologyOverField_baseChange_field
      ((Spec (.of (PowerSeries k))).residueField x) k l f _ hleft
      (SheafOfModules.unit (g.fiber x).ringCatSheaf) 0
    have e₂ := finrank_cohomologyOverField_eq_of_iso k f (Scheme.Modules.pullbackUnitIso l) 0
    exact e₁.symm.trans (e₂.trans (finrank_cohomologyOverField_unit_zero_eq_one f))
  have hconst := hlc.apply_eq_of_preconnectedSpace (genericPoint k) x
  rw [hχ, hχ, h0x, finrank_cohomologyOverField_unit_zero_eq_one, ← hgx] at hconst
  omega

include h in
/-- **`f_*𝒪 = 𝒪` universally on the generic fibre** (Stacks 0E0L): the generic fibre is proper,
flat and of finite presentation over its field, geometrically reduced (it is smooth) and
geometrically connected (`geometricallyConnected_genericFibre`). -/
theorem isIso_c_genericFibre [IsProper g] [Flat g] [LocallyOfFinitePresentation g]
    [Smooth (g.fiberToSpecResidueField (genericPoint k))] [GeometricallyReduced f]
    [GeometricallyConnected f] :
    IsIso (g.fiberToSpecResidueField (genericPoint k)).c ∧
      ∀ {X' S' : Scheme.{u}} {s : S' ⟶ Spec ((Spec (.of (PowerSeries k))).residueField
          (genericPoint k))} {s' : X' ⟶ g.fiber (genericPoint k)} {c' : X' ⟶ S'},
        IsPullback s' c' (g.fiberToSpecResidueField (genericPoint k)) s → IsIso c'.c := by
  have := geometricallyConnected_genericFibre g f h
  have : GeometricallyReduced (g.fiberToSpecResidueField (genericPoint k)) :=
    geometricallyReduced_of_smooth _
  exact Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.isIso_c_and_isIso_c_of_isPullback _

/-- A morphism of schemes whose structure map `𝒪_Y ⟶ f_*𝒪_X` is invertible induces an
isomorphism on global functions. -/
theorem isIso_appTop_of_isIso_c {X' Y' : Scheme.{u}} (c : X' ⟶ Y') [IsIso c.c] :
    IsIso c.appTop :=
  inferInstanceAs (IsIso (c.c.app (Opposite.op ⊤)))

end PowerSeriesFamily

end AlgebraicGeometry

end
