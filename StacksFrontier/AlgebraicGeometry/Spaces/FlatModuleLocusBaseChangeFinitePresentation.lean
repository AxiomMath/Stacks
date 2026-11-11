module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseConditionsFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# The flat locus under flat base change, for a module of finite presentation on the site

This file proves Stacks 05WW for a module of finite presentation on the small étale site, under
exactly the hypotheses of the source: Stacks 05VW at a geometric point is a theorem of this
development (`StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange`), and it gives both
inclusions of the set equality.  `StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusBaseChange`
states the same equality for a module which is quasi-coherent only on the étale scheme charts,
where that comparison with geometric points is not available.

The source's module is a quasi-coherent `𝒪_X`-module of finite presentation, that is a module on
the small étale site of `X`; here it is `SheafOfModules.IsFinitePresentationOnSite` on that site
(Stacks 03DL), which implies quasi-coherence on the site
(`SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`), so no separate
quasi-coherence hypothesis is taken.

## Main results

* `Space.flatLocus_modulePullback_eq_preimage_of_isFinitePresentationOnSite`:
  the set equality of Stacks 05WW.
* `Space.flatLocus_modulePullback_eq_preimage_and_isOpen_of_isFinitePresentationOnSite`:
  **Stacks 05WW**, the set equality and the openness of the locus.

## References

* [Stacks Project, Tag 05WW](https://stacks.math.columbia.edu/tag/05WW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/- The topology on points is a `def`, not an instance; as in
`StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusBaseChange` it is made a local instance. -/
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-! ### The flat locus of the base change, from finite presentation on the small étale site -/

/-- **Stacks 05WW, the set equality, with no hypothesis beyond the source's own.** In a
cartesian square of algebraic spaces over `S` with `f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'`
and `g' : X' ⟶ X` whose base morphism `g` is flat, the locus of points of `|X'|` at which the
inverse image `(g')^*F` of an `𝒪_X`-module of finite presentation on the small étale site is
flat over `Y'` is the inverse image under `|g'| : |X'| ⟶ |X|` of the locus of points of `|X|`
at which `F` is flat over `Y`.

Both inclusions are the two implications of Stacks 05VW, read at a geometric representative of
the point: the inclusion `⊆` is
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback`, flatness of `g` being
read pointwise by Stacks 03MM (`AlgebraicGeometry.Space.isFlat_iff_forall_isFlatAt`), and the
inclusion `⊇` is `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`, both
proved in this development.

Finite presentation of `f` is not needed for the equality, and finite presentation of `F`
enters only as the quasi-coherence of `F` and of its inverse image under which flatness at a
point of `|X|` agrees with flatness at a geometric point above it; the finite-presentation
hypotheses of Stacks 05WW are what makes the right-hand side open, by Stacks 05WV, and are
used in `flatLocus_modulePullback_eq_preimage_and_isOpen_of_isFinitePresentationOnSite`. -/
@[stacks 05WW "the set equality; the finite-presentation hypotheses of the source enter \
through Stacks 05WV in \
flatLocus_modulePullback_eq_preimage_and_isOpen_of_isFinitePresentationOnSite"]
theorem flatLocus_modulePullback_eq_preimage_of_isFinitePresentationOnSite
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : SheafOfModules.IsFinitePresentationOnSite F)
    (hg : IsFlat B S hS g.hom) :
    flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' flatLocus B S hS X.2 f.hom F := by
  have hpb : IsPullback g' f' f g :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) (by simpa using sq)
  have := hF
  have : SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS g').obj F) := by
    rw [modulePullback_eq]
    exact Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite
      (smallEtaleRingedToposModulesHom B S hS g') F hF
  refine Set.ext fun x' => ?_
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X'.1 x'
  rw [Set.mem_preimage,
    mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f'
      ((modulePullback B S hS g').obj F) xbar,
    ← geometricPointMap_image g'.hom xbar,
    mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F (geometricPointMap g'.hom xbar)]
  exact ⟨fun hx => isFlatOverAtGeometricPoint_of_modulePullback B S hS hpb F xbar
      ((isFlat_iff_forall_isFlatAt B S hS g.hom).1 hg _) hx,
    isFlatOverAtGeometricPoint_modulePullback B S hS hpb F xbar⟩

/-- **Stacks 05WW, with no hypothesis beyond the source's own.** Let a cartesian square of
algebraic spaces over `S` be given, with `f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'` and
`g' : X' ⟶ X`.  Assume `g` is flat, `f` is locally of finite presentation, and the `𝒪_X`-module
`F` is of finite presentation on the small étale site.  Then the locus of points of `|X'|` at
which the inverse image `(g')^*F` is flat over `Y'` is the inverse image under
`|g'| : |X'| ⟶ |X|` of the open subset of Stacks 05WV, and is therefore itself open.

The equality is
`AlgebraicGeometry.Space.flatLocus_modulePullback_eq_preimage_of_isFinitePresentationOnSite`,
which is where Stacks 05VW and the flatness of `g` are used.  Openness of the subset of `|X|`
is Stacks 05WV, `AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`,
whose chartwise hypotheses on `F` are supplied by the finite presentation of `F` on the site,
and the map on points is continuous by clause (2) of Stacks 03BX. -/
@[stacks 05WW "the locus on the base change is the inverse image of the open subset of \
Stacks 05WV, hence open"]
theorem flatLocus_modulePullback_eq_preimage_and_isOpen_of_isFinitePresentationOnSite
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hg : IsFlat B S hS g.hom)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite F) :
    flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) =
        pointsMap B S hS X'.1 g'.hom ⁻¹' flatLocus B S hS X.2 f.hom F ∧
      IsOpen (flatLocus B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)) := by
  have : SheafOfModules.IsFinitePresentationOnSite F := hF
  have heq := flatLocus_modulePullback_eq_preimage_of_isFinitePresentationOnSite B S hS sq F hF hg
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS X.2 f.hom F hf
    (isQuasicoherentOnCharts_of_isFinitePresentationOnSite B S hS X.2 F hF)
    (isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X F
      (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite F) hF)).preimage
    (continuous_pointsMap B S hS g'.hom)

end AlgebraicGeometry.Space

end
