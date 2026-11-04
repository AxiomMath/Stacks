module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.AffineQuasiCompactImmersion
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FiniteGroupoidThickening
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantPrincipalOpenGenericOrbits
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOneQuasiAffine.InvariantCore
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOneQuasiAffine.DenseFlatOpen

/-!
# The quasi-affine case of an invariant affine open in codimension one

Let `(U, R, s, t, c)` be a groupoid scheme with `s` and `t` finite, let `U` be separated and
locally Noetherian, and let `u ∈ U` be a point such that `dim(𝒪_{U, u'}) ≤ 1` for every point
`u'` of the `R`-orbit of `u`. The first step of the proof of [Stacks, Tag 0ABI] reduces the
existence of an `R`-invariant affine open containing `u` to the case where `u` lies in an
`R`-invariant open contained in an affine open, so that `U` may be taken quasi-affine. This file,
with the two parts of the proof it imports, carries out the remaining nine steps of that proof in
that situation.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_le_isAffineOpen`:
  given an invariant open `V` containing `u` and contained in an affine open, the point `u` lies
  in an invariant affine open. This is the quasi-affine case of [Stacks, Tag 0ABI]; combined with
  the reduction it gives the tag, which is where the tag attribute sits, in
  `StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOne`.

### What is assumed

The single hypothesis `H06AD` is [Stacks, Tag 06AD] -- a thickening of an affine scheme is
affine -- in the universally quantified shape in which
`AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen` ([Stacks, Tag 0ABF])
and `AlgebraicGeometry.exists_invariant_affine_open_with_finiteLocallyFree_thickening`
([Stacks, Tag 0ABC]) carry it. It enters only through the two applications of 0ABF, which is
where the source's proof needs it as well, and nothing else is assumed. The hypothesis is not an
assumed result: 06AD is proved in this repository as
`Stacks.Thickenings.isAffine_of_isThickening`, and
`Stacks.Thickenings.forall_isAffine_of_isThickening` discharges it -- which is what
`StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOne`, where
the tag attribute sits, does.

## Implementation notes

The steps of the source's proof appear as follows. Steps 3 to 7 are in
`InvariantAffineOpenDimensionOneQuasiAffine.DenseFlatOpen`, and Steps 8 to 10 in
`InvariantAffineOpenDimensionOneQuasiAffine.InvariantCore`.

* Step 2, the passage to a dense invariant open on which the structure maps are finite locally
  free, is `exists_invariant_affineOpen_of_isNoetherian_isQuasiAffine`. In place of the source's
  two replacements of `U` by a smaller scheme along [Stacks, Tag 0ABE] -- its reduction, and the
  closure of the open `W` of [Stacks, Tag 0ABA] -- the groupoid is restricted once, to the
  scheme-theoretic image of the invariant thickening of 0ABA, and 0ABE is applied once, at the
  end. The reduction of `U` is not needed: it serves in the source only to identify the two
  subschemes `W' ⊆ W` of 0ABA, and what the argument uses is that the thickening is a dense open
  of its image, which holds without it.

The `R`-orbit of a point `u` is spelled as the set of points reached by an arrow with source
`u`, matching [Stacks, Tag 0ABF] and [Stacks, Tag 0ABG]; invariance is
`Stacks.Groupoids.IsInvariantOpen`, and `dim(𝒪_{U, u'}) ≤ 1` is `Ring.KrullDimLE 1` on the
stalk.

## References

* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 0ABA](https://stacks.math.columbia.edu/tag/0ABA)
* [Stacks Project, Tag 0ABE](https://stacks.math.columbia.edu/tag/0ABE)
* [Stacks Project, Tag 0ABF](https://stacks.math.columbia.edu/tag/0ABF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The structure map of the canonical restriction sends the transport of `x'` along
`objects_eq` to the image of `x'`. -/
private lemma restrict_mapObjects_eqToHom_apply {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) (x' : U'.left) :
    (AlgebraicGeometry.GroupoidScheme.restrict G g).hom.mapObjects.left
      ((eqToHom (AlgebraicGeometry.GroupoidScheme.restrict G g).objects_eq.symm).left x') =
        g.left x' := by
  have h : eqToHom (AlgebraicGeometry.GroupoidScheme.restrict G g).objects_eq.symm ≫
      (AlgebraicGeometry.GroupoidScheme.restrict G g).hom.mapObjects = g := by
    rw [(AlgebraicGeometry.GroupoidScheme.restrict G g).mapObjects_eq]
    simp
  exact congrArg (fun f : U' ⟶ G.objects => f.left x') h

/-- **[Stacks, Tag 0ABE] for the canonical restriction.** An invariant affine open neighbourhood
of the point of the object scheme of the restriction of a groupoid scheme along an integral
morphism meeting every orbit that corresponds to a point `x'` of the restricting scheme gives an
invariant affine open neighbourhood of the image of `x'`. This is
`AlgebraicGeometry.exists_invariant_affine_open_of_restriction_integral` stated for
`AlgebraicGeometry.GroupoidScheme.restrict` and for a point of the restricting scheme. -/
private lemma exists_invariant_affineOpen_of_integral_restrict {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [IsIntegralHom G.source.left]
    [IsIntegralHom G.target.left] {U' : Over S} (g : U' ⟶ G.objects) [IsIntegralHom g.left]
    (hOrbit : ∀ x : G.objects.left, ∃ x' : U'.left,
      ∃ r : G.arrows.left, G.source.left r = x ∧ G.target.left r = g.left x')
    (x' : U'.left)
    (hW : ∃ W' : (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid.objects.left.Opens,
      Stacks.Groupoids.IsInvariantOpen
          (AlgebraicGeometry.GroupoidScheme.restrict G g).groupoid W' ∧
        IsAffineOpen W' ∧
          ((AlgebraicGeometry.GroupoidScheme.restrict G g).objects_eq.symm ▸ x') ∈ W') :
    ∃ W : G.objects.left.Opens,
      Stacks.Groupoids.IsInvariantOpen G W ∧ IsAffineOpen W ∧ g.left x' ∈ W := by
  obtain ⟨W', hW'inv, hW'aff, hx'⟩ := hW
  have hx'' :
      (eqToHom (AlgebraicGeometry.GroupoidScheme.restrict G g).objects_eq.symm).left x' ∈ W' := by
    rw [over_eqToHom_apply_in_restriction
      (AlgebraicGeometry.GroupoidScheme.restrict G g).objects_eq x']
    exact hx'
  obtain ⟨W, hWinv, hWaff, hmem⟩ :=
    AlgebraicGeometry.exists_invariant_affine_open_of_restriction_integral G
      (AlgebraicGeometry.GroupoidScheme.restrict G g) hOrbit _ W' hW'inv hW'aff hx''
  refine ⟨W, hWinv, hWaff, ?_⟩
  exact restrict_mapObjects_eqToHom_apply G g x' ▸ hmem

/-- **Steps 2 to 10 of the source's proof of [Stacks, Tag 0ABI].** For a groupoid scheme with
finite source and target whose object scheme is Noetherian and quasi-affine, a point whose orbit
has stalks of Krull dimension at most one lies in an invariant affine open.

[Stacks, Tag 0ABA] supplies an invariant open `W` carrying an invariant thickening over which
the restricted groupoid has finite locally free structure maps, and whose closure has saturation
everything; the groupoid is restricted to the scheme-theoretic image of the thickening, which
receives the thickening as a dense open, and the previous lemma applies there. The point is
moved into that image by the choice of a point of its orbit in the closure of `W`, and the
resulting invariant affine open is pushed back along the restriction by
[Stacks, Tag 0ABE]. -/
private lemma exists_invariant_affineOpen_of_isNoetherian_isQuasiAffine
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [IsNoetherian G.objects.left] [G.objects.left.IsQuasiAffine]
    (x : G.objects.left)
    (hdim : ∀ y, (∃ r : G.arrows.left, G.source.left r = x ∧ G.target.left r = y) →
      Ring.KrullDimLE 1 (G.objects.left.presheaf.stalk y)) :
    ∃ V : G.objects.left.Opens, Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧ x ∈ V := by
  classical
  obtain ⟨W, W', i, hmono, hWinv, _, hsat, hi, hfree⟩ :=
    AlgebraicGeometry.exists_invariant_thickening_finiteLocallyFree_restriction G
  have : IsClosedImmersion i := hi.1
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian i
  let m := i ≫ W.ι
  have : NoetherianSpace W' := m.isEmbedding.isInducing.noetherianSpace
  let g : Over.mk (m ≫ G.objects.hom) ⟶ G.objects := Over.homMk m
  let K := AlgebraicGeometry.GroupoidScheme.restrict G g
  have : IsIso (eqToHom K.objects_eq).left := isIso_over_eqToHom_left _
  have : IsIso (eqToHom K.objects_eq.symm).left := isIso_over_eqToHom_left _
  have : IsIso (eqToHom K.arrows_eq).left := isIso_over_eqToHom_left _
  have : MorphismProperty.RespectsIso @IsImmersion :=
    MorphismProperty.RespectsIso.mk _ (fun e q _ => IsImmersion.comp e.hom q)
      (fun e q _ => IsImmersion.comp q e.hom)
  have hKimm : IsImmersion K.hom.mapObjects.left :=
    (restriction_mapObjects_property_iff G g K @IsImmersion).2
      (show IsImmersion m from inferInstance)
  have : IsLocallyNoetherian K.groupoid.objects.left :=
    LocallyOfFiniteType.isLocallyNoetherian K.hom.mapObjects.left
  have hWnoeth : IsLocallyNoetherian (Over.mk (m ≫ G.objects.hom)).left :=
    show IsLocallyNoetherian W' from inferInstance
  obtain ⟨_, _⟩ := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian
    (AlgebraicGeometry.restrictionSource G g).left).1 hfree.1
  obtain ⟨_, _⟩ := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian
    (AlgebraicGeometry.restrictionTarget G g).left).1 hfree.2
  obtain ⟨_, _, _, _⟩ : IsFinite K.groupoid.source.left ∧ Flat K.groupoid.source.left ∧
      IsFinite K.groupoid.target.left ∧ Flat K.groupoid.target.left := by
    rw [K.source_eq, K.target_eq]
    simp only [Over.comp_left]
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  let gZ : Over.mk (m.imageι ≫ G.objects.hom) ⟶ G.objects := Over.homMk m.imageι
  let R := AlgebraicGeometry.GroupoidScheme.restrict G gZ
  have : IsClosedImmersion gZ.left := show IsClosedImmersion m.imageι from inferInstance
  have hRimm : IsClosedImmersion R.hom.mapObjects.left :=
    (restriction_mapObjects_property_iff G gZ R @IsClosedImmersion).2 inferInstance
  have : IsLocallyNoetherian R.groupoid.objects.left :=
    LocallyOfFiniteType.isLocallyNoetherian R.hom.mapObjects.left
  have : CompactSpace R.groupoid.objects.left :=
    QuasiCompact.compactSpace_of_compactSpace R.hom.mapObjects.left
  have : IsNoetherian R.groupoid.objects.left := ⟨⟩
  have : R.groupoid.objects.left.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isImmersion R.hom.mapObjects.left
  have hfinite := finite_restriction_maps G gZ R
  have : IsFinite R.groupoid.source.left := hfinite.1
  have : IsFinite R.groupoid.target.left := hfinite.2
  have : IsIso (eqToHom R.objects_eq.symm).left := isIso_over_eqToHom_left _
  let k₀ : Over.mk (m ≫ G.objects.hom) ⟶ Over.mk (m.imageι ≫ G.objects.hom) :=
    Over.homMk m.toImage (by simp)
  let k : K.groupoid.objects ⟶ R.groupoid.objects :=
    eqToHom K.objects_eq ≫ k₀ ≫ eqToHom R.objects_eq.symm
  have : IsOpenImmersion k.left := by
    show IsOpenImmersion ((eqToHom K.objects_eq).left ≫ m.toImage ≫
      (eqToHom R.objects_eq.symm).left)
    infer_instance
  have : IsDominant k.left := by
    show IsDominant ((eqToHom K.objects_eq).left ≫ m.toImage ≫
      (eqToHom R.objects_eq.symm).left)
    infer_instance
  have hk : k ≫ R.hom.mapObjects = K.hom.mapObjects := by
    rw [R.mapObjects_eq, K.mapObjects_eq]
    dsimp [k]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    congr 1
    exact Over.OverMorphism.ext m.toImage_imageι
  have hmRange : Set.range m = (W : Set G.objects.left) := by
    show Set.range (W.ι ∘ i) = _
    rw [Set.range_comp, hi.2.range_eq, Set.image_univ]
    exact W.range_ι
  have hkRange : Set.range k.left = R.hom.mapObjects.left ⁻¹' (W : Set G.objects.left) := by
    have hKr : Set.range K.hom.mapObjects.left = (W : Set G.objects.left) :=
      (range_restriction_mapObjects G g K).trans hmRange
    rw [← hKr]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (congrArg (fun f => f.left t) hk).symm⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, R.hom.mapObjects.left.isEmbedding.injective
        ((congrArg (fun f => f.left t) hk).trans ht)⟩
  have hkinv : Stacks.Groupoids.IsInvariantSet R.groupoid (Set.range k.left) := by
    rw [hkRange]
    intro r hr
    have hs := congrArg (fun f => f.left r) R.hom.map_source
    have ht := congrArg (fun f => f.left r) R.hom.map_target
    change G.source.left (R.hom.mapArrows.left r) =
      R.hom.mapObjects.left (R.groupoid.source.left r) at hs
    change G.target.left (R.hom.mapArrows.left r) =
      R.hom.mapObjects.left (R.groupoid.target.left r) at ht
    show R.hom.mapObjects.left (R.groupoid.target.left r) ∈ W
    exact ht ▸ hWinv (R.hom.mapArrows.left r) (hs.symm ▸ hr)
  have : Mono K.hom.mapObjects := Over.mono_of_mono_left _
  have : Mono R.hom.mapObjects := Over.mono_of_mono_left _
  obtain ⟨a, sq, hat, _⟩ := source_isPullback_of_open_fullyFaithful_factor
    K.hom R.hom K.evaluation_fullyFaithful R.evaluation_fullyFaithful k hk hkinv
  have himage : Set.range m.imageι = closure (W : Set G.objects.left) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker, hmRange]
  have hOrbit : ∀ y : G.objects.left, ∃ z : m.image, ∃ r : G.arrows.left,
      G.source.left r = y ∧ G.target.left r = m.imageι z := by
    intro y
    obtain ⟨z, hz, hzW⟩ := exists_orbit_point_mem_closure_of_saturation G W hsat y
    obtain ⟨z', rfl⟩ := (show z ∈ Set.range m.imageι by rwa [himage])
    exact ⟨z', hz⟩
  obtain ⟨z, r, hrs, hrt⟩ := hOrbit x
  let zR := (eqToHom R.objects_eq.symm).left z
  have hzR : R.hom.mapObjects.left zR = m.imageι z := restrict_mapObjects_eqToHom_apply G gZ z
  have hdimR : ∀ y, (∃ q : R.groupoid.arrows.left,
      R.groupoid.source.left q = zR ∧ R.groupoid.target.left q = y) →
      Ring.KrullDimLE 1 (R.groupoid.objects.left.presheaf.stalk y) := by
    apply orbit_stalk_dimension_le_one_of_groupoidHom R.groupoid G R.hom zR
    rintro y ⟨q, hqs, hqt⟩
    obtain ⟨c, hcs, hct⟩ := exists_comp_point G q r (hqs.trans (hzR.trans hrt.symm))
    exact hdim y ⟨c, hcs.trans hrs, hct.trans hqt⟩
  obtain ⟨V, hVi, hVa, hzV⟩ := exists_invariant_affineOpen_of_dense_flat_open H06AD
    R.groupoid K.groupoid k a sq hat ((isDominant_iff k.left).1 inferInstance) zR hdimR
  obtain ⟨V, hVi, hVa, hzV⟩ := exists_invariant_affineOpen_of_integral_restrict G gZ
    hOrbit z ⟨V, hVi, hVa, (over_eqToHom_apply_in_restriction R.objects_eq z) ▸ hzV⟩
  exact ⟨V, hVi, hVa, mem_of_mem_orbit_invariant_open G V hVi ⟨r, hrs, hrt⟩ hzV⟩

/-- **The quasi-affine case of [Stacks, Tag 0ABI], granted [Stacks, Tag 06AD].** Let `G` be a
groupoid scheme whose source and target maps are finite and whose object scheme is separated and
locally Noetherian, let `V` be an invariant open of the object scheme contained in an affine
open, and let `u ∈ V` be a point such that every point of its orbit has a stalk of Krull
dimension at most one. Then `u` lies in an invariant affine open of the object scheme.

This is what the first step of the source's proof reduces [Stacks, Tag 0ABI] to: the restriction
of `G` to `V` is a groupoid scheme with finite source and target whose object scheme is
Noetherian and quasi-affine, since `V` is an open of an affine open, so
`exists_invariant_affineOpen_of_isNoetherian_isQuasiAffine` applies to it, and the invariant
affine open it produces is carried back along the open immersion of `V`.

The hypothesis `H06AD` is [Stacks, Tag 06AD] -- a thickening of an affine scheme is affine --
and is the only thing assumed. -/
theorem exists_isInvariantOpen_isAffineOpen_mem_of_le_isAffineOpen
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [G.objects.left.IsSeparated] [IsLocallyNoetherian G.objects.left]
    (V U' : G.objects.left.Opens) (hVinv : Stacks.Groupoids.IsInvariantOpen G V)
    (hU'aff : IsAffineOpen U') (hVU' : V ≤ U') (u : G.objects.left) (huV : u ∈ V)
    (hdim : ∀ u' : G.objects.left,
      (∃ r : G.arrows.left, G.source.left.base r = u ∧ G.target.left.base r = u') →
        Ring.KrullDimLE 1 (G.objects.left.presheaf.stalk u')) :
    ∃ W : G.objects.left.Opens,
      Stacks.Groupoids.IsInvariantOpen G W ∧ IsAffineOpen W ∧ u ∈ W := by
  classical
  have : IsAffine U'.toScheme := hU'aff
  have : IsNoetherian U'.toScheme := ⟨⟩
  let g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk V.ι
  let R := AlgebraicGeometry.GroupoidScheme.restrict G g
  have : IsOpenImmersion g.left := show IsOpenImmersion V.ι from inferInstance
  have hginv : Stacks.Groupoids.IsInvariantSet G (Set.range g.left) := by
    show Stacks.Groupoids.IsInvariantSet G (Set.range V.ι)
    rw [V.range_ι]
    exact hVinv
  have : IsOpenImmersion R.hom.mapObjects.left :=
    (restriction_mapObjects_property_iff G g R @IsOpenImmersion).2 inferInstance
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsFinite R.groupoid.source.left :=
    (restriction_source_property_iff_of_invariant_open G g hginv R @IsFinite).2
      (finite_over_pullback_snd G.source g)
  have : IsFinite R.groupoid.target.left :=
    (groupoid_source_property_iff_target R.groupoid @IsFinite).1 inferInstance
  have hRrange : Set.range R.hom.mapObjects.left = (V : Set G.objects.left) := by
    rw [range_restriction_mapObjects G g R]
    exact V.range_ι
  have hRU : Set.range R.hom.mapObjects.left ⊆ Set.range U'.ι := by
    simpa only [hRrange, U'.range_ι] using SetLike.coe_subset_coe.mpr hVU'
  let j := IsOpenImmersion.lift U'.ι R.hom.mapObjects.left hRU
  have hj : j ≫ U'.ι = R.hom.mapObjects.left := IsOpenImmersion.lift_fac ..
  have : IsOpenImmersion (j ≫ U'.ι) := hj.symm ▸ inferInstance
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j U'.ι
  have : IsLocallyNoetherian R.groupoid.objects.left := LocallyOfFiniteType.isLocallyNoetherian j
  have : NoetherianSpace R.groupoid.objects.left := j.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian R.groupoid.objects.left := ⟨⟩
  have : R.groupoid.objects.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion j
  obtain ⟨y, hy⟩ := (show u ∈ Set.range R.hom.mapObjects.left by rwa [hRrange])
  have hdimR := orbit_stalk_dimension_le_one_of_groupoidHom R.groupoid G R.hom y
    (by simpa only [hy] using hdim)
  obtain ⟨W, hWinv, hWaff, hyW⟩ :=
    exists_invariant_affineOpen_of_isNoetherian_isQuasiAffine H06AD R.groupoid y hdimR
  exact ⟨_, invariant_image_of_restriction G g R (hRrange.symm ▸ hVinv) _ hWinv,
    hWaff.image_of_isOpenImmersion _, ⟨y, hyW, hy⟩⟩

end AlgebraicGeometry.GroupoidScheme

end
