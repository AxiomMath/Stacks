module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus

/-!
# The codimension-zero points of a Zariski locally quasi-separated algebraic space

A Zariski locally quasi-separated algebraic space over a scheme `S` has a dense open subspace
which is a scheme, and that subspace contains every point of codimension `0`: this is
**Stacks 06NH** in full.

The density clause is
`AlgebraicGeometry.Space.denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver` of
`StacksFrontier/AlgebraicGeometry/Spaces/ZariskiLocallyQuasiSeparatedSchematicLocus.lean`. This
module proves the codimension-zero clause and assembles the two into one statement about the
schematic locus of Tag 03JH.

## Main results

* `AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_of_isOpenSubspace`: the schematic
  locus of an open subspace maps into the schematic locus of the ambient space.
* `AlgebraicGeometry.Space.codimensionZero_mem_schematicLocus_of_affineQuasiCompactEtaleAtlas`:
  the codimension-zero clause for a space carrying a single affine quasi-compact surjective
  étale atlas.
* `AlgebraicGeometry.Space.codimensionZero_mem_schematicLocus_of_isZariskiLocallyQuasiSeparated`
  is the codimension-zero clause of **Stacks 06NH**, and
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_codimensionZero` is
  **Stacks 06NH** entire; its form over `S` is
  `exists_denseRange_isOpenSubspace_codimensionZero_of_isZariskiLocallyQuasiSeparatedOver`.
* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_mem_range_of_mem_genericPoints`:
  **Stacks 0ADC**, the final statement: a generic point of an irreducible component of a
  quasi-separated algebraic space lies in an open subspace which is a scheme. It needs exactly
  the codimension-zero clause of Tag 06NH, so it is proved here rather than alongside the rest of
  Tag 0ADC in
  `StacksFrontier/AlgebraicGeometry/Spaces/ZariskiLocallyQuasiSeparatedSchematicLocus.lean`.

## Implementation notes

The source's route is followed. Tag 03W7 replaces Zariski local quasi-separatedness by a
Zariski covering whose members carry a quasi-compact surjective étale atlas `q : h_A ⟶ X_i`
by an affine scheme, and Tag 03JH makes the question local in the only sense needed here: a
point lying in a representable open subspace lies in the schematic locus, which is
`AlgebraicGeometry.Space.range_pointsMap_ι_le_schematicLocus`, and an open subspace of an open
subspace is an open subspace, which is
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isOpenSubspace`. Being
étale, the inclusion of a member of the covering preserves the dimension of the local ring
(Tag 0A4H), so the point to be placed is again of codimension `0` on the member.

Above a codimension-zero point `x` of such a member, `q` is finite after shrinking the member:
`q` is separated because `A` is an affine scheme (Tag 03FZ), hence quasi-separated, and of
finite type because it is étale and quasi-compact; being étale it is locally quasi-finite, so
it is quasi-finite at every point of `h_A` and its field fibre above `x` is finite by the
equivalence of conditions (1) and (2) of Tag 0ACZ. Condition (3) of that tag — which is where
the source's Tag 02NW enters, and is proved from it in
`StacksFrontier/AlgebraicGeometry/Spaces/GenericallyFinite.lean` — produces an open subspace
`V ⊆ X_i` containing `x` over which `q` becomes finite. The source instead shrinks `A` to an
`R`-invariant open on which the first projection of `R = A ×_{X_i} A` is finite and forms the
quotient; here the shrinking happens on the target, so no invariance has to be arranged and no
quotient has to be formed.

The base change of `q` along `V ⊆ X_i` is represented by an object `N` of the site, because
the inclusion of an open subspace is relatively representable, and the second projection
`N ⟶ A` is an open immersion, so the underlying scheme of `N` is open in an affine scheme and
therefore quasi-separated. The chart `h_N ⟶ V` is finite by construction and étale and
surjective as a base change of `q`, which is exactly the hypothesis of Tag 0BAS; its
codimension-zero clause,
`AlgebraicGeometry.Space.codimensionZero_mem_schematicLocus`, places the point in the
schematic locus of `V`, and the two localisation steps carry it to the schematic locus of `X`.

Tag 06NH is stated under exactly the hypotheses of the source: an algebraic space over `S`
which is Zariski locally quasi-separated in the absolute sense of Tag 03BS part (4), and nothing
else; Tag 03W7 turns this into Zariski local quasi-separatedness over `S`, under which the
proof runs. Tag 03W7 is used only
through its implications `(1) ⇒ (4) ⇒ (3)`, which do not mention the slice over the terminal
scheme, so the containment of that scheme in the site is not needed here even as a device.
Where it is unavoidable — in the density clause, which passes through the absolute notion of
Tag 03BS part (4) — it is supplied by
`AlgebraicGeometry.BigFppfSite.contains_terminal`, which holds of every big fppf site.

## References

* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03W7](https://stacks.math.columbia.edu/tag/03W7)
* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 0ACZ](https://stacks.math.columbia.edu/tag/0ACZ)
* [Stacks Project, Tag 0ADC](https://stacks.math.columbia.edu/tag/0ADC)
* [Stacks Project, Tag 0BAS](https://stacks.math.columbia.edu/tag/0BAS)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high)
    hasPullbacks_presheaf_ZariskiLocallyQuasiSeparatedCodimensionZero :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high)
    hasPullback_presheaf_ZariskiLocallyQuasiSeparatedCodimensionZero
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A point of an open subspace which lies in the schematic locus of that subspace has its
image in the schematic locus of the ambient algebraic space.

The schematic locus of the subspace is a representable open subspace of it by Tag 03JH, hence
a representable open subspace of the ambient space, hence below its schematic locus. -/
theorem mem_range_pointsMap_schematicLocus_of_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : Subfunctor X} (hV : IsOpenSubspace B S hS V) {z : points B S hS V.toFunctor}
    (hz : z ∈ Set.range (pointsMap B S hS (schematicLocus B S hS V.toFunctor).toFunctor
      (schematicLocus B S hS V.toFunctor).ι)) :
    pointsMap B S hS V.toFunctor V.ι z ∈
      Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
        (schematicLocus B S hS X).ι) := by
  obtain ⟨hWopen, hWrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hV.1
  obtain ⟨K, hKopen, hKrep, hKrange⟩ :=
    exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hX hV hWopen hWrep
  refine range_pointsMap_ι_le_schematicLocus B S hS K hKopen hKrep ?_
  obtain ⟨w, rfl⟩ := hz
  rw [hKrange]
  exact ⟨w, pointsMap_comp_apply B S hS _ _ w⟩

/-- A point of an open subspace has local ring dimension `0` if its image in the ambient
algebraic space does, since open immersions are étale. -/
private theorem localRingDimension_eq_zero_of_pointsMap_ι
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {V : Subfunctor X} (hV : IsOpenSubspace B S hS V) {z : points B S hS V.toFunctor}
    (hz : localRingDimension B S hS (pointsMap B S hS V.toFunctor V.ι z) = 0) :
    localRingDimension B S hS z = 0 :=
  (localRingDimension_pointsMap_of_etale B S hS hV.1 hX V.ι
    (isEtale_of_isOpenImmersion B S hS hV.2) z).symm.trans hz

/-- **The codimension-zero clause of Stacks 06NH for a single affine chart.** If an algebraic
space over `S` carries a quasi-compact surjective étale atlas by an affine scheme, then each of
its points of codimension `0` lies in the schematic locus of Tag 03JH.

Tag 0ACZ shrinks the space to an open subspace over which the atlas is finite, and Tag 0BAS
applies to that subspace. -/
theorem codimensionZero_mem_schematicLocus_of_affineQuasiCompactEtaleAtlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hatlas : HasAffineQuasiCompactEtaleAtlas B S hS X)
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0) :
    x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
      (schematicLocus B S hS X).ι) := by
  classical
  obtain ⟨A, q, hAaff, hqc, hqsurj, hqetale⟩ := hatlas
  have hA : IsAlgebraicSpace B S hS (yoneda.obj A) := isAlgebraicSpace_yoneda B S hS A
  have hq : IsEtale B S hS q := (isEtale_iff_presheaf_of_yoneda B S hS q).mpr hqetale
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
  -- `q` is quasi-separated and of finite type
  have hqqs : IsQuasiSeparated B S hS q :=
    isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX A inferInstance q hq)
  have hqft : IsFiniteType B S hS q := ⟨isLocallyOfFiniteType_of_isEtale B S hS hX hq, hqc⟩
  -- the field fibre of `q` above `x` is finite, `q` being locally quasi-finite
  obtain ⟨p, hp⟩ := Quot.exists_rep x
  have hfield : Set.Finite (Set.univ : Set (points B S hS
      (pullback q (yonedaEquiv.symm p.value)))) :=
    (finite_fieldFiber_iff_quasiFiniteAt_fiber B S hS hA hX q hqqs hqft x p hp).mpr
      fun w _ ↦ isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hA
        (isLocallyQuasiFinite_of_isEtale B S hS hX hq) w
  -- Tag 0ACZ: an open subspace containing `x` over which `q` is finite
  obtain ⟨V, hV, ⟨z, rfl⟩, hfin⟩ :=
    exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber B S hS hA hX q hqqs hqft
      x p hp hx hfield
  -- the base change of `q` along `V`, as a chart of `V` by an object of the site
  set N := hV.2.rep.pullback q
  set a : yoneda.obj N ⟶ V.toFunctor := hV.2.rep.fst q
  set t : N ⟶ A := hV.2.rep.snd q
  have sq : IsPullback a (yoneda.map t) V.ι q := hV.2.rep.isPullback q
  have _ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) :=
    hV.2.property_snd q
  have hNqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj N) :=
    AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map t)
  -- the chart is finite, étale and surjective
  have hNalg : IsAlgebraicSpace B S hS (yoneda.obj N) := isAlgebraicSpace_yoneda B S hS N
  have hPalg : IsAlgebraicSpace B S hS (pullback q V.ι) :=
    isAlgebraicSpace_pullback B S hS q V.ι hA hV.1 hX
  let e : yoneda.obj N ≅ pullback q V.ι :=
    sq.flip.isoIsPullback _ _ (IsPullback.of_hasPullback q V.ι)
  have hea : e.hom ≫ pullback.snd q V.ι = a :=
    sq.flip.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback q V.ι)
  have hafin : IsFinite B S hS a := by
    refine (isFinite_iff_representable B S hS a hNalg hV.1).2 ?_
    have h := ((isFinite_iff_representable B S hS (pullback.snd q V.ι) hPalg hV.1).1 hfin).2
    have ha := MorphismProperty.RespectsIso.precomp _ e.hom _ h
    rw [hea] at ha
    exact ⟨ha.rep, ha⟩
  have hEbc : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hSbc : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have haetale : IsEtale B S hS a :=
    (isEtale_iff_presheaf_of_yoneda B S hS a).mpr (hEbc.of_isPullback sq.flip hqetale)
  have hasurj : IsSurjective B S hS a :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS V.toFunctor hV.1 N a).1
      (hSbc.of_isPullback sq.flip hqsurj)
  -- Tag 0BAS on `V`, then Tag 03JH to return to `X`
  exact mem_range_pointsMap_schematicLocus_of_isOpenSubspace B S hS hX hV
    (codimensionZero_mem_schematicLocus B S hS V.toFunctor hV.1
      ⟨N, a, hNqs, hafin, haetale, hasurj⟩ z
      (localRingDimension_eq_zero_of_pointsMap_ι B S hS hX hV hx))

/-- **Stacks 06NH, codimension-zero points.** Every point of codimension `0` of a Zariski
locally quasi-separated algebraic space over `S` lies in the schematic locus of Tag 03JH, so
in a dense open subspace which is a scheme.

Tag 03W7 covers the space by open subspaces carrying affine quasi-compact surjective étale
atlases, and the inclusion of a member of the covering, being étale, preserves both the
dimension of the local ring at a point (Tag 0A4H) and the schematic locus. -/
theorem codimensionZero_mem_schematicLocus_of_isZariskiLocallyQuasiSeparated
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F)
    (x : points B S hS F) (hx : localRingDimension B S hS x = 0) :
    x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι) := by
  obtain ⟨I, U, hcover, hatlas⟩ :=
    hasAffineQuasiCompactEtaleCover_of_hasAffineQuasiCompactEtaleCoverIntoAffineBase B S hS
      (hasAffineQuasiCompactEtaleCoverIntoAffineBase_of_isZariskiLocallyQuasiSeparatedOver
        B S hS hF hqs)
  have hxU : x ∈ ⋃ i, Set.range (pointsMap B S hS (U i).toFunctor (U i).ι) := by
    rw [(isZariskiCover_iff_iUnion_points B S hS F hF I U hcover.1).1 hcover]
    exact Set.mem_univ x
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hxU
  exact mem_range_pointsMap_schematicLocus_of_isOpenSubspace B S hS hF (hcover.1 i)
    (codimensionZero_mem_schematicLocus_of_affineQuasiCompactEtaleAtlas B S hS
      (hcover.1 i).1 (hatlas i) y
      (localRingDimension_eq_zero_of_pointsMap_ι B S hS hF (hcover.1 i) hx))

/-- **Stacks 06NH, over `S`.** An algebraic space over `S` which is Zariski locally
quasi-separated over `S` has a dense open subspace which is a scheme, and every point of
codimension `0` of the space lies in that subspace. The subspace is the schematic locus of
Tag 03JH. -/
theorem exists_denseRange_isOpenSubspace_codimensionZero_of_isZariskiLocallyQuasiSeparatedOver
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsZariskiLocallyQuasiSeparatedOver B S hS F) :
    ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) ∧
      ∀ x : points B S hS F, localRingDimension B S hS x = 0 →
        x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) :=
  ⟨schematicLocus B S hS F,
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).1,
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2,
    denseRange_schematicLocus_of_isZariskiLocallyQuasiSeparatedOver B S hS B.contains_terminal
      F hF hqs,
    codimensionZero_mem_schematicLocus_of_isZariskiLocallyQuasiSeparated B S hS F hF hqs⟩

/-- **Stacks 06NH.** A Zariski locally quasi-separated algebraic space over `S` — for instance
a quasi-separated one — has a dense open subspace which is a scheme, and every point of
codimension `0` of the space lies in that subspace. The subspace is the schematic locus of
Tag 03JH.

Zariski local quasi-separatedness is the absolute notion of Tag 03BS part (4), as in the
source; by Tag 03W7 it is equivalent to the notion over `S`, which is how the proof uses it. The
containment `hZ` of the terminal scheme in the site is the argument of that absolute notion; it
holds in every big fppf site, by `AlgebraicGeometry.BigFppfSite.contains_terminal`. -/
@[stacks 06NH]
theorem exists_denseRange_isRepresentable_isOpenSubspace_codimensionZero
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ F) :
    ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) ∧
      ∀ x : points B S hS F, localRingDimension B S hS x = 0 →
        x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isOpenSubspace_codimensionZero_of_isZariskiLocallyQuasiSeparatedOver
    B S hS F hF (((isZariskiLocallyQuasiSeparatedOver_tfae B S hS hZ F hF).out 2 1).mp hqs)

/-! ### The final statement of Tag 0ADC -/

/-- **Stacks 0ADC, the final statement.** A generic point of an irreducible component of the
space of points of a quasi-separated algebraic space over `S` lies in an open subspace which
is a scheme, namely in the schematic locus of Tag 03JH.

The equivalence of the tag's conditions (1), (2) and (3) is
`AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated`;
the codimension-zero clause of Tag 06NH which carries such a generic point into the schematic
locus is `codimensionZero_mem_schematicLocus_of_isZariskiLocallyQuasiSeparated` above. -/
@[stacks 0ADC "the final statement"]
theorem exists_isRepresentable_isOpenSubspace_mem_range_of_mem_genericPoints
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (x : points B S hS F) (hx : x ∈ genericPoints (points B S hS F)) :
    ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) :=
  ⟨schematicLocus B S hS F,
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).1,
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2,
    codimensionZero_mem_schematicLocus_of_isZariskiLocallyQuasiSeparated B S hS F hF
      (isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated B S hS hZ F hF hqs) x
      ((localRingDimension_eq_zero_iff_mem_genericPoints_of_quasiSeparated B S hS hZ F hF hqs
        x).mpr hx)⟩

end AlgebraicGeometry.Space

end
