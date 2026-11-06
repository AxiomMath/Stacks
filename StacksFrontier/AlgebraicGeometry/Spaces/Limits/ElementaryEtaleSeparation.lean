module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.UniversallyClosedSeparation

/-!
# Separating a closed subset over an elementary étale neighbourhood

Tag 0CM8 separates a closed subset of `|X ×_Y Z|` from a point `z` of `|Z|` after passing to an
étale neighbourhood `(V, v) → (Z, z)`. When `Z` is a scheme the neighbourhood can be taken
*elementary*: the canonical morphism `Spec κ(z) ⟶ Z` factors through it, so `v` and `z` have
the same residue field.

This is the refinement that survives for an arbitrary algebraic space `Y` with no hypothesis on
`Z ⟶ Y`. The source's own refinement asks for `V` to be an affine *open* neighbourhood of `z`,
which for a general `Y` amounts to a Zariski-local factorization of `Z ⟶ Y` at `z` through an
affine scheme locally of finite presentation over `Y`, by
`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_separation`;
reading that off an affine étale chart `U` of `Y` would need a section of the étale morphism
`Z ×_Y U ⟶ Z` near `z`, and therefore the local ring at `z` to be unchanged. The elementary
condition asks only for the residue field, and that much is always available because a
field-valued point of an arbitrary algebraic space always lifts along some affine étale chart.

## Main results

* `AlgebraicGeometry.Space.exists_affine_elementary_etale_separation`: Tag 0CM8 for `Z` a
  scheme, with `V` and `Z'` affine and the étale neighbourhood of `z` elementary.

## Implementation notes

The chart of `Y` is chosen by
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_fieldValuedPoint`, applied to the
canonical field-valued point of `z` pushed into `Y`. Its pullback along `Z₀ ⟶ Y` is an object
of the site étale over `Z₀` through which that field-valued point factors; an affine open
around the image of the field-valued point is the chart handed to the core of Tag 0CM8, and the
core shrinks it again around the same point, so the field-valued point survives into the
neighbourhood the core returns.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ElementaryEtaleSeparation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_ElementaryEtaleSeparation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The chart data of Tag 0CM8 at a point `z` of a scheme `Z₀` over an algebraic space `Y`,
refined so that the canonical field-valued point of `z` factors through the chart: an affine
`U` étale over `Y`, an affine `V₀` étale over `Z₀` whose morphism to `Y` factors through `U`, a
point `v₀` of `|V₀|` above `z`, and a morphism from `Spec κ(z)` to `V₀` over `Z₀` hitting it. -/
private theorem exists_elementary_chart_factorization
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y) (g : yoneda.obj Z₀ ⟶ Y)
    (pt : FieldValuedPoint B S hS (yoneda.obj Z₀)) :
    ∃ (U V₀ : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y) (p₀ : V₀ ⟶ Z₀) (α₀ : V₀ ⟶ U)
      (s₀ : FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt ⟶ V₀)
      (v₀ : points B S hS (yoneda.obj V₀)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧
      IsEtale B S hS ι ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map p₀) ∧
      yoneda.map p₀ ≫ g = yoneda.map α₀ ≫ ι ∧
      s₀ ≫ p₀ = pt.siteHom ∧
      pointsMap B S hS (yoneda.obj V₀) (yoneda.map p₀) v₀ =
        pt.class B S hS (yoneda.obj Z₀) ∧
      pointsToScheme B S hS V₀ v₀ = (BigFppfOver.toScheme B S hS).map s₀
        (IsLocalRing.closedPoint pt.carrier) := by
  classical
  have := subsingleton_toScheme_siteObject B S hS _ pt
  set k : (FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt) ⟶ Z₀ := pt.siteHom with hkdef
  obtain ⟨U, ι, t, hUaff, hιet, ht⟩ := exists_affine_etale_chart_of_fieldValuedPoint B S hS hY
    (FieldValuedPoint.map B S hS (yoneda.obj Z₀) g pt)
  have htk : yoneda.map t ≫ ι = yoneda.map k ≫ g := by
    rw [ht, fieldMorphism_map, hkdef, fieldMorphism_yoneda]
  have hιetP : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ι :=
    presheaf_etale_of_isEtale B S hS hιet
  have hιRep : yoneda.relativelyRepresentable ι := hιetP.rep
  obtain ⟨m, hm⟩ : ∃ m : FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt ⟶
      hιRep.pullback g, yoneda.map m =
        (hιRep.isPullback g).lift (yoneda.map t) (yoneda.map k) htk :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hmsnd : m ≫ hιRep.snd g = k := by
    refine yoneda.map_injective ?_
    rw [CategoryTheory.Functor.map_comp, hm]
    exact (hιRep.isPullback g).lift_snd _ _ _
  obtain ⟨-, ⟨D, hD, rfl⟩, hωD, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj
      (hιRep.pullback g)).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((BigFppfOver.toScheme B S hS).map m
        (IsLocalRing.closedPoint pt.carrier))) isOpen_univ
  obtain ⟨V₀, jW, hjWopen, hjWrange, hV₀aff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS (hιRep.pullback g) ⟨D, hD⟩
  obtain ⟨s₀, hs₀⟩ := exists_comp_eq_of_isOpenImmersion_of_range_subset B S hS jW m hjWopen (by
    rw [hjWrange]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint pt.carrier)]
    exact hωD)
  set taut := (pt.tautologicalPoint B S hS (yoneda.obj Z₀)).class B S hS
    (yoneda.obj (FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt)) with htautdef
  have hptaut : pointsToScheme B S hS
      (FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt) taut =
      IsLocalRing.closedPoint pt.carrier := by
    have h : pointsToScheme B S hS
        (FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt) taut =
        (BigFppfOver.toScheme B S hS).map
          (𝟙 (FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀) pt))
          (IsLocalRing.closedPoint pt.carrier) := rfl
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  have hkv : pointsMap B S hS _ (yoneda.map k) taut = pt.class B S hS (yoneda.obj Z₀) := by
    rw [hkdef, ← fieldMorphism_yoneda, htautdef, pointsMap_fieldMorphism_tautologicalPoint]
  refine ⟨U, V₀, ι, jW ≫ hιRep.snd g, jW ≫ hιRep.fst' g, s₀,
    pointsMap B S hS _ (yoneda.map s₀) taut, hUaff, hV₀aff, hιet, ?_, ?_, ?_, ?_, ?_⟩
  · exact (presheaf_yoneda_map_etale_iff B S hS _).2 (by
      rw [(BigFppfOver.toScheme B S hS).map_comp]
      have : AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map jW) := hjWopen
      have : Etale ((BigFppfOver.toScheme B S hS).map (hιRep.snd g)) :=
        hιetP.property g (hιRep.fst g) (hιRep.snd g) (hιRep.isPullback g)
      infer_instance)
  · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      Category.assoc, hιRep.map_fst', hιRep.w g]
  · rw [← Category.assoc, hs₀, hmsnd]
  · rw [← pointsMap_comp_apply, ← CategoryTheory.Functor.map_comp,
      ← Category.assoc, hs₀, hmsnd, hkv]
  · rw [pointsToScheme_pointsMap_yoneda, hptaut]

/-- **Stacks 0CM8 for `Z` a scheme, with an elementary étale neighbourhood.** Let
`f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S` with `Z` represented by
an object `Z₀` of the site, let `z` be a point of `|Z₀|`, and let `T` be a closed subset of
`|X ×_Y Z₀|` whose image in `|Z₀|` misses `z`. Then the conclusion of Tag 0CM8 holds with `V`
and `Z'` affine and with the étale neighbourhood `p : V ⟶ Z₀` *elementary*: the canonical
morphism `Spec κ(z) ⟶ Z₀` factors through it, so `v` and `z` have the same residue field.

The source asks only for an étale neighbourhood. The elementary refinement holds for an
arbitrary algebraic space `Y`, because the chart of `Y` can be chosen to receive the
field-valued point of `z`. -/
@[stacks 0CM8 "the separation statement for Z a scheme, with V and Z' affine and the etale \
neighbourhood of z elementary -- the canonical morphism Spec kappa(z) -> Z factors through it \
-- and with clauses (1), (2) and (3) unchanged"]
theorem exists_affine_elementary_etale_separation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : yoneda.obj Z₀ ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (yoneda.obj Z₀))
    (T : Set (points B S hS (pullback f g))) (hT : IsClosed T)
    (hz : z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T) :
    ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ yoneda.obj Z₀) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
      (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
      (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b)
      (s : FieldValuedPoint.siteObject B S hS (yoneda.obj Z₀)
        (schemePointRepresentative B S hS Z₀ (pointsToScheme B S hS Z₀ z)) ⟶ V),
      p = yoneda.map pV ∧
      s ≫ pV = (schemePointRepresentative B S hS Z₀ (pointsToScheme B S hS Z₀ z)).siteHom ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
      IsEtale B S hS p ∧
      pointsMap B S hS (yoneda.obj V) p v = z ∧
      p ≫ g = a ≫ b ∧
      IsLocallyOfFinitePresentation B S hS b ∧
      IsClosed T' ∧
      pointsMap B S hS (yoneda.obj V) a v ∉
        pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
      r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
      r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
      IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
      q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
      q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
      pointsMap B S hS (pullback f (p ≫ g)) q ''
        (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T' := by
  classical
  have := subsingleton_toScheme_siteObject B S hS _
    (schemePointRepresentative B S hS Z₀ (pointsToScheme B S hS Z₀ z))
  obtain ⟨U, V₀, ι, p₀, α₀, s₀, v₀, hUaff, hV₀aff, hιet, hp₀et, hfac₀, hs₀k, hv₀, hptV₀⟩ :=
    exists_elementary_chart_factorization B S hS hY g
      (schemePointRepresentative B S hS Z₀ (pointsToScheme B S hS Z₀ z))
  rw [class_schemePointRepresentative_pointsToScheme] at hv₀
  obtain ⟨V, Z', jV, v, a, b, T', r, q, hVaff, hZ'aff, hjVetale, hjVopen, hv, hpv, hpg,
    hblfp, hT'closed, hT'not, hr₁, hr₂, sqr, hqqfst, hqqsnd, hsub⟩ :=
    exists_separation_of_affine_lfp_chart B S hS hX hY f g hf z T hT hz ι hUaff
      (isLocallyOfFinitePresentation_of_isEtale B S hS hιet) hV₀aff
      (yoneda.map p₀) α₀ hfac₀ v₀ hv₀
  obtain ⟨s, hs⟩ := exists_comp_eq_of_isOpenImmersion_of_range_subset B S hS jV s₀ hjVopen (by
    rintro _ ⟨x, rfl⟩
    refine ⟨pointsToScheme B S hS V v, ?_⟩
    rw [← pointsToScheme_pointsMap_yoneda, hv, hptV₀]
    exact congrArg ((BigFppfOver.toScheme B S hS).map s₀) (Subsingleton.elim _ x))
  refine ⟨V, Z', yoneda.map jV ≫ yoneda.map p₀, jV ≫ p₀, v, a, b, T', r, q, s, ?_, ?_,
    hVaff, hZ'aff, ?_, hpv, hpg, hblfp, hT'closed, hT'not, hr₁, hr₂, sqr, hqqfst, hqqsnd,
    hsub⟩
  · rw [← CategoryTheory.Functor.map_comp]
  · rw [← Category.assoc, hs, hs₀k]
  · exact isEtale_of_presheaf_etale B S hS (MorphismProperty.comp_mem _ _ _
      ((presheaf_yoneda_map_etale_iff B S hS jV).2 hjVetale) hp₀et)

end AlgebraicGeometry.Space

end
