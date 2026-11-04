module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.BaseFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothBaseChange07U4

/-!
# The normalization descends along smooth surjective morphisms

Let `T` be an algebraic space over `S` with normalization `T^ν ⟶ T` (Stacks 07U4), and let
`v : V ⟶ T` be a smooth surjective morphism of algebraic spaces. If a morphism `w : W ⟶ T` of
algebraic spaces becomes the normalization of `V` after base change along `v`, that is
`W ×_T V ≅ V^ν` over `V`, then `W ≅ T^ν` over `T`.

This is the descent step behind "the base change property holds for every smooth morphism from a
scheme" in the proof of Stacks 0GMJ, which the source omits.

## Main results

* `AlgebraicGeometry.Space.isNormal_of_isFlat_of_isSurjective`: normality of algebraic spaces
  descends along flat surjective morphisms.
* `AlgebraicGeometry.Space.exists_localRingDimension_eq_zero_of_isFlat_of_isSurjective`: a point
  of codimension zero of the target of a flat surjective morphism of algebraic spaces is the
  image of a point of codimension zero of the source.
* `AlgebraicGeometry.Space.NormalizationData.exists_iso_of_isPullback_of_isSmooth`: the descent
  statement.

## Implementation notes

The comparison `W ⟶ T^ν` is the one given by the universal property of the normalization
(Stacks 0BB4, part (4)): `W` is normal because `W ×_T V ≅ V^ν` is and normality descends along
the flat surjection `W ×_T V ⟶ W`, and `W ⟶ T` preserves codimension zero because every point of
codimension zero of `W` lifts to one of `V^ν`. It is an isomorphism because its base change along
the fppf covering `V^ν ⟶ T^ν` is (Stacks 041Y): `V^ν = T^ν ×_T V` by Stacks 07U4, part (4), and
the base change of the comparison is then the identity of `V^ν`, by the uniqueness half of the
universal property.

## References

* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0GMC](https://stacks.math.columbia.edu/tag/0GMC)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Normality of algebraic spaces descends along flat surjective morphisms.** Every étale
chart `V ⟶ Y` of the target is covered, by Stacks 02X1, by an étale chart `U ⟶ X` of the source
with a flat surjective morphism `U ⟶ V`, and normality of schemes descends along flat surjective
morphisms. -/
theorem isNormal_of_isFlat_of_isSurjective {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hsurj : IsSurjective B S hS f) (hXn : IsNormal B S hS X) :
    IsNormal B S hS Y := by
  let T := BigFppfOver.toScheme B S hS
  have hXall := (isNormal_iff_forall_etale B S hS X hX).mp hXn
  refine (isNormal_iff_forall_etale B S hS Y hY).mpr fun V b hb => ?_
  obtain ⟨U, a, h, haE, hcomm, -, hhsurj⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hb
  have : Surjective (T.map h) := hhsurj hsurj
  have : Flat (T.map h) := hflat U V a b h haE hb hcomm
  have : _root_.AlgebraicGeometry.IsNormal (T.obj U) := hXall U a haE
  exact isNormal_of_flat_surjective (T.map h)

/-- **Points of codimension zero lift along flat surjective morphisms of algebraic spaces.** A
point of codimension zero of `Y` lies over a generic point `v` of an étale chart `V ⟶ Y`; an étale
chart `U ⟶ X` over `V` (Stacks 02X1) maps flatly and surjectively onto `V`, so some point of `U`
lies over `v`, and a generic point of `U` specializing to it maps to a generalization of `v`,
which is `v` itself. -/
theorem exists_localRingDimension_eq_zero_of_isFlat_of_isSurjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (_hflat : IsFlat B S hS f) (hsurj : IsSurjective B S hS f) (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ x : points B S hS X, localRingDimension B S hS x = 0 ∧ pointsMap B S hS X f x = y := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, hbS, hbE⟩ := hY.exists_atlas
  obtain ⟨v, hv⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY V b).mp hbS y
  have hvgen : pointsToScheme B S hS V v ∈ genericPoints (T.obj V) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hY y).mp hy V b _
      ((isEtale_iff_presheaf_of_yoneda B S hS b).mpr hbE)
      (hv ▸ chartPoint_pointsToScheme B S hS V b v)
  obtain ⟨U, a, h, haE, hcomm, -, hhsurj⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hbE
  have : Surjective (T.map h) := hhsurj hsurj
  obtain ⟨u, hu⟩ := (T.map h).surjective (pointsToScheme B S hS V v)
  let η : genericPoints (T.obj U) :=
    genericPoints.ofComponent
      ⟨irreducibleComponent u, irreducibleComponent_mem_irreducibleComponents u⟩
  have hη : η.1 ⤳ u :=
    (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent
  have hspec : T.map h η.1 ⤳ pointsToScheme B S hS V v := hu ▸ hη.map (T.map h).continuous
  have heq : T.map h η.1 = pointsToScheme B S hS V v := by
    have hrev : closure ({T.map h η.1} : Set (T.obj V)) ⊆ closure {pointsToScheme B S hS V v} :=
      hvgen.2 isIrreducible_singleton.closure hspec.closure_subset
    exact (hspec.antisymm (specializes_iff_closure_subset.mpr hrev)).eq
  obtain ⟨u', hu'⟩ := surjective_pointsToScheme B S hS U η.1
  refine ⟨pointsMap B S hS _ a u', ?_, ?_⟩
  · exact (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).mpr
      ⟨U, a, η.1, (isEtale_iff_presheaf_of_yoneda B S hS a).mpr haE,
        hu' ▸ chartPoint_pointsToScheme B S hS U a u', η.2⟩
  · have hv' : pointsMap B S hS _ (yoneda.map h) u' = v := by
      refine injective_pointsToScheme B S hS V ?_
      rw [pointsToScheme_pointsMap_yoneda, hu', heq]
    rw [← pointsMap_comp_apply, ← hcomm, pointsMap_comp_apply, hv', hv]

/-- **Stacks 03MH for a cartesian square of presheaves between algebraic spaces.** -/
theorem isSurjective_of_isPullback_presheaf {P Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {p : P ⟶ Z} {q : P ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hg : IsSurjective B S hS g) : IsSurjective B S hS q :=
  isSurjective_of_isPullback B S hS (isPullback_homMk B S hS hZ hX hY hP sq) hg

/-- A morphism of algebraic spaces whose base change along a smooth surjective morphism is an
identity is an isomorphism (Stacks 041Y). -/
theorem isIso_of_isPullback_id_of_isSmooth {W N N' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hN : IsAlgebraicSpace B S hS N)
    (hN' : IsAlgebraicSpace B S hS N') {a : W ⟶ N} {m : N' ⟶ N} {g : N' ⟶ W}
    (hm : IsSmooth B S hS m) (hms : IsSurjective B S hS m) (hup : IsPullback g (𝟙 N') a m) :
    IsIso a := by
  let Wa : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Na : AlgebraicSpaces B S hS := ⟨N, hN⟩
  let Na' : AlgebraicSpaces B S hS := ⟨N', hN'⟩
  let aA : Wa ⟶ Na := ObjectProperty.homMk a
  let mA : Na' ⟶ Na := ObjectProperty.homMk m
  let gA : Na' ⟶ Wa := ObjectProperty.homMk g
  have hupA : IsPullback gA (𝟙 Na') aA mA := isPullback_homMk B S hS hW hN' hN hN' hup
  have hmem : Presieve.ofArrows (fun _ : PUnit.{u + 1} => Na') (fun _ => mA) ∈
      Topology.precoverage.{u, u} .fppf B S hS Na :=
    ⟨PUnit, fun _ => Na', fun _ => mA, rfl, Na.property, fun _ => Na'.property,
      { target_isAlgebraicSpace := hN
        source_isAlgebraicSpace := fun _ => hN'
        flat := fun _ => isFlat_of_isSmooth B S hS m hm
        locallyOfFinitePresentation := fun _ =>
          isLocallyOfFinitePresentation_of_isSmooth B S hS hm
        jointly_surjective :=
          Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit, hms x⟩ }⟩
  have : IsIso aA := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := MorphismProperty.isomorphisms _) hmem ?_
    rintro U k _ ⟨⟩
    rw [← hupA.isoPullback_inv_snd]
    exact (inferInstance : IsIso (hupA.isoPullback.inv ≫ 𝟙 Na'))
  exact Functor.map_isIso (ObjectProperty.ι _) aA

namespace NormalizationData

/-- **The normalization descends along a smooth surjective morphism.** Let `D` be normalization
data for an algebraic space `T` over `S`, let `v : V ⟶ T` be a smooth surjective morphism of
algebraic spaces and `D'` normalization data for `V`, and let `w : W ⟶ T` be a morphism of
algebraic spaces whose base change along `v` is the normalization of `V`: there is a cartesian
square

```
V^ν ---g---> W
 |           |
 v           v w
 V  ---v---> T
```

Then `W` is the normalization of `T`: there is an isomorphism `W ≅ T^ν` over `T`. -/
theorem exists_iso_of_isPullback_of_isSmooth {T W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS T) (hT : IsAlgebraicSpace B S hS T)
    (hW : IsAlgebraicSpace B S hS W) (hV : IsAlgebraicSpace B S hS V)
    (w : W ⟶ T) (v : V ⟶ T) (hv : IsSmooth B S hS v) (hvs : IsSurjective B S hS v)
    (D' : NormalizationData B S hS V) (g : D'.space ⟶ W) (hsq : IsPullback g D'.hom w v) :
    ∃ e : W ≅ D.space, e.hom ≫ D.hom = w := by
  have hgF : IsFlat B S hS g :=
    isFlat_of_isSmooth B S hS g (isSmooth_of_isPullback hsq D'.isAlgebraicSpace hV hW hT hv)
  have hgS : IsSurjective B S hS g :=
    isSurjective_of_isPullback_presheaf D'.isAlgebraicSpace hV hW hT hsq.flip hvs
  have hvF : IsFlat B S hS v := isFlat_of_isSmooth B S hS v hv
  have hWn : IsNormal B S hS W :=
    isNormal_of_isFlat_of_isSurjective D'.isAlgebraicSpace hW g hgF hgS (D'.isNormal hV)
  have hgenM : ∀ z : points B S hS D'.space, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS _ (D'.hom ≫ v) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply]
    exact localRingDimension_eq_zero_of_isFlat B S hS hV hT v hvF _
      ((D'.bijOn_codimensionZeroPoints_hom hV).1 hz)
  have hgen : ∀ z : points B S hS W, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS W w z) = 0 := by
    intro z hz
    obtain ⟨z'', hz'', rfl⟩ :=
      exists_localRingDimension_eq_zero_of_isFlat_of_isSurjective D'.isAlgebraicSpace hW g hgF
        hgS z hz
    rw [← pointsMap_comp_apply, hsq.w]
    exact hgenM _ hz''
  obtain ⟨a, ha, -⟩ := D.existsUnique_lift_hom hT hW hWn w hgen
  obtain ⟨m, hm⟩ := D.isPullback_hom_of_isSmooth D' hT hV v hv
  have hga : g ≫ a = m :=
    (D.existsUnique_lift_hom hT D'.isAlgebraicSpace (D'.hasEtaleLocalProperty_isNormal hV)
      (D'.hom ≫ v) hgenM).unique (by rw [Category.assoc, ha, hsq.w]) hm.w
  have hup : IsPullback g (𝟙 _) a m :=
    IsPullback.of_bot (by rwa [Category.id_comp, ha]) (by rw [hga, Category.id_comp]) hm
  have : IsIso a := isIso_of_isPullback_id_of_isSmooth hW D.isAlgebraicSpace D'.isAlgebraicSpace
    (isSmooth_of_isPullback hm D'.isAlgebraicSpace hV D.isAlgebraicSpace hT hv)
    (isSurjective_of_isPullback_presheaf D'.isAlgebraicSpace hV D.isAlgebraicSpace hT hm.flip hvs)
    hup
  exact ⟨asIso a, ha⟩

end NormalizationData

end AlgebraicGeometry.Space

end
