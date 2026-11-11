module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutAbstractSquares
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFlatGluing

/-!
# The Rim-Schlessinger condition for flat families of morphisms of schemes

Example [Stacks Project, Tag 0E3T] presents the flat families of morphisms of schemes over
`𝒞_Λ` as a category cofibered in groupoids.  The first assertion of
[Stacks Project, Tag 0E3U] is that this category satisfies the Rim-Schlessinger condition (RS),
and the second is that the deformation category of a fixed morphism `X ⟶ Y` of schemes over the
residue field is then a deformation category.

This file proves the first assertion with no hypothesis.  The second then follows from
`Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategory` and is stated,
with no hypothesis, as
`Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategoryProjection` in
`StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional`,
which imports this file.

A cospan of families whose second leg is surjective
on bases lies over a cocartesian square of spectra, and the fibre product of the families is
assembled by gluing twice over that one square: the targets are glued to a scheme `Z_t` and the
sources to a scheme `Z_s`, and the morphism `Z_s ⟶ Z_t` is the one the universal property of
the pushout of the sources supplies.  Both gluings use the same two facts about flat schemes
over a pushout, `Stacks.Pushout.isPullback_of_isPushout_glued` (the last assertion of
[Stacks Project, Tag 07RV]) and `Stacks.Pushout.isPushout_restrictions_of_flat` (the
equivalence assertion of the closing paragraph of [Stacks Project, Tag 07RX]), together with
`Deformation.Examples.flat_glued_of_isPushout` for the flatness of the glued structure
morphisms.

## Main results

* `Deformation.Examples.isPullback_desc_of_flat_of_isPushout`: a flat scheme over the base of a
  cocartesian square receives the glued scheme cartesianly -- the half of the universal property
  that the two gluings share.
* `Deformation.Examples.satisfiesRS_schemeMorphismFamilyFunctor`: flat families of morphisms of
  schemes over `𝒞_Λ` satisfy condition (RS), unconditionally.

## Implementation notes

**Two gluings, one base square.**  A family of morphisms carries two schemes over its base, and
a morphism of families records the target square over the base
(`Deformation.Examples.SchemeMorphismFamily.Hom.target_pullback`) and the source square over
the *target* (`Deformation.Examples.SchemeMorphismFamily.Hom.source_pullback`).  The gluing
argument needs the source square over the *base*; that is
`Deformation.Examples.isPullback_source_toBase`, obtained by pasting the two recorded squares.
With it, the targets and the sources are two instances of one and the same gluing problem over
the one cocartesian square of spectra, and the two recorded squares are recovered at the end:
the target square is the gluing output directly, and the source square over the target comes
from `Deformation.Examples.isPullback_morphism_of_isPullback_toBase` applied to the two source-
and target-over-base squares.

**Where the commuting square of the glued morphism comes from.**  Nothing identifies
`Z_s ⟶ Z_t` beyond its two restrictions, and
`Deformation.Examples.isPullback_morphism_of_isPullback_toBase` needs that identification as an
input: it is `CategoryTheory.IsPushout.inl_desc` and `CategoryTheory.IsPushout.inr_desc` for
the descent map defining `Z_s ⟶ Z_t`.

**No bundling structure.**  The two gluing facts and the flatness of the glued structure
morphism are used directly rather than through `Deformation.Examples.FlatGluingSquares`, for
the same reason as in `Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection`: there is
then one copy of each fact, and no predicate whose inhabitedness has to be argued separately.
Both gluing facts take the commuting square of the restrictions as a genuine input, which is
what `Deformation.Examples.IsFlatGluing` omitted and was made uninhabited by.

## References

* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0E3U](https://stacks.math.columbia.edu/tag/0E3U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

open Deformation.ArtinianLocalAlgCat Stacks.Thickenings

/-- Two commuting squares over a commuting square give equal composites to its corner. -/
private theorem comp_comp_eq_of_comm {C : Type*} [Category C] {S S₁ S₂ T Y Y₁ Y₂ : C}
    {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁} {b₂ : S₂ ⟶ T} {b₁ : S₁ ⟶ T} {y : Y ⟶ S}
    {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂}
    (hpo : j₂ ≫ b₂ = j₁ ≫ b₁) (h₂ : g₂ ≫ y₂ = y ≫ j₂) (h₁ : g₁ ≫ y₁ = y ≫ j₁) :
    g₂ ≫ y₂ ≫ b₂ = g₁ ≫ y₁ ≫ b₁ := by
  rw [← Category.assoc, h₂, Category.assoc, hpo, ← Category.assoc, ← h₁, Category.assoc]

/-- **A flat scheme over the base receives the glued scheme cartesianly.**  Let
`IsPushout j₂ j₁ b₂ b₁` present `T` as `S₁ ⨿_S S₂`, let `Z` be glued over it from `Y₁` and
`Y₂`, and let `w : W ⟶ S'` be flat with `β : T ⟶ S'` and two cartesian squares exhibiting `Y₁`
and `Y₂` as the base changes of `W` along `b₁ ≫ β` and `b₂ ≫ β`.  Then the map `Z ⟶ W` induced
by those two is cartesian over `β`.

This is the half of the universal property of a glued family that does not mention the base
category, so the gluing of the sources and the gluing of the targets both use it.  It is the
argument of [Stacks Project, Tag 0DY8]: `W ×_{S'} T` is glued from `Y₁` and `Y₂` as well, by
`Stacks.Pushout.isPushout_restrictions_of_flat`, so the comparison with `Z` is an isomorphism
over `T` and over `W`. -/
theorem isPullback_desc_of_flat_of_isPushout {S S₁ S₂ T S' : Scheme.{v}}
    {j₂ : S ⟶ S₂} {j₁ : S ⟶ S₁} {b₂ : S₂ ⟶ T} {b₁ : S₁ ⟶ T}
    (hj₂ : IsThickening j₂) [IsAffineHom j₁] (hpo : IsPushout j₂ j₁ b₂ b₁)
    {Y Y₁ Y₂ Z W : Scheme.{v}} {y : Y ⟶ S} {y₁ : Y₁ ⟶ S₁} {y₂ : Y₂ ⟶ S₂} {z : Z ⟶ T}
    {w : W ⟶ S'} {β : T ⟶ S'}
    {g₁ : Y ⟶ Y₁} {g₂ : Y ⟶ Y₂} {c₁ : Y₁ ⟶ Z} {c₂ : Y₂ ⟶ Z} {v₁ : Y₁ ⟶ W} {v₂ : Y₂ ⟶ W}
    (hw : Flat w) (h₁ : IsPullback g₁ y y₁ j₁) (h₂ : IsPullback g₂ y y₂ j₂)
    (hZ : IsPushout g₂ g₁ c₂ c₁)
    (hz₁ : c₁ ≫ z = y₁ ≫ b₁) (hz₂ : c₂ ≫ z = y₂ ≫ b₂)
    (hv₁ : IsPullback v₁ y₁ w (b₁ ≫ β)) (hv₂ : IsPullback v₂ y₂ w (b₂ ≫ β))
    (hcomm : g₂ ≫ v₂ = g₁ ≫ v₁) :
    IsPullback (hZ.desc v₂ v₁ hcomm) z w β := by
  have := hw
  -- the base change of `W` to `T`, and the two given schemes read inside it
  have hWpb : IsPullback (Limits.pullback.fst w β) (Limits.pullback.snd w β) w β :=
    IsPullback.of_hasPullback _ _
  obtain ⟨e₁, hef₁, hes₁⟩ : ∃ e : Y₁ ⟶ Limits.pullback w β,
      e ≫ Limits.pullback.fst w β = v₁ ∧ e ≫ Limits.pullback.snd w β = y₁ ≫ b₁ :=
    ⟨hWpb.lift v₁ (y₁ ≫ b₁) (by rw [hv₁.w, Category.assoc]), hWpb.lift_fst _ _ _,
      hWpb.lift_snd _ _ _⟩
  obtain ⟨e₂, hef₂, hes₂⟩ : ∃ e : Y₂ ⟶ Limits.pullback w β,
      e ≫ Limits.pullback.fst w β = v₂ ∧ e ≫ Limits.pullback.snd w β = y₂ ≫ b₂ :=
    ⟨hWpb.lift v₂ (y₂ ≫ b₂) (by rw [hv₂.w, Category.assoc]), hWpb.lift_fst _ _ _,
      hWpb.lift_snd _ _ _⟩
  have he₁ : IsPullback e₁ y₁ (Limits.pullback.snd w β) b₁ :=
    IsPullback.of_right (by rwa [hef₁]) hes₁ hWpb
  have he₂ : IsPullback e₂ y₂ (Limits.pullback.snd w β) b₂ :=
    IsPullback.of_right (by rwa [hef₂]) hes₂ hWpb
  have hyb := comp_comp_eq_of_comm hpo.w h₂.w h₁.w
  have hcs : g₂ ≫ e₂ = g₁ ≫ e₁ := by
    refine hWpb.hom_ext ?_ ?_
    · simpa only [Category.assoc, hef₁, hef₂] using hcomm
    · simpa only [Category.assoc, hes₁, hes₂] using hyb
  -- the base change is glued from the same two schemes, so it is isomorphic to `Z` over both
  have hWpush : IsPushout g₂ g₁ e₂ e₁ :=
    Stacks.Pushout.isPushout_restrictions_of_flat hj₂ hpo inferInstance hcs he₁ he₂ h₁ h₂
  have hθ₁ : c₁ ≫ (hZ.isoIsPushout _ _ hWpush).hom = e₁ := hZ.inr_isoIsPushout_hom _ _ hWpush
  have hθ₂ : c₂ ≫ (hZ.isoIsPushout _ _ hWpush).hom = e₂ := hZ.inl_isoIsPushout_hom _ _ hWpush
  have hθfst : (hZ.isoIsPushout _ _ hWpush).hom ≫ Limits.pullback.fst w β =
      hZ.desc v₂ v₁ hcomm := by
    refine hZ.hom_ext ?_ ?_
    · rw [← Category.assoc, hθ₂, hef₂, hZ.inl_desc]
    · rw [← Category.assoc, hθ₁, hef₁, hZ.inr_desc]
  have hθsnd : (hZ.isoIsPushout _ _ hWpush).hom ≫ Limits.pullback.snd w β = z := by
    refine hZ.hom_ext ?_ ?_
    · rw [← Category.assoc, hθ₂, hes₂, hz₂]
    · rw [← Category.assoc, hθ₁, hes₁, hz₁]
  refine hWpb.of_iso (hZ.isoIsPushout _ _ hWpush).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hθfst, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hθsnd, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A cartesian square over `baseSpecMap (b ≫ q)` is one over `baseSpecMap q ≫ baseSpecMap b`. -/
private theorem isPullback_baseSpecMap_comp {A B C : ArtinianLocalAlgCat.{u, v, v} Λ k}
    {P₁ P₂ : Scheme.{v}} {fst : P₁ ⟶ P₂} {snd : P₁ ⟶ baseSpec C} {bot : P₂ ⟶ baseSpec A}
    (b : A ⟶ B) (q : B ⟶ C) (h : IsPullback fst snd bot (baseSpecMap (b ≫ q))) :
    IsPullback fst snd bot (baseSpecMap q ≫ baseSpecMap b) := by
  rwa [← baseSpecMap_comp]

/-- **Stacks Project, Tag 0E3U, first assertion.**  The category of flat families of morphisms
of schemes over `𝒞_Λ` of Example 0E3T satisfies the Rim-Schlessinger condition (RS), with no
hypothesis.

The fibre product of a cospan of families over a surjection of bases is glued twice over the
one cocartesian square of spectra that the surjection produces: the sources are glued, the
targets are glued, and the morphism between the two glued schemes is the descent of the two
given morphisms along the pushout of the sources. -/
@[stacks 0E3U "condition (RS) for the category of all flat families of morphisms of schemes of \
Example 0E3T -- the first assertion -- with nothing assumed. The two gluing facts it rests on \
are the last assertion of Tag 07RV and the equivalence assertion of the closing paragraph of \
Tag 07RX, both proved in this repository: Stacks.Pushout.isPullback_of_isPushout_glued and \
Stacks.Pushout.isPushout_restrictions_of_flat. The pushout of spectra, the existence of the \
glued family, the flatness of its two structure morphisms and both halves of the universal \
property are proved as well. The in-particular assertion, that the deformation category of a \
fixed morphism of schemes over k is a deformation category, is \
Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategoryProjection"]
theorem satisfiesRS_schemeMorphismFamilyFunctor :
    SatisfiesRS (schemeMorphismFamilyFunctor.{u, v} (Λ := Λ) (k := k)) := by
  classical
  refine ⟨schemeMorphismFamilyFunctor_cofiberedInGroupoids, ?_⟩
  intro X₁ X₂ X f₁ f₂ hsj
  have hsurj : Function.Surjective f₂.base.hom := hsj
  let hor : Function.Surjective f₁.base.hom ∨ Function.Surjective f₂.base.hom := Or.inr hsurj
  let P : ArtinianLocalAlgCat.{u, v, v} Λ k := pullbackObj_of_surjective f₁.base f₂.base hor
  let q₁ : P ⟶ X₁.base := pullbackFst_of_surjective f₁.base f₂.base hor
  let q₂ : P ⟶ X₂.base := pullbackSnd_of_surjective f₁.base f₂.base hor
  have hbp : IsPullback q₁ q₂ f₁.base f₂.base := isPullback_of_surjective _ _ hor
  have hpo : IsPushout (baseSpecMap f₂.base) (baseSpecMap f₁.base)
      (baseSpecMap q₂) (baseSpecMap q₁) :=
    isPushout_baseSpecMap_of_surjective f₁.base f₂.base hsurj
  have hthick : IsFiniteOrderThickening (baseSpecMap f₂.base) :=
    isFiniteOrderThickening_baseSpecMap f₂.base hsurj
  -- the four squares over the base: the two targets and, by pasting, the two sources
  have ht₁ : IsPullback f₁.target X.targetToBase X₁.targetToBase (baseSpecMap f₁.base) :=
    f₁.target_pullback
  have ht₂ : IsPullback f₂.target X.targetToBase X₂.targetToBase (baseSpecMap f₂.base) :=
    f₂.target_pullback
  have hs₁ : IsPullback f₁.source X.sourceToBase X₁.sourceToBase (baseSpecMap f₁.base) :=
    isPullback_source_toBase f₁
  have hs₂ : IsPullback f₂.source X.sourceToBase X₂.sourceToBase (baseSpecMap f₂.base) :=
    isPullback_source_toBase f₂
  have hiT : IsFiniteOrderThickening f₂.target := isFiniteOrderThickening_of_isPullback ht₂ hthick
  have hiS : IsFiniteOrderThickening f₂.source := isFiniteOrderThickening_of_isPullback hs₂ hthick
  have hfT : IsAffineHom f₁.target :=
    MorphismProperty.of_isPullback ht₁.flip
      (inferInstanceAs (IsAffineHom (baseSpecMap f₁.base)))
  have hfS : IsAffineHom f₁.source :=
    MorphismProperty.of_isPullback hs₁.flip
      (inferInstanceAs (IsAffineHom (baseSpecMap f₁.base)))
  have : HasPushout f₂.target f₁.target :=
    Stacks.Pushout.hasPushout_of_isFiniteOrderThickening_of_isAffineHom f₂.target f₁.target hiT
  have : HasPushout f₂.source f₁.source :=
    Stacks.Pushout.hasPushout_of_isFiniteOrderThickening_of_isAffineHom f₂.source f₁.source hiS
  have hZt : IsPushout f₂.target f₁.target (Limits.pushout.inl f₂.target f₁.target)
      (Limits.pushout.inr f₂.target f₁.target) := IsPushout.of_hasPushout _ _
  have hZs : IsPushout f₂.source f₁.source (Limits.pushout.inl f₂.source f₁.source)
      (Limits.pushout.inr f₂.source f₁.source) := IsPushout.of_hasPushout _ _
  set ct₂ := Limits.pushout.inl f₂.target f₁.target
  set ct₁ := Limits.pushout.inr f₂.target f₁.target
  set cs₂ := Limits.pushout.inl f₂.source f₁.source
  set cs₁ := Limits.pushout.inr f₂.source f₁.source
  -- the structure morphisms of the two glued schemes
  have hwt := comp_comp_eq_of_comm hpo.w ht₂.w ht₁.w
  have hws := comp_comp_eq_of_comm hpo.w hs₂.w hs₁.w
  set zt := hZt.desc (X₂.targetToBase ≫ baseSpecMap q₂) (X₁.targetToBase ≫ baseSpecMap q₁) hwt
  set zs := hZs.desc (X₂.sourceToBase ≫ baseSpecMap q₂) (X₁.sourceToBase ≫ baseSpecMap q₁) hws
  have hzt₂ : ct₂ ≫ zt = X₂.targetToBase ≫ baseSpecMap q₂ := hZt.inl_desc _ _ _
  have hzt₁ : ct₁ ≫ zt = X₁.targetToBase ≫ baseSpecMap q₁ := hZt.inr_desc _ _ _
  have hzs₂ : cs₂ ≫ zs = X₂.sourceToBase ≫ baseSpecMap q₂ := hZs.inl_desc _ _ _
  have hzs₁ : cs₁ ≫ zs = X₁.sourceToBase ≫ baseSpecMap q₁ := hZs.inr_desc _ _ _
  have hztflat : Flat zt :=
    flat_glued_of_isPushout hthick hpo X₁.target_flat X₂.target_flat ht₁ ht₂ hZt hzt₁ hzt₂
  have hzsflat : Flat zs :=
    flat_glued_of_isPushout hthick hpo X₁.source_flat X₂.source_flat hs₁ hs₂ hZs hzs₁ hzs₂
  -- the glued morphism, and the two cartesian squares of the glued family
  have hmw := comp_comp_eq_of_comm hZt.w f₂.source_pullback.w.symm f₁.source_pullback.w.symm
  set mZ := hZs.desc (X₂.morphism ≫ ct₂) (X₁.morphism ≫ ct₁) hmw
  have hmZ₂ : cs₂ ≫ mZ = X₂.morphism ≫ ct₂ := hZs.inl_desc _ _ _
  have hmZ₁ : cs₁ ≫ mZ = X₁.morphism ≫ ct₁ := hZs.inr_desc _ _ _
  have hob : mZ ≫ zt = zs := by
    refine hZs.hom_ext ?_ ?_
    · rw [← Category.assoc, hmZ₂, Category.assoc, hzt₂, ← Category.assoc, X₂.over_base, hzs₂]
    · rw [← Category.assoc, hmZ₁, Category.assoc, hzt₁, ← Category.assoc, X₁.over_base, hzs₁]
  obtain ⟨hct₁, hct₂⟩ :=
    Stacks.Pushout.isPullback_of_isPushout_glued hthick.isThickening hpo ht₁ ht₂ hZt hzt₁ hzt₂
  obtain ⟨hcs₁, hcs₂⟩ :=
    Stacks.Pushout.isPullback_of_isPushout_glued hthick.isThickening hpo hs₁ hs₂ hZs hzs₁ hzs₂
  let ZF : SchemeMorphismFamily.{u, v} Λ k :=
    { base := P
      source := Limits.pushout f₂.source f₁.source
      target := Limits.pushout f₂.target f₁.target
      morphism := mZ
      sourceToBase := zs
      targetToBase := zt
      over_base := hob
      source_flat := hzsflat
      target_flat := hztflat }
  let a₁ : ZF ⟶ X₁ :=
    { base := q₁
      source := cs₁
      target := ct₁
      source_pullback :=
        isPullback_morphism_of_isPullback_toBase (P := ZF) (Q := X₁) hct₁ hcs₁ hmZ₁.symm
      target_pullback := hct₁ }
  let a₂ : ZF ⟶ X₂ :=
    { base := q₂
      source := cs₂
      target := ct₂
      source_pullback :=
        isPullback_morphism_of_isPullback_toBase (P := ZF) (Q := X₂) hct₂ hcs₂ hmZ₂.symm
      target_pullback := hct₂ }
  have hw : a₁ ≫ f₁ = a₂ ≫ f₂ :=
    SchemeMorphismFamily.Hom.ext hbp.w hZs.w.symm hZt.w.symm
  have hlift : ∀ t : Limits.PullbackCone f₁ f₂, ∃ m : t.pt ⟶ ZF,
      (m ≫ a₁ = t.fst ∧ m ≫ a₂ = t.snd) ∧
        ∀ m' : t.pt ⟶ ZF, (m' ≫ a₁ = t.fst ∧ m' ≫ a₂ = t.snd) → m' = m := by
    intro t
    have hcond := t.condition
    have hbase : t.fst.base ≫ f₁.base = t.snd.base ≫ f₂.base :=
      congrArg (fun g : t.pt ⟶ X => g.base) hcond
    have hsrc : f₁.source ≫ t.fst.source = f₂.source ≫ t.snd.source :=
      congrArg (fun g : t.pt ⟶ X => g.source) hcond
    have htgt : f₁.target ≫ t.fst.target = f₂.target ≫ t.snd.target :=
      congrArg (fun g : t.pt ⟶ X => g.target) hcond
    let b : t.pt.base ⟶ P := hbp.lift t.fst.base t.snd.base hbase
    have hb₁ : b ≫ q₁ = t.fst.base := hbp.lift_fst _ _ _
    have hb₂ : b ≫ q₂ = t.snd.base := hbp.lift_snd _ _ _
    set mT := hZt.desc t.snd.target t.fst.target htgt.symm
    set mS := hZs.desc t.snd.source t.fst.source hsrc.symm
    have hmT₂ : ct₂ ≫ mT = t.snd.target := hZt.inl_desc _ _ _
    have hmT₁ : ct₁ ≫ mT = t.fst.target := hZt.inr_desc _ _ _
    have hmS₂ : cs₂ ≫ mS = t.snd.source := hZs.inl_desc _ _ _
    have hmS₁ : cs₁ ≫ mS = t.fst.source := hZs.inr_desc _ _ _
    -- the two given families are the base changes of the cone's own schemes
    have hvt₁ := isPullback_baseSpecMap_comp b _ (hb₁ ▸ t.fst.target_pullback)
    have hvt₂ := isPullback_baseSpecMap_comp b _ (hb₂ ▸ t.snd.target_pullback)
    have hvs₁ := isPullback_baseSpecMap_comp b _ (hb₁ ▸ isPullback_source_toBase t.fst)
    have hvs₂ := isPullback_baseSpecMap_comp b _ (hb₂ ▸ isPullback_source_toBase t.snd)
    have hcartT : IsPullback mT zt t.pt.targetToBase (baseSpecMap b) :=
      isPullback_desc_of_flat_of_isPushout hthick.isThickening hpo t.pt.target_flat ht₁ ht₂
        hZt hzt₁ hzt₂ hvt₁ hvt₂ htgt.symm
    have hcartS : IsPullback mS zs t.pt.sourceToBase (baseSpecMap b) :=
      isPullback_desc_of_flat_of_isPushout hthick.isThickening hpo t.pt.source_flat hs₁ hs₂
        hZs hzs₁ hzs₂ hvs₁ hvs₂ hsrc.symm
    have hcommM : mZ ≫ mT = mS ≫ t.pt.morphism := by
      refine hZs.hom_ext ?_ ?_
      · rw [← Category.assoc, hmZ₂, Category.assoc, hmT₂, ← Category.assoc, hmS₂]
        exact t.snd.source_pullback.w
      · rw [← Category.assoc, hmZ₁, Category.assoc, hmT₁, ← Category.assoc, hmS₁]
        exact t.fst.source_pullback.w
    refine ⟨{ base := b
              source := mS
              target := mT
              source_pullback := isPullback_morphism_of_isPullback_toBase
                (P := t.pt) (Q := ZF) hcartT hcartS hcommM
              target_pullback := hcartT }, ⟨?_, ?_⟩, ?_⟩
    · exact SchemeMorphismFamily.Hom.ext hb₁ hmS₁ hmT₁
    · exact SchemeMorphismFamily.Hom.ext hb₂ hmS₂ hmT₂
    · intro m' hm'
      have hb' : m'.base = b :=
        hbp.hom_ext ((congrArg (fun g : t.pt ⟶ X₁ => g.base) hm'.1).trans hb₁.symm)
          ((congrArg (fun g : t.pt ⟶ X₂ => g.base) hm'.2).trans hb₂.symm)
      refine SchemeMorphismFamily.Hom.ext hb' (hZs.hom_ext ?_ ?_) (hZt.hom_ext ?_ ?_)
      · exact (congrArg (fun g : t.pt ⟶ X₂ => g.source) hm'.2).trans hmS₂.symm
      · exact (congrArg (fun g : t.pt ⟶ X₁ => g.source) hm'.1).trans hmS₁.symm
      · exact (congrArg (fun g : t.pt ⟶ X₂ => g.target) hm'.2).trans hmT₂.symm
      · exact (congrArg (fun g : t.pt ⟶ X₁ => g.target) hm'.1).trans hmT₁.symm
  refine ⟨Limits.PullbackCone.mk a₁ a₂ hw, ⟨?_⟩, ?_⟩
  · exact Limits.PullbackCone.IsLimit.mk hw (fun t => (hlift t).choose)
      (fun t => (hlift t).choose_spec.1.1) (fun t => (hlift t).choose_spec.1.2)
      fun t m' h₁ h₂ => (hlift t).choose_spec.2 m' ⟨h₁, h₂⟩
  · refine ⟨Limits.IsLimit.ofIsoLimit hbp.isLimit
      (Limits.PullbackCone.ext (Iso.refl _) ?_ ?_)⟩
    · exact (Category.id_comp q₁).symm
    · exact (Category.id_comp q₂).symm

end Deformation.Examples

end
