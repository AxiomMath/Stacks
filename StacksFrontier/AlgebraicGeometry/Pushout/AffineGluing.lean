module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.RingTheory.FibreProduct.Localization
public import StacksFrontier.RingTheory.FibreProduct.Spectrum

/-!
# Gluing `Spec` of a fibre product of rings

Let `p : A' ⟶ A` be a surjection of commutative rings, let `q : B ⟶ A` be arbitrary, and let

```
B' ---q'---> A'
|            |
p'           p
v            v
B ----q----> A
```

be a cartesian square of rings, so that `B'` is a model for the fibre product `B ×_A A'`.  This
file assembles, one geometric layer at a time, the statement that applying `Spec` turns this
square into a *pushout* square: first for the underlying topological spaces, then for the
structure sheaves on a basis of basic opens, and finally for sheafed spaces.  The last layer is
promoted to schemes in `StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout`.

## Main definitions

* `Stacks.Pushout.colimitSectionsCone` is the cone, over the componentwise diagram of a diagram
  of presheafed spaces on an open of the colimit, whose point is the sections of the colimit
  presheaf there.

## Main results

* `Stacks.Pushout.isPushout_specTopMap_of_isPullback`: the square of prime spectra is a pushout
  of topological spaces.
* `Stacks.Pushout.isPullback_sections_of_isLocalizationAway`: localizing the cartesian square of
  rings away from an element of `B'` leaves it cartesian.
* `Stacks.Pushout.isIso_app_basicOpen_of_isPullback`: the comparison map from the colimit of
  presheafed spaces to `Spec B'` is an isomorphism on sections over each basic open.
* `Stacks.Pushout.isPushout_specSheafedSpaceMap_of_isPullback`: the square of spectra is a
  pushout of sheafed spaces.

## Implementation notes

The affine *algebra* of this situation — that the fibre product square is cocartesian in
`CommRingCat`, that `B' → B` is surjective and that `B' → A'` is integral when `q` is — already
lives in `StacksFrontier.AlgebraicGeometry.Pushout.Affine`.  What is added here is the
*geometric* universal property, which the source (Stacks Tag 0ET0) obtains by identifying the
structure sheaf of `Spec B'` with a fibre product of direct images.

The source proves that identification by viewing both sides as quasi-coherent modules and
comparing global sections, citing Schemes Tags 01LC and 01IB.  That route is avoided here: the
comparison is checked directly on the basis of basic opens, where every ring in sight is a
localization and the cartesian square of localizations
(`RingFibreProduct.isPullback_localization_away`, Stacks Tag 01Z8) applies.  Consequently this
development depends only on the ring-theoretic inputs Tags 0B7J and 01Z8, both of which are
already available in `StacksFrontier.RingTheory.FibreProduct`.

The layers are kept separate because each is transported along a different forgetful functor,
and the intermediate statements are phrased with `Spec.topMap` and `Spec.sheafedSpaceMap` rather
than `Spec.map` so that the transports are the ones Mathlib provides.

## References

* [Stacks Project, Tag 0B7J](https://stacks.math.columbia.edu/tag/0B7J)
* [Stacks Project, Tag 01Z8](https://stacks.math.columbia.edu/tag/01Z8)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Pushout

/-- **The pushout of topological spaces.**  For a cartesian square of rings whose map `p` to
the base ring is surjective, the induced square of prime spectra is a pushout square of
topological spaces.  This is Stacks Tag 0B7J, transported from `PrimeSpectrum.comap` to
`Spec.topMap` along the canonical identification of `B'` with the chosen fibre product. -/
theorem isPushout_specTopMap_of_isPullback {A A' B B' : CommRingCat.{u}}
    (p : A' ⟶ A) (q : B ⟶ A) (p' : B' ⟶ B) (q' : B' ⟶ A')
    (h : IsPullback p' q' q p) (hp : Function.Surjective p) :
    IsPushout (Spec.topMap q) (Spec.topMap p) (Spec.topMap p') (Spec.topMap q') := by
  let s : RingFibreProduct.Situation q.hom p.hom (RingHom.ker p.hom) := ⟨hp, rfl⟩
  let h₀ := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit q p)
  let e := h.isoIsPullback B A' h₀
  apply (RingFibreProduct.primeSpectrum_isPushout s).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Spec.toTop.mapIso e.op)
  · exact Category.comp_id _ |>.trans (Category.id_comp _).symm
  · exact Category.comp_id _ |>.trans (Category.id_comp _).symm
  · change Spec.topMap (CommRingCat.pullbackCone q p).fst ≫
      Spec.topMap e.hom = _
    simp only [Iso.refl_hom]
    rw [← Spec.topMap_comp]
    congr 1
    exact h.isoIsPullback_hom_fst B A' h₀
  · change Spec.topMap (CommRingCat.pullbackCone q p).snd ≫
      Spec.topMap e.hom = _
    simp only [Iso.refl_hom]
    rw [← Spec.topMap_comp]
    congr 1
    exact h.isoIsPullback_hom_snd B A' h₀

/-- **Localizing the cartesian square of rings.**  Fix an element `r` of the fibre product
`B'`.  If `L`, `LB`, `LP` and `LA` are localizations of `B'`, `B`, `A'` and `A` away from `r`
and its three images, and the four comparison maps are compatible with the structure maps,
then the resulting square is again cartesian.  This is the localized form of Stacks Tag 01Z8,
stated for arbitrary models of the localizations so that it can be applied to the rings of
sections of the structure sheaves on basic opens. -/
theorem isPullback_sections_of_isLocalizationAway
    {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A) (q : B ⟶ A)
    (p' : B' ⟶ B) (q' : B' ⟶ A') (h : IsPullback p' q' q p) (r : B')
    {L LA LB LP : CommRingCat.{u}}
    [Algebra B' L] [Algebra A LA] [Algebra B LB] [Algebra A' LP]
    [IsLocalization.Away r L] [IsLocalization.Away (q (p' r)) LA]
    [IsLocalization.Away (p' r) LB] [IsLocalization.Away (q' r) LP]
    (a : L ⟶ LB) (b : L ⟶ LP) (c : LB ⟶ LA) (d : LP ⟶ LA)
    (ha : a.hom.comp (algebraMap B' L) = (algebraMap B LB).comp p'.hom)
    (hb : b.hom.comp (algebraMap B' L) = (algebraMap A' LP).comp q'.hom)
    (hc : c.hom.comp (algebraMap B LB) = (algebraMap A LA).comp q.hom)
    (hd : d.hom.comp (algebraMap A' LP) = (algebraMap A LA).comp p.hom) :
    IsPullback a b c d := by
  have hr : q (p' r) = p (q' r) := ConcreteCategory.congr_hom h.w r
  have H := RingFibreProduct.isPullback_localization_away q.hom p.hom p'.hom q'.hom h
    r (p' r) (q' r) rfl rfl hr
  apply H.of_iso
    (IsLocalization.algEquiv (.powers r) (Localization.Away r) L).toRingEquiv.toCommRingCatIso
    (IsLocalization.algEquiv (.powers (p' r))
      (Localization.Away (p' r)) LB).toRingEquiv.toCommRingCatIso
    (IsLocalization.algEquiv (.powers (q' r))
      (Localization.Away (q' r)) LP).toRingEquiv.toCommRingCatIso
    (IsLocalization.algEquiv (.powers (q (p' r)))
      (Localization.Away (q (p' r))) LA).toRingEquiv.toCommRingCatIso
  · apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (.powers r)
    ext x
    simpa [Localization.awayLift, IsLocalization.Away.lift_eq] using (DFunLike.congr_fun ha x).symm
  · apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (.powers r)
    ext x
    simpa [Localization.awayLift, IsLocalization.Away.lift_eq] using (DFunLike.congr_fun hb x).symm
  · apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (.powers (p' r))
    ext x
    simpa [Localization.awayMap, IsLocalization.Away.map] using (DFunLike.congr_fun hc x).symm
  · apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (.powers (q' r))
    ext x
    simpa [Localization.awayLift, IsLocalization.Away.lift_eq] using (DFunLike.congr_fun hd x).symm

/-- A cone over a diagram indexed by `WalkingSpanᵒᵖ` is limiting as soon as its two nontrivial
legs form a cartesian square.  The leg at `WalkingSpan.zero` is then forced. -/
noncomputable def isLimitOfIsPullbackSpanOp
    {C : Type*} [Category C] {D : WalkingSpanᵒᵖ ⥤ C} (c : Cone D)
    (h : IsPullback (c.π.app (op WalkingSpan.left)) (c.π.app (op WalkingSpan.right))
      (D.map WalkingSpan.Hom.fst.op) (D.map WalkingSpan.Hom.snd.op)) : IsLimit c where
  lift s := h.lift (s.π.app (op WalkingSpan.left)) (s.π.app (op WalkingSpan.right))
    ((s.w WalkingSpan.Hom.fst.op).trans (s.w WalkingSpan.Hom.snd.op).symm)
  fac s j := by
    rcases j with ⟨_ | (_ | _)⟩
    · rw [← c.w WalkingSpan.Hom.fst.op, ← Category.assoc, IsPullback.lift_fst]
      exact s.w WalkingSpan.Hom.fst.op
    · exact h.lift_fst _ _ _
    · exact h.lift_snd _ _ _
  uniq s m hm := h.hom_ext ((hm _).trans (h.lift_fst _ _ _).symm)
    ((hm _).trans (h.lift_snd _ _ _).symm)

/-- The cone, over the componentwise diagram of `F` on an open `U` of the colimit, whose point
is the ring of sections of the colimit presheaf on `U` and whose legs are the components of the
colimit inclusions.  Its limiting property is the statement that the structure sheaf of a
colimit of presheafed spaces is computed componentwise. -/
noncomputable def colimitSectionsCone
    {J : Type*} [Category J]
    [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ CommRingCat.{u}]
    (F : J ⥤ PresheafedSpace CommRingCat.{u})
    [HasColimit F] (U : Opens (colimit F).carrier) :
    Cone (PresheafedSpace.componentwiseDiagram F U) :=
  (limit.cone _).extend (PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit F U).hom

/-- The legs of `Stacks.Pushout.colimitSectionsCone` are, by construction, the components of
the canonical comparison isomorphism followed by the projections of the limit cone. -/
lemma colimitSectionsCone_π
    {J : Type*} [Category J]
    [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ CommRingCat.{u}]
    (F : J ⥤ PresheafedSpace CommRingCat.{u})
    [HasColimit F] (U : Opens (colimit F).carrier) (j : J) :
    (colimitSectionsCone F U).π.app (op j) =
      (PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit F U).hom ≫
        limit.π (PresheafedSpace.componentwiseDiagram F U) (op j) :=
  rfl

/-- `Stacks.Pushout.colimitSectionsCone` is a limit cone: this is Mathlib's componentwise
description of the structure sheaf of a colimit of presheafed spaces. -/
noncomputable def colimitSectionsConeIsLimit
    {J : Type*} [Category J]
    [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ CommRingCat.{u}]
    (F : J ⥤ PresheafedSpace CommRingCat.{u})
    [HasColimit F] (U : Opens (colimit F).carrier) :
    IsLimit (colimitSectionsCone F U) := by
  apply (limit.isLimit _).ofIsoLimit
  exact Cone.ext (PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit F U).symm
    (fun j => by simp [colimitSectionsCone])

/-- Sections of the structure sheaf of `Spec R` over an open equal to `D(f)` form a localization
of `R` away from `f`. -/
private theorem isLocalizationAway_of_eq_basicOpen {R : CommRingCat.{u}} (f : R)
    {W : Opens (PrimeSpectrum R)} (hW : W = PrimeSpectrum.basicOpen f) :
    letI := StructureSheaf.openAlgebra R (op W)
    IsLocalization.Away f ((Spec.structureSheaf R).obj.obj (op W)) := by
  subst hW
  exact StructureSheaf.IsLocalization.to_basicOpen R f

/-- Under a map `k` from the colimit of `Spec B ← Spec A → Spec A'` to `Spec B'` compatible with
the two inclusions, the preimage of `D(r)` in each component is the basic open of the image of
`r`. -/
private theorem preimage_basicOpen_colimitι_comp {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A)
    (q : B ⟶ A) (p' : B' ⟶ B) (q' : B' ⟶ A')
    (k : colimit ((span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p) ⋙
      SheafedSpace.forgetToPresheafedSpace)) ⟶
      (Spec.sheafedSpaceObj B').toPresheafedSpace)
    (hk₁ : colimit.ι _ WalkingSpan.left ≫ k = (Spec.sheafedSpaceMap p').hom)
    (hk₂ : colimit.ι _ WalkingSpan.right ≫ k = (Spec.sheafedSpaceMap q').hom) (r : B') :
    (Opens.map (colimit.ι _ WalkingSpan.left ≫ k).base).obj (PrimeSpectrum.basicOpen r) =
        PrimeSpectrum.basicOpen (p' r) ∧
      (Opens.map (colimit.ι _ WalkingSpan.right ≫ k).base).obj (PrimeSpectrum.basicOpen r) =
        PrimeSpectrum.basicOpen (q' r) ∧
      (Opens.map (colimit.ι _ WalkingSpan.zero ≫ k).base).obj (PrimeSpectrum.basicOpen r) =
        PrimeSpectrum.basicOpen (q (p' r)) := by
  have hl : (Opens.map (colimit.ι _ WalkingSpan.left ≫ k).base).obj (PrimeSpectrum.basicOpen r) =
      PrimeSpectrum.basicOpen (p' r) := by
    rw [hk₁]
    exact PrimeSpectrum.comap_basicOpen p'.hom r
  refine ⟨hl, ?_, ?_⟩
  · rw [hk₂]
    exact PrimeSpectrum.comap_basicOpen q'.hom r
  · rw [← colimit.w (span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p) ⋙
      SheafedSpace.forgetToPresheafedSpace) WalkingSpan.Hom.fst, Category.assoc]
    change (Opens.map (Spec.sheafedSpaceMap q).hom.base).obj
      ((Opens.map (colimit.ι _ WalkingSpan.left ≫ k).base).obj (PrimeSpectrum.basicOpen r)) = _
    rw [hl]
    exact PrimeSpectrum.comap_basicOpen q.hom (p' r)

/-- Under a map `k` from the colimit of `Spec B ← Spec A → Spec A'` to `Spec B'` compatible with
the two inclusions, the sections over `D(r)` and its preimages form a cartesian square. -/
private theorem isPullback_colimitSectionsCone_extend_basicOpen
    {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A) (q : B ⟶ A)
    (p' : B' ⟶ B) (q' : B' ⟶ A') (h : IsPullback p' q' q p)
    (k : colimit ((span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p) ⋙
      SheafedSpace.forgetToPresheafedSpace)) ⟶
      (Spec.sheafedSpaceObj B').toPresheafedSpace)
    (hk₁ : colimit.ι _ WalkingSpan.left ≫ k = (Spec.sheafedSpaceMap p').hom)
    (hk₂ : colimit.ι _ WalkingSpan.right ≫ k = (Spec.sheafedSpaceMap q').hom) (r : B') :
    IsPullback
      (((colimitSectionsCone _ ((Opens.map k.base).obj (PrimeSpectrum.basicOpen r))).extend
        (k.c.app (op (PrimeSpectrum.basicOpen r)))).π.app (op WalkingSpan.left))
      (((colimitSectionsCone _ ((Opens.map k.base).obj (PrimeSpectrum.basicOpen r))).extend
        (k.c.app (op (PrimeSpectrum.basicOpen r)))).π.app (op WalkingSpan.right))
      ((PresheafedSpace.componentwiseDiagram _
        ((Opens.map k.base).obj (PrimeSpectrum.basicOpen r))).map WalkingSpan.Hom.fst.op)
      ((PresheafedSpace.componentwiseDiagram _
        ((Opens.map k.base).obj (PrimeSpectrum.basicOpen r))).map WalkingSpan.Hom.snd.op) := by
  let F := span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p) ⋙
    SheafedSpace.forgetToPresheafedSpace
  let U := PrimeSpectrum.basicOpen r
  let D := PresheafedSpace.componentwiseDiagram F ((Opens.map k.base).obj U)
  let c := colimitSectionsCone F ((Opens.map k.base).obj U)
  let c' := c.extend (k.c.app (op U))
  obtain ⟨hl, hr, hz⟩ := preimage_basicOpen_colimitι_comp p q p' q' k hk₁ hk₂ r
  let : Algebra B' c'.pt := StructureSheaf.openAlgebra B' (op U)
  let : Algebra B (D.obj (op WalkingSpan.left)) := StructureSheaf.openAlgebra B _
  let : Algebra A' (D.obj (op WalkingSpan.right)) := StructureSheaf.openAlgebra A' _
  let : Algebra A (D.obj (op WalkingSpan.zero)) := StructureSheaf.openAlgebra A _
  have : IsLocalization.Away r c'.pt := StructureSheaf.IsLocalization.to_basicOpen B' r
  have : IsLocalization.Away (p' r) (D.obj (op WalkingSpan.left)) :=
    isLocalizationAway_of_eq_basicOpen _ hl
  have : IsLocalization.Away (q' r) (D.obj (op WalkingSpan.right)) :=
    isLocalizationAway_of_eq_basicOpen _ hr
  have : IsLocalization.Away (q (p' r)) (D.obj (op WalkingSpan.zero)) :=
    isLocalizationAway_of_eq_basicOpen _ hz
  apply isPullback_sections_of_isLocalizationAway p q p' q' h r (L := c'.pt)
    (LB := D.obj (op WalkingSpan.left)) (LP := D.obj (op WalkingSpan.right))
    (LA := D.obj (op WalkingSpan.zero))
  · apply CommRingCat.hom_ext_iff.mp
    change CommRingCat.ofHom (algebraMap B' c'.pt) ≫
        (k.c.app (op U) ≫ c.π.app (op WalkingSpan.left)) =
      p' ≫ CommRingCat.ofHom (algebraMap B (D.obj (op WalkingSpan.left)))
    rw [colimitSectionsCone_π, PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    change CommRingCat.ofHom (algebraMap B' c'.pt) ≫
      (colimit.ι F WalkingSpan.left ≫ k).c.app (op U) = _
    rw [PresheafedSpace.congr_app hk₁]
    exact StructureSheaf.toOpen_comp_comap_assoc p'.hom U _
  · apply CommRingCat.hom_ext_iff.mp
    change CommRingCat.ofHom (algebraMap B' c'.pt) ≫
        (k.c.app (op U) ≫ c.π.app (op WalkingSpan.right)) =
      q' ≫ CommRingCat.ofHom (algebraMap A' (D.obj (op WalkingSpan.right)))
    rw [colimitSectionsCone_π, PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    change CommRingCat.ofHom (algebraMap B' c'.pt) ≫
      (colimit.ι F WalkingSpan.right ≫ k).c.app (op U) = _
    rw [PresheafedSpace.congr_app hk₂]
    exact StructureSheaf.toOpen_comp_comap_assoc q'.hom U _
  · apply CommRingCat.hom_ext_iff.mp
    change CommRingCat.ofHom (algebraMap B (D.obj (op WalkingSpan.left))) ≫
      D.map WalkingSpan.Hom.fst.op = q ≫
        CommRingCat.ofHom (algebraMap A (D.obj (op WalkingSpan.zero)))
    exact StructureSheaf.toOpen_comp_comap_assoc q.hom _ _
  · apply CommRingCat.hom_ext_iff.mp
    change CommRingCat.ofHom (algebraMap A' (D.obj (op WalkingSpan.right))) ≫
      D.map WalkingSpan.Hom.snd.op = p ≫
        CommRingCat.ofHom (algebraMap A (D.obj (op WalkingSpan.zero)))
    exact StructureSheaf.toOpen_comp_comap_assoc p.hom _ _

/-- **The structure-sheaf comparison is an isomorphism on basic opens.**  Let `k` be a map from
the colimit of `Spec B ← Spec A → Spec A'` in presheafed spaces to `Spec B'` compatible with the
two inclusions.  Then `k` is an isomorphism on sections over every basic open `D(r)`, `r ∈ B'`.

Both sides are localizations of `B'`, `B`, `A'` and `A` away from `r` and its images, so the
claim reduces, through `Stacks.Pushout.colimitSectionsConeIsLimit`, to the cartesian square of
localizations `Stacks.Pushout.isPullback_sections_of_isLocalizationAway`.  This is the step for
which the source appeals to quasi-coherence of pushforwards (Stacks Tags 01LC and 01IB); the
localization argument used here needs neither. -/
lemma isIso_app_basicOpen_of_isPullback
    {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A) (q : B ⟶ A)
    (p' : B' ⟶ B) (q' : B' ⟶ A') (h : IsPullback p' q' q p)
    (k : colimit ((span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p) ⋙
      SheafedSpace.forgetToPresheafedSpace)) ⟶
      (Spec.sheafedSpaceObj B').toPresheafedSpace)
    (hk₁ : colimit.ι _ WalkingSpan.left ≫ k = (Spec.sheafedSpaceMap p').hom)
    (hk₂ : colimit.ι _ WalkingSpan.right ≫ k = (Spec.sheafedSpaceMap q').hom)
    (r : B') : IsIso (k.c.app (op (PrimeSpectrum.basicOpen r))) := by
  let F := span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p) ⋙
    SheafedSpace.forgetToPresheafedSpace
  let U := PrimeSpectrum.basicOpen r
  let V := (Opens.map k.base).obj U
  let c := colimitSectionsCone F V
  let c' := c.extend (k.c.app (op U))
  let m : c' ⟶ c := { hom := k.c.app (op U), w := fun _ => rfl }
  have : IsIso m := (isLimitOfIsPullbackSpanOp c'
    (isPullback_colimitSectionsCone_extend_basicOpen p q p' q' h k hk₁ hk₂ r)).hom_isIso
    (colimitSectionsConeIsLimit F V) m
  exact (Cone.forget (PresheafedSpace.componentwiseDiagram F V)).map_isIso m

/-- For a cartesian square of rings whose map `p` to the base ring is surjective, the canonical
map from the colimit of `Spec B ← Spec A → Spec A'` in sheafed spaces to `Spec B'` is a
homeomorphism on underlying spaces. -/
private theorem isIso_base_colimitDesc_of_isPullback {A A' B B' : CommRingCat.{u}}
    (p : A' ⟶ A) (q : B ⟶ A) (p' : B' ⟶ B) (q' : B' ⟶ A')
    (h : IsPullback p' q' q p) (hp : Function.Surjective p)
    (w : Spec.sheafedSpaceMap q ≫ Spec.sheafedSpaceMap p' =
      Spec.sheafedSpaceMap p ≫ Spec.sheafedSpaceMap q') :
    IsIso (colimit.desc (span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p))
      (PushoutCocone.mk _ _ w)).hom.base := by
  let F := span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p)
  let s := PushoutCocone.mk _ _ w
  have ht : IsColimit ((SheafedSpace.forget CommRingCat).mapCocone s) :=
    (isColimitMapCoconePushoutCoconeEquiv _ _).symm
      (isPushout_specTopMap_of_isPullback p q p' q' h hp).isColimit
  let m := (Cocone.functoriality F (SheafedSpace.forget CommRingCat)).map
    ((colimit.isColimit F).descCoconeMorphism s)
  have : IsIso m := (isColimitOfPreserves (SheafedSpace.forget CommRingCat)
    (colimit.isColimit F)).hom_isIso ht m
  exact (Cocone.forget _).map_isIso m

/-- **The pushout of sheafed spaces.**  For a cartesian square of rings whose map `p` to the
base ring is surjective, the induced square of spectra is a pushout square of sheafed spaces.

The canonical map from the colimit to `Spec B'` is an isomorphism on underlying spaces by
`Stacks.Pushout.isPushout_specTopMap_of_isPullback` and an isomorphism on structure sheaves
because it is one over the basis of basic opens, by
`Stacks.Pushout.isIso_app_basicOpen_of_isPullback`. -/
theorem isPushout_specSheafedSpaceMap_of_isPullback
    {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A) (q : B ⟶ A)
    (p' : B' ⟶ B) (q' : B' ⟶ A') (h : IsPullback p' q' q p)
    (hp : Function.Surjective p) :
    IsPushout (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p)
      (Spec.sheafedSpaceMap p') (Spec.sheafedSpaceMap q') := by
  let F := span (Spec.sheafedSpaceMap q) (Spec.sheafedSpaceMap p)
  have w : Spec.sheafedSpaceMap q ≫ Spec.sheafedSpaceMap p' =
      Spec.sheafedSpaceMap p ≫ Spec.sheafedSpaceMap q' := by
    rw [← Spec.sheafedSpaceMap_comp, ← Spec.sheafedSpaceMap_comp, h.w]
  let s := PushoutCocone.mk _ _ w
  let k := colimit.desc F s
  have hk₁ : colimit.ι F WalkingSpan.left ≫ k = Spec.sheafedSpaceMap p' :=
    colimit.ι_desc s WalkingSpan.left
  have hk₂ : colimit.ι F WalkingSpan.right ≫ k = Spec.sheafedSpaceMap q' :=
    colimit.ι_desc s WalkingSpan.right
  have hk₀ : IsIso k.hom.base := isIso_base_colimitDesc_of_isPullback p q p' q' h hp w
  let e := preservesColimitIso SheafedSpace.forgetToPresheafedSpace F
  let k' := e.inv ≫ SheafedSpace.forgetToPresheafedSpace.map k
  have hk' (j : WalkingSpan) (f : _ ⟶ _) (hf : colimit.ι F j ≫ k = f) :
      colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j ≫ k' =
        SheafedSpace.forgetToPresheafedSpace.map f := by
    change colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j ≫
      e.inv ≫ SheafedSpace.forgetToPresheafedSpace.map k = _
    rw [← Category.assoc, ι_preservesColimitIso_inv, ← Functor.map_comp, hf]
  have he : IsIso e.inv.c := PresheafedSpace.c_isIso_of_iso e.inv
  have hc (r : B') : IsIso (k.hom.c.app (op (PrimeSpectrum.basicOpen r))) := by
    have hcomp := isIso_app_basicOpen_of_isPullback p q p' q' h k' (hk' _ _ hk₁) (hk' _ _ hk₂) r
    change IsIso (k.hom.c.app (op (PrimeSpectrum.basicOpen r)) ≫
      e.inv.c.app (op ((Opens.map k.hom.base).obj (PrimeSpectrum.basicOpen r)))) at hcomp
    have hg : IsIso (e.inv.c.app
        (op ((Opens.map k.hom.base).obj (PrimeSpectrum.basicOpen r)))) :=
      NatIso.isIso_app_of_isIso (α := e.inv.c) _
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hg hcomp
  let φ : (Spec.sheafedSpaceObj B').sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat k.hom.base).obj (colimit F).sheaf := ⟨k.hom.c⟩
  have hφ : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens hc
  have hkc : IsIso k.hom.c := (TopCat.Sheaf.forget CommRingCat _).map_isIso φ
  have : IsIso (SheafedSpace.forgetToPresheafedSpace.map k) :=
    PresheafedSpace.isIso_of_components k.hom
  have : IsIso k := isIso_of_reflects_iso k SheafedSpace.forgetToPresheafedSpace
  have : IsIso ((colimit.isColimit F).desc s) := ‹IsIso k›
  exact IsPushout.of_isColimit ((colimit.isColimit F).ofPointIso (t := s))

end Stacks.Pushout

end
