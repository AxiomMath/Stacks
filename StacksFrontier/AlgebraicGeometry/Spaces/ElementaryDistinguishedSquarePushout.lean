module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal

/-!
# Elementary distinguished squares are pushouts

An elementary distinguished square on an algebraic space `W` over a scheme `S` consists of an
open subspace `U` of `W` and an étale morphism `f : V ⟶ W` restricting to an isomorphism over
the reduced closed complement of `U`. Such a square is cocartesian: `W` is the pushout of
`U ← U ×_W V → V` in the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isPushout_elementaryDistinguishedSquare`: **Stacks 0DVI**, the
  pushout property of an elementary distinguished square.
* `AlgebraicGeometry.Space.isEtaleCovering_of_isElementaryDistinguishedSquare`: `{U ⟶ W, V ⟶ W}`
  is an étale covering of `W`.
* `AlgebraicGeometry.Space.isEtaleCovering_overlap_of_isElementaryDistinguishedSquare`:
  `{V ⟶ V ×_W V, U ×_W V ×_W V ⟶ V ×_W V}`, the first map the relative diagonal, is an étale
  covering of `V ×_W V`.

## References

* [Stacks Project, Tag 0DVI](https://stacks.math.columbia.edu/tag/0DVI)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Presheaves of types on the big fppf site have pullbacks (supplied once, since instance search
for them through the functor category times out). -/
local instance (priority := high) hasPullbacks_presheaf_elementaryDistinguishedSquarePushout
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

local instance (priority := high) hasPullback_presheaf_elementaryDistinguishedSquarePushout
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Two morphisms out of a fibre product which agree after composing with the two projections
agree on every pair of morphisms with equal composites into the base of that fibre product. -/
private theorem comp_eq_of_pullback_comp_eq {C : Type*} [Category C] {T X Y Z P : C}
    {fX : X ⟶ Z} {fY : Y ⟶ Z} [HasPullback fX fY] {gX : X ⟶ P} {gY : Y ⟶ P}
    (hg : pullback.fst fX fY ≫ gX = pullback.snd fX fY ≫ gY)
    (α : T ⟶ X) (β : T ⟶ Y) (hαβ : α ≫ fX = β ≫ fY) :
    α ≫ gX = β ≫ gY := by
  have h := pullback.lift α β hαβ ≫= hg
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at h

/-- The pullback of `i` along the first projection composed with `f`, over `V ×_W V`, maps to `W`
compatibly with both projections of `V ×_W V` followed by `f`. -/
private theorem pullback_overlap_condition {C : Type*} [Category C] [HasPullbacks C]
    {W V X : C} (i : X ⟶ W) (f : V ⟶ W) :
    pullback.fst i (pullback.fst f f ≫ f) ≫ i =
        (pullback.snd i (pullback.fst f f ≫ f) ≫ pullback.fst f f) ≫ f ∧
      pullback.fst i (pullback.fst f f ≫ f) ≫ i =
        (pullback.snd i (pullback.fst f f ≫ f) ≫ pullback.snd f f) ≫ f := by
  have h : pullback.fst i (pullback.fst f f ≫ f) ≫ i =
      (pullback.snd i (pullback.fst f f ≫ f) ≫ pullback.fst f f) ≫ f := by
    rw [Category.assoc]
    exact pullback.condition
  exact ⟨h, by rw [h]; simp only [Category.assoc, pullback.condition]⟩

/-- A point of the ambient space lying on a subspace over which a morphism restricts to an
isomorphism is in the image of that morphism on points. -/
private theorem exists_point_of_isIso_fromPreimage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : Subfunctor W) (f : V ⟶ W) (x : points B S hS W)
    (hx : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι))
    (his : IsIso (D.fromPreimage f)) :
    ∃ y : points B S hS V, pointsMap B S hS V f y = x := by
  obtain ⟨z, rfl⟩ := hx
  have : IsIso (D.fromPreimage f) := his
  obtain ⟨p, hp⟩ := pointsMap_surjective_of_isIso B S hS (D.fromPreimage f) z
  refine ⟨pointsMap B S hS (D.preimage f).toFunctor (D.preimage f).ι p, ?_⟩
  rw [← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply, hp]

/-- Every point of the target of an elementary distinguished square lies either on the open
subspace or in the image of the étale morphism. -/
private theorem points_covered_by_open_or_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f)
    (x : points B S hS W) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∨
      ∃ y : points B S hS V, pointsMap B S hS V f y = x := by
  classical
  by_cases hx : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · exact Or.inl hx
  · refine Or.inr (exists_point_of_isIso_fromPreimage B S hS
      (reducedClosedSubspace B S hS W hW
        (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ h.isClosedComplement)
      f x ?_ h.isIsoOverComplement)
    rwa [range_pointsMap_ι_reducedClosedSubspace]

/-- The open subspace and the étale morphism of an elementary distinguished square form an
étale covering of the target. -/
private theorem isEtaleCovering_elementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsEtaleCovering B S hS
      (fun | false => U.toFunctor | true => V)
      (fun | false => U.ι | true => f) := by
  classical
  refine ⟨hW, ?_, ?_, ?_⟩
  · intro i
    cases i
    · exact h.isOpenSubspace.1
    · exact h.isAlgebraicSpace
  · intro i
    cases i
    · exact isEtale_of_presheaf_etale B S hS
        (presheaf_etale_of_isOpenImmersion B S hS h.isOpenSubspace.2)
    · exact h.isEtale
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨z, hz⟩ | ⟨y, hy⟩ := points_covered_by_open_or_etale B S hS hW U f h x
    · exact Set.mem_iUnion.mpr ⟨false, ⟨z, hz⟩⟩
    · exact Set.mem_iUnion.mpr ⟨true, ⟨y, hy⟩⟩

/-- The open subspace and the étale morphism of an elementary distinguished square form an
fppf covering of the target. -/
private theorem isFppfCovering_elementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsFppfCovering B S hS
      (fun | false => U.toFunctor | true => V)
      (fun | false => U.ι | true => f) :=
  isFppfCovering_of_isEtaleCovering B S hS
    (isEtaleCovering_elementaryDistinguishedSquare B S hS hW U f h)

/-- Every point of `V ×_W V` lies either on the relative diagonal of `f` or on the part of
`V ×_W V` lying over the open subspace `U`. -/
private theorem overlap_points_covered_by_diagonal_or_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f)
    (x : points B S hS (pullback f f)) :
    x ∈ Set.range (pointsMap B S hS V (pullback.diagonal f)) ∨
      x ∈ Set.range (pointsMap B S hS (pullback U.ι (pullback.fst f f ≫ f))
        (pullback.snd U.ι (pullback.fst f f ≫ f))) := by
  classical
  set q : pullback f f ⟶ W := pullback.fst f f ≫ f with hq
  by_cases hy : pointsMap B S hS (pullback f f) q x ∈
      Set.range (pointsMap B S hS U.toFunctor U.ι)
  · obtain ⟨z, hz⟩ := hy
    obtain ⟨t, -, ht⟩ :=
      exists_points_of_isPullback B S hS (IsPullback.of_hasPullback U.ι q) z x hz
    exact Or.inr ⟨t, ht⟩
  · obtain ⟨D, hD, hrange⟩ :
        ∃ (D : Subfunctor W), IsIso (D.fromPreimage f) ∧
          Set.range (pointsMap B S hS D.toFunctor D.ι) =
            (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
      ⟨_, h.isIsoOverComplement,
        range_pointsMap_ι_reducedClosedSubspace B S hS W hW _ h.isClosedComplement⟩
    have hyD : pointsMap B S hS (pullback f f) q x ∈
        Set.range (pointsMap B S hS D.toFunctor D.ι) := by
      rwa [hrange]
    obtain ⟨d, hd⟩ := hyD
    obtain ⟨t, -, ht⟩ :=
      exists_points_of_isPullback B S hS (IsPullback.of_hasPullback D.ι q) d x hd
    set sD : pullback D.ι q ⟶ D.toFunctor := pullback.fst D.ι q with hsD
    set sR : pullback D.ι q ⟶ pullback f f := pullback.snd D.ι q with hsR
    set a₁ : pullback D.ι q ⟶ V := sR ≫ pullback.fst f f with ha₁
    set a₂ : pullback D.ι q ⟶ V := sR ≫ pullback.snd f f with ha₂
    obtain ⟨h₁, h₂⟩ := pullback_overlap_condition D.ι f
    have hE : IsPullback (D.fromPreimage f) (D.preimage f).ι D.ι f :=
      Subfunctor.isPullback_preimage f D
    have : IsIso (D.fromPreimage f) := hD
    have hl : hE.lift sD a₁ h₁ = hE.lift sD a₂ h₂ := by
      refine (cancel_mono (D.fromPreimage f)).1 ?_
      rw [hE.lift_fst, hE.lift_fst]
    have ha : a₁ = a₂ := by
      have h' := hl =≫ (D.preimage f).ι
      rwa [hE.lift_snd, hE.lift_snd] at h'
    have hdiag : sR = a₁ ≫ pullback.diagonal f := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, ha₁]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, ha, ha₂]
    refine Or.inl ⟨pointsMap B S hS (pullback D.ι q) a₁ t, ?_⟩
    rw [← pointsMap_comp_apply, ← hdiag]
    exact ht

/-- The relative diagonal of `f` and the part of `V ×_W V` lying over the open subspace form
an étale covering of `V ×_W V`. -/
private theorem isEtaleCovering_overlap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsEtaleCovering B S hS
      (fun | false => V | true => pullback U.ι (pullback.fst f f ≫ f))
      (fun | false => pullback.diagonal f
           | true => pullback.snd U.ι (pullback.fst f f ≫ f)) := by
  classical
  let W' : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let V' : AlgebraicSpaces B S hS := ⟨V, h.isAlgebraicSpace⟩
  let U' : AlgebraicSpaces B S hS := ⟨U.toFunctor, h.isOpenSubspace.1⟩
  let v' : V' ⟶ W' := ObjectProperty.homMk f
  let i' : U' ⟶ W' := ObjectProperty.homMk U.ι
  let R' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS v' v'
  let r₁ : R' ⟶ V' := ObjectProperty.homMk (pullback.fst f f)
  let T' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS i' (r₁ ≫ v')
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst U.ι (pullback.fst f f ≫ f)) : T' ⟶ U')
      (ObjectProperty.homMk (pullback.snd U.ι (pullback.fst f f ≫ f)) : T' ⟶ R')
      i' (r₁ ≫ v') :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS i' (r₁ ≫ v')
  refine ⟨isAlgebraicSpace_pullback B S hS f f h.isAlgebraicSpace h.isAlgebraicSpace hW,
    ?_, ?_, ?_⟩
  · intro i
    cases i
    · exact h.isAlgebraicSpace
    · exact T'.property
  · intro i
    cases i
    · exact isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS
        (isOpenImmersion_diagonal_of_isUnramified B S hS h.isAlgebraicSpace hW f
          (isUnramified_of_isEtale B S hS h.isEtale)))
    · exact isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS
        (isOpenImmersion_of_isPullback B S hS hsq h.isOpenSubspace.2))
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain hx | hx := overlap_points_covered_by_diagonal_or_open B S hS hW U f h x
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩

/-- The relative diagonal of `f` and the part of `V ×_W V` lying over the open subspace form
an fppf covering of `V ×_W V`. -/
private theorem isFppfCovering_overlap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsFppfCovering B S hS
      (fun | false => V | true => pullback U.ι (pullback.fst f f ≫ f))
      (fun | false => pullback.diagonal f
           | true => pullback.snd U.ι (pullback.fst f f ≫ f)) :=
  isFppfCovering_of_isEtaleCovering B S hS (isEtaleCovering_overlap B S hS hW U f h)

/-- The fppf covering condition transports along an equality of the families of sources and
a heterogeneous equality of the families of morphisms. -/
private theorem isFppfCovering_of_heq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X Y : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : ∀ i, X i ⟶ Z) (r : ∀ i, Y i ⟶ Z) (hr : IsFppfCovering B S hS Y r)
    (hXY : X = Y) (hpr : ∀ i, HEq (p i) (r i)) :
    IsFppfCovering B S hS X p := by
  cases hXY
  exact funext (fun i => eq_of_heq (hpr i)) ▸ hr

/-- Two morphisms out of `V` which agree on `U ×_W V` have equal composites with the two
projections of `V ×_W V`. -/
private theorem maps_equal_on_overlap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hZ : IsAlgebraicSpace B S hS Z)
    (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f)
    (gU : U.toFunctor ⟶ Z) (gV : V ⟶ Z)
    (hagree : pullback.snd U.ι f ≫ gV = pullback.fst U.ι f ≫ gU) :
    pullback.fst f f ≫ gV = pullback.snd f f ≫ gV := by
  classical
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let V' : AlgebraicSpaces B S hS := ⟨V, h.isAlgebraicSpace⟩
  let R' : AlgebraicSpaces B S hS :=
    ⟨pullback f f, isAlgebraicSpace_pullback B S hS f f h.isAlgebraicSpace
      h.isAlgebraicSpace hW⟩
  let T' : AlgebraicSpaces B S hS :=
    ⟨pullback U.ι (pullback.fst f f ≫ f),
      isAlgebraicSpace_pullback B S hS U.ι (pullback.fst f f ≫ f) h.isOpenSubspace.1
        (isAlgebraicSpace_pullback B S hS f f h.isAlgebraicSpace h.isAlgebraicSpace hW) hW⟩
  let K : Bool → AlgebraicSpaces B S hS := fun | false => V' | true => T'
  let k : ∀ i, K i ⟶ R' := fun
    | false => ObjectProperty.homMk (pullback.diagonal f)
    | true => ObjectProperty.homMk (pullback.snd U.ι (pullback.fst f f ≫ f))
  let a : R' ⟶ Z' := ObjectProperty.homMk (pullback.fst f f ≫ gV)
  let b : R' ⟶ Z' := ObjectProperty.homMk (pullback.snd f f ≫ gV)
  have hcov : IsFppfCovering B S hS (fun i => (K i).obj) (fun i => (k i).hom) := by
    refine isFppfCovering_of_heq B S hS (X := fun i => (K i).obj)
      (Y := fun | false => V | true => pullback U.ι (pullback.fst f f ≫ f))
      (Z := pullback f f) (fun i => (k i).hom)
      (fun | false => pullback.diagonal f
           | true => pullback.snd U.ι (pullback.fst f f ≫ f))
      (isFppfCovering_overlap B S hS hW U f h) ?_ ?_
    · funext i; cases i <;> rfl
    · intro i; cases i <;> rfl
  have hk : ∀ i, k i ≫ a = k i ≫ b := by
    intro i
    refine ObjectProperty.hom_ext _ ?_
    cases i
    · show pullback.diagonal f ≫ pullback.fst f f ≫ gV =
        pullback.diagonal f ≫ pullback.snd f f ≫ gV
      rw [← Category.assoc, ← Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
    · set sU : pullback U.ι (pullback.fst f f ≫ f) ⟶ U.toFunctor :=
        pullback.fst U.ι (pullback.fst f f ≫ f) with hsU
      set sR : pullback U.ι (pullback.fst f f ≫ f) ⟶ pullback f f :=
        pullback.snd U.ι (pullback.fst f f ≫ f) with hsR
      obtain ⟨h₁, h₂⟩ := pullback_overlap_condition U.ι f
      show sR ≫ pullback.fst f f ≫ gV = sR ≫ pullback.snd f f ≫ gV
      rw [← Category.assoc, ← Category.assoc]
      exact (comp_eq_of_pullback_comp_eq hagree.symm _ _ h₁).symm.trans
        (comp_eq_of_pullback_comp_eq hagree.symm _ _ h₂)
  exact congrArg (fun m : R' ⟶ Z' => m.hom)
    (AlgebraicSpaces.hom_ext_of_isFppfCovering B S hS k hcov hk)

/-- **Stacks 0DVI.** An elementary distinguished square is a pushout square in the category
of algebraic spaces over the base scheme: the target is glued from the open subspace and the
étale morphism along their fibre product. -/
@[stacks 0DVI]
theorem isPushout_elementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsPushout
      (ObjectProperty.homMk (pullback.snd U.ι f) :
        AlgebraicSpaces.fiberProduct B S hS
            (ObjectProperty.homMk U.ι :
              (⟨U.toFunctor, h.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩)
            (ObjectProperty.homMk f :
              (⟨V, h.isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩) ⟶
          ⟨V, h.isAlgebraicSpace⟩)
      (ObjectProperty.homMk (pullback.fst U.ι f) :
        _ ⟶ (⟨U.toFunctor, h.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk f :
        (⟨V, h.isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩)
      (ObjectProperty.homMk U.ι :
        (⟨U.toFunctor, h.isOpenSubspace.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩) := by
  classical
  let U' : AlgebraicSpaces B S hS := ⟨U.toFunctor, h.isOpenSubspace.1⟩
  let V' : AlgebraicSpaces B S hS := ⟨V, h.isAlgebraicSpace⟩
  let W' : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let i : U' ⟶ W' := ObjectProperty.homMk U.ι
  let f' : V' ⟶ W' := ObjectProperty.homMk f
  let P : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS i f'
  let a : P ⟶ V' := ObjectProperty.homMk (pullback.snd U.ι f)
  let b : P ⟶ U' := ObjectProperty.homMk (pullback.fst U.ι f)
  show IsPushout a b f' i
  have hcomm : a ≫ f' = b ≫ i :=
    ObjectProperty.hom_ext _ (pullback.condition (f := U.ι) (g := f)).symm
  refine ⟨⟨hcomm⟩, ⟨?_⟩⟩
  let Q : Bool → AlgebraicSpaces B S hS := fun | false => U' | true => V'
  let e : ∀ j, Q j ⟶ W' := fun | false => i | true => f'
  have he : IsFppfCovering B S hS (fun j => (Q j).obj) (fun j => (e j).hom) := by
    refine isFppfCovering_of_heq B S hS (X := fun j => (Q j).obj)
      (Y := fun | false => U.toFunctor | true => V) (Z := W)
      (fun j => (e j).hom) (fun | false => U.ι | true => f)
      (isFppfCovering_elementaryDistinguishedSquare B S hS hW U f h) ?_ ?_
    · funext j; cases j <;> rfl
    · intro j; cases j <;> rfl
  have descExists : ∀ s : PushoutCocone a b,
      ∃ d : W' ⟶ s.pt, f' ≫ d = s.inl ∧ i ≫ d = s.inr := by
    intro s
    have hcond : pullback.snd U.ι f ≫ s.inl.hom = pullback.fst U.ι f ≫ s.inr.hom :=
      congrArg (fun m : P ⟶ s.pt => m.hom) s.condition
    let g : ∀ j, Q j ⟶ s.pt := fun | false => s.inr | true => s.inl
    have hg : ∀ (j k : Bool) (T : AlgebraicSpaces B S hS) (α : T ⟶ Q j) (β : T ⟶ Q k),
        α ≫ e j = β ≫ e k → α ≫ g j = β ≫ g k := by
      intro j k T α β hαβ
      refine ObjectProperty.hom_ext _ ?_
      cases j <;> cases k
      · have hαβ' : α.hom ≫ U.ι = β.hom ≫ U.ι :=
          congrArg (fun m : T ⟶ W' => m.hom) hαβ
        show α.hom ≫ s.inr.hom = β.hom ≫ s.inr.hom
        rw [(cancel_mono U.ι).1 hαβ']
      · have hαβ' : α.hom ≫ U.ι = β.hom ≫ f :=
          congrArg (fun m : T ⟶ W' => m.hom) hαβ
        exact comp_eq_of_pullback_comp_eq hcond.symm α.hom β.hom hαβ'
      · have hαβ' : β.hom ≫ U.ι = α.hom ≫ f :=
          (congrArg (fun m : T ⟶ W' => m.hom) hαβ).symm
        exact (comp_eq_of_pullback_comp_eq hcond.symm β.hom α.hom hαβ').symm
      · have hαβ' : α.hom ≫ f = β.hom ≫ f :=
          congrArg (fun m : T ⟶ W' => m.hom) hαβ
        exact comp_eq_of_pullback_comp_eq
          (maps_equal_on_overlap B S hS hW s.pt.property U f h s.inr.hom s.inl.hom hcond)
          α.hom β.hom hαβ'
    obtain ⟨d, hd, -⟩ :=
      AlgebraicSpaces.existsUnique_desc_of_isFppfCovering B S hS e he s.pt g hg
    exact ⟨d, hd true, hd false⟩
  refine PushoutCocone.IsColimit.mk hcomm (fun s => (descExists s).choose)
    (fun s => (descExists s).choose_spec.1) (fun s => (descExists s).choose_spec.2) ?_
  intro s m hm₀ hm₁
  refine AlgebraicSpaces.hom_ext_of_isFppfCovering B S hS e he (fun j => ?_)
  cases j
  · exact hm₁.trans (descExists s).choose_spec.2.symm
  · exact hm₀.trans (descExists s).choose_spec.1.symm

/-- The open subspace and the étale morphism of an elementary distinguished square form an
étale covering of the target. -/
theorem isEtaleCovering_of_isElementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsEtaleCovering B S hS
      (fun | false => U.toFunctor | true => V)
      (fun | false => U.ι | true => f) :=
  isEtaleCovering_elementaryDistinguishedSquare B S hS hW U f h

/-- The relative diagonal of the étale morphism of an elementary distinguished square and the
part of `V ×_W V` lying over the open subspace form an étale covering of `V ×_W V`. -/
theorem isEtaleCovering_overlap_of_isElementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) :
    IsEtaleCovering B S hS
      (fun | false => V | true => pullback U.ι (pullback.fst f f ≫ f))
      (fun | false => pullback.diagonal f
           | true => pullback.snd U.ι (pullback.fst f f ≫ f)) :=
  isEtaleCovering_overlap B S hS hW U f h

end AlgebraicGeometry.Space

end
