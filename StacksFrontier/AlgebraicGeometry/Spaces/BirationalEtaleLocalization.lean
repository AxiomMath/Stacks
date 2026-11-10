module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BirationalDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Birationality after an affine étale localization

An affine étale localization of a birational morphism of decent algebraic spaces with finitely
many irreducible components is again such a morphism: the fibre product is decent, it has
finitely many irreducible components, and its projection to the affine étale space is
birational.

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_pullback_of_isEtale` is decency of the fibre product.
* `AlgebraicGeometry.Space.finite_irreducibleComponents_pullback_of_isEtale` is finiteness of
  the set of irreducible components of the fibre product.
* `AlgebraicGeometry.Space.isBirational_pullback_snd_of_isEtale` is birationality of the
  projection.

## Implementation notes

Birationality is `AlgebraicGeometry.Space.IsBirational`, which is parameterised by decency of
the source and the target, as the source statement is; the same decency serves Stacks 0ABU and
0ABV. Where the local ring at a generic point is computed, the representable open subspace with
dense point set is produced from decency by
`AlgebraicGeometry.Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace`.

Generic points are transported along an étale morphism in both directions by Stacks 0ABV,
`AlgebraicGeometry.Space.mem_genericPoints_tfae`. Finiteness for the affine étale space `V`
comes from finiteness for `Y` together with finiteness of the fibres of `|V| → |Y|`, which is
condition (1) of Stacks 03JV at a point of a decent space, applied to the affine étale chart
`V → Y` itself. Injectivity on generic points of `|X ×_Y V| → |V|` is where Stacks 0BBD
enters: over the generic point `y` of `|Y|` below a generic point `v` of `|V|`, the morphism
`f` becomes an isomorphism after base change to `Spec 𝒪_{Y,y}`, and `v` lifts to a point of
that base change, so the fibre of `|X ×_Y V| → |V|` over `v` is a single point.

Birationality of the projection is then the isomorphism of local rings. The spectrum of the
local ring of `V` at `v` factors through the generic stalk of `Y` at `y`, so the base change
of `f` to it is an isomorphism; transporting that isomorphism through the schematic charts of
`X ×_Y V` and of `V` — the latter representable, so its schematic chart is an isomorphism —
exhibits the induced map of local rings as a stalk map of a morphism which is a base change of
`Spec 𝒪_{V,v} → V`, hence an isomorphism on that stalk.

## References

* [Stacks Project, Tag 0B4D](https://stacks.math.columbia.edu/tag/0B4D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for pullbacks of presheaves on the big fppf site times out at the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_BirationalEtaleLocalization :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_BirationalEtaleLocalization
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private theorem chartEtale_of_isEtale (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : yoneda.obj U ⟶ F} (hf : IsEtale B S hS f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f :=
  presheaf_etale_of_isEtale B S hS hf

private theorem genericPoints_map_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentY : IsDecentSpace B S hS Y)
    {f : X ⟶ Y} (hf : IsEtale B S hS f)
    (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X)) :
    letI := pointTopology B S hS Y
    pointsMap B S hS X f x ∈ genericPoints (points B S hS Y) := by
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
  have htfae := mem_genericPoints_tfae B S hS hY hdecentY (pointsMap B S hS X f x)
  have hex : ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z)
      (a : Z ⟶ Y) (z : points B S hS Z), IsEtale B S hS a ∧
        pointsMap B S hS Z a z = pointsMap B S hS X f x ∧
        (let := pointTopology B S hS Z; z ∈ genericPoints (points B S hS Z)) :=
    ⟨X, hX, f, x, hf, rfl, hx⟩
  exact (htfae.out 3 1).mp hex

private theorem genericPoints_preimage_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentY : IsDecentSpace B S hS Y)
    {f : X ⟶ Y} (hf : IsEtale B S hS f)
    (x : points B S hS X)
    (hy : letI := pointTopology B S hS Y
      pointsMap B S hS X f x ∈ genericPoints (points B S hS Y)) :
    letI := pointTopology B S hS X
    x ∈ genericPoints (points B S hS X) := by
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
  have htfae := mem_genericPoints_tfae B S hS hY hdecentY (pointsMap B S hS X f x)
  have hall := (htfae.out 1 2).mp hy
  exact hall X hX f hf x rfl

/-- The canonical field-valued point of the generic stalk spectrum: the closed point of the
spectrum of the local ring, with the field of the chosen schematic representative. -/
private noncomputable def genericStalkFieldPoint
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (y : points B S hS Y)
    (hy : letI := pointTopology B S hS Y
      y ∈ genericPoints (points B S hS Y)) :
    FieldValuedPoint B S hS
      (yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy)) := by
  let U := schematicScheme B S hS hY
  let T := (BigFppfOver.toScheme B S hS).obj U
  let p := schematicRepresentative B S hS hY hdenseY hfiniteY y hy
  let a := (BigFppfOver.toScheme B S hS).map p.value
  let z := schemePoint B S hS U p
  let R := T.presheaf.stalk z
  let G := genericStalkSpec B S hS hY hdenseY hfiniteY y hy
  let P : BigFppfOver B S hS := p.siteObject B S hS (yoneda.obj U)
  let s : B.inclusion.obj P.left ⟶ B.inclusion.obj G.left := by
    change Spec (.of p.carrier) ⟶ Spec R
    exact Spec.map (Scheme.stalkClosedPointTo a)
  let s' := B.inclusion.preimage s
  let q : G.left ⟶ U.left := B.inclusion.preimage (T.fromSpecStalk z)
  have hqMap : B.inclusion.map q = T.fromSpecStalk z := B.inclusion.map_preimage _
  have hG : B.inclusion.map G.hom = T.fromSpecStalk z ≫ B.inclusion.map U.hom := by
    change B.inclusion.map (q ≫ U.hom) = _
    rw [Functor.map_comp, hqMap]
    rfl
  have hP : B.inclusion.map P.hom = p.toBase := by
    simp [P, FieldValuedPoint.siteObject]
  have hPa : a ≫ B.inclusion.map U.hom = p.toBase := by
    calc
      a ≫ B.inclusion.map U.hom =
          B.inclusion.map p.value.left ≫ B.inclusion.map U.hom := rfl
      _ = B.inclusion.map (p.value.left ≫ U.hom) :=
        (Functor.map_comp B.inclusion p.value.left U.hom).symm
      _ = B.inclusion.map P.hom := congrArg B.inclusion.map p.value.w
      _ = p.toBase := hP
  letI : Field p.carrier := p.field
  have hfactor : s ≫ T.fromSpecStalk z = a := by
    change Spec.map (Scheme.stalkClosedPointTo a) ≫
      T.fromSpecStalk (a (IsLocalRing.closedPoint p.carrier)) = a
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of p.carrier) (f := a)
  have hcompat : B.inclusion.map (s' ≫ G.hom) = B.inclusion.map P.hom := by
    calc
      B.inclusion.map (s' ≫ G.hom) = B.inclusion.map s' ≫ B.inclusion.map G.hom := by
        rw [Functor.map_comp]
      _ = s ≫ T.fromSpecStalk z ≫ B.inclusion.map U.hom := by
        rw [B.inclusion.map_preimage, hG]
        rfl
      _ = a ≫ B.inclusion.map U.hom :=
        congrArg (fun t => t ≫ B.inclusion.map U.hom) hfactor
      _ = p.toBase := hPa
      _ = B.inclusion.map P.hom := hP.symm
  exact { carrier := p.carrier, field := p.field, contained := p.contained
          toBase := p.toBase
          value := (Over.homMk s' (B.inclusion.map_injective hcompat) : P ⟶ G) }

private theorem pointsMap_genericStalkFieldPoint
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (y : points B S hS Y)
    (hy : letI := pointTopology B S hS Y
      y ∈ genericPoints (points B S hS Y)) :
    pointsMap B S hS (yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy))
      (fromGenericStalk B S hS hY hdenseY hfiniteY y hy)
      ((genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy).class
        B S hS (yoneda.obj (genericStalkSpec B S hS hY hdenseY hfiniteY y hy))) = y := by
  let U := schematicScheme B S hS hY
  let T := (BigFppfOver.toScheme B S hS).obj U
  let p := schematicRepresentative B S hS hY hdenseY hfiniteY y hy
  let a := (BigFppfOver.toScheme B S hS).map p.value
  let z := schemePoint B S hS U p
  let R := T.presheaf.stalk z
  let G := genericStalkSpec B S hS hY hdenseY hfiniteY y hy
  let P : BigFppfOver B S hS := p.siteObject B S hS (yoneda.obj U)
  let q : G.left ⟶ U.left := B.inclusion.preimage (T.fromSpecStalk z)
  have hqMap : B.inclusion.map q = T.fromSpecStalk z := B.inclusion.map_preimage _
  let s : B.inclusion.obj P.left ⟶ B.inclusion.obj G.left := by
    change Spec (.of p.carrier) ⟶ Spec R
    let : Field p.carrier := p.field
    exact Spec.map (Scheme.stalkClosedPointTo a)
  let qOver : G ⟶ U := Over.homMk q rfl
  have hfactor : Spec.map (Scheme.stalkClosedPointTo a) ≫ T.fromSpecStalk z = a := by
    change Spec.map (Scheme.stalkClosedPointTo a) ≫
      T.fromSpecStalk (a (IsLocalRing.closedPoint p.carrier)) = a
    let : Field p.carrier := p.field
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of p.carrier) (f := a)
  have hleft :
      (genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy).value.left ≫ q =
        p.value.left := by
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage s ≫ q) = B.inclusion.map p.value.left
    rw [Functor.map_comp, B.inclusion.map_preimage, hqMap]
    exact hfactor
  have hvalue :
      (genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy).value ≫ qOver = p.value :=
    Over.OverMorphism.ext hleft
  have hmapped :
      (FieldValuedPoint.map B S hS (yoneda.obj G) (yoneda.map qOver)
        (genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy)).class B S hS
          (yoneda.obj U) = p.class B S hS (yoneda.obj U) := by
    have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj U)
        (FieldValuedPoint.map B S hS (yoneda.obj G) (yoneda.map qOver)
          (genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy)) p := by
      refine ⟨𝟙 p.siteObject, ?_⟩
      change p.value = _
      exact hvalue.symm
    exact (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj U)
      (FieldValuedPoint.map B S hS (yoneda.obj G) (yoneda.map qOver)
        (genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy)) p).2
      ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) _, hdom⟩
  change pointsMap B S hS (yoneda.obj G)
    (yoneda.map qOver ≫ schematicChart B S hS hY) _ = y
  rw [pointsMap_comp_apply, pointsMap_class, hmapped]
  exact (exists_schematicRepresentative B S hS hY hdenseY hfiniteY y hy).choose_spec

private theorem genericStalkFieldPoint_closedPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hd : HasDenseRepresentableOpenSubspace B S hS F)
    (hn : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) :
    schemePoint B S hS _ (genericStalkFieldPoint B S hS hF hd hn x hx) =
      IsLocalRing.closedPoint (genericLocalRing B S hS hF hd hn x hx) := by
  let U := schematicScheme B S hS hF
  let p := schematicRepresentative B S hS hF hd hn x hx
  let G := genericStalkSpec B S hS hF hd hn x hx
  let a := (BigFppfOver.toScheme B S hS).map p.value
  let s : B.inclusion.obj (p.siteObject B S hS (yoneda.obj U)).left ⟶
      B.inclusion.obj G.left := Spec.map (Scheme.stalkClosedPointTo a)
  change B.inclusion.map (B.inclusion.preimage s) _ = _
  rw [B.inclusion.map_preimage]
  exact @Spec_closedPoint _ _ _ _ (Scheme.stalkClosedPointTo a)
    (Scheme.isLocalHom_stalkClosedPointTo (R := .of p.carrier) a)

private theorem isIso_pullback_snd_comp {C : Type*} [Category C] [HasPullbacks C]
    {X Y T Z : C} (f : X ⟶ Y) (h : T ⟶ Y) (a : Z ⟶ T)
    [IsIso (pullback.snd f h)] : IsIso (pullback.snd f (a ≫ h)) := by
  let e := pullbackLeftPullbackSndIso f h a
  have he : e.inv ≫ pullback.snd (pullback.snd f h) a = pullback.snd f (a ≫ h) := by
    simp [e]
  rw [← he]
  infer_instance

private theorem isIso_pullback_snd_of_comp_eq {C : Type*} [Category C] [HasPullbacks C]
    {X Y T Z : C} (f : X ⟶ Y) (h : T ⟶ Y) (a : Z ⟶ T) (k : Z ⟶ Y)
    (hk : k = a ≫ h) [IsIso (pullback.snd f h)] : IsIso (pullback.snd f k) := by
  subst k
  exact isIso_pullback_snd_comp f h a

private theorem isIso_pullback_snd_of_composite {C : Type*} [Category C] [HasPullbacks C]
    {X Y V T : C} (f : X ⟶ Y) (g : V ⟶ Y) (h : T ⟶ V)
    [IsIso (pullback.snd f (h ≫ g))] : IsIso (pullback.snd (pullback.snd f g) h) := by
  let e := pullbackLeftPullbackSndIso f g h
  have he : e.hom ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h := by
    simp [e]
  rw [← he]
  infer_instance

private theorem isIso_pullback_snd_pullback_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y T V : C} (f : X ⟶ Y) (h : T ⟶ Y) (g : V ⟶ Y)
    [IsIso (pullback.snd f h)] :
    IsIso (pullback.snd (pullback.snd f g) (pullback.fst g h)) := by
  have : IsIso (pullback.snd f (pullback.fst g h ≫ g)) :=
    isIso_pullback_snd_of_comp_eq f h (pullback.snd g h) _ pullback.condition
  exact isIso_pullback_snd_of_composite f g _

private theorem exists_point_pullback
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    (x : points B S hS F) (y : points B S hS G)
    (hxy : pointsMap B S hS F f x = pointsMap B S hS G g y) :
    ∃ w : points B S hS (pullback f g),
      pointsMap B S hS _ (pullback.fst f g) w = x ∧
      pointsMap B S hS _ (pullback.snd f g) w = y :=
  exists_point_of_isPullback_presheaf B S hS (IsPullback.of_hasPullback f g) x y hxy

private theorem pointsMap_injective_over_isIso_pullback
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) [IsIso (pullback.snd f g)]
    (x x' : points B S hS F) (y : points B S hS G)
    (hx : pointsMap B S hS F f x = pointsMap B S hS G g y)
    (hxx' : pointsMap B S hS F f x = pointsMap B S hS F f x') : x = x' := by
  obtain ⟨w, hw, hwy⟩ := exists_point_pullback B S hS f g x y hx
  obtain ⟨w', hw', hw'y⟩ := exists_point_pullback B S hS f g x' y (hxx'.symm.trans hx)
  have : Mono (pullback.snd f g) := IsIso.mono_of_iso _
  have heq : w = w' :=
    pointsMap_injective_of_mono B S hS _ (hwy.trans hw'y.symm)
  exact hw.symm.trans ((congrArg (pointsMap B S hS _ (pullback.fst f g)) heq).trans hw')

/-- A chart whose source has a point lying over every open of its scheme that contains the
given point factors through any open immersion whose image contains the image of that
point. -/
private theorem lift_open_of_local
    {U T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (j : yoneda.obj U ⟶ F) (hj : IsOpenImmersion B S hS j)
    (f : yoneda.obj T ⟶ F)
    (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hp : ∀ O : ((BigFppfOver.toScheme B S hS).obj T).Opens,
      schemePoint B S hS T p ∈ O → O = ⊤)
    (q : points B S hS (yoneda.obj U))
    (hq : pointsMap B S hS _ j q = pointsMap B S hS _ f (p.class B S hS _)) :
    ∃ l : T ⟶ U, yoneda.map l ≫ j = f := by
  let Q := BigFppfOver.toScheme B S hS
  let r := hj.1.snd f
  let e := (hj.1.isPullback f).isoPullback
  obtain ⟨w, hwU, hwT⟩ := exists_point_pullback B S hS j f q (p.class B S hS _) hq
  let wA := pointsMap B S hS _ e.inv w
  have hwA : pointsMap B S hS _ (yoneda.map r) wA = p.class B S hS _ := by
    rw [← pointsMap_comp_apply]
    simpa [e, r] using hwT
  obtain ⟨pA, hpA⟩ := Quot.exists_rep wA
  have hpt : Q.map r (schemePoint B S hS _ pA) = schemePoint B S hS T p := by
    rw [← schemePoint_map_yoneda]
    apply schemePoint_eq_of_class_eq
    simpa only [← pointsMap_class, hpA] using hwA
  have : AlgebraicGeometry.IsOpenImmersion (Q.map r) := hj.property_snd f
  have hrange : (Q.map r).opensRange = ⊤ := hp _ (hpt ▸ Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩)
  have : Surjective (Q.map r) := ⟨by
    intro x
    apply Scheme.Hom.mem_opensRange.mp
    rw [hrange]
    trivial⟩
  have : IsIso (Q.map r) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso r := isIso_of_reflects_iso r Q
  refine ⟨inv r ≫ hj.1.fst' f, ?_⟩
  rw [Functor.map_comp, Category.assoc, hj.1.map_fst', hj.1.w]
  change yoneda.map (inv r) ≫ yoneda.map r ≫ f = f
  rw [← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The schematic locus of a representable presheaf is everything, so its schematic chart is
an isomorphism. -/
private theorem isIso_schematicChart_yoneda (V : BigFppfOver B S hS) :
    IsIso (schematicChart B S hS (isAlgebraicSpace_yoneda B S hS V)) := by
  let F := yoneda.obj V
  let hF := isAlgebraicSpace_yoneda B S hS V
  let topSub : Subfunctor F := ⊤
  let e : topSub.toFunctor ≅ F :=
    { hom := topSub.ι
      inv := Subfunctor.lift (𝟙 F) (by intro T x hx; trivial)
      hom_inv_id := by ext T x; rfl
      inv_hom_id := by ext T x; rfl }
  have : IsIso topSub.ι := e.isIso_hom
  have htopAlg : IsAlgebraicSpace B S hS topSub.toFunctor :=
    isAlgebraicSpace_of_iso B S hS e.symm hF
  have htopOpen : IsOpenImmersion B S hS topSub.ι := by
    let P := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
    exact MorphismProperty.RespectsIso.postcomp P topSub.ι (𝟙 _) (P.id_mem _)
  have : topSub.toFunctor.IsRepresentable := isRepresentable_of_natIso F e.symm
  have htop : schematicLocus B S hS F = ⊤ :=
    top_le_iff.mp (le_schematicLocus B S hS F topSub ⟨htopAlg, htopOpen⟩ inferInstance)
  have hι : IsIso (schematicLocus B S hS F).ι := by
    rw [htop]
    exact e.isIso_hom
  unfold schematicChart
  dsimp only
  exact IsIso.comp_isIso' (Iso.isIso_hom _) hι

private theorem exists_lift_fromSpecStalk
    {Z : Scheme.{u}} (R : CommRingCat.{u}) [IsLocalRing R]
    (m : Spec R ⟶ Z) (z : Z) (hz : m (IsLocalRing.closedPoint R) = z) :
    ∃ n : Spec R ⟶ Spec (Z.presheaf.stalk z), n ≫ Z.fromSpecStalk z = m := by
  subst z
  exact ⟨Spec.map (Scheme.stalkClosedPointTo m), Scheme.Spec_stalkClosedPointTo_fromSpecStalk m⟩

/-- A morphism of representing objects sends the scheme point of a field-valued point to that of
another one when their images agree along a monomorphic chart. -/
private theorem map_schemePoint_eq_of_pointsMap_eq
    {T U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (j : yoneda.obj U ⟶ F) [Mono j] (l : T ⟶ U)
    (pT : FieldValuedPoint B S hS (yoneda.obj T)) (pU : FieldValuedPoint B S hS (yoneda.obj U))
    (h : pointsMap B S hS _ j (pointsMap B S hS _ (yoneda.map l) (pT.class B S hS _)) =
      pointsMap B S hS _ j (pU.class B S hS _)) :
    (BigFppfOver.toScheme B S hS).map l (schemePoint B S hS T pT) = schemePoint B S hS U pU := by
  rw [← schemePoint_map_yoneda]
  apply schemePoint_eq_of_class_eq
  apply pointsMap_injective_of_mono B S hS j
  rw [← pointsMap_class]
  exact h

/-- In a scheme isomorphic to the spectrum of a local ring, every open containing the point
over the closed point is everything. -/
theorem eq_top_of_mem_of_iso_spec_closedPoint {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (e : X ≅ Spec R) {x : X} (hx : e.hom x = IsLocalRing.closedPoint R)
    {O : X.Opens} (hO : x ∈ O) : O = ⊤ := by
  have hpre : IsLocalRing.closedPoint R ∈ O.comap e.inv.base.hom := by
    change e.inv (IsLocalRing.closedPoint R) ∈ O
    rw [← hx]
    simpa using hO
  have heq := (IsLocalRing.closedPoint_mem_iff _).mp hpre
  ext y
  have hy : e.hom y ∈ O.comap e.inv.base.hom := by
    rw [heq]
    trivial
  simpa using hy

/-- A morphism from a local scheme sending its closed point to a generic point of `Y`
factors through the generic stalk spectrum of `Y` there. -/
private theorem exists_factor_genericStalk_of_local
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hd : HasDenseRepresentableOpenSubspace B S hS Y)
    (hn : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (y : points B S hS Y)
    (hy : letI := pointTopology B S hS Y
      y ∈ genericPoints (points B S hS Y))
    (T : BigFppfOver B S hS) (R : CommRingCat.{u}) [IsLocalRing R]
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R)
    (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hp : e.hom (schemePoint B S hS T p) = IsLocalRing.closedPoint R)
    (f : yoneda.obj T ⟶ Y)
    (hf : pointsMap B S hS _ f (p.class B S hS _) = y) :
    ∃ t : T ⟶ genericStalkSpec B S hS hY hd hn y hy,
      yoneda.map t ≫ fromGenericStalk B S hS hY hd hn y hy = f := by
  let Q := BigFppfOver.toScheme B S hS
  let U := schematicScheme B S hS hY
  let j := schematicChart B S hS hY
  let pY := schematicRepresentative B S hS hY hd hn y hy
  have hpY : pointsMap B S hS _ j (pY.class B S hS _) = y :=
    (exists_schematicRepresentative B S hS hY hd hn y hy).choose_spec
  have hj := isOpenImmersion_schematicChart B S hS hY
  have : Mono j := mono_of_isOpenImmersion B S hS j hj
  obtain ⟨l, hl⟩ := lift_open_of_local B S hS j hj f p
    (fun _ hO => eq_top_of_mem_of_iso_spec_closedPoint e hp hO)
    (pY.class B S hS _) (hpY.trans hf.symm)
  have hz : Q.map l (schemePoint B S hS T p) = schemePoint B S hS U pY :=
    map_schemePoint_eq_of_pointsMap_eq B S hS j l p pY (by
      rw [← pointsMap_comp_apply, hl, hf, hpY])
  let m := e.inv ≫ Q.map l
  have hm : m (IsLocalRing.closedPoint R) = schemePoint B S hS U pY := by
    rw [← hp]
    simpa [m] using hz
  obtain ⟨n, hnfac⟩ := exists_lift_fromSpecStalk R m _ hm
  let G := genericStalkSpec B S hS hY hd hn y hy
  let qG := genericStalkInclusion B S hS hY hd hn y hy
  let t₀ : Q.obj T ⟶ Q.obj G := e.hom ≫ n
  have ht₀ : t₀ ≫ Q.map qG = Q.map l := by
    rw [toScheme_map_genericStalkInclusion]
    change (e.hom ≫ n) ≫ _ = _
    rw [Category.assoc, hnfac]
    simp [m]
  let tL : T.left ⟶ G.left := B.inclusion.preimage t₀
  have hleft : tL ≫ qG.left = l.left := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    exact ht₀
  let t : T ⟶ G := Over.homMk tL (by
    rw [← qG.w, ← Category.assoc, hleft]
    exact l.w)
  have ht : t ≫ qG = l := Over.OverMorphism.ext hleft
  refine ⟨t, ?_⟩
  change yoneda.map t ≫ yoneda.map qG ≫ j = f
  rw [← Functor.map_comp_assoc, ht]
  exact hl

private theorem isPullback_inv_snd_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso (pullback.snd f g)] :
    IsPullback (inv (pullback.snd f g) ≫ pullback.fst f g) (𝟙 Y) f g := by
  apply IsPullback.of_iso_pullback
    ⟨by simp [Category.assoc, pullback.condition]⟩ (asIso (pullback.snd f g)).symm
  · rfl
  · simp

private theorem isIso_stalkMap_of_isPullback_fromSpecStalk
    {C D : Scheme} (r : C ⟶ D) (z : C)
    (t : Spec (D.presheaf.stalk (r z)) ⟶ C)
    (ht : t (IsLocalRing.closedPoint (D.presheaf.stalk (r z))) = z)
    (sq : IsPullback t (𝟙 _) r (D.fromSpecStalk (r z))) : IsIso (r.stalkMap z) := by
  let a := Spec.map (r.stalkMap z)
  have ha : a ≫ t = C.fromSpecStalk z := by
    have hcomm : C.fromSpecStalk z ≫ r = a ≫ D.fromSpecStalk (r z) :=
      (Scheme.SpecMap_stalkMap_fromSpecStalk r).symm
    have h₁ := sq.lift_fst _ _ hcomm
    have h₂ := sq.lift_snd _ _ hcomm
    simpa using h₂ ▸ h₁
  obtain ⟨n, hn⟩ := exists_lift_fromSpecStalk (D.presheaf.stalk (r z)) t z ht
  have han : a ≫ n = 𝟙 _ := by
    apply (cancel_mono (C.fromSpecStalk z)).mp
    simpa only [Category.assoc, hn, Category.id_comp] using ha
  have hna : n ≫ a = 𝟙 _ := by
    apply (cancel_mono (D.fromSpecStalk (r z))).mp
    rw [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, hn]
    simpa using sq.w
  have haIso : IsIso a := ⟨⟨n, han, hna⟩⟩
  have : IsIso (Scheme.Spec.map (r.stalkMap z).op) := haIso
  have hi : IsIso (r.stalkMap z).op := isIso_of_reflects_iso (r.stalkMap z).op Scheme.Spec
  exact @isIso_unop _ _ _ _ (r.stalkMap z).op hi

private theorem isIso_stalkMap_of_isPullback_fromSpecStalk_at
    {C D : Scheme.{u}} (r : C ⟶ D) (z : C) (zD : D) (hzD : r z = zD)
    (t : Spec (D.presheaf.stalk zD) ⟶ C)
    (ht : t (IsLocalRing.closedPoint (D.presheaf.stalk zD)) = z)
    (sq : IsPullback t (𝟙 _) r (D.fromSpecStalk zD)) : IsIso (r.stalkMap z) := by
  subst zD
  exact isIso_stalkMap_of_isPullback_fromSpecStalk r z t ht sq

private theorem isEtale_pullback_fst
    {X V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : V ⟶ Y) (hg : IsEtale B S hS g) :
    IsEtale B S hS (pullback.fst f g) := by
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Vsp : AlgebraicSpaces B S hS := ⟨V, hV⟩
  let fsp : Xsp ⟶ Ysp := ObjectProperty.homMk f
  let gsp : Vsp ⟶ Ysp := ObjectProperty.homMk g
  let Wsp := AlgebraicSpaces.fiberProduct B S hS fsp gsp
  let p : Wsp ⟶ Xsp := ObjectProperty.homMk (pullback.fst fsp.hom gsp.hom)
  let q : Wsp ⟶ Vsp := ObjectProperty.homMk (pullback.snd fsp.hom gsp.hom)
  have hpull : IsPullback p q fsp gsp := by
    simpa [p, q] using AlgebraicSpaces.isPullback_fiberProduct B S hS fsp gsp
  have hp : IsEtale B S hS p.hom :=
    isEtale_of_isPullback B S hS q p gsp fsp hpull.flip hg
  simpa [p, Wsp, AlgebraicSpaces.fiberProduct, fsp, gsp] using hp

/-- The point space of a decent algebraic space is `T0` and quasi-sober. -/
private theorem t0_and_quasiSober_points {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hd : IsDecentSpace B S hS F) :
    letI := pointTopology B S hS F
    T0Space (points B S hS F) ∧ QuasiSober (points B S hS F) := by
  let := pointTopology B S hS F
  exact stacksSober_iff_t0_and_quasiSober.mp (stacksSober_points_of_isDecentSpace B S hS hF hd)

/-- **Stacks 0B4D, decency.** The base change of a decent algebraic space along an étale
morphism from a representable presheaf is decent. -/
@[stacks 0B4D "decent"]
theorem isDecentSpace_pullback_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X)
    (V : BigFppfOver B S hS)
    (f : X ⟶ Y) (g : yoneda.obj V ⟶ Y) (hg : IsEtale B S hS g) :
    IsDecentSpace B S hS (pullback f g) :=
  isDecentSpace_of_isEtale B S hS (pullback.fst f g)
    (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY) hX
    (isEtale_pullback_fst B S hS hX (isAlgebraicSpace_yoneda B S hS V) hY f g hg) hdecentX

/-- An affine étale localization of a decent algebraic space with finitely many irreducible
components again has finitely many irreducible components. -/
theorem finite_irreducibleComponents_of_isEtale_of_isAffine
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (g : yoneda.obj V ⟶ Y) (hg : IsEtale B S hS g) :
    letI := pointTopology B S hS (yoneda.obj V)
    (irreducibleComponents (points B S hS (yoneda.obj V))).Finite := by
  classical
  let Ypts := points B S hS Y
  let Vpts := points B S hS (yoneda.obj V)
  let : TopologicalSpace Ypts := pointTopology B S hS Y
  let : TopologicalSpace Vpts := pointTopology B S hS (yoneda.obj V)
  have hVdecent := isDecentSpace_of_isEtale B S hS g
    (isAlgebraicSpace_yoneda B S hS V) hY hg hdecentY
  obtain ⟨_, _⟩ := t0_and_quasiSober_points B S hS hY hdecentY
  obtain ⟨_, _⟩ := t0_and_quasiSober_points B S hS (isAlgebraicSpace_yoneda B S hS V) hVdecent
  have hfiniteYgp : (genericPoints Ypts).Finite := genericPoints.finite hfiniteY
  have : Finite (genericPoints Ypts) := hfiniteYgp.to_subtype
  have hmapGeneric (v : genericPoints Vpts) :
      pointsMap B S hS (yoneda.obj V) g v.1 ∈ genericPoints Ypts :=
    genericPoints_map_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS V) hY hdecentY hg
      v.1 v.2
  let m : genericPoints Vpts → genericPoints Ypts := fun v =>
    ⟨pointsMap B S hS (yoneda.obj V) g v.1, hmapGeneric v⟩
  have hgChart := chartEtale_of_isEtale B S hS V hg
  have hfiber (y : genericPoints Ypts) :
      (pointsMap B S hS (yoneda.obj V) g ⁻¹' {y.1}).Finite :=
    ((hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative
      B S hS Y hY y.1).2 (hdecentY y.1) V (by assumption) g hgChart).1
  have himage : (m '' (Set.univ : Set (genericPoints Vpts))).Finite := Set.toFinite _
  have hfiniteVgp : (Set.univ : Set (genericPoints Vpts)).Finite :=
    Set.Finite.of_finite_fibers m himage (by
      intro y hy
      have hpre : (m ⁻¹' {y}).Finite := by
        refine ((hfiber y).preimage Subtype.val_injective.injOn).subset fun v hv => ?_
        change m v = y at hv
        exact congrArg Subtype.val hv
      simpa using hpre)
  have : Finite (genericPoints Vpts) := Set.finite_univ_iff.mp hfiniteVgp
  have : Finite (irreducibleComponents Vpts) :=
    Finite.of_equiv _ (genericPoints.equiv (α := Vpts))
  exact Set.toFinite _

/-- The projection of the base change of a birational morphism along an étale morphism maps
generic points to generic points. -/
theorem pointsMap_pullback_snd_mem_genericPoints
    {X V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (g : V ⟶ Y) (hg : IsEtale B S hS g) (w : points B S hS (pullback f g))
    (hw : letI := pointTopology B S hS (pullback f g)
      w ∈ genericPoints (points B S hS (pullback f g))) :
    letI := pointTopology B S hS V
    pointsMap B S hS _ (pullback.snd f g) w ∈ genericPoints (points B S hS V) := by
  let W := pullback f g
  let p := pullback.fst f g
  let q := pullback.snd f g
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
  let x := pointsMap B S hS W p w
  have hx : x ∈ genericPoints (points B S hS X) :=
    genericPoints_map_of_isEtale B S hS (isAlgebraicSpace_pullback B S hS f g hX hV hY) hX
      hdecentX (isEtale_pullback_fst B S hS hX hV hY f g hg) w hw
  have hy := (hf.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY).mapsTo hx
  have hxy : pointsMap B S hS X f x = pointsMap B S hS V g (pointsMap B S hS W q w) := by
    have h := congrArg (fun k : W ⟶ Y => pointsMap B S hS W k w)
      (pullback.condition (f := f) (g := g))
    rw [pointsMap_comp_apply, pointsMap_comp_apply] at h
    simpa [x, p, q] using h
  have hyV : pointsMap B S hS V g (pointsMap B S hS W q w) ∈
      genericPoints (points B S hS Y) := by
    rwa [← hxy]
  exact genericPoints_preimage_of_isEtale B S hS hV hY hdecentY hg _ hyV

private theorem bijOn_genericPoints_pullback_snd
    {X V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (g : V ⟶ Y) (hg : IsEtale B S hS g) :
    letI := pointTopology B S hS (pullback f g)
    letI := pointTopology B S hS V
    Set.BijOn (pointsMap B S hS _ (pullback.snd f g))
      (genericPoints (points B S hS (pullback f g)))
      (genericPoints (points B S hS V)) := by
  classical
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  let W := pullback f g
  let hW : IsAlgebraicSpace B S hS W := isAlgebraicSpace_pullback B S hS f g hX hV hY
  let : TopologicalSpace (points B S hS W) := pointTopology B S hS W
  let : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
  let : TopologicalSpace (points B S hS V) := pointTopology B S hS V
  let p := pullback.fst f g
  let q := pullback.snd f g
  have hp : IsEtale B S hS p := isEtale_pullback_fst B S hS hX hV hY f g hg
  have hbijection := hf.bijOn B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY
  have hmapGeneric (w : genericPoints (points B S hS W)) :
      pointsMap B S hS W q w.1 ∈ genericPoints (points B S hS V) :=
    pointsMap_pullback_snd_mem_genericPoints B S hS hX hV hY hdecentX hdecentY hfiniteX
      hfiniteY f hf g hg w.1 w.2
  let m : genericPoints (points B S hS W) → genericPoints (points B S hS V) := fun w =>
    ⟨pointsMap B S hS W q w.1, hmapGeneric w⟩
  have hinj : Function.Injective m := by
    intro w w' heq
    have hqeq : pointsMap B S hS W q w.1 = pointsMap B S hS W q w'.1 :=
      congrArg Subtype.val heq
    let v := pointsMap B S hS W q w.1
    let y := pointsMap B S hS V g v
    have hy : y ∈ genericPoints (points B S hS Y) :=
      genericPoints_map_of_isEtale B S hS hV hY hdecentY hg v (hmapGeneric w)
    let a := fromGenericStalk B S hS hY hdenseY hfiniteY y hy
    let t := (genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy).class B S hS _
    have ht : pointsMap B S hS _ a t = y :=
      pointsMap_genericStalkFieldPoint B S hS hY hdenseY hfiniteY y hy
    obtain ⟨v', hv', -⟩ := exists_point_pullback B S hS g a v t ht.symm
    have : IsIso (pullback.snd f a) :=
      isIso_pullback_snd_fromGenericStalk_of_isBirational
        B S hS hY hfiniteY y hy hdecentY hX hdecentX hfiniteX f hf
    have : IsIso (pullback.snd q (pullback.fst g a)) := isIso_pullback_snd_pullback_fst f a g
    exact Subtype.ext <| pointsMap_injective_over_isIso_pullback B S hS q (pullback.fst g a)
      w.1 w'.1 v' hv'.symm hqeq
  refine ⟨fun w hw => hmapGeneric ⟨w, hw⟩, ?_, ?_⟩
  · intro w hw w' hw' heq
    exact congrArg Subtype.val (hinj (a₁ := ⟨w, hw⟩) (a₂ := ⟨w', hw'⟩) (Subtype.ext heq))
  · intro v hv
    have hy := genericPoints_map_of_isEtale B S hS hV hY hdecentY hg v hv
    obtain ⟨x, hx, hxy⟩ := hbijection.surjOn hy
    obtain ⟨w, hwx, hwv⟩ := exists_point_pullback B S hS f g x v hxy
    refine ⟨w, ?_, hwv⟩
    apply genericPoints_preimage_of_isEtale B S hS hW hX hdecentX hp
    change pointsMap B S hS _ (pullback.fst f g) w ∈ _
    rw [hwx]
    exact hx

/-- **Stacks 0B4D, finitely many irreducible components.** An affine étale localization of a
birational morphism of decent algebraic spaces with finitely many irreducible components has
a source with finitely many irreducible components. -/
@[stacks 0B4D "finitely many irreducible components"]
theorem finite_irreducibleComponents_pullback_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (g : yoneda.obj V ⟶ Y) (hg : IsEtale B S hS g) :
    letI := pointTopology B S hS (pullback f g)
    (irreducibleComponents (points B S hS (pullback f g))).Finite := by
  let W := pullback f g
  let hW := isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY
  let := pointTopology B S hS W
  let := pointTopology B S hS (yoneda.obj V)
  obtain ⟨_, _⟩ := t0_and_quasiSober_points B S hS hW
    (isDecentSpace_pullback_of_isEtale B S hS hX hY hdecentX V f g hg)
  have hbij := bijOn_genericPoints_pullback_snd B S hS hX
    (isAlgebraicSpace_yoneda B S hS V) hY hdecentX hdecentY
    hfiniteX hfiniteY f hf g hg
  have hVfinite :=
    finite_irreducibleComponents_of_isEtale_of_isAffine B S hS hY hdecentY hfiniteY V g hg
  have hVdecent := isDecentSpace_of_isEtale B S hS g
    (isAlgebraicSpace_yoneda B S hS V) hY hg hdecentY
  obtain ⟨_, _⟩ := t0_and_quasiSober_points B S hS (isAlgebraicSpace_yoneda B S hS V) hVdecent
  have : Finite (genericPoints (points B S hS (yoneda.obj V))) :=
    (genericPoints.finite hVfinite).to_subtype
  have : Finite (genericPoints (points B S hS W)) :=
    Finite.of_injective (fun w : genericPoints (points B S hS W) =>
      (⟨pointsMap B S hS _ (pullback.snd f g) w.1, hbij.mapsTo w.2⟩ :
        genericPoints (points B S hS (yoneda.obj V))))
      (fun w w' h => Subtype.ext (hbij.injOn w.2 w'.2 (congrArg Subtype.val h)))
  have : Finite (irreducibleComponents (points B S hS W)) :=
    Finite.of_equiv _ (genericPoints.equiv (α := points B S hS W))
  exact Set.toFinite _

/-- At a generic point of an étale source, the base change of a birational morphism becomes an
isomorphism over the generic stalk spectrum of the source. -/
theorem isIso_pullback_snd_pullback_snd_fromGenericStalk
    {X V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hV : IsAlgebraicSpace B S hS V)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (g : V ⟶ Y) (hg : IsEtale B S hS g)
    (hdV : HasDenseRepresentableOpenSubspace B S hS V)
    (hnV : (letI := pointTopology B S hS V
      (irreducibleComponents (points B S hS V)).Finite))
    (v : points B S hS V)
    (hv : letI := pointTopology B S hS V
      v ∈ genericPoints (points B S hS V)) :
    IsIso (pullback.snd (pullback.snd f g) (fromGenericStalk B S hS hV hdV hnV v hv)) := by
  have hdenseY := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hY hdecentY
  let := pointTopology B S hS Y
  let aD := fromGenericStalk B S hS hV hdV hnV v hv
  let pGD := genericStalkFieldPoint B S hS hV hdV hnV v hv
  have hpGDmap : pointsMap B S hS _ aD (pGD.class B S hS _) = v :=
    pointsMap_genericStalkFieldPoint B S hS hV hdV hnV v hv
  let y := pointsMap B S hS V g v
  have hy : y ∈ genericPoints (points B S hS Y) :=
    genericPoints_map_of_isEtale B S hS hV hY hdecentY hg v hv
  obtain ⟨k, hk⟩ := exists_factor_genericStalk_of_local B S hS hY hdenseY hfiniteY y hy
    (genericStalkSpec B S hS hV hdV hnV v hv) (genericLocalRing B S hS hV hdV hnV v hv)
    (Iso.refl _) pGD (genericStalkFieldPoint_closedPoint B S hS hV hdV hnV v hv) (aD ≫ g)
    (by rw [pointsMap_comp_apply, hpGDmap])
  let aY := fromGenericStalk B S hS hY hdenseY hfiniteY y hy
  have : IsIso (pullback.snd f aY) :=
    isIso_pullback_snd_fromGenericStalk_of_isBirational
      B S hS hY hfiniteY y hy hdecentY hX hdecentX hfiniteX f hf
  have : IsIso (pullback.snd f (aD ≫ g)) :=
    isIso_pullback_snd_of_comp_eq f aY (yoneda.map k) (aD ≫ g) hk.symm
  exact isIso_pullback_snd_of_composite f g aD

/-- A pullback square along an isomorphic chart, restricted through a monomorphic chart,
descends to a pullback square of representing objects. -/
theorem isPullback_of_isPullback_yoneda
    {G C D : BigFppfOver B S hS} {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {jC : yoneda.obj C ⟶ F} [Mono jC] {jD : yoneda.obj D ⟶ H} [IsIso jD]
    {q : F ⟶ H} {s : yoneda.obj G ⟶ F} {aD : yoneda.obj G ⟶ H}
    (sq : IsPullback s (𝟙 _) q aD)
    {t : G ⟶ C} (ht : yoneda.map t ≫ jC = s)
    {r : C ⟶ D} (hr : yoneda.map r ≫ jD = jC ≫ q)
    {gD : G ⟶ D} (hgD : yoneda.map gD ≫ jD = aD) :
    IsPullback t (𝟙 _) r gD := by
  subst hgD
  have sqTop : IsPullback (yoneda.map t) (𝟙 _) jC s :=
    IsPullback.of_vert_isIso_mono ⟨by simpa only [Category.id_comp] using ht⟩
  have sqComp : IsPullback (yoneda.map t) (𝟙 _) (jC ≫ q) (yoneda.map gD ≫ jD) := by
    simpa only [Category.id_comp] using sqTop.paste_vert sq
  have sqRep : IsPullback (yoneda.map t) (𝟙 _) (yoneda.map r) (yoneda.map gD) := by
    apply sqComp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso jD).symm
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
      rw [← hr]
      simp
    · simp
  have htr : t ≫ r = gD := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, Category.id_comp] using sqRep.w
  exact IsPullback.of_map yoneda (by simpa only [Category.id_comp] using htr)
    (by simpa only [CategoryTheory.Functor.map_id] using sqRep)

/-- A pullback square of the generic stalk inclusion between schematic charts, sending the
closed point to the chosen point, makes the induced map of local rings an isomorphism. -/
theorem isIso_genericLocalRingMap_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdenseX : HasDenseRepresentableOpenSubspace B S hS X)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y) (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    (hy : letI := pointTopology B S hS Y
      pointsMap B S hS X f x ∈ genericPoints (points B S hS Y))
    (r : schematicScheme B S hS hX ⟶ schematicScheme B S hS hY)
    (hr : yoneda.map r ≫ schematicChart B S hS hY = schematicChart B S hS hX ≫ f)
    (t : genericStalkSpec B S hS hY hdenseY hfiniteY _ hy ⟶ schematicScheme B S hS hX)
    (sq : IsPullback t (𝟙 _) r (genericStalkInclusion B S hS hY hdenseY hfiniteY _ hy))
    (ht : (BigFppfOver.toScheme B S hS).map t
        (IsLocalRing.closedPoint (genericLocalRing B S hS hY hdenseY hfiniteY _ hy)) =
      schemePoint B S hS _ (schematicRepresentative B S hS hX hdenseX hfiniteX x hx))
    (hpoint : (BigFppfOver.toScheme B S hS).map r
        (schemePoint B S hS _ (schematicRepresentative B S hS hX hdenseX hfiniteX x hx)) =
      schemePoint B S hS _ (schematicRepresentative B S hS hY hdenseY hfiniteY _ hy)) :
    IsIso (genericLocalRingMap B S hS hX hY hdenseX hdenseY hfiniteX hfiniteY f x hx hy) := by
  let Q := BigFppfOver.toScheme B S hS
  let D := schematicScheme B S hS hY
  let zC := schemePoint B S hS _ (schematicRepresentative B S hS hX hdenseX hfiniteX x hx)
  let zD := schemePoint B S hS _ (schematicRepresentative B S hS hY hdenseY hfiniteY _ hy)
  have hgD : Q.map (genericStalkInclusion B S hS hY hdenseY hfiniteY _ hy) =
      (Q.obj D).fromSpecStalk zD :=
    toScheme_map_genericStalkInclusion B S hS hY hdenseY hfiniteY _ hy
  have sqScheme : IsPullback (Q.map t) (𝟙 _) (Q.map r) ((Q.obj D).fromSpecStalk zD) := by
    simpa only [CategoryTheory.Functor.map_id, hgD] using sq.map Q
  have hstalk : IsIso ((Q.map r).stalkMap zC) :=
    isIso_stalkMap_of_isPullback_fromSpecStalk_at (Q.map r) zC zD hpoint (Q.map t) ht sqScheme
  have hformula := (exists_genericLocalRingMap B S hS hX hY hdenseX hdenseY hfiniteX hfiniteY
    f x hx hy).choose_spec (schematicGenericChart B S hS hX hdenseX hfiniteX x hx)
    (schematicGenericChart B S hS hY hdenseY hfiniteY _ hy) r hr.symm hpoint
  unfold genericLocalRingMap
  rw [hformula]
  change IsIso (_ ≫ _ ≫ (Q.map r).stalkMap zC ≫ _)
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso'
    (eqToIso (congrArg (fun z => (Q.obj D).presheaf.stalk z) hpoint.symm)).isIso_hom
    (IsIso.comp_isIso' hstalk (Iso.isIso_hom _)))

private theorem isIso_genericLocalRingMap_of_isPullback_fromGenericStalk
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hV : IsAlgebraicSpace B S hS V)
    (hDW : HasDenseRepresentableOpenSubspace B S hS W)
    (hDV : HasDenseRepresentableOpenSubspace B S hS V)
    (hnW : (letI := pointTopology B S hS W
      (irreducibleComponents (points B S hS W)).Finite))
    (hnV : (letI := pointTopology B S hS V
      (irreducibleComponents (points B S hS V)).Finite))
    (q : W ⟶ V) (w : points B S hS W)
    (hw : letI := pointTopology B S hS W
      w ∈ genericPoints (points B S hS W))
    (hv : letI := pointTopology B S hS V
      pointsMap B S hS W q w ∈ genericPoints (points B S hS V))
    [IsIso (schematicChart B S hS hV)]
    (s : yoneda.obj (genericStalkSpec B S hS hV hDV hnV _ hv) ⟶ W)
    (sq : IsPullback s (𝟙 _) q (fromGenericStalk B S hS hV hDV hnV _ hv))
    (hsp : pointsMap B S hS _ s
      ((genericStalkFieldPoint B S hS hV hDV hnV _ hv).class B S hS _) = w) :
    IsIso (genericLocalRingMap B S hS hW hV hDW hDV hnW hnV q w hw hv) := by
  let Q := BigFppfOver.toScheme B S hS
  let v := pointsMap B S hS W q w
  let pGD := genericStalkFieldPoint B S hS hV hDV hnV v hv
  have hpGD : schemePoint B S hS _ pGD =
      IsLocalRing.closedPoint (genericLocalRing B S hS hV hDV hnV v hv) :=
    genericStalkFieldPoint_closedPoint B S hS hV hDV hnV v hv
  let jC := schematicChart B S hS hW
  let jD := schematicChart B S hS hV
  let pC := schematicRepresentative B S hS hW hDW hnW w hw
  let pD := schematicRepresentative B S hS hV hDV hnV v hv
  have hjC := isOpenImmersion_schematicChart B S hS hW
  have : Mono jC := mono_of_isOpenImmersion B S hS jC hjC
  have hpC : pointsMap B S hS _ jC (pC.class B S hS _) = w :=
    (exists_schematicRepresentative B S hS hW hDW hnW w hw).choose_spec
  have hpD : pointsMap B S hS _ jD (pD.class B S hS _) = v :=
    (exists_schematicRepresentative B S hS hV hDV hnV v hv).choose_spec
  obtain ⟨t, ht⟩ := lift_open_of_local B S hS jC hjC s pGD
    (fun O hO => (IsLocalRing.closedPoint_mem_iff O).mp (hpGD ▸ hO))
    (pC.class B S hS _) (hpC.trans hsp.symm)
  have htpoint : Q.map t (IsLocalRing.closedPoint (genericLocalRing B S hS hV hDV hnV v hv)) =
      schemePoint B S hS _ pC := by
    rw [← hpGD]
    exact map_schemePoint_eq_of_pointsMap_eq B S hS jC t pGD pC (by
      rw [← pointsMap_comp_apply, ht, hsp, hpC])
  let r : schematicScheme B S hS hW ⟶ schematicScheme B S hS hV :=
    yoneda.preimage (jC ≫ q ≫ inv jD)
  have hr : yoneda.map r ≫ jD = jC ≫ q := by
    rw [Functor.map_preimage]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have : Mono jD := IsIso.mono_of_iso _
  have hpoint : Q.map r (schemePoint B S hS _ pC) = schemePoint B S hS _ pD := by
    exact map_schemePoint_eq_of_pointsMap_eq B S hS jD r pC pD (by
      rw [← pointsMap_comp_apply, hr, pointsMap_comp_apply, hpC, hpD])
  exact isIso_genericLocalRingMap_of_isPullback B S hS hW hV hDW hDV hnW hnV q w hw hv r hr t
    (isPullback_of_isPullback_yoneda B S hS sq ht hr
      (gD := genericStalkInclusion B S hS hV hDV hnV v hv) rfl) htpoint hpoint

/-- **Stacks 0B4D, birationality.** An affine étale localization of a birational morphism of
decent algebraic spaces with finitely many irreducible components is birational. -/
@[stacks 0B4D "birational", ega "IV 6.15.4.1" "étale affine case"]
theorem isBirational_pullback_snd_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecentX : IsDecentSpace B S hS X) (hdecentY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y)
    (hf : IsBirational B S hS hX hY hdecentX hdecentY hfiniteX hfiniteY f)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (g : yoneda.obj V ⟶ Y) (hg : IsEtale B S hS g) :
    IsBirational B S hS
      (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS V) hY)
      (isAlgebraicSpace_yoneda B S hS V)
      (isDecentSpace_pullback_of_isEtale B S hS hX hY hdecentX V f g hg)
      (isDecentSpace_of_isEtale B S hS g (isAlgebraicSpace_yoneda B S hS V) hY hg hdecentY)
      (finite_irreducibleComponents_pullback_of_isEtale B S hS hX hY hdecentX hdecentY
        hfiniteX hfiniteY f hf V g hg)
      (finite_irreducibleComponents_of_isEtale_of_isAffine B S hS hY hdecentY hfiniteY V g hg)
      (pullback.snd f g) := by
  classical
  let W := pullback f g
  let hV := isAlgebraicSpace_yoneda B S hS V
  let hW := isAlgebraicSpace_pullback B S hS f g hX hV hY
  let hdW := isDecentSpace_pullback_of_isEtale B S hS hX hY hdecentX V f g hg
  let hdV := isDecentSpace_of_isEtale B S hS g hV hY hg hdecentY
  let hDW := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hW hdW
  let hDV := hasDenseRepresentableOpenSubspace_of_isDecentSpace B S hS hV hdV
  let hnW := finite_irreducibleComponents_pullback_of_isEtale B S hS hX hY hdecentX hdecentY
    hfiniteX hfiniteY f hf V g hg
  let hnV := finite_irreducibleComponents_of_isEtale_of_isAffine B S hS hY hdecentY hfiniteY
    V g hg
  let q := pullback.snd f g
  let := pointTopology B S hS W
  let := pointTopology B S hS (yoneda.obj V)
  have hbij := bijOn_genericPoints_pullback_snd B S hS hX hV hY hdecentX hdecentY
    hfiniteX hfiniteY f hf g hg
  refine ⟨hbij, fun w hw => ?_⟩
  let v := pointsMap B S hS W q w
  have hv : v ∈ genericPoints (points B S hS (yoneda.obj V)) := hbij.mapsTo hw
  let aD := fromGenericStalk B S hS hV hDV hnV v hv
  let pGD := genericStalkFieldPoint B S hS hV hDV hnV v hv
  have hpGDmap : pointsMap B S hS _ aD (pGD.class B S hS _) = v :=
    pointsMap_genericStalkFieldPoint B S hS hV hDV hnV v hv
  have : IsIso (pullback.snd q aD) := isIso_pullback_snd_pullback_snd_fromGenericStalk B S hS
    hX hV hY hdecentX hdecentY hfiniteX hfiniteY f hf g hg hDV hnV v hv
  let s := inv (pullback.snd q aD) ≫ pullback.fst q aD
  have sq : IsPullback s (𝟙 _) q aD := isPullback_inv_snd_fst q aD
  have hs : s ≫ q = aD := by simpa only [Category.id_comp] using sq.w
  have hsp : pointsMap B S hS _ s (pGD.class B S hS _) = w := by
    apply pointsMap_injective_over_isIso_pullback B S hS q aD _ w (pGD.class B S hS _)
    · rw [← pointsMap_comp_apply, hs]
    · rw [← pointsMap_comp_apply, hs, hpGDmap]
  have : IsIso (schematicChart B S hS hV) := isIso_schematicChart_yoneda B S hS V
  change IsIso (genericLocalRingMap B S hS hW hV hDW hDV hnW hnV q w hw hv)
  exact isIso_genericLocalRingMap_of_isPullback_fromGenericStalk B S hS hW hV hDW hDV hnW hnV q
    w hw hv s sq hsp

end AlgebraicGeometry.Space

end
