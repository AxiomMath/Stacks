module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria

/-!
# Universal closedness of a quasi-compact morphism with decent source

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` with `X`
decent. Then `f` is universally closed exactly when it satisfies the existence part of the
valuative criterion.

One direction is Stacks 03KA and needs no decency. For the other, a valuative square for `f`
presents the generic point of its valuation ring as a point of the fibre product
`X ×_Y Spec R`; universal closedness makes the image of the closure of that point in
`|Spec R|` closed, and it contains the generic point, so it is all of `|Spec R|` and in
particular contains the closed point. Decency of the fibre product is what lets that
specialization be lifted to an étale scheme chart of the fibre product (Stacks 03K2), and
there it is realized by a valuation subring of the residue field at the generic point of the
chart, which is the dominating extension the criterion asks for.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_iff_valuativeCriterion_existence`:
  **Stacks 03KJ**.
* `AlgebraicGeometry.Space.universallyClosed_iff_valuativeCriterion_existence_of_isDecent`:
  **Stacks 03M6**, the same equivalence for a quasi-compact morphism which is decent as a
  morphism, with no decency hypothesis on its source.

## Implementation notes

Decency of `X` is `AlgebraicGeometry.Space.IsDecentSpace`, condition (4) of Stacks 03JV. It
is used only through two consequences: it passes to the source of a representable
morphism, so each base change `X ×_Y h_T` is again decent
(`AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`), and it implies
condition (2) of Stacks 03JS, finiteness of the fibre of every affine étale chart above every
point (`AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_isDecentSpace`), which is
the hypothesis Stacks 03K2 takes. The equivalences of Stacks 03JV are *not* used, and are not
available here.

The valuation subring is produced by `IsLocalRing.exists_factor_valuationRing` applied to the
composite `𝒪_{V, z} ⟶ 𝒪_{V, z'} ⟶ L` of the specialization map of a chart `V` with the local
homomorphism attached to the lifted generic point, as in Stacks 01J8; the resulting
`Spec A ⟶ V` carries the closed point of `Spec A` to `z`, which is what makes the homomorphism
`R ⟶ A` local and hence the extension dominating.

## References

* [Stacks Project, Tag 01J8](https://stacks.math.columbia.edu/tag/01J8)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 03JS](https://stacks.math.columbia.edu/tag/03JS)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03KA](https://stacks.math.columbia.edu/tag/03KA)
* [Stacks Project, Tag 03KJ](https://stacks.math.columbia.edu/tag/03KJ)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03M6](https://stacks.math.columbia.edu/tag/03M6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local instance (priority := high) hasLimit_cospan_presheaf_UniversallyClosedValuative
    {Z₁ Z₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-- **A valuation subring realizing a specialization along a morphism to a local spectrum.**
Let `t : V ⟶ Spec R` be a morphism of schemes with `R` a local ring, let `g : Spec L ⟶ V` be
a field-valued point of `V` whose image specializes to `z`, and assume `t z` is the closed
point of `Spec R`. Then there is a valuation subring `A` of `L` dominating `R` and a morphism
`Spec A ⟶ V` restricting to `g` over `L` and factoring `t` through `Spec R`.

The subring is produced by factoring the composite of the specialization map
`𝒪_{V, z} ⟶ 𝒪_{V, g(closed point)}` with the local homomorphism attached to `g` through a
valuation subring of `L`, as in Stacks 01J8. -/
@[ega "II 7.1.4" "special case"]
private theorem exists_valuationSubring_lift_of_specializes
    {R L : Type u} [CommRing R] [IsLocalRing R] [Field L]
    {V : Scheme.{u}} (t : V ⟶ Spec (.of R)) (g : Spec (.of L) ⟶ V)
    (z : V) (hgz : g (IsLocalRing.closedPoint L) ⤳ z)
    (htz : t z = IsLocalRing.closedPoint R) :
    ∃ (A : ValuationSubring L) (ρ : R →+* A) (ℓ : Spec (.of A) ⟶ V),
      IsLocalHom ρ ∧
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ ℓ = g ∧
      ℓ ≫ t = Spec.map (CommRingCat.ofHom ρ) := by
  let β : V.presheaf.stalk z ⟶ CommRingCat.of L :=
    V.presheaf.stalkSpecializes hgz ≫ Scheme.stalkClosedPointTo g
  obtain ⟨A, hA, hlocal⟩ := IsLocalRing.exists_factor_valuationRing β.hom
  let c : V.presheaf.stalk z ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (β.hom.codRestrict A.toSubring hA)
  let ℓ : Spec (.of A) ⟶ V := Spec.map c ≫ V.fromSpecStalk z
  have hfactor : Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ ℓ = g := by
    show Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫
      (Spec.map c ≫ V.fromSpecStalk z) = g
    rw [← Spec.map_comp_assoc]
    show Spec.map β ≫ V.fromSpecStalk z = g
    dsimp only [β]
    rw [Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgz]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := g)
  have _ : IsLocalRing A.toSubring := A.isLocalRing
  have hcentre : ℓ (IsLocalRing.closedPoint A) = z := by
    have hc : Spec.map c (IsLocalRing.closedPoint A) =
        IsLocalRing.closedPoint (V.presheaf.stalk z) :=
      @IsLocalRing.comap_closedPoint _ _ _ _ _ _
        (β.hom.codRestrict A.toSubring hA) hlocal
    show V.fromSpecStalk z (Spec.map c (IsLocalRing.closedPoint A)) = z
    rw [hc, V.fromSpecStalk_closedPoint]
  let ρ : R →+* A := (Spec.preimage (ℓ ≫ t)).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = ℓ ≫ t := Spec.map_preimage _
  refine ⟨A, ρ, ℓ, ?_, hfactor, hρ.symm⟩
  rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
  show Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint A) = _
  rw [hρ]
  show t (ℓ (IsLocalRing.closedPoint A)) = _
  rw [hcentre, htz]

/-- Decency passes to every base change of a morphism along a scheme-valued point of its
target: the projection to the source is representable. -/
private theorem isDecentSpace_pullback_yoneda
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hdecent : IsDecentSpace B S hS X) (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y) :
    IsDecentSpace B S hS (pullback g f) := by
  have hA := isAlgebraicSpace_yoneda B S hS T
  have hP := isAlgebraicSpace_pullback B S hS g f hA hX hY
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hgRep : yoneda.relativelyRepresentable g :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := Y)).mp
      hY.diagonal_representable g
  have hsndRep : yoneda.relativelyRepresentable (pullback.snd g f) :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (IsPullback.of_hasPullback g f) hgRep
  exact isDecentSpace_of_relativelyRepresentable B S hS hP (pullback.snd g f) hsndRep hdecent

/-- A universally closed morphism all of whose base changes along scheme-valued points of the
target are decent satisfies the existence part of the valuative criterion. -/
private theorem valuativeCriterion_existence_of_universallyClosed
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hdecent : ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
      IsDecentSpace B S hS (pullback g f))
    (huc : UniversallyClosed B S hS f) :
    ValuativeCriterion.Existence f := by
  classical
  intro q
  let T_A := siteObject B S hS q.ring_mem q.base
  have hA := isAlgebraicSpace_yoneda B S hS T_A
  let P := pullback q.special f
  have hP := isAlgebraicSpace_pullback B S hS q.special f hA hX hY
  let T_K := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  let qFrac : T_K ⟶ T_A := q.fracHom
  let pGenNat : yoneda.obj T_K ⟶ P :=
    pullback.lift (yoneda.map qFrac) q.generic q.comm.symm
  have hcomp : pGenNat ≫ pullback.fst q.special f = yoneda.map qFrac :=
    pullback.lift_fst _ _ _
  let pGen : FieldValuedPoint B S hS P :=
    { carrier := q.K
      contained := q.field_mem
      toBase := Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base
      value := pGenNat.app (Opposite.op T_K) (𝟙 T_K) }
  let xGen := pGen.class B S hS P
  let pEta : FieldValuedPoint B S hS (yoneda.obj T_A) :=
    { carrier := q.K
      contained := q.field_mem
      toBase := Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base
      value := yonedaEquiv (yoneda.map qFrac) }
  let ASpec : Scheme.{u} := Spec (.of q.R)
  have hEta : schemePoint B S hS T_A pEta = genericPoint ASpec := by
    show (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))
      (IsLocalRing.closedPoint q.K) = _
    exact spec_algebraMap_closedPoint_eq_genericPoint
  have hEtaSpec : ∀ x : ASpec, genericPoint ASpec ⤳ x := fun x ↦
    (genericPoint_spec _).specializes (Set.mem_univ x)
  have hgenMap : pointsMap B S hS P (pullback.fst q.special f) xGen =
      pEta.class B S hS (yoneda.obj T_A) := by
    rw [pointsMap_class]
    refine congrArg (FieldValuedPoint.class B S hS (yoneda.obj T_A)) ?_
    exact congrArg (fun value ↦
      ({ carrier := q.K, contained := q.field_mem,
         toBase := Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base,
         value := value } : FieldValuedPoint B S hS (yoneda.obj T_A)))
      (congrArg (fun k ↦ k.app (Opposite.op T_K) (𝟙 T_K)) hcomp)
  -- The closed point of `Spec R`, presented by its residue field.
  let cpoint : ASpec := IsLocalRing.closedPoint (CommRingCat.of q.R)
  let κ := ASpec.residueField cpoint
  have hκmem : B.Contains (Spec κ) := B.residueField_spec_contains q.ring_mem cpoint
  let cMap := ASpec.fromSpecResidueField cpoint
  let cObj := siteObject B S hS hκmem (cMap ≫ q.base)
  let cArrow : cObj ⟶ T_A := Over.homMk (ObjectProperty.homMk cMap)
  let pClosed : FieldValuedPoint B S hS (yoneda.obj T_A) :=
    { carrier := κ
      contained := hκmem
      toBase := cMap ≫ q.base
      value := yonedaEquiv (yoneda.map cArrow) }
  have hClosedPoint : schemePoint B S hS T_A pClosed = cpoint := by
    show cMap (IsLocalRing.closedPoint κ) = cpoint
    exact ASpec.fromSpecResidueField_apply cpoint _
  -- Universal closedness makes the image of the closure of the generic point closed.
  let W := pointsMap B S hS P (pullback.fst q.special f) '' closure ({xGen} : Set _)
  have hW : IsClosed W := huc (yoneda.obj T_A) hA q.special _ isClosed_closure
  have hpEta : pEta.class B S hS (yoneda.obj T_A) ∈ W :=
    ⟨xGen, subset_closure (by simp), hgenMap⟩
  have hWuniv : W = Set.univ :=
    eq_univ_of_isClosed_of_specializes T_A W hW _ hpEta fun t ↦ by
      rw [show pointsToScheme B S hS T_A (pEta.class B S hS (yoneda.obj T_A)) =
        genericPoint ASpec from hEta]
      exact hEtaSpec t
  obtain ⟨xSpecial, hxSpecial, hspecialMap⟩ :
      pClosed.class B S hS (yoneda.obj T_A) ∈ W := hWuniv.symm ▸ Set.mem_univ _
  have hspecializes : xGen ⤳ xSpecial := specializes_iff_mem_closure.2 hxSpecial
  -- Lift the specialization to an étale chart of the fibre product, by Stacks 03K2.
  obtain ⟨U, φ, hφsurj, hφet⟩ := hP.exists_atlas
  obtain ⟨p, hp⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS P hP U φ).1 hφsurj xSpecial
  have hfinite := hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS
    (hdecent T_A q.special) xGen
  obtain ⟨p', hp'p, hp'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hP
    hspecializes hfinite U φ hφet p hp
  -- Compare the two points of the chart through a common field of definition.
  obtain ⟨p, rfl⟩ := Quot.exists_rep p
  obtain ⟨p', rfl⟩ := Quot.exists_rep p'
  have heq : (FieldValuedPoint.map B S hS (yoneda.obj U) φ p').class B S hS P =
      pGen.class B S hS P := hp'
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (FieldValuedPoint.class_eq_class_iff B S hS P _ _).mp heq
  change r.siteObject B S hS P ⟶ p'.siteObject B S hS (yoneda.obj U) at a
  change r.siteObject B S hS P ⟶ T_K at b
  let v : r.siteObject B S hS P ⟶ U := a ≫ p'.value
  let V : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj U
  let g : Spec (.of r.carrier) ⟶ V := B.inclusion.map v.left
  let z : V := schemePoint B S hS U p
  have hgp' : g (IsLocalRing.closedPoint r.carrier) = schemePoint B S hS U p' := by
    show (B.inclusion.map p'.value.left)
      ((B.inclusion.map a.left) (IsLocalRing.closedPoint r.carrier)) = _
    rw [show (B.inclusion.map a.left) (IsLocalRing.closedPoint r.carrier) =
      IsLocalRing.closedPoint p'.carrier from
      Subsingleton.elim (α := PrimeSpectrum p'.carrier) _ _]
    rfl
  have hgz : g (IsLocalRing.closedPoint r.carrier) ⤳ z := by
    rw [hgp']
    exact hp'p.map (schemePointsHomeomorph B S hS U).continuous
  -- The chart lies over `Spec R`, and `z` lies over its closed point.
  let t : U ⟶ T_A := yoneda.preimage (φ ≫ pullback.fst q.special f)
  have ht : yoneda.map t = φ ≫ pullback.fst q.special f := yoneda.map_preimage _
  let tScheme : V ⟶ Spec (.of q.R) := B.inclusion.map t.left
  have htz : tScheme z = cpoint := by
    have hh : pointsMap B S hS (yoneda.obj U) (yoneda.map t)
        (p.class B S hS (yoneda.obj U)) = pClosed.class B S hS (yoneda.obj T_A) := by
      rw [ht, pointsMap_comp_apply, hp]
      exact hspecialMap
    have hh' := congrArg (pointsToScheme B S hS T_A) hh
    rw [pointsToScheme_pointsMap] at hh'
    exact hh'.trans hClosedPoint
  -- The two composites with the chart agree, read on site objects.
  have hv : yoneda.map v ≫ φ = yoneda.map b ≫ pGenNat := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    show φ.app _ (a ≫ p'.value) = pGenNat.app _ b
    have ha' : φ.app _ (a ≫ p'.value) = r.value :=
      (congrArg (fun k ↦ k p'.value) (φ.naturality a.op)).trans ha
    have hb' := congrArg (fun k ↦ k (𝟙 T_K)) (pGenNat.naturality b.op)
    change pGenNat.app _ (b ≫ 𝟙 T_K) = P.map b.op (pGenNat.app _ (𝟙 T_K)) at hb'
    rw [Category.comp_id] at hb'
    exact ha'.trans (hb'.trans hb).symm
  have hgt : g ≫ tScheme = B.inclusion.map b.left ≫
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := by
    have hh : v ≫ t = b ≫ qFrac := by
      apply yoneda.map_injective
      rw [Functor.map_comp, ht, ← Category.assoc, hv, Category.assoc]
      show yoneda.map b ≫ (pGenNat ≫ pullback.fst q.special f) = _
      rw [hcomp]
      exact (yoneda.map_comp b qFrac).symm
    exact congrArg (fun k ↦ B.inclusion.map (Over.Hom.left k)) hh
  -- The valuation subring dominating `R` inside the residue field of the lifted point.
  obtain ⟨A, ρ, ℓ, hρlocal, hℓ, hℓt⟩ :=
    exists_valuationSubring_lift_of_specializes tScheme g z hgz htz
  have hAmem : B.Contains (Spec (.of A)) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      A.toSubring r.contained
  let baseA := ℓ ≫ B.inclusion.map U.hom
  let AObj := siteObject B S hS hAmem baseA
  let KObj := siteObject B S hS r.contained
    (Spec.map (CommRingCat.ofHom (algebraMap A r.carrier)) ≫ baseA)
  let ℓOver : AObj ⟶ U := Over.homMk (ObjectProperty.homMk ℓ)
  have hbaseK : Spec.map (CommRingCat.ofHom (algebraMap A r.carrier)) ≫ baseA =
      r.toBase := by
    dsimp only [baseA]
    rw [← Category.assoc, hℓ]
    exact congrArg B.inclusion.map (Over.w v)
  let idK : KObj ⟶ r.siteObject B S hS P := Over.homMk
    (𝟙 (B.obj r.contained)) (by
      apply ObjectProperty.hom_ext
      exact (Category.id_comp _).trans hbaseK.symm)
  let frac : KObj ⟶ AObj := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap A r.carrier))))
  have hfrac : frac ≫ ℓOver = idK ≫ v := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show Spec.map (CommRingCat.ofHom (algebraMap A r.carrier)) ≫ ℓ = 𝟙 _ ≫ g
    simpa using hℓ
  let genericOver : KObj ⟶ T_K := idK ≫ b
  let specialOver : AObj ⟶ T_A := ℓOver ≫ t
  let fieldMap : q.K →+* r.carrier := (Spec.preimage (B.inclusion.map b.left)).hom
  have hfield : Spec.map (CommRingCat.ofHom fieldMap) = B.inclusion.map b.left :=
    Spec.map_preimage _
  have hring : B.inclusion.map specialOver.left = Spec.map (CommRingCat.ofHom ρ) := hℓt
  have hbaseA : baseA = Spec.map (CommRingCat.ofHom ρ) ≫ q.base := by
    rw [← hring]
    exact (congrArg B.inclusion.map (Over.w specialOver)).symm
  have hcompat : (algebraMap A r.carrier).comp ρ = fieldMap.comp (algebraMap q.R q.K) := by
    have he : CommRingCat.ofHom ((algebraMap A r.carrier).comp ρ) =
        CommRingCat.ofHom (fieldMap.comp (algebraMap q.R q.K)) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        ← hℓt, ← Category.assoc, hℓ, hfield]
      exact hgt
    exact congrArg CommRingCat.Hom.hom he
  -- The dominating extension, with its lift.
  let lift : yoneda.obj AObj ⟶ X := yoneda.map ℓOver ≫ φ ≫ pullback.snd q.special f
  have hgeneric : yoneda.map frac ≫ lift = yoneda.map genericOver ≫ q.generic := by
    calc
      yoneda.map frac ≫ lift =
          yoneda.map (frac ≫ ℓOver) ≫ φ ≫ pullback.snd q.special f := by
        simp only [lift, Functor.map_comp, Category.assoc]
      _ = yoneda.map idK ≫ (yoneda.map v ≫ φ) ≫ pullback.snd q.special f := by
        rw [hfrac]
        simp only [Functor.map_comp, Category.assoc]
      _ = yoneda.map idK ≫ (yoneda.map b ≫ pGenNat) ≫ pullback.snd q.special f := by
        rw [hv]
      _ = yoneda.map genericOver ≫ q.generic := by
        simp only [genericOver, Functor.map_comp, Category.assoc, pGenNat,
          pullback.lift_snd]
  have hspecial : lift ≫ f = yoneda.map specialOver ≫ q.special := by
    dsimp only [lift, specialOver]
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc φ, ← ht]
    simp only [Functor.map_comp, Category.assoc]
  let square : ValuativeSquare f :=
    { R := A, K := r.carrier, ring_mem := hAmem, field_mem := r.contained
      base := baseA
      generic := yoneda.map genericOver ≫ q.generic
      special := yoneda.map specialOver ≫ q.special
      comm := by
        show (yoneda.map genericOver ≫ q.generic) ≫ f =
          yoneda.map frac ≫ (yoneda.map specialOver ≫ q.special)
        rw [← hgeneric, Category.assoc, hspecial] }
  exact ⟨{ square := square, ringMap := ρ, fieldMap := fieldMap
           isLocalHom := hρlocal, fraction_comm := hcompat, base_comm := hbaseA
           genericOver := genericOver
           genericOver_left := by
             show 𝟙 _ ≫ B.inclusion.map b.left = Spec.map (CommRingCat.ofHom fieldMap)
             rw [Category.id_comp, hfield]
           specialOver := specialOver, specialOver_left := hring
           generic_comm := rfl, special_comm := rfl },
    ⟨⟨lift, hgeneric, hspecial⟩⟩⟩

/-- **Stacks 03KJ.** A quasi-compact morphism of algebraic spaces over `S` whose source is a
decent algebraic space is universally closed exactly when it satisfies the existence part of
the valuative criterion. -/
@[stacks 03KJ]
theorem universallyClosed_iff_valuativeCriterion_existence
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (hdecent : IsDecentSpace B S hS X) :
    UniversallyClosed B S hS f ↔ ValuativeCriterion.Existence f :=
  ⟨valuativeCriterion_existence_of_universallyClosed B S hS hX hY f
      (isDecentSpace_pullback_yoneda B S hS hX hY f hdecent),
    universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence hX hY f hf⟩

/-- **Stacks 03M6.** A quasi-compact morphism of algebraic spaces over `S` which is decent as a
morphism is universally closed exactly when it satisfies the existence part of the valuative
criterion.

A valuative square for `f` has its bottom edge `Spec R ⟶ Y`, so it is a valuative square for
the base change `X ×_Y Spec R ⟶ Spec R`, which is quasi-compact and has decent source; that
base change is universally closed, hence satisfies the existence part by Stacks 03KJ, and a
dominating extension solving the square there solves the original one after composing the lift
with the projection to `X`. -/
@[stacks 03M6]
theorem universallyClosed_iff_valuativeCriterion_existence_of_isDecent
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (hdecent : IsDecent B S hS f) :
    UniversallyClosed B S hS f ↔ ValuativeCriterion.Existence f := by
  refine ⟨fun hclosed q ↦ ?_,
    universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence hX hY f hf⟩
  let T := siteObject B S hS q.ring_mem q.base
  let g : yoneda.obj T ⟶ Y := q.special
  have hT := isAlgebraicSpace_yoneda B S hS T
  let p := pullback.fst g f
  have hpval : ValuativeCriterion.Existence p :=
    (universallyClosed_iff_valuativeCriterion_existence B S hS
      (isAlgebraicSpace_pullback B S hS g f hT hX hY) hT p
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hf)
      (hdecent T g)).mp (universallyClosed_pullback B S hS f g hclosed)
  let qP : ValuativeSquare p :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
      generic := pullback.lift (yoneda.map q.fracHom) q.generic q.comm.symm
      special := 𝟙 (yoneda.obj T)
      comm := (pullback.lift_fst _ _ _).trans (Category.comp_id _).symm }
  obtain ⟨e, ⟨l⟩⟩ := hpval qP
  let q' : ValuativeSquare f :=
    { R := e.square.R, K := e.square.K, ring_mem := e.square.ring_mem
      field_mem := e.square.field_mem, base := e.square.base
      generic := yoneda.map e.genericOver ≫ q.generic
      special := yoneda.map e.specialOver ≫ q.special
      comm := by rw [Category.assoc, q.comm, ← Category.assoc, e.yonedaMap_genericOver_comp_fracHom,
        Category.assoc] }
  let e' : q.DominatingExtension :=
    { square := q', ringMap := e.ringMap, fieldMap := e.fieldMap
      isLocalHom := e.isLocalHom, fraction_comm := e.fraction_comm, base_comm := e.base_comm
      genericOver := e.genericOver, genericOver_left := e.genericOver_left
      specialOver := e.specialOver, specialOver_left := e.specialOver_left
      generic_comm := rfl, special_comm := rfl }
  refine ⟨e', ⟨{ map := l.map ≫ pullback.snd g f, generic_comm := ?_, special_comm := ?_ }⟩⟩
  · show yoneda.map e.square.fracHom ≫ l.map ≫ pullback.snd g f =
      yoneda.map e.genericOver ≫ q.generic
    rw [← Category.assoc, l.generic_comm, e.generic_comm, Category.assoc, pullback.lift_snd]
  · calc
      l.map ≫ pullback.snd g f ≫ f = l.map ≫ p ≫ g := by rw [← pullback.condition]
      _ = e.square.special ≫ g := by rw [← Category.assoc, l.special_comm]
      _ = yoneda.map e.specialOver ≫ q.special := by
        rw [e.special_comm]
        show (yoneda.map e.specialOver ≫ 𝟙 (yoneda.obj T)) ≫ q.special = _
        rw [Category.comp_id]

end AlgebraicGeometry.Space

end
