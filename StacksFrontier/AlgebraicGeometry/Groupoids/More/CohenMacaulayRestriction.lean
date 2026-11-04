module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibrewiseDenseRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport

/-!
# The Cohen–Macaulay locus of a flat groupoid

For a groupoid scheme with flat, locally finitely presented source and target maps there is an
open `W` of the object scheme whose inverse image under the target is the maximal
Cohen–Macaulay locus of the source map, and — by applying the inverse morphism of the groupoid,
which swaps source and target — whose inverse image under the source is the maximal
Cohen–Macaulay locus of the target map.  Both inverse images still map onto the object scheme,
because the Cohen–Macaulay locus of a flat, locally finitely presented morphism is dense in
every fibre and is contained in `W`.  Restricting the groupoid to `W` therefore gives a
groupoid whose source and target maps are Cohen–Macaulay and locally of finite presentation.

## Main definitions

* `AlgebraicGeometry.cohenMacaulayOpen` chooses the open of objects on which the groupoid
  becomes Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.exists_open_source_cohenMacaulay_locus` and
  `AlgebraicGeometry.target_cohenMacaulay_locus` identify the maximal loci.
* `AlgebraicGeometry.target_from_source_surjective` and
  `AlgebraicGeometry.source_from_target_surjective` give surjectivity.
* `AlgebraicGeometry.restricted_source_cohenMacaulay`,
  `AlgebraicGeometry.restricted_target_cohenMacaulay`,
  `AlgebraicGeometry.restricted_source_locallyOfFinitePresentation` and
  `AlgebraicGeometry.restricted_target_locallyOfFinitePresentation` give Cohen–Macaulayness and
  local finite presentation for the two maps of the restricted groupoid.
* `AlgebraicGeometry.cohenMacaulay_sourceIso_iff` and
  `AlgebraicGeometry.cohenMacaulay_targetIso_iff` say that Cohen–Macaulayness with locally
  Noetherian fibres is unchanged by composing with an isomorphism on either side.

## Implementation notes

The locally Noetherian fibre witness required by
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` is existentially quantified in the maximal-locus
predicate and in the restriction assertions.  This adds no hypothesis to the source lemma.  The
restricted groupoid itself is the canonical `AlgebraicGeometry.GroupoidScheme.restrict`.  The
first two results express parts (1) and (2), the surjectivity results parts (3) and (4), and
the final four results part (5).

## References

* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The fibre product of a morphism with the identity is the source of the morphism. -/
private noncomputable def identityTargetPullbackIso {U R : Scheme.{u}}
    (t : R ⟶ U) : pullback (𝟙 U) t ≅ R :=
  asIso (pullback.snd (𝟙 U) t)

/-- `identityTargetPullbackIso` carries the morphism to the first projection. -/
private theorem identityTargetPullbackIso_hom_fst {U R : Scheme.{u}}
    (t : R ⟶ U) :
    (identityTargetPullbackIso t).hom ≫ t = pullback.fst (𝟙 U) t := by
  simp [identityTargetPullbackIso, ← pullback.condition]

/-- Associativity of the two fibre products occurring in a restriction. -/
private noncomputable def sourcePullbackAssocIso {C : Type*} [Category C]
    {T R W U : C}
    (t : T ⟶ R) (s : R ⟶ U) (g : W ⟶ U)
    [HasPullback s g] [HasPullback t (pullback.fst s g)]
    [HasPullback (t ≫ s) g] :
    pullback t (pullback.fst s g) ≅ pullback (t ≫ s) g :=
  pullbackRightPullbackFstIso s g t

/-- The second projection through `sourcePullbackAssocIso`. -/
private theorem sourcePullbackAssocIso_hom_snd {C : Type*} [Category C]
    {T R W U : C} (t : T ⟶ R) (s : R ⟶ U) (g : W ⟶ U)
    [HasPullback s g] [HasPullback t (pullback.fst s g)]
    [HasPullback (t ≫ s) g] :
    (sourcePullbackAssocIso t s g).hom ≫ pullback.snd (t ≫ s) g =
      pullback.snd t (pullback.fst s g) ≫ pullback.snd s g :=
  pullbackRightPullbackFstIso_hom_snd s g t

/-- The fibre product of an open immersion with a morphism is the inverse image open. -/
private noncomputable def targetOpenPullbackIso {X Y : Scheme.{u}}
    (W : Y.Opens) (f : X ⟶ Y) :
    pullback W.ι f ≅ f ⁻¹ᵁ W := by
  let V := f ⁻¹ᵁ W
  exact IsOpenImmersion.isoOfRangeEq (pullback.snd W.ι f) V.ι (by
    simp [V, IsOpenImmersion.range_pullbackSnd])

/-- `fiberIsoOfSourceIso` sends the canonical point of the fibre of a precomposition with an
isomorphism to the canonical point of the fibre. -/
private theorem fiberIsoOfSourceIso_asFiber {X Y S : Scheme.{u}}
    (e : X ≅ Y) (f : Y ⟶ S) (x : X) :
    (fiberIsoOfEq (e.hom ≫ f) (Scheme.Hom.comp_apply e.hom f x) ≪≫
      fiberIsoOfSourceIso (f := f) e rfl (f (e.hom x))).hom ((e.hom ≫ f).asFiber x) =
        f.asFiber (e.hom x) := by
  have hmap : (fiberIsoOfSourceIso (f := f) e rfl (f (e.hom x))).hom ≫
      f.fiberι (f (e.hom x)) =
      (e.hom ≫ f).fiberι (f (e.hom x)) ≫ e.hom := by
    show (asIso (pullback.map (e.hom ≫ f) (S.fromSpecResidueField (f (e.hom x))) f
      (S.fromSpecResidueField (f (e.hom x))) e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))).hom ≫
        pullback.fst f (S.fromSpecResidueField (f (e.hom x))) =
          pullback.fst (e.hom ≫ f) (S.fromSpecResidueField (f (e.hom x))) ≫ e.hom
    rw [asIso_hom, pullback.map, pullback.lift_fst]
  have hpoint := Scheme.Hom.comp_apply e.hom f x
  let c := fiberIsoOfEq (e.hom ≫ f) hpoint ≪≫
    fiberIsoOfSourceIso (f := f) e rfl (f (e.hom x))
  have hmapc : c.hom ≫ f.fiberι (f (e.hom x)) =
      (e.hom ≫ f).fiberι ((e.hom ≫ f) x) ≫ e.hom := by
    dsimp [c]
    calc
      ((fiberIsoOfEq (e.hom ≫ f) hpoint).hom ≫
          (fiberIsoOfSourceIso (f := f) e rfl (f (e.hom x))).hom) ≫
          f.fiberι (f (e.hom x)) =
          (fiberIsoOfEq (e.hom ≫ f) hpoint).hom ≫
            ((fiberIsoOfSourceIso (f := f) e rfl (f (e.hom x))).hom ≫
              f.fiberι (f (e.hom x))) := by simp [Category.assoc]
      _ = _ := by
        cases hpoint
        exact hmap
  apply (f.fiberι (f (e.hom x))).isEmbedding.injective
  calc
    f.fiberι (f (e.hom x)) (c.hom ((e.hom ≫ f).asFiber x)) =
        (c.hom ≫ f.fiberι (f (e.hom x))) ((e.hom ≫ f).asFiber x) := rfl
    _ = ((e.hom ≫ f).fiberι ((e.hom ≫ f) x) ≫ e.hom)
        ((e.hom ≫ f).asFiber x) := by rw [hmapc]
    _ = e.hom x := by
      show e.hom ((e.hom ≫ f).fiberι ((e.hom ≫ f) x) ((e.hom ≫ f).asFiber x)) = _
      rw [Scheme.Hom.fiberι_asFiber]
    _ = f.fiberι (f (e.hom x)) (f.asFiber (e.hom x)) := by simp

/-- Cohen–Macaulayness of the local ring at a point is invariant under an open-immersion
isomorphism. -/
private theorem isCohenMacaulayLocalRing_stalk_iff_of_iso {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (j : X ≅ Y) (z : X) (w : Y) (hj : j.hom z = w) :
    IsCohenMacaulayLocalRing (X.presheaf.stalk z) ↔
      IsCohenMacaulayLocalRing (Y.presheaf.stalk w) := by
  subst hj
  have : IsIso (j.hom.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion j.hom)).2 z
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
    (asIso (j.hom.stalkMap z)).commRingCatIsoToRingEquiv).symm

/-- Cohen–Macaulayness at a point is invariant under an isomorphism of the source. -/
private theorem isCohenMacaulayAt_sourceIso_iff {X Y S : Scheme.{u}}
    (e : X ≅ Y) (f : Y ⟶ S)
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y))
    (he : ∀ y : S, IsLocallyNoetherian ((e.hom ≫ f).fiber y)) (x : X) :
    Scheme.Hom.IsCohenMacaulayAt (e.hom ≫ f) he x ↔
      Scheme.Hom.IsCohenMacaulayAt f hf (e.hom x) := by
  have hy : (e.hom ≫ f) x = f (e.hom x) := Scheme.Hom.comp_apply e.hom f x
  let j := fiberIsoOfEq (e.hom ≫ f) hy ≪≫ fiberIsoOfSourceIso (f := f) e rfl (f (e.hom x))
  have : IsLocallyNoetherian ((e.hom ≫ f).fiber ((e.hom ≫ f) x)) := he _
  have : IsLocallyNoetherian (f.fiber (f (e.hom x))) := hf _
  refine and_congr ?_ (isCohenMacaulayLocalRing_stalk_iff_of_iso j _ _
    (fiberIsoOfSourceIso_asFiber e f x))
  change RingHom.Flat ((e.hom ≫ f).stalkMap x).hom ↔ RingHom.Flat (f.stalkMap (e.hom x)).hom
  rw [Stacks.ModuleSkyscraper.stalkMap_hom_comp]
  exact RingHom.Flat.comp_iff_of_bijective_left
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap x))

/-- Being a Cohen–Macaulay morphism is invariant under an isomorphism of the source. -/
public theorem cohenMacaulay_sourceIso_iff {X Y S : Scheme.{u}}
    (e : X ≅ Y) (f : Y ⟶ S) :
    (∃ hf : ∀ y : S, IsLocallyNoetherian ((e.hom ≫ f).fiber y),
      Scheme.Hom.IsCohenMacaulay (e.hom ≫ f) hf) ↔
    (∃ hf : ∀ y : S, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulay f hf) := by
  constructor
  · rintro ⟨he, hCM⟩
    let hf : ∀ y : S, IsLocallyNoetherian (f.fiber y) := fun y =>
      have := he y
      isLocallyNoetherian_of_isOpenImmersion (fiberIsoOfSourceIso (f := f) e rfl y).inv
    exact ⟨hf, fun x => by
      simpa using (isCohenMacaulayAt_sourceIso_iff e f hf he (e.inv x)).mp (hCM (e.inv x))⟩
  · rintro ⟨hf, hCM⟩
    let he : ∀ y : S, IsLocallyNoetherian ((e.hom ≫ f).fiber y) := fun y =>
      have := hf y
      isLocallyNoetherian_of_isOpenImmersion (fiberIsoOfSourceIso (f := f) e rfl y).hom
    exact ⟨he, fun x => (isCohenMacaulayAt_sourceIso_iff e f hf he x).mpr (hCM (e.hom x))⟩

/-- Postcomposing with an isomorphism identifies the fibres over corresponding points. -/
private noncomputable def fiberIsoOfTargetIsoOfEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Z) (z : Z) (y : Y) (hz : e.inv z = y) :
    (f ≫ e.hom).fiber z ≅ f.fiber y := by
  let k₀ := Spec.map (e.inv.residueFieldMap z)
  let k₁ := Spec.map (Y.residueFieldCongr hz.symm).hom
  let k : Spec (Z.residueField z) ⟶ Spec (Y.residueField y) := k₀ ≫ k₁
  let F := pullback.map (f ≫ e.hom) (Z.fromSpecResidueField z)
      f (Y.fromSpecResidueField y) (𝟙 X) k e.inv (by simp [Category.assoc]) (by
        calc
          Z.fromSpecResidueField z ≫ e.inv =
              k₀ ≫ Y.fromSpecResidueField (e.inv z) :=
            (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField e.inv z).symm
          _ = k₀ ≫ (k₁ ≫ Y.fromSpecResidueField y) := by
            rw [Scheme.residueFieldCongr_fromSpecResidueField hz.symm]
          _ = k ≫ Y.fromSpecResidueField y := by
            simp [k, Category.assoc])
  have : IsIso e.inv := e.isIso_inv
  have : IsIso (e.inv.residueFieldMap z) := by infer_instance
  have : IsIso k₀ := by dsimp [k₀]; infer_instance
  have : IsIso k₁ := by dsimp [k₁]; infer_instance
  have : IsIso k := by dsimp [k]; infer_instance
  have : IsIso F := by dsimp only [F]; exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact @asIso Scheme _ _ _ F ‹IsIso F›

/-- Postcomposing with an isomorphism does not change the fibre through a given point. -/
private noncomputable def fiberIsoOfTargetIsoAt {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Z) (x : X) :
    (f ≫ e.hom).fiber ((f ≫ e.hom) x) ≅ f.fiber (f x) :=
  fiberIsoOfTargetIsoOfEq f e _ _ (by simp)

/-- The first component of `fiberIsoOfTargetIsoAt`. -/
private theorem fiberIsoOfTargetIsoAt_fiberι {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Z) (x : X) :
    (fiberIsoOfTargetIsoAt f e x).hom ≫ f.fiberι (f x) =
      (f ≫ e.hom).fiberι ((f ≫ e.hom) x) ≫ 𝟙 X :=
  pullback.lift_fst _ _ _

/-- `fiberIsoOfTargetIsoAt` preserves the canonical point of the fibre. -/
private theorem fiberIsoOfTargetIsoAt_asFiber {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Z) (x : X) :
    (fiberIsoOfTargetIsoAt f e x).hom ((f ≫ e.hom).asFiber x) = f.asFiber x := by
  apply (f.fiberι (f x)).isEmbedding.injective
  calc
    f.fiberι (f x) ((fiberIsoOfTargetIsoAt f e x).hom ((f ≫ e.hom).asFiber x)) =
        ((fiberIsoOfTargetIsoAt f e x).hom ≫ f.fiberι (f x))
          ((f ≫ e.hom).asFiber x) := rfl
    _ = ((f ≫ e.hom).fiberι ((f ≫ e.hom) x) ≫ 𝟙 X)
        ((f ≫ e.hom).asFiber x) := by rw [fiberIsoOfTargetIsoAt_fiberι]
    _ = x := by simpa using Scheme.Hom.fiberι_asFiber (f ≫ e.hom) x
    _ = f.fiberι (f x) (f.asFiber x) := (Scheme.Hom.fiberι_asFiber f x).symm

/-- Cohen–Macaulayness at a point is invariant under an isomorphism of the target. -/
private theorem isCohenMacaulayAt_targetIso_iff {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Z)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (he : ∀ z : Z, IsLocallyNoetherian ((f ≫ e.hom).fiber z)) (x : X) :
    Scheme.Hom.IsCohenMacaulayAt (f ≫ e.hom) he x ↔
      Scheme.Hom.IsCohenMacaulayAt f hf x := by
  let j := fiberIsoOfTargetIsoAt f e x
  have : IsLocallyNoetherian ((f ≫ e.hom).fiber ((f ≫ e.hom) x)) := he _
  have : IsLocallyNoetherian (f.fiber (f x)) := hf _
  refine and_congr ?_ (isCohenMacaulayLocalRing_stalk_iff_of_iso j _ _
    (fiberIsoOfTargetIsoAt_asFiber f e x))
  change RingHom.Flat ((f ≫ e.hom).stalkMap x).hom ↔ RingHom.Flat (f.stalkMap x).hom
  rw [Stacks.ModuleSkyscraper.stalkMap_hom_comp]
  exact RingHom.Flat.comp_iff_of_bijective_right
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap (f x)))

/-- Being a Cohen–Macaulay morphism is invariant under an isomorphism of the target. -/
public theorem cohenMacaulay_targetIso_iff {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (e : Y ≅ Z) :
    (∃ he : ∀ z : Z, IsLocallyNoetherian ((f ≫ e.hom).fiber z),
      Scheme.Hom.IsCohenMacaulay (f ≫ e.hom) he) ↔
    (∃ hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulay f hf) := by
  constructor
  · rintro ⟨he, hcm⟩
    let hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y) := fun y =>
      have := he (e.hom y)
      isLocallyNoetherian_of_isOpenImmersion (fiberIsoOfTargetIsoOfEq f e (e.hom y) y (by simp)).inv
    exact ⟨hf, fun x => (isCohenMacaulayAt_targetIso_iff f e hf he x).mp (hcm x)⟩
  · rintro ⟨hf, hcm⟩
    let he : ∀ z : Z, IsLocallyNoetherian ((f ≫ e.hom).fiber z) := fun z =>
      have := hf (e.inv z)
      isLocallyNoetherian_of_isOpenImmersion
        (fiberIsoOfTargetIsoOfEq f e z (e.inv z) rfl).hom
    exact ⟨he, fun x => (isCohenMacaulayAt_targetIso_iff f e hf he x).mpr (hcm x)⟩

/-- An isomorphism of schemes identifies the inverse image of an open with that open. -/
private noncomputable def sourceIsoRestrict {X Y : Scheme.{u}}
    (e : X ≅ Y) (V : Y.Opens) : (e.hom ⁻¹ᵁ V : Scheme) ≅ (V : Scheme) := by
  let V' : X.Opens := e.hom ⁻¹ᵁ V
  let k : ↑V' ⟶ Y := V'.ι ≫ e.hom
  have hrange : k.opensRange = V := by
    apply TopologicalSpace.Opens.ext
    ext y
    change (∃ x : ↑V', e.hom (V'.ι x) = y) ↔ y ∈ V
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hy
      refine ⟨⟨e.inv y, ?_⟩, ?_⟩
      · change e.hom (e.inv y) ∈ V
        simpa using hy
      · simp
  exact k.isoOpensRange ≪≫ Y.isoOfEq hrange

/-- Being a Cohen–Macaulay locus is invariant under an isomorphism of the source. -/
private theorem cohenMacaulay_restrict_sourceIso_iff {X Y S : Scheme.{u}}
    (e : X ≅ Y) (f : Y ⟶ S) (V : Y.Opens) :
    (∃ hf : ∀ y : S, IsLocallyNoetherian
        (((e.hom ⁻¹ᵁ V).ι ≫ e.hom ≫ f).fiber y),
      Scheme.Hom.IsCohenMacaulay ((e.hom ⁻¹ᵁ V).ι ≫ e.hom ≫ f) hf) ↔
    (∃ hf : ∀ y : S, IsLocallyNoetherian ((V.ι ≫ f).fiber y),
      Scheme.Hom.IsCohenMacaulay (V.ι ≫ f) hf) := by
  let V' : X.Opens := e.hom ⁻¹ᵁ V
  let eV := sourceIsoRestrict e V
  have heq : eV.hom ≫ (V.ι ≫ f) = V'.ι ≫ e.hom ≫ f := by
    dsimp [eV, sourceIsoRestrict, V']
    simp [Category.assoc]
  rw [← heq]
  exact cohenMacaulay_sourceIso_iff eV (V.ι ≫ f)

/-- There is an open of objects whose inverse image under the target is the
greatest open on which the source map is Cohen–Macaulay. -/
@[stacks 0460 "part (1)"]
public theorem exists_open_source_cohenMacaulay_locus {S : Scheme.{u}}
    (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    ∃ W : G.objects.left.Opens,
      IsGreatest
        {V : G.arrows.left.Opens |
          ∃ hf : ∀ y : G.objects.left,
            IsLocallyNoetherian ((V.ι ≫ G.source.left).fiber y),
            Scheme.Hom.IsCohenMacaulay (V.ι ≫ G.source.left) hf}
        (G.target.left ⁻¹ᵁ W) := by
  let D : FlatLocallyFinitelyPresentedGroupoidSituation := {
    S := S
    groupoid := G
    U' := G.objects.left
    g := 𝟙 _
  }
  obtain ⟨W, hW⟩ := exists_open_with_preimage_maximal_cohenMacaulayLocus D
  let e := identityTargetPullbackIso G.target.left
  let V := G.target.left ⁻¹ᵁ W
  let V' := e.hom ⁻¹ᵁ V
  let Umax := (pullback.fst (𝟙 G.objects.left) G.target.left) ⁻¹ᵁ W
  have hbase : e.hom ≫ G.target.left = pullback.fst (𝟙 G.objects.left) G.target.left :=
    identityTargetPullbackIso_hom_fst G.target.left
  have hD : D.h = e.hom ≫ G.source.left := rfl
  have hmax : V' = Umax := by
    apply TopologicalSpace.Opens.ext
    ext x
    simp [V', Umax, V, ← hbase]
  have hDmax : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian ((Umax.ι ≫ D.h).fiber y),
      Scheme.Hom.IsCohenMacaulay (Umax.ι ≫ D.h) hf := hW.1
  rw [← hmax, hD] at hDmax
  refine ⟨W, (cohenMacaulay_restrict_sourceIso_iff e G.source.left V).mp
    (by simpa [Category.assoc] using hDmax), ?_⟩
  rintro V₀ ⟨hf₀, hcm₀⟩
  obtain ⟨hf, hcm⟩ := (cohenMacaulay_restrict_sourceIso_iff e G.source.left V₀).mpr ⟨hf₀, hcm₀⟩
  have hpre' : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (((e.hom ⁻¹ᵁ V₀).ι ≫ D.h).fiber y),
      Scheme.Hom.IsCohenMacaulay ((e.hom ⁻¹ᵁ V₀).ι ≫ D.h) hf :=
    ⟨hf, by simpa [hD, Category.assoc] using hcm⟩
  have hle : e.hom ⁻¹ᵁ V₀ ≤ Umax := hW.2 hpre'
  intro x hx
  have hxmax : e.inv x ∈ Umax := hle (by simpa using hx)
  simpa [Umax, V, ← hbase] using hxmax

/-- The open of objects whose target inverse image is the maximal
Cohen–Macaulay locus of the source map. -/
public noncomputable def cohenMacaulayOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] : G.objects.left.Opens :=
  Classical.choose (exists_open_source_cohenMacaulay_locus G)

/-- The inverse image of the object open under the source is the greatest
open on which the target map is Cohen–Macaulay. -/
@[stacks 0460 "part (2)"]
public theorem target_cohenMacaulay_locus {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    IsGreatest
      {V : G.arrows.left.Opens |
        ∃ hf : ∀ y : G.objects.left,
          IsLocallyNoetherian ((V.ι ≫ G.target.left).fiber y),
          Scheme.Hom.IsCohenMacaulay (V.ι ≫ G.target.left) hf}
      (G.source.left ⁻¹ᵁ cohenMacaulayOpen G) := by
  have : IsIso G.inverse.left := groupoidInverse_left_isIso G
  let e : G.arrows.left ≅ G.arrows.left := asIso G.inverse.left
  let W := Classical.choose (exists_open_source_cohenMacaulay_locus G)
  let Vmax := G.target.left ⁻¹ᵁ W
  let Umax := G.source.left ⁻¹ᵁ W
  have hsource : IsGreatest
      {V : G.arrows.left.Opens | ∃ hf : ∀ y : G.objects.left,
          IsLocallyNoetherian ((V.ι ≫ G.source.left).fiber y),
          Scheme.Hom.IsCohenMacaulay (V.ι ≫ G.source.left) hf} Vmax := by
    simpa [Vmax] using Classical.choose_spec (exists_open_source_cohenMacaulay_locus G)
  have hsymm : e.hom ≫ G.target.left = G.source.left :=
    congrArg Over.Hom.left G.target_inverse
  have hforward : e.hom ≫ G.source.left = G.target.left :=
    congrArg Over.Hom.left G.source_inverse
  have htransferMax := cohenMacaulay_restrict_sourceIso_iff e G.source.left Vmax
  have hmaxMem : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian ((Umax.ι ≫ G.target.left).fiber y),
      Scheme.Hom.IsCohenMacaulay (Umax.ι ≫ G.target.left) hf := by
    have heq : e.hom ⁻¹ᵁ Vmax = Umax := by
      apply TopologicalSpace.Opens.ext
      ext x
      simp [Vmax, Umax, ← hsymm]
    have ht := htransferMax.mpr hsource.1
    have hmap : Umax.ι ≫ G.target.left = Umax.ι ≫ e.hom ≫ G.source.left := by
      simp [hforward]
    rw [hmap]
    rwa [heq] at ht
  refine ⟨hmaxMem, ?_⟩
  rintro V ⟨hf, hcm⟩
  let V0 := e.hom ''ᵁ V
  let eV := Scheme.Hom.isoImage e.hom V
  let f0 := V0.ι ≫ G.source.left
  have hmap : eV.hom ≫ f0 = V.ι ≫ G.target.left := by
    dsimp [eV, f0, V0]
    rw [Scheme.Hom.isoImage_hom_ι_assoc e.hom V G.source.left, hforward]
  have htargetPre : ∃ hf' : ∀ y : G.objects.left,
      IsLocallyNoetherian ((eV.hom ≫ f0).fiber y),
      Scheme.Hom.IsCohenMacaulay (eV.hom ≫ f0) hf' := by
    refine ⟨fun y => by simpa only [hmap] using hf y, ?_⟩
    simpa only [hmap] using hcm
  have hle : V0 ≤ Vmax := hsource.2 ((cohenMacaulay_sourceIso_iff eV f0).mp htargetPre)
  intro x hx
  have hx0 : e.hom x ∈ V0 := by simpa [V0]
  have htarget : G.target.left (e.hom x) ∈ W := hle hx0
  have hpoint : G.target.left (e.hom x) = G.source.left x :=
    congrArg (fun k : G.arrows.left ⟶ G.objects.left => k x) hsymm
  have hsrc : G.source.left x ∈ W := by simpa [hpoint] using htarget
  simpa [Umax, W, cohenMacaulayOpen] using hsrc

/-- A flat, locally finitely presented morphism with a section stays surjective on any open
containing its Cohen–Macaulay locus. -/
private theorem surjective_restrict_of_cohenMacaulay_locus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (W : X.Opens)
    (hmax : IsGreatest
      {V : X.Opens | ∃ hf : ∀ y : Y, IsLocallyNoetherian ((V.ι ≫ f).fiber y),
        Scheme.Hom.IsCohenMacaulay (V.ι ≫ f) hf} W) :
    Surjective (W.ι ≫ f) := by
  classical
  let hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y
  have hopen : IsOpen {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} :=
    isOpen_setOf_isCohenMacaulayAt f
  let L : X.Opens := ⟨_, hopen⟩
  let hfL : ∀ y : Y, IsLocallyNoetherian ((L.ι ≫ f).fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (L.ι ≫ f) y
  have hcmL : Scheme.Hom.IsCohenMacaulay (L.ι ≫ f) hfL :=
    fun x => cohenMacaulayAt_of_openImmersion_source L.ι f hf hfL x x.property
  have hle : L ≤ W := hmax.2 ⟨hfL, hcmL⟩
  have hDense := dense_cohenMacaulayAt_fiber f
  refine ⟨?_⟩
  intro y
  have hid : f (s y) = y := by simpa using congrArg (fun k => k y) hs
  have : Nonempty (f.fiber y) := ⟨(fiberIsoOfEq f hid).hom (f.asFiber (s y))⟩
  obtain ⟨z, hz⟩ := (hDense y).nonempty
  let x := f.fiberι y z
  have hxCM : Scheme.Hom.IsCohenMacaulayAt f hf x := by simpa [x] using hz
  have hxy : f x = y := by
    have hxpre : x ∈ f ⁻¹' {y} := by
      rw [← f.range_fiberι y]
      exact ⟨z, rfl⟩
    simpa using hxpre
  exact ⟨⟨x, hle hxCM⟩, hxy⟩

/-- The target remains surjective on the inverse image of the open under the source. -/
@[stacks 0460 "part (3)"]
public theorem target_from_source_surjective {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    Surjective ((G.source.left ⁻¹ᵁ cohenMacaulayOpen G).ι ≫ G.target.left) :=
  surjective_restrict_of_cohenMacaulay_locus G.target.left G.identity.left
    (congrArg Over.Hom.left G.target_identity) _ (target_cohenMacaulay_locus G)

/-- The source remains surjective on the inverse image of the open under the target. -/
@[stacks 0460 "part (4)"]
public theorem source_from_target_surjective {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    Surjective ((G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι ≫ G.source.left) :=
  surjective_restrict_of_cohenMacaulay_locus G.source.left G.identity.left
    (congrArg Over.Hom.left G.source_identity) _ (by
      simpa [cohenMacaulayOpen] using
        Classical.choose_spec (exists_open_source_cohenMacaulay_locus G))

/-- The source map of the canonical arrow scheme of a restriction to an open is Cohen–Macaulay
as soon as the source map is Cohen–Macaulay on the target preimage of that open. -/
private theorem restrictionSource_cohenMacaulay_of_targetPreimage {S : Scheme.{u}}
    (G : GroupoidScheme S) (W : G.objects.left.Opens)
    (hV : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (((G.target.left ⁻¹ᵁ W).ι ≫ G.source.left).fiber y),
      Scheme.Hom.IsCohenMacaulay ((G.target.left ⁻¹ᵁ W).ι ≫ G.source.left) hf) :
    ∃ hf : ∀ y : W, IsLocallyNoetherian
      ((restrictionSource G
        (Over.homMk (U := Over.mk (W.ι ≫ G.objects.hom)) (V := G.objects)
          W.ι (by rfl))).left.fiber y),
      Scheme.Hom.IsCohenMacaulay
        (restrictionSource G
          (Over.homMk (U := Over.mk (W.ι ≫ G.objects.hom)) (V := G.objects)
            W.ι (by rfl))).left hf := by
  classical
  let V : G.arrows.left.Opens := G.target.left ⁻¹ᵁ W
  let g : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects :=
    Over.homMk (U := Over.mk (W.ι ≫ G.objects.hom)) (V := G.objects) W.ι (by rfl)
  let A := pullback g G.target
  let t := pullback.snd g G.target
  let fV := V.ι ≫ G.source.left
  let eAcomp : A.left ≅ pullback W.ι G.target.left :=
    PreservesPullback.iso (Over.forget S) g G.target
  let eAopen := targetOpenPullbackIso W G.target.left
  let eA : A.left ≅ V := eAcomp ≪≫ eAopen
  have heAopen : eAopen.hom ≫ V.ι = pullback.snd W.ι G.target.left := by
    dsimp [eAopen, targetOpenPullbackIso, V]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have heA : eA.hom ≫ V.ι = t.left := by
    show eAcomp.hom ≫ (eAopen.hom ≫ V.ι) = (pullback.snd g G.target).left
    calc
      _ = eAcomp.hom ≫ pullback.snd W.ι G.target.left := by rw [heAopen]
      _ = (Over.forget S).map (pullback.snd g G.target) :=
        PreservesPullback.iso_hom_snd (Over.forget S) g G.target
      _ = (pullback.snd g G.target).left := rfl
  let fOver := t ≫ G.source
  let fA := fOver.left
  rcases hV with ⟨hfV, hcmV⟩
  obtain ⟨hfA', hcmA'⟩ := (cohenMacaulay_sourceIso_iff eA fV).mpr ⟨hfV, hcmV⟩
  have heqA : eA.hom ≫ fV = fA := by
    dsimp [fV, fA]
    rw [← Category.assoc, heA]
    rfl
  let hfA : ∀ y : G.objects.left, IsLocallyNoetherian (fA.fiber y) := by
    intro y
    simpa only [heqA] using hfA' y
  have hcmA : Scheme.Hom.IsCohenMacaulay fA hfA := by
    intro x
    simpa only [heqA] using hcmA' x
  have : LocallyOfFiniteType W.ι := inferInstance
  let hfQ : ∀ y : W, IsLocallyNoetherian ((pullback.snd fA W.ι).fiber y) :=
    fun y => isLocallyNoetherian_fiber_pullback fA W.ι hfA y
  have hcmQ : Scheme.Hom.IsCohenMacaulay (pullback.snd fA W.ι) hfQ :=
    fun x => isCohenMacaulayAt_pullback fA W.ι hfA x (hcmA ((pullback.fst fA W.ι).base x))
  let qOver := pullback fOver g
  let Q := pullback fA W.ι
  let eQ : qOver.left ≅ Q := by
    show (Over.forget S).obj qOver ≅
      pullback ((Over.forget S).map fOver) ((Over.forget S).map g)
    simpa [Over.forget_map, fA] using
      (PreservesPullback.iso (Over.forget S) fOver g)
  let eAssoc : restrictionArrows G g ≅ qOver := by
    show pullback t (pullback.fst G.source g) ≅ pullback fOver g
    exact sourcePullbackAssocIso t G.source g
  let eAssocScheme := (Over.forget S).mapIso eAssoc
  let eP : (restrictionArrows G g).left ≅ Q := eAssocScheme ≪≫ eQ
  have heAssoc : eAssoc.hom ≫ pullback.snd fOver g = restrictionSource G g := by
    show (sourcePullbackAssocIso (pullback.snd g G.target) G.source g).hom ≫
        pullback.snd ((pullback.snd g G.target) ≫ G.source) g =
      pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.snd G.source g
    exact sourcePullbackAssocIso_hom_snd (pullback.snd g G.target) G.source g
  have heQ : eQ.hom ≫ pullback.snd fA W.ι = (pullback.snd fOver g).left := by
    show (PreservesPullback.iso (Over.forget S) fOver g).hom ≫
      pullback.snd (Over.Hom.left fOver) (Over.Hom.left g) =
        (pullback.snd fOver g).left
    exact PreservesPullback.iso_hom_snd (Over.forget S) fOver g
  have heP : eP.hom ≫ pullback.snd fA W.ι = (restrictionSource G g).left := by
    calc
      eP.hom ≫ pullback.snd fA W.ι =
          eAssocScheme.hom ≫ (eQ.hom ≫ pullback.snd fA W.ι) := by
            simp [eP, Category.assoc]
      _ = eAssocScheme.hom ≫ (pullback.snd fOver g).left := by rw [heQ]
      _ = (restrictionSource G g).left := congrArg (fun k => k.left) heAssoc
  rcases (cohenMacaulay_sourceIso_iff eP (pullback.snd fA W.ι)).mpr
      ⟨hfQ, hcmQ⟩ with ⟨hfP, hcmP⟩
  exact ⟨fun y => by simpa [g, heP] using hfP y, fun x => by simpa [g, heP] using hcmP x⟩

/-- The source map of the restricted groupoid is Cohen–Macaulay. -/
@[stacks 0460 "part (5): source Cohen–Macaulay"]
public theorem restricted_source_cohenMacaulay {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    let U' := cohenMacaulayOpen G
    let g : Over.mk (U'.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk U'.ι
    let f := (GroupoidScheme.restrict G g).groupoid.source.left
    ∃ hf : ∀ y, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulay f hf := by
  let W := cohenMacaulayOpen G
  let U := Over.mk (W.ι ≫ G.objects.hom)
  let g : U ⟶ G.objects := Over.homMk W.ι
  let R := GroupoidScheme.restrict G g
  have hmax := Classical.choose_spec (exists_open_source_cohenMacaulay_locus G)
  have hV : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (((G.target.left ⁻¹ᵁ W).ι ≫ G.source.left).fiber y),
      Scheme.Hom.IsCohenMacaulay ((G.target.left ⁻¹ᵁ W).ι ≫ G.source.left) hf := by
    simpa [W, cohenMacaulayOpen] using hmax.1
  have hRaw := restrictionSource_cohenMacaulay_of_targetPreimage G W hV
  have : IsIso (Over.Hom.left (eqToHom R.arrows_eq)) :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.arrows_eq)))
  have : IsIso (Over.Hom.left (eqToHom R.objects_eq)) :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.objects_eq)))
  let eX : R.groupoid.arrows.left ≅ (restrictionArrows G g).left :=
    asIso (Over.Hom.left (eqToHom R.arrows_eq))
  let eY : R.groupoid.objects.left ≅ U.left :=
    asIso (Over.Hom.left (eqToHom R.objects_eq))
  let q := restrictionSource G g
  obtain ⟨hfY, hcmY⟩ := (cohenMacaulay_targetIso_iff q.left eY.symm).mpr hRaw
  let fY := q.left ≫ eY.symm.hom
  obtain ⟨hf, hcm⟩ := (cohenMacaulay_sourceIso_iff eX fY).mpr ⟨hfY, hcmY⟩
  have hsource : eX.hom ≫ q.left ≫ eY.symm.hom = R.groupoid.source.left := by
    have h := congrArg Over.Hom.left R.source_eq
    simpa [eX, eY, q, Category.assoc] using h.symm
  refine ⟨fun y => by rw [← hsource]; exact hf y, ?_⟩
  intro x
  have hcm' : Scheme.Hom.IsCohenMacaulayAt
      (eX.hom ≫ q.left ≫ eY.symm.hom) hf x := by
    simpa [fY, Category.assoc] using hcm x
  simpa only [R, hsource] using hcm'

/-- The target map of the restricted groupoid is Cohen–Macaulay. -/
@[stacks 0460 "part (5): target Cohen–Macaulay"]
public theorem restricted_target_cohenMacaulay {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    let U' := cohenMacaulayOpen G
    let g : Over.mk (U'.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk U'.ι
    let f := (GroupoidScheme.restrict G g).groupoid.target.left
    ∃ hf : ∀ y, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulay f hf := by
  let W := cohenMacaulayOpen G
  let U := Over.mk (W.ι ≫ G.objects.hom)
  let g : U ⟶ G.objects := Over.homMk W.ι
  let R := GroupoidScheme.restrict G g
  rcases restricted_source_cohenMacaulay G with ⟨hfS, hcmS⟩
  have : IsIso R.groupoid.inverse.left := groupoidInverse_left_isIso R.groupoid
  let e : R.groupoid.arrows.left ≅ R.groupoid.arrows.left := asIso R.groupoid.inverse.left
  have hmap : e.hom ≫ R.groupoid.source.left = R.groupoid.target.left :=
    congrArg Over.Hom.left R.groupoid.source_inverse
  obtain ⟨hfT, hcmT⟩ :=
    (cohenMacaulay_sourceIso_iff e R.groupoid.source.left).mpr ⟨hfS, hcmS⟩
  exact ⟨fun y => by simpa [hmap] using hfT y, fun x => by simpa [hmap] using hcmT x⟩

/-- The source map of the restricted groupoid is locally of finite presentation. -/
@[stacks 0460 "part (5): source locally of finite presentation"]
public theorem restricted_source_locallyOfFinitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S) [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    let U' := cohenMacaulayOpen G
    let g : Over.mk (U'.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk U'.ι
    LocallyOfFinitePresentation (GroupoidScheme.restrict G g).groupoid.source.left := by
  exact restrictionSource_locallyOfFinitePresentation G (cohenMacaulayOpen G).ι

/-- The target map of the restricted groupoid is locally of finite presentation. -/
@[stacks 0460 "part (5): target locally of finite presentation"]
public theorem restricted_target_locallyOfFinitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S) [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    let U' := cohenMacaulayOpen G
    let g : Over.mk (U'.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk U'.ι
    LocallyOfFinitePresentation (GroupoidScheme.restrict G g).groupoid.target.left := by
  exact restrictionTarget_locallyOfFinitePresentation G (cohenMacaulayOpen G).ι

end AlgebraicGeometry
