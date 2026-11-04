module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalFamilyDatum
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongFpqcCovering

/-!
# Restricting a family of morphisms, and its descent data, to an open of the base

Let `𝒰 = {X i ⟶ S}` be a family of morphisms of schemes with fixed target and let `U` be an open
subscheme of `S`. Restricting every member of the family over `U` gives a family
`{(X i) ×_S U ⟶ U}` over `U`, and the inclusion of `U` makes the restricted family the source of
a morphism of families over `U.ι`. Pulling descent data back along that morphism restricts them
to `U`, and the construction carries canonical descent data to canonical descent data.

## Main definitions

* `AlgebraicGeometry.PreZeroHypercover.restrictBase` is the restricted family.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.ofRestrictBase` is the morphism of families it
  sits in.

## Main results

* `AlgebraicGeometry.PreZeroHypercover.isPullback_restrictBase`: each member of the restricted
  family is a base change of the corresponding member of the original family.
* `AlgebraicGeometry.PreZeroHypercover.mem_fpqcPrecoverage_restrictBase`: the restriction of an
  fpqc covering family of `S` is an fpqc covering family of `U`.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- The family of morphisms obtained by restricting a family over `S` to an open `U` of `S`:
its `i`-th member is `f i` restricted over `U`, a morphism `(f i) ⁻¹ᵁ U ⟶ U`. -/
def PreZeroHypercover.restrictBase {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (U : S.Opens) : PreZeroHypercover.{u} U.toScheme where
  I₀ := 𝒰.I₀
  X i := ((𝒰.f i) ⁻¹ᵁ U).toScheme
  f i := (𝒰.f i) ∣_ U

/-- Restricting a family to an open of the base, as a morphism of families over the inclusion
of that open. -/
def MorphismOfSchemeFamilies.ofRestrictBase {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (U : S.Opens) : MorphismOfSchemeFamilies.{u} where
  sourceBase := U.toScheme
  targetBase := S
  sourceFamily := PreZeroHypercover.restrictBase 𝒰 U
  targetFamily := 𝒰
  baseHom := U.ι
  familyHom :=
    { s₀ := id
      h₀ := fun i ↦ ((𝒰.f i) ⁻¹ᵁ U).ι
      w₀ := fun i ↦ (morphismRestrict_ι (𝒰.f i) U).symm }

/-- The `i`-th member of the family restricted to an open `U` of the base exhibits
`(f i) ⁻¹ᵁ U` as the base change of `f i` along the inclusion of `U`. -/
lemma PreZeroHypercover.isPullback_restrictBase {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (U : S.Opens) (i : 𝒰.I₀) :
    IsPullback ((PreZeroHypercover.restrictBase 𝒰 U).f i) ((𝒰.f i ⁻¹ᵁ U).ι) U.ι (𝒰.f i) :=
  isPullback_morphismRestrict (𝒰.f i) U

/-- A property of morphisms stable under base change passes from a member of a family to the
corresponding member of its restriction to an open of the base. -/
lemma PreZeroHypercover.restrictBase_prop {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (U : S.Opens) {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] (i : 𝒰.I₀)
    (h : P (𝒰.f i)) : P ((PreZeroHypercover.restrictBase 𝒰 U).f i) :=
  MorphismProperty.of_isPullback (PreZeroHypercover.isPullback_restrictBase 𝒰 U i).flip h

/-- A property of morphisms stable under base change passes from the components of a descent
datum to those of its restriction to an open of the base. -/
lemma DescentData.restrictBase_prop_obj {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (U : S.Opens) {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (D : DescentData 𝒰.f) (i : 𝒰.I₀) (h : P (D.obj i).hom) :
    P ((((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U)).functor.obj D).obj i).hom) := by
  rw [(MorphismOfSchemeFamilies.pullbackFunctor
    (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U)).obj_eq D]
  exact MorphismProperty.baseChange_obj ((𝒰.f i ⁻¹ᵁ U).ι) (D.obj i) h

/-- **The restriction of an fpqc covering family to an open of the base is an fpqc covering
family of that open.** -/
lemma PreZeroHypercover.mem_fpqcPrecoverage_restrictBase {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{u} S) (U : S.Opens)
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) :
    Presieve.ofArrows (PreZeroHypercover.restrictBase 𝒰 U).X
        (PreZeroHypercover.restrictBase 𝒰 U).f ∈ Scheme.fpqcPrecoverage U.toScheme :=
  Precoverage.mem_coverings_of_isPullback 𝒰.f h𝒰 U.ι _ (fun i ↦ (𝒰.f i ⁻¹ᵁ U).ι)
    (PreZeroHypercover.isPullback_restrictBase 𝒰 U)

section Canonical

open MorphismOfSchemeFamilies

attribute [local implicit_reducible] CanonicalDatum.datum CanonicalDatum.functor

/-- The gluing isomorphisms of the canonical descent datum of `W` preserve the projection
to `W`. -/
lemma canonicalDatum_gluingPullbackIso_hom_snd_fst {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) (W : Over S) (i j : I) :
    ((CanonicalDatum.datum f W).gluingPullbackIso i j).hom ≫
        pullback.snd (f i) (((CanonicalDatum.datum f W).obj j).hom ≫ f j) ≫
        pullback.fst W.hom (f j) =
      pullback.fst (((CanonicalDatum.datum f W).obj i).hom ≫ f i) (f j) ≫
        pullback.fst W.hom (f i) := by
  have h := (canonicalFamilyDescentFunctor f).gluing W i j
  simp only [eqToHom_refl, Over.id_left, Category.id_comp] at h
  exact h

variable (F : MorphismOfSchemeFamilies.{u}) (W : Over F.targetBase)

/-- The pullback along a morphism of families of the canonical descent datum of a scheme over
the target base. -/
abbrev pulledBackCanonicalDatum : DescentData F.sourceFamily.f :=
  pulledBackDatum F (CanonicalDatum.datum F.targetFamily.f W)

/-- The comparison map on the targets of the gluing isomorphisms of a pulled-back descent
datum projects to the chosen pullback of the component at the second index. -/
private lemma pulledBackDatumTargetMap_snd (D : DescentData F.targetFamily.f)
    (i j : F.sourceFamily.I₀) :
    pulledBackDatumTargetMap F D i j ≫
        pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
          ((D.obj (F.familyHom.s₀ j)).hom ≫ F.targetFamily.f (F.familyHom.s₀ j)) =
      pullback.snd (F.sourceFamily.f i)
          (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
        (pulledBackDatumObjIso F D j).hom.left ≫
        pullback.fst (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) :=
  pullback.lift_snd _ _ _

/-- The comparison map on the sources of the gluing isomorphisms of a pulled-back descent
datum projects to the chosen pullback of the component at the first index. -/
private lemma pulledBackDatumSourceMap_fst (D : DescentData F.targetFamily.f)
    (i j : F.sourceFamily.I₀) :
    pulledBackDatumSourceMap F D i j ≫
        pullback.fst ((D.obj (F.familyHom.s₀ i)).hom ≫
          F.targetFamily.f (F.familyHom.s₀ i)) (F.targetFamily.f (F.familyHom.s₀ j)) =
      pullback.fst (((pulledBackDatum F D).obj i).hom ≫ F.sourceFamily.f i)
          (F.sourceFamily.f j) ≫
        (pulledBackDatumObjIso F D i).hom.left ≫
        pullback.fst (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) :=
  pullback.lift_fst _ _ _

/-- The component at `i` of the pullback along a morphism of families of the canonical descent
datum of `W`, identified with the fibre product of the base change of `W` to the source base
with the `i`-th member of the source family. -/
def pulledBackCanonicalObjIsoOver (i : F.sourceFamily.I₀) :
    (pulledBackCanonicalDatum F W).obj i ≅
      (Over.pullback (F.sourceFamily.f i)).obj ((Over.pullback F.baseHom).obj W) :=
  pullbackCompObjIso W (F.familyHom.h₀ i) (F.targetFamily.f (F.familyHom.s₀ i))
      (F.sourceFamily.f i ≫ F.baseHom) (F.familyHom.w₀ i) ≪≫
    (pullbackCompObjIso W (F.sourceFamily.f i) F.baseHom
      (F.sourceFamily.f i ≫ F.baseHom) rfl).symm

/-- The identification of the components, followed by the projection to the base change of `W`
and then the projection to `W`, is the composite of the two projections to `W`. -/
lemma pulledBackCanonicalObjIsoOver_hom_left_fst_fst (i : F.sourceFamily.I₀) :
    (pulledBackCanonicalObjIsoOver F W i).hom.left ≫
        pullback.fst (pullback.snd W.hom F.baseHom) (F.sourceFamily.f i) ≫
        pullback.fst W.hom F.baseHom =
      (pulledBackDatumObjIso F (CanonicalDatum.datum F.targetFamily.f W) i).hom.left ≫
        pullback.fst ((CanonicalDatum.datum F.targetFamily.f W).obj
          (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) ≫
        pullback.fst W.hom (F.targetFamily.f (F.familyHom.s₀ i)) := by
  have h₁ := pullbackCompObjIso_hom_left_fst W (F.familyHom.h₀ i)
    (F.targetFamily.f (F.familyHom.s₀ i)) (F.sourceFamily.f i ≫ F.baseHom) (F.familyHom.w₀ i)
  have h₂ := pullbackCompObjIso_hom_left_fst W (F.sourceFamily.f i) F.baseHom
    (F.sourceFamily.f i ≫ F.baseHom) rfl
  have hinv : (pullbackCompObjIso W (F.sourceFamily.f i) F.baseHom
          (F.sourceFamily.f i ≫ F.baseHom) rfl).inv.left ≫
        pullback.fst (pullback.snd W.hom F.baseHom) (F.sourceFamily.f i) ≫
        pullback.fst W.hom F.baseHom =
      pullback.fst W.hom (F.sourceFamily.f i ≫ F.baseHom) := by
    rw [← h₂, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp]
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, Iso.symm_hom, hinv]
  exact h₁.trans (Category.id_comp _).symm

/-- The identification of the components is compatible with the structure maps over the `i`-th
member of the source family. -/
lemma pulledBackCanonicalObjIsoOver_hom_left_fst_snd (i : F.sourceFamily.I₀) :
    (pulledBackCanonicalObjIsoOver F W i).hom.left ≫
        pullback.fst (pullback.snd W.hom F.baseHom) (F.sourceFamily.f i) ≫
        pullback.snd W.hom F.baseHom =
      ((pulledBackCanonicalDatum F W).obj i).hom ≫ F.sourceFamily.f i := by
  rw [pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ F.sourceFamily.f i) (Over.w (pulledBackCanonicalObjIsoOver F W i).hom)

/-- The gluing isomorphisms of the pullback along a morphism of families of the canonical
descent datum of `W` preserve the projection to the base change of `W`. -/
lemma pulledBackCanonicalObjIsoOver_gluing (i j : F.sourceFamily.I₀) :
    ((pulledBackCanonicalDatum F W).gluingPullbackIso i j).hom ≫
        pullback.snd (F.sourceFamily.f i)
          (((pulledBackCanonicalDatum F W).obj j).hom ≫ F.sourceFamily.f j) ≫
        (pulledBackCanonicalObjIsoOver F W j).hom.left ≫
        pullback.fst (pullback.snd W.hom F.baseHom) (F.sourceFamily.f j) =
      pullback.fst (((pulledBackCanonicalDatum F W).obj i).hom ≫ F.sourceFamily.f i)
          (F.sourceFamily.f j) ≫
        (pulledBackCanonicalObjIsoOver F W i).hom.left ≫
        pullback.fst (pullback.snd W.hom F.baseHom) (F.sourceFamily.f i) := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [pulledBackCanonicalObjIsoOver_hom_left_fst_fst F W j,
      pulledBackCanonicalObjIsoOver_hom_left_fst_fst F W i]
    have key := congrArg (fun q ↦ q ≫
        pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
          (((CanonicalDatum.datum F.targetFamily.f W).obj (F.familyHom.s₀ j)).hom ≫
            F.targetFamily.f (F.familyHom.s₀ j)) ≫
        pullback.fst W.hom (F.targetFamily.f (F.familyHom.s₀ j)))
      (pulledBackDatum_gluing F (CanonicalDatum.datum F.targetFamily.f W) i j)
    simp only [Category.assoc,
      reassoc_of% (pulledBackDatumTargetMap_snd F
        (CanonicalDatum.datum F.targetFamily.f W) i j),
      canonicalDatum_gluingPullbackIso_hom_snd_fst F.targetFamily.f W (F.familyHom.s₀ i)
        (F.familyHom.s₀ j),
      reassoc_of% (pulledBackDatumSourceMap_fst F
        (CanonicalDatum.datum F.targetFamily.f W) i j)] at key
    exact key
  · have hc : pullback.snd (F.sourceFamily.f i)
          (((pulledBackCanonicalDatum F W).obj j).hom ≫ F.sourceFamily.f j) ≫
        ((pulledBackCanonicalDatum F W).obj j).hom ≫ F.sourceFamily.f j =
        pullback.fst (F.sourceFamily.f i)
          (((pulledBackCanonicalDatum F W).obj j).hom ≫ F.sourceFamily.f j) ≫
          F.sourceFamily.f i := pullback.condition.symm
    simp only [Category.assoc]
    rw [pulledBackCanonicalObjIsoOver_hom_left_fst_snd F W j,
      pulledBackCanonicalObjIsoOver_hom_left_fst_snd F W i, hc,
      reassoc_of% (DescentData.gluingPullbackIso_hom_fst'
        (pulledBackCanonicalDatum F W) i j)]

/-- **The canonical descent datum pulls back to the canonical descent datum.** The pullback
along a morphism of families of the canonical descent datum of `W` is the canonical descent
datum of the base change of `W` to the base of the source family. -/
def pulledBackCanonicalDatumIsoOver :
    pulledBackDatum F ((canonicalFamilyDescentFunctor F.targetFamily.f).functor.obj W) ≅
      (canonicalFamilyDescentFunctor F.sourceFamily.f).functor.obj
        ((Over.pullback F.baseHom).obj W) :=
  DescentData.isoCanonicalDatum _ _ (pulledBackCanonicalObjIsoOver F W)
    (pulledBackCanonicalObjIsoOver_gluing F W)

/-- The pullback functor on descent data along a morphism of families carries the canonical
descent datum of `W` to the canonical descent datum of the base change of `W`. -/
def pullbackFunctorCanonicalObjIsoOver :
    (pullbackFunctor F).functor.obj
        ((canonicalFamilyDescentFunctor F.targetFamily.f).functor.obj W) ≅
      (canonicalFamilyDescentFunctor F.sourceFamily.f).functor.obj
        ((Over.pullback F.baseHom).obj W) :=
  eqToIso ((pullbackFunctor F).obj_eq _) ≪≫ pulledBackCanonicalDatumIsoOver F W

end Canonical

/-- The canonical descent datum of a scheme over `S` restricts, over an open `U` of `S`, to the
canonical descent datum of its base change to `U`. -/
def DescentData.restrictBaseCanonicalIso {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (U : S.Opens) (W : Over S) :
    (MorphismOfSchemeFamilies.pullbackFunctor
        (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U)).functor.obj
      ((canonicalFamilyDescentFunctor 𝒰.f).functor.obj W) ≅
    (canonicalFamilyDescentFunctor (PreZeroHypercover.restrictBase 𝒰 U).f).functor.obj
      ((Over.pullback U.ι).obj W) :=
  pullbackFunctorCanonicalObjIsoOver (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U) W

/-- Family effectivity restricts to an open of the base. -/
theorem DescentData.isFamilyEffective_restrictBase {S : Scheme.{u}}
    {𝒰 : PreZeroHypercover.{u} S} (U : S.Opens) {D : DescentData 𝒰.f}
    (h : D.IsFamilyEffective) :
    ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U)).functor.obj D).IsFamilyEffective := by
  obtain ⟨W, ⟨e⟩⟩ := h
  exact ⟨(Over.pullback U.ι).obj W,
    ⟨(DescentData.restrictBaseCanonicalIso 𝒰 U W).symm ≪≫
      (MorphismOfSchemeFamilies.pullbackFunctor
        (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U)).functor.mapIso e⟩⟩

end AlgebraicGeometry

end

end
