module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSectionSetoid
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.CategoryTheory.FiberedInSetoids.EquivalentFiberedInSets

/-!
# Pic_{X/B} as an algebraic space: the model, and the case with a section

Stacks 0D2C asserts that for `f : X ⟶ B` flat, of finite presentation and proper with
`𝒪_T ≅ f_{T, *}𝒪_{X_T}` for every scheme `T` over `B`, the relative Picard functor `Pic_{X/B}` of
Stacks 0D25 is an algebraic space.  This file proves the parts of that statement that do not go
through the algebraicity of the Picard stack.

## What "an algebraic space over `B`" means for a functor on the test schemes

`Pic_{X/B}` is a functor on the test schemes over `B`, `AlgebraicGeometry.Space.SchemesOver`,
with values in `Type (u + 1)`.  It is *an algebraic space over `B`* when it is isomorphic to the
universe lift of the functor of points over `B` of an algebraic space `H` with a morphism
`p : H ⟶ B` (`AlgebraicGeometry.Space.IsAlgebraicSpaceOver`).  Stacks 0D2C reads `Pic_{X/B}` as a
sheaf on `(Sch/S)_{fppf}` with a morphism to `B`: its value at `T` is the set of pairs `(h, ξ)` of
`h : T ⟶ B` and `ξ ∈ Pic_{X/B}(T, h)`.  That is the *total presheaf*
`AlgebraicGeometry.Space.OverTotal`, and by `AlgebraicGeometry.Space.isAlgebraicSpaceOver_of_model`
an algebraic space `F` over `S` naturally identified with the total presheaf of a functor `R` on
the test schemes makes `R` an algebraic space over `B`.

## The case with a section

When `f` has a section `σ`, `Picardstack_{X/B, σ}` is an algebraic stack fibred in setoids, so
that its presheaf of isomorphism classes is an algebraic space (Stacks 0D2B, 02ZX); this presheaf
is `T ↦ ∐_{h : T ⟶ B} Ker(σ_T^*)` (Stacks 0D2B), which is `Pic_{X/B}` (Stacks 0D28).  The
identification is natural in `T`
(`AlgebraicGeometry.Space.sectionedPicardIsoClassEquivOverTotal_naturality`), giving
`AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace`:
if `Picardstack_{X/B, σ}` is representable by an algebraic space, then `Pic_{X/B}` is an
algebraic space over `B`.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 0D2B](https://stacks.math.columbia.edu/tag/0D2B)
* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Total

variable {Y : AlgebraicSpaces B S hS} (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))

/-- **A functor on the test schemes over `Y` is an algebraic space over `Y`**: it is isomorphic
to the universe lift of the functor of points over `Y` of an algebraic space `H` with a
morphism `p : H ⟶ Y`. -/
def IsAlgebraicSpaceOver : Prop :=
  ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y),
    Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ R)

variable {R} in
/-- Being an algebraic space over `Y` transports along an isomorphism of functors on the test
schemes over `Y`. -/
theorem IsAlgebraicSpaceOver.of_iso {R' : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)} (e : R ≅ R')
    (h : IsAlgebraicSpaceOver R) : IsAlgebraicSpaceOver R' := by
  obtain ⟨H, p, ⟨c⟩⟩ := h
  exact ⟨H, p, ⟨c ≪≫ e⟩⟩

/-- The value at a scheme `U` of the site of the *total presheaf* of `R`: a morphism
`h : U ⟶ Y` together with a section of `R` over the test scheme `(U, h)`. -/
abbrev OverTotal (U : BigFppfOver B S hS) : Type (u + 1) :=
  Σ h : (schemeSpaceFunctor B S hS).obj U ⟶ Y, R.obj (op (CostructuredArrow.mk h))

/-- Restriction of the total presheaf of `R` along a morphism `g : V ⟶ U` of the site:
`(h, r) ↦ (g ≫ h, r|_V)`. -/
def overTotalMap {U V : BigFppfOver B S hS} (g : V ⟶ U) (a : OverTotal R U) : OverTotal R V :=
  ⟨(schemeSpaceFunctor B S hS).map g ≫ a.1,
    R.map (CostructuredArrow.homMk
      (f := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ a.1))
      (f' := CostructuredArrow.mk a.1) g rfl).op a.2⟩

/-- The comparison from an element of the total presheaf of `R` lying over the test scheme `T`
to the value of `R` at `T`. -/
def overTotalToValue (T : SchemesOver Y) (a : OverTotal R T.left) (ha : a.1 = T.hom) :
    R.obj (op T) :=
  R.map (CostructuredArrow.homMk (f := T) (f' := CostructuredArrow.mk a.1) (𝟙 T.left)
    (by simp [ha])).op a.2

/-- The comparison `overTotalToValue` only depends on the element of the total presheaf. -/
theorem overTotalToValue_congr (T : SchemesOver Y) {a a' : OverTotal R T.left} (e : a = a')
    (ha : a.1 = T.hom) :
    overTotalToValue R T a ha = overTotalToValue R T a' (e ▸ ha) := by
  subst e; rfl

/-- The comparison from the elements of the total presheaf over a test scheme `T` to the value of
`R` at `T` is injective. -/
theorem overTotalToValue_injective (T : SchemesOver Y) {a a' : OverTotal R T.left}
    (ha : a.1 = T.hom) (ha' : a'.1 = T.hom)
    (h : overTotalToValue R T a ha = overTotalToValue R T a' ha') : a = a' := by
  obtain ⟨b, r⟩ := a
  obtain ⟨b', r'⟩ := a'
  dsimp only at ha ha'
  subst ha ha'
  have hk : IsIso (CostructuredArrow.homMk (f := T) (f' := CostructuredArrow.mk T.hom)
      (𝟙 T.left) (by simp)) := by
    refine ⟨CostructuredArrow.homMk (𝟙 T.left) (by simp), ?_, ?_⟩ <;>
      ext <;> simp
  have hinj := ((isIso_iff_bijective (R.map (CostructuredArrow.homMk (f := T)
    (f' := CostructuredArrow.mk T.hom) (𝟙 T.left) (by simp)).op)).1 inferInstance).1
  exact Sigma.ext rfl (heq_of_eq (hinj h))

/-- The comparison from the total presheaf to the values of `R` commutes with restriction. -/
theorem overTotalToValue_overTotalMap {U T : SchemesOver Y} (g : U ⟶ T) (a : OverTotal R T.left)
    (ha : a.1 = T.hom) (ha' : (overTotalMap R g.left a).1 = U.hom) :
    overTotalToValue R U (overTotalMap R g.left a) ha' =
      R.map g.op (overTotalToValue R T a ha) := by
  obtain ⟨b, r⟩ := a
  dsimp only at ha
  subst ha
  change R.map (CostructuredArrow.homMk (f := U)
      (f' := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left ≫ T.hom)) (𝟙 _) _).op
      (R.map (CostructuredArrow.homMk
        (f := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left ≫ T.hom))
        (f' := CostructuredArrow.mk T.hom) g.left rfl).op r) =
    R.map g.op (R.map (CostructuredArrow.homMk (f := T) (f' := CostructuredArrow.mk T.hom)
      (𝟙 _) _).op r)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  exact congrArg (fun k ↦ R.map (Quiver.Hom.op k) r)
    (CostructuredArrow.hom_ext _ _ ((Category.id_comp _).trans (Category.comp_id _).symm))

section Model

variable {R} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (e : ∀ U, F.obj (op U) ≃ OverTotal R U)
  (he : ∀ {U V : BigFppfOver B S hS} (g : V ⟶ U) (x : F.obj (op U)),
    e V (F.map g.op x) = overTotalMap R g (e U x))

include he in
/-- The morphism of presheaves from a model of the total presheaf of `R` to `Y`, remembering the
morphism to `Y`. -/
def modelToBase : F ⟶ Y.1 where
  app U := ↾fun x ↦ testPoint (CostructuredArrow.mk (e U.unop x).1)
  naturality {U V} g := by
    ext x
    change testPoint (CostructuredArrow.mk (e V.unop (F.map g.unop.op x)).1) =
      Y.1.map g (testPoint (CostructuredArrow.mk (e U.unop x).1))
    rw [he]
    exact (testPoint_naturality (CostructuredArrow.homMk
      (f := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.unop ≫ (e U.unop x).1))
      (f' := CostructuredArrow.mk (e U.unop x).1) g.unop rfl)).symm

/-- A morphism from the scheme underlying a test scheme `T` to `Y` with the same section of `Y`
as `T` is the structure morphism of `T`. -/
theorem eq_hom_of_testPoint_mk_eq {T : SchemesOver Y}
    (h : (schemeSpaceFunctor B S hS).obj T.left ⟶ Y)
    (ht : testPoint (CostructuredArrow.mk h) = testPoint T) : h = T.hom :=
  InducedCategory.hom_ext (yonedaEquiv.injective ht)

/-- The morphism to `Y` sends a section of the model to the section of `Y` that its first
component is. -/
theorem modelToBase_app (U : BigFppfOver B S hS) (x : F.obj (op U)) :
    (modelToBase F e he).app (op U) x = testPoint (CostructuredArrow.mk (e U x).1) :=
  rfl

variable {F e he} in
/-- A point of the model over `Y` at a test scheme `T` lies over the structure morphism of `T`. -/
theorem model_fst_eq (hF : IsAlgebraicSpace B S hS F) (T : SchemesOver Y)
    (x : spacePointsOverObj (ObjectProperty.homMk (P := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F) (X := ⟨F, hF⟩) (modelToBase F e he)) T) :
    (e T.left x.1).1 = T.hom :=
  eq_hom_of_testPoint_mk_eq _ x.2

variable {F e he} in
/-- The comparison from the points over `Y` of a model of the total presheaf of `R` to `R`. -/
def modelPointsToValue (hF : IsAlgebraicSpace B S hS F) (T : SchemesOver Y)
    (x : spacePointsOverObj (ObjectProperty.homMk (P := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F) (X := ⟨F, hF⟩) (modelToBase F e he)) T) : R.obj (op T) :=
  overTotalToValue R T (e T.left x.1) (model_fst_eq hF T x)

variable {F e he} in
/-- The comparison from the points of the model over `Y` to the values of `R` is bijective. -/
theorem bijective_modelPointsToValue (hF : IsAlgebraicSpace B S hS F) (T : SchemesOver Y) :
    Function.Bijective (modelPointsToValue (he := he) hF T) := by
  refine ⟨fun x x' hx ↦ Subtype.ext ((e T.left).injective
    (overTotalToValue_injective R T _ _ hx)), fun r ↦ ?_⟩
  let a : OverTotal R T.left := ⟨T.hom, R.map (CostructuredArrow.homMk
    (f := CostructuredArrow.mk T.hom) (f' := T) (𝟙 T.left) (by simp)).op r⟩
  refine ⟨⟨(e T.left).symm a, ?_⟩, ?_⟩
  · change testPoint (CostructuredArrow.mk (e T.left ((e T.left).symm a)).1) = testPoint T
    rw [Equiv.apply_symm_apply]
    rfl
  · rw [modelPointsToValue, overTotalToValue_congr R T (Equiv.apply_symm_apply _ a)]
    simp only [overTotalToValue, a, ← Functor.map_comp_apply, ← op_comp]
    rw [show CostructuredArrow.homMk (f := T) (f' := CostructuredArrow.mk T.hom) (𝟙 T.left)
        (by simp) ≫ CostructuredArrow.homMk (f := CostructuredArrow.mk T.hom) (f' := T) (𝟙 T.left)
        (by simp) = 𝟙 T from CostructuredArrow.hom_ext _ _ (Category.id_comp _), op_id,
      Functor.map_id_apply]

variable {F e he} in
/-- The comparison from the points of the model over `Y` to the values of `R` is natural. -/
theorem modelPointsToValue_naturality (hF : IsAlgebraicSpace B S hS F) {U T : SchemesOver Y}
    (g : U ⟶ T) (x : spacePointsOverObj (ObjectProperty.homMk (P := fun F :
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) (X := ⟨F, hF⟩)
      (modelToBase F e he)) T) :
    modelPointsToValue hF U ((spacePointsOver _).map g.op x) =
      R.map g.op (modelPointsToValue hF T x) :=
  (overTotalToValue_congr R U (he g.left x.1) _).trans (overTotalToValue_overTotalMap R g _ _ _)

variable {F} in
include he in
/-- Let `R` be a functor on the test schemes over `Y`, and let `F` be an algebraic space over `S`
whose value at every scheme `U` is identified, naturally in `U`, with the pairs `(h, r)` of a
morphism `h : U ⟶ Y` and a section `r` of `R` over the test scheme `(U, h)`.  Then `R` is an
algebraic space over `Y`: the morphism `F ⟶ Y` is the first component, and the points of `F`
over `Y` at a test scheme `T` are the pairs over the structure morphism of `T`, that is the
sections of `R` over `T`. -/
theorem isAlgebraicSpaceOver_of_model (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicSpaceOver R :=
  ⟨⟨F, hF⟩, ObjectProperty.homMk (modelToBase F e he),
    ⟨NatIso.ofComponents (fun T ↦ (Equiv.ulift.trans (Equiv.ofBijective _
      (bijective_modelPointsToValue (he := he) hF T.unop))).toIso) fun {T T'} g ↦ by
      ext ⟨x⟩
      exact modelPointsToValue_naturality hF g.unop x⟩⟩

end Model

end Total

/-! ### With a section: the isomorphism classes of `Picardstack_{X/B, σ}` and `Pic_{X/B}` -/

section Sectioned

open PicardSituation

variable {s : PicardSituation B S hS} {σ : s.base ⟶ s.X} {hσ : σ ≫ s.f = 𝟙 s.base}
  (hc : ModulePushforwardCoherence B S hS) (ht : SectionTransportCoherence hc σ hσ)

/-- Restriction of `∐_{h : U ⟶ B} Ker(σ_U^*)` along a morphism `g : V ⟶ U` of the site:
`(h, x) ↦ (g ≫ h, x|_V)`. -/
def kernelCoproductMap {U V : BigFppfOver B S hS} (g : V ⟶ U)
    (a : SectionKernelCoproduct σ hσ U) : SectionKernelCoproduct σ hσ V :=
  ⟨(schemeSpaceFunctor B S hS).map g ≫ a.1,
    ⟨s.picardMap (CostructuredArrow.homMk
      (f := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ a.1))
      (f' := CostructuredArrow.mk a.1) g rfl) a.2.1, by
      rw [sectionPicardPullback_picardMap, a.2.2, picardPullback_zero]⟩⟩

/-- **The map from `∐ Ker(σ_U^*)` to the isomorphism classes of `Picardstack_{X/B, σ}` is
natural in `U`.** -/
theorem kernelCoproductToIsoClass_kernelCoproductMap (hstr : s.StructureSheafMapIso)
    {U V : BigFppfOver B S hS} (g : V ⟶ U) (a : SectionKernelCoproduct σ hσ U) :
    letI := (sectionedPicardCFG hc ht).2.isFibered
    kernelCoproductToIsoClass hc ht V (kernelCoproductMap g a) =
      (sectionedPicardCFG hc ht).val.p.isoClassPresheaf.map g.op
        (kernelCoproductToIsoClass hc ht U a) := by
  let := (sectionedPicardCFG hc ht).2.isFibered
  obtain ⟨h, x⟩ := a
  let b : CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ h) ⟶ CostructuredArrow.mk h :=
    CostructuredArrow.homMk g rfl
  let A := kernelObject (σ := σ) (hσ := hσ) h x
  let A' := kernelObject (σ := σ) (hσ := hσ) ((schemeSpaceFunctor B S hS).map g ≫ h)
    (kernelCoproductMap g ⟨h, x⟩).2
  have hcl : picardClass _ A'.toPicardObject.lineBundle A'.toPicardObject.invertible =
      picardClass _ ((modulePullback B S hS (baseChangeMap s.f b)).obj A.toPicardObject.lineBundle)
        (modulePullbackInvertible (baseChangeMap s.f b) _ A.toPicardObject.invertible) := by
    have h1 := picardClass_kernelObject (σ := σ) (hσ := hσ) _ (kernelCoproductMap g ⟨h, x⟩).2
    have h2 := picardClass_kernelObject (σ := σ) (hσ := hσ) h x
    refine h1.trans ?_
    change s.picardMap b x.1 = _
    conv_lhs => rw [← h2]
    exact picardPullback_picardClass (baseChangeMap s.f b) A.toPicardObject.lineBundle
      A.toPicardObject.invertible
  obtain ⟨e⟩ := (picardClass_eq_picardClass_iff _ _ _ _ _).1 hcl
  obtain ⟨m, hm⟩ := exists_sectionedPicardHom (A := A') (C := A) (hstr _) b e.symm
  have hpm : (sectionedPicardCFG hc ht).val.p.map m = g := congrArg CommaMorphism.left hm
  have key := Functor.isoClassPresheaf_map_isoClassMk_of_hom (sectionedPicardCFG hc ht).2
    (y := A) (x := A') m
  rw [hpm] at key
  exact key.symm

variable {hc ht} in
/-- **Stacks 0D28 on the coproduct**: `(h, x) ↦ (h, image of x in Pic_{X/B}(U, h))` is a bijection
from `∐_{h : U ⟶ B} Ker(σ_U^*)` onto the total presheaf of `Pic_{X/B}` at `U`. -/
def kernelCoproductEquivOverTotal (hstr : s.StructureSheafMapIso) (U : BigFppfOver B S hS) :
    SectionKernelCoproduct σ hσ U ≃ OverTotal s.picardFunctor U :=
  Equiv.sigmaCongrRight fun h ↦
    (Equiv.subtypeEquivRight fun x ↦ by
      rw [AddMonoidHom.mem_ker, sectionPicardPullbackHom_apply]).trans
    (Equiv.ofBijective _ (s.picardSequence_splitExact σ hσ hstr (CostructuredArrow.mk h)).2.2.2.2.2)

/-- The bijection of Stacks 0D28 on the coproduct keeps `h` and sends `x` to its image in
`Pic_{X/B}`. -/
theorem kernelCoproductEquivOverTotal_apply (hstr : s.StructureSheafMapIso) {U : BigFppfOver B S hS}
    (a : SectionKernelCoproduct σ hσ U) :
    kernelCoproductEquivOverTotal hstr U a = ⟨a.1, s.picardClassMap _ a.2.1⟩ :=
  rfl

/-- The bijection of Stacks 0D28 on the coproduct is natural in the scheme. -/
theorem kernelCoproductEquivOverTotal_kernelCoproductMap (hstr : s.StructureSheafMapIso)
    {U V : BigFppfOver B S hS} (g : V ⟶ U) (a : SectionKernelCoproduct σ hσ U) :
    kernelCoproductEquivOverTotal hstr V (kernelCoproductMap g a) =
      overTotalMap s.picardFunctor g (kernelCoproductEquivOverTotal hstr U a) :=
  Sigma.ext rfl (heq_of_eq (picardClassMap_picardMap _ _))

/-- **The isomorphism classes of `Picardstack_{X/B, σ}` are the total presheaf of `Pic_{X/B}`**:
Stacks 0D2B followed by Stacks 0D28, at a scheme `U` of the site. -/
def sectionedPicardIsoClassEquivOverTotal (hstr : s.StructureSheafMapIso) (U : BigFppfOver B S hS) :
    Quotient (isIsomorphicSetoid ((sectionedPicardCFG hc ht).val.p.Fiber U)) ≃
      OverTotal s.picardFunctor U :=
  (sectionedPicardIsoClassEquiv hc ht hstr U).trans (kernelCoproductEquivOverTotal hstr U)

/-- The identification of the isomorphism classes of `Picardstack_{X/B, σ}` with the total
presheaf of `Pic_{X/B}` is natural in the scheme. -/
theorem sectionedPicardIsoClassEquivOverTotal_naturality (hstr : s.StructureSheafMapIso)
    {U V : BigFppfOver B S hS} (g : V ⟶ U)
    (c : Quotient (isIsomorphicSetoid ((sectionedPicardCFG hc ht).val.p.Fiber U))) :
    letI := (sectionedPicardCFG hc ht).2.isFibered
    sectionedPicardIsoClassEquivOverTotal hc ht hstr V
        ((sectionedPicardCFG hc ht).val.p.isoClassPresheaf.map g.op c) =
      overTotalMap s.picardFunctor g (sectionedPicardIsoClassEquivOverTotal hc ht hstr U c) := by
  let := (sectionedPicardCFG hc ht).2.isFibered
  obtain ⟨a, rfl⟩ := (sectionedPicardIsoClassEquiv hc ht hstr U).symm.surjective c
  have hsymm : ∀ (W : BigFppfOver B S hS) (b : SectionKernelCoproduct σ hσ W),
      (sectionedPicardIsoClassEquiv hc ht hstr W).symm b = kernelCoproductToIsoClass hc ht W b :=
    fun _ _ ↦ rfl
  have h1 : ∀ (W : BigFppfOver B S hS) (b : SectionKernelCoproduct σ hσ W),
      sectionedPicardIsoClassEquivOverTotal hc ht hstr W (kernelCoproductToIsoClass hc ht W b) =
        kernelCoproductEquivOverTotal hstr W b := fun W b ↦
    congrArg (kernelCoproductEquivOverTotal hstr W)
      ((sectionedPicardIsoClassEquiv hc ht hstr W).apply_symm_apply b)
  rw [hsymm, ← kernelCoproductToIsoClass_kernelCoproductMap hc ht hstr g a, h1, h1]
  exact kernelCoproductEquivOverTotal_kernelCoproductMap hstr g a

/-- In Situation 0D25 let `σ` be a section of `f` and assume that `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every test scheme `T`.  If `Picardstack_{X/B, σ}` is representable by an algebraic
space, then `Pic_{X/B}` is an algebraic space over `B`. -/
theorem isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace
    (hstr : s.StructureSheafMapIso)
    (hrep : IsRepresentableByAlgebraicSpace B S hS (sectionedPicardCFG hc ht)) :
    IsAlgebraicSpaceOver s.picardFunctor := by
  let := (sectionedPicardCFG hc ht).2.isFibered
  obtain ⟨-, F, hF, e', he'⟩ := (isRepresentableByAlgebraicSpace_iff B S hS _).1 hrep
  refine isAlgebraicSpaceOver_of_model (F := F)
    (fun U ↦ (e' (op U)).symm.trans (sectionedPicardIsoClassEquivOverTotal hc ht hstr U))
    (fun {U V} g x ↦ ?_) hF
  obtain ⟨c, rfl⟩ := (e' (op U)).surjective x
  rw [Equiv.trans_apply, Equiv.trans_apply, ← he', Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  exact sectionedPicardIsoClassEquivOverTotal_naturality hc ht hstr g c

end Sectioned

end AlgebraicGeometry.Space

end
