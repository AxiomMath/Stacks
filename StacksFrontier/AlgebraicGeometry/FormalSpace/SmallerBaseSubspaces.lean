module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerSituation

/-!
# Representables, open subspaces and completions over a smaller base

Let `g : V ⟶ S` be a morphism of the big fppf site. Stacks 04SG identifies presheaves on the big
fppf site of `V` with presheaves on the big fppf site of `S` over the representable presheaf of
`g` (`AlgebraicGeometry.smallerBasePresheafEquivalence`, whose inverse is
`AlgebraicGeometry.Space.smallerBaseInverse`). This file describes how representable presheaves,
open subspaces and completions behave under this identification.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseInverseYonedaIso`: the representable presheaf of an object
  `A` over `V` is attached to the representable presheaf of `A` viewed over `S`, with its morphism
  to `V`.
* `AlgebraicGeometry.Space.smallerBaseInverseOpenIso`: the subfunctor of `X_V` cut out by the
  inverse image of a set `W` of points of `X` is attached to the subfunctor of `X` cut out by `W`.

## Main results

* `AlgebraicGeometry.Space.subset_preimage_of_completionSheaf_hom`: a morphism of completions
  `X_{/T} ⟶ Y_{/Z}` lying over `f : X ⟶ Y` forces `T ⊆ f⁻¹ Z`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Completion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism `X_{/T} ⟶ X` from a completion into the universe lift of a sheaf `X` is the
identification of the completion with the completion subfunctor followed by the inclusion. -/
theorem completionSheafToAmbient_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) :
    completionSheafToAmbient B S hS X hX' T =
      (completionSheafIsoSubfunctor B S hS hX T).hom ≫ (completionSubfunctor B S hS X T).ι :=
  (Iso.inv_comp_eq _).1 (toSheafify_comp_completionSheafToAmbient B S hS X hX' T)

/-- A section of a completion of a sheaf `X`, carried into the universe lift of `X`, is a section
of the completion subfunctor. -/
theorem completionSheafToAmbient_app_mem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) {U : (BigFppfOver B S hS)ᵒᵖ}
    (σ : (completionSheaf B S hS X T).obj.obj U) :
    (completionSheafToAmbient B S hS X hX' T).app U σ ∈
      (completionSubfunctor B S hS X T).obj U := by
  rw [completionSheafToAmbient_eq B S hS hX hX' T]
  exact ((completionSheafIsoSubfunctor B S hS hX T).hom.app U σ).2

/-- **A morphism of completions over `f` confines the points.** Let `f : X ⟶ Y` be a morphism of
sheaves and let `m : X_{/T} ⟶ Y_{/Z}` be a morphism of completions lying over `f`. Then `f`
carries `T` into `Z`. -/
theorem subset_preimage_of_completionSheaf_hom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hY' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (Y ⋙ uliftFunctor.{u + 1}))
    (f : X ⟶ Y) {T : Set (points B S hS X)} {Z : Set (points B S hS Y)}
    (m : completionSheaf B S hS X T ⟶ completionSheaf B S hS Y Z)
    (hm : m.hom ≫ completionSheafToAmbient B S hS Y hY' Z =
      completionSheafToAmbient B S hS X hX' T ≫ Functor.whiskerRight f uliftFunctor.{u + 1}) :
    T ⊆ pointsMap B S hS X f ⁻¹' Z := by
  intro x hx
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  have hs : HasImageIn B S hS X T p.siteObject p.value :=
    (hasImageIn_iff_class_mem B S hS X T p).2 hx
  let σ : (completionSheaf B S hS X T).obj.obj (op p.siteObject) :=
    ((BigFppfOver.topology B S hS).toSheafify (completionSubfunctor B S hS X T).toFunctor).app
      (op p.siteObject) ⟨ULift.up p.value, hs⟩
  have hσ : (completionSheafToAmbient B S hS X hX' T).app (op p.siteObject) σ =
      ULift.up p.value :=
    congrArg (fun k => k.app (op p.siteObject) ⟨ULift.up p.value, hs⟩)
      (toSheafify_comp_completionSheafToAmbient B S hS X hX' T)
  have hmem := completionSheafToAmbient_app_mem B S hS hY hY' Z (m.hom.app (op p.siteObject) σ)
  have hval : (completionSheafToAmbient B S hS Y hY' Z).app (op p.siteObject)
      (m.hom.app (op p.siteObject) σ) = ULift.up (f.app (op p.siteObject) p.value) := by
    have := congrArg (fun k => k.app (op p.siteObject) σ) hm
    simp only [NatTrans.comp_app, types_comp_apply] at this
    rw [this, hσ]
    rfl
  rw [hval] at hmem
  have hq := (hasImageIn_iff_class_mem B S hS Y Z
    (FieldValuedPoint.map B S hS X f p)).1 hmem
  rwa [← pointsMap_class] at hq

/-- The restriction morphism of completions is compatible with the morphisms into the universe
lifts of sheaves. -/
theorem completionSheafRestrict_comp_completionSheafToAmbient
    {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T)
    (hF' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F' ⋙ uliftFunctor.{u + 1}))
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F ⋙ uliftFunctor.{u + 1})) :
    (completionSheafRestrict B S hS f T' T h).hom ≫ completionSheafToAmbient B S hS F hF T =
      completionSheafToAmbient B S hS F' hF' T' ≫ Functor.whiskerRight f uliftFunctor.{u + 1} := by
  let J := BigFppfOver.topology B S hS
  refine J.sheafify_hom_ext _ _ hF ?_
  have hA : J.toSheafify (completionSubfunctor B S hS F' T').toFunctor ≫
      (completionSheafRestrict B S hS f T' T h).hom =
      completionSubfunctorRestrict B S hS f T' T h ≫
        J.toSheafify (completionSubfunctor B S hS F T).toFunctor :=
    (J.toSheafify_naturality _).symm
  have hB : completionSubfunctorRestrict B S hS f T' T h ≫ (completionSubfunctor B S hS F T).ι =
      (completionSubfunctor B S hS F' T').ι ≫ Functor.whiskerRight f uliftFunctor.{u + 1} := rfl
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hA).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (toSheafify_comp_completionSheafToAmbient B S hS F hF T)).trans <|
    hB.trans <| (congrArg (· ≫ Functor.whiskerRight f uliftFunctor.{u + 1})
      (toSheafify_comp_completionSheafToAmbient B S hS F' hF' T').symm).trans
      (Category.assoc _ _ _)

end Completion

section SmallerBase

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- The morphism `(A ⟶ V ⟶ S) ⟶ (V ⟶ S)` of the big fppf site of `S` underlying an object `A` of
the big fppf site of `V`. -/
abbrev smallerBaseStructureHom (A : BigFppfOver B V hV) :
    (Over.map g).obj A ⟶ (Over.mk g : BigFppfOver B S hS) :=
  Over.homMk A.hom

/-- The representable presheaf of an object `A` of the big fppf site of `V`, viewed over `S`
together with its morphism to the representable presheaf of `V`. -/
abbrev smallerBaseYonedaOver (A : BigFppfOver B V hV) :
    Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mk (yoneda.map (smallerBaseStructureHom B V S hV hS g A))

/-- **The representable presheaf over a smaller base.** The representable presheaf of an object
`A` of the big fppf site of `V` is the presheaf that Stacks 04SG attaches to the representable
presheaf of `A` viewed over `S`, with its morphism to the representable presheaf of `V`: a
morphism `W ⟶ A` over `V` is a morphism `W ⟶ A` over `S` whose composite with `A ⟶ V` is the
structure morphism of `W`. -/
def smallerBaseInverseYonedaIso (A : BigFppfOver B V hV) :
    yoneda.obj A ≅ smallerBaseInverse B V S hV hS g (smallerBaseYonedaOver B V S hV hS g A) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun f => ⟨(Over.map g).map f, Over.OverMorphism.ext (Over.w f)⟩
      invFun := fun x => Over.homMk x.1.left (congrArg CommaMorphism.left x.2)
      left_inv := fun _ => Over.OverMorphism.ext rfl
      right_inv := fun _ => Subtype.ext (Over.OverMorphism.ext rfl) })
    (fun _ => by ext; exact Subtype.ext (Over.OverMorphism.ext rfl))

/-- **Open subspaces over a smaller base.** For a presheaf `X` over the representable presheaf of
`g : V ⟶ S` and a set `W` of points of `X`, the subfunctor of `X_V` cut out by the inverse image of
`W` under `AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph` is the presheaf attached to
the subfunctor of `X` cut out by `W` (Stacks 03BZ). -/
def smallerBaseInverseOpenIso
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (W : Set (points B S hS X.left)) :
    (openSubspaceOfPoints B V hV (smallerBaseInverse B V S hV hS g X)
        (pointsSmallerBaseInverseHomeomorph B V S hV hS g X ⁻¹' W)).toFunctor ≅
      smallerBaseInverse B V S hV hS g
        (Over.mk ((openSubspaceOfPoints B S hS X.left W).ι ≫ X.hom)) :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ⟨⟨x.1.1,
        (mem_openSubspaceOfPoints_smallerBaseInverse_iff B V S hV hS g X W x.1).1 x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩,
        (mem_openSubspaceOfPoints_smallerBaseInverse_iff B V S hV hS g X W ⟨y.1.1, y.2⟩).2 y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- The identification `AlgebraicGeometry.Space.smallerBaseInverseOpenIso` is compatible with the
inclusions into `X_V`. -/
@[reassoc (attr := simp)]
theorem smallerBaseInverseOpenIso_hom_comp
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (W : Set (points B S hS X.left)) :
    (smallerBaseInverseOpenIso B V S hV hS g X W).hom ≫
        (smallerBasePresheafEquivalence B V S hV hS g).inverse.map
          (Over.homMk (openSubspaceOfPoints B S hS X.left W).ι :
            Over.mk ((openSubspaceOfPoints B S hS X.left W).ι ≫ X.hom) ⟶ X) =
      (openSubspaceOfPoints B V hV (smallerBaseInverse B V S hV hS g X)
        (pointsSmallerBaseInverseHomeomorph B V S hV hS g X ⁻¹' W)).ι := rfl

/-- The universe lift of `X_V`, viewed over `S`, is the universe lift of `X`. -/
def smallerBaseAmbientIso
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    FormalSpace.smallerBaseULift B V S hV hS g
        (smallerBaseInverse B V S hV hS g X ⋙ uliftFunctor.{u + 1}) ≅
      X.left ⋙ uliftFunctor.{u + 1} :=
  FormalSpace.smallerBaseULiftWhiskerIso B V S hV hS g _ ≪≫
    Functor.isoWhiskerRight ((smallerBasePresheafForgetIso B V S hV hS g).app _ ≪≫
      smallerBaseInverseRelocalizeIso B V S hV hS g X) uliftFunctor.{u + 1}

/-- The identification `AlgebraicGeometry.Space.smallerBaseAmbientIso` is natural. -/
theorem smallerBaseAmbientIso_hom_naturality
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y) :
    FormalSpace.smallerBaseULiftMap B V S hV hS g
        (Functor.whiskerRight ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f)
          uliftFunctor.{u + 1}) ≫ (smallerBaseAmbientIso B V S hV hS g Y).hom =
      (smallerBaseAmbientIso B V S hV hS g X).hom ≫
        Functor.whiskerRight f.left uliftFunctor.{u + 1} := by
  ext T p
  obtain ⟨φ, ⟨x⟩⟩ := p
  exact (congrArg ULift.up (NatTrans.naturality_apply f.left
    (smallerBaseFactorHom B V S hV hS g (Over.w φ)).op x.1)).symm

/-- **Completion over a smaller base, with the morphism into the ambient space.** The
identification `AlgebraicGeometry.Artin.ContractionSituation.smallerBaseCompletionIso` of the
sheaf attached to `X_{V,/T_V}` with `X_{/T}` is compatible with the morphisms into the universe
lifts of `X_V` and of `X`. -/
theorem smallerBaseCompletionIso_hom_comp_completionSheafToAmbient
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S hS X.left) (T : Set (points B S hS X.left)) :
    (Artin.ContractionSituation.smallerBaseCompletionIso B V S hV hS g X hX T).hom.hom ≫
        completionSheafToAmbient B S hS X.left (FormalSpace.isSheaf_comp_uliftFunctor B S hS hX) T =
      FormalSpace.smallerBaseULiftMap B V S hV hS g
          (completionSheafToAmbient B V hV (smallerBaseInverse B V S hV hS g X)
            (FormalSpace.isSheaf_comp_uliftFunctor B V hV
              (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX))
            (smallerBaseInverseSet B V S hV hS g X T)) ≫
        (smallerBaseAmbientIso B V S hV hS g X).hom := by
  rw [completionSheafToAmbient_eq B S hS hX.isSheaf, completionSheafToAmbient_eq B V hV
    (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX).isSheaf,
    ← FormalSpace.smallerBaseULiftMap_comp]
  change ((FormalSpace.smallerBaseULiftMap B V S hV hS g _ ≫
    (completionSubfunctorSmallerBaseIso B V S hV hS g X T).hom.left) ≫
      (completionSheafIsoSubfunctor B S hS hX.isSheaf T).inv) ≫
        (completionSheafIsoSubfunctor B S hS hX.isSheaf T).hom ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1

/-- A morphism into the completion over `V`, transported to `S` and composed with
`AlgebraicGeometry.Artin.ContractionSituation.smallerBaseCompletionIso`, is compatible with the
morphisms into the universe lifts of `X_V` and of `X`. -/
theorem smallerBaseSheafFunctor_map_comp_completionSheafToAmbient
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S hS X.left) (T : Set (points B S hS X.left))
    {P : Sheaf (BigFppfOver.topology B V hV) (Type (u + 1))}
    (φ : P ⟶ completionSheaf B V hV (smallerBaseInverse B V S hV hS g X)
      (smallerBaseInverseSet B V S hV hS g X T)) :
    ((FormalSpace.smallerBaseSheafFunctor B V S hV hS g).map φ ≫
        (Artin.ContractionSituation.smallerBaseCompletionIso B V S hV hS g X hX T).hom).hom ≫
      completionSheafToAmbient B S hS X.left (FormalSpace.isSheaf_comp_uliftFunctor B S hS hX) T =
      FormalSpace.smallerBaseULiftMap B V S hV hS g
          (φ.hom ≫ completionSheafToAmbient B V hV (smallerBaseInverse B V S hV hS g X)
            (FormalSpace.isSheaf_comp_uliftFunctor B V hV
              (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX))
            (smallerBaseInverseSet B V S hV hS g X T)) ≫
        (smallerBaseAmbientIso B V S hV hS g X).hom :=
  (congrArg (FormalSpace.smallerBaseULiftMap B V S hV hS g φ.hom ≫ ·)
    (smallerBaseCompletionIso_hom_comp_completionSheafToAmbient B V S hV hS g X hX T)).trans
    (FormalSpace.smallerBaseULiftMap_comp_assoc B V S hV hS g _ _ _)

/-- The identification `AlgebraicGeometry.Space.smallerBaseInverseRelocalizeIso` is natural. -/
@[reassoc]
theorem smallerBaseInverseRelocalizeIso_hom_naturality
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y) :
    (OverShriek.relocalizePresheafFunctor g).map
        ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) ≫
        (smallerBaseInverseRelocalizeIso B V S hV hS g Y).hom =
      (smallerBaseInverseRelocalizeIso B V S hV hS g X).hom ≫ f.left := by
  ext T y
  obtain ⟨⟨ψ, s⟩, hψ⟩ := y
  exact (NatTrans.naturality_apply f.left (smallerBaseFactorHom B V S hV hS g hψ).op s.1).symm

/-- The homeomorphism `AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph` is natural. -/
theorem pointsSmallerBaseInverseHomeomorph_naturality
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y)
    (y : points B V hV (smallerBaseInverse B V S hV hS g X)) :
    pointsSmallerBaseInverseHomeomorph B V S hV hS g Y
        (pointsMap B V hV _ ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) y) =
      pointsMap B S hS X.left f.left (pointsSmallerBaseInverseHomeomorph B V S hV hS g X y) := by
  rw [pointsSmallerBaseInverseHomeomorph_apply, pointsSmallerBaseInverseHomeomorph_apply,
    pointsRelocalize_naturality]
  simpa only [pointsMap_comp, Function.comp_apply] using
    congrFun (congrArg (pointsMap B S hS _)
      (smallerBaseInverseRelocalizeIso_hom_naturality B V S hV hS g f))
      (pointsRelocalize B V S hV hS g _ y)

/-- **Properness over a smaller base.** A morphism of presheaves over the representable presheaf
of `g : V ⟶ S` whose underlying morphism of algebraic spaces over `S` is proper induces a proper
morphism of the attached algebraic spaces over `V`. -/
theorem isProper_smallerBaseInverse_map
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X.left) (hY : IsAlgebraicSpace B S hS Y.left)
    (hf : IsProper B S hS f.left) :
    IsProper B V hV ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) := by
  rw [← isProper_relocalize_iff B V hV S hS g
    (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX)
    (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g Y hY)]
  refine isProper_of_arrowIso B S hS f.left _ (smallerBaseInverseRelocalizeIso B V S hV hS g X).inv
    (smallerBaseInverseRelocalizeIso B V S hV hS g Y).inv ?_ hf
  rw [Iso.inv_comp_eq, ← Category.assoc, ← smallerBaseInverseRelocalizeIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- If `f : X ⟶ Y` carries the set `T` of points of `X` into the set `T'` of points of `Y`, then
the morphism over `V` attached to `f` carries the set of points corresponding to `T` into the set
of points corresponding to `T'`. -/
theorem smallerBaseInverseSet_subset
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y)
    {T : Set (points B S hS X.left)} {T' : Set (points B S hS Y.left)}
    (h : T ⊆ pointsMap B S hS X.left f.left ⁻¹' T') :
    smallerBaseInverseSet B V S hV hS g X T ⊆
      pointsMap B V hV _ ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) ⁻¹'
        smallerBaseInverseSet B V S hV hS g Y T' := by
  intro y hy
  change pointsSmallerBaseInverseHomeomorph B V S hV hS g Y _ ∈ T'
  rw [pointsSmallerBaseInverseHomeomorph_naturality]
  exact h hy

/-- **Completion over a smaller base is natural.** The identifications
`AlgebraicGeometry.Artin.ContractionSituation.smallerBaseCompletionIso` carry the morphism of
completions over `V` induced by `f` to the morphism of completions over `S` induced by `f`. -/
theorem smallerBaseSheafFunctor_map_completionSheafRestrict_comp
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X.left) (hY : IsAlgebraicSpace B S hS Y.left)
    (T : Set (points B S hS X.left)) (T' : Set (points B S hS Y.left))
    (h : T ⊆ pointsMap B S hS X.left f.left ⁻¹' T') :
    (FormalSpace.smallerBaseSheafFunctor B V S hV hS g).map
        (completionSheafRestrict B V hV
          ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f)
          _ _ (smallerBaseInverseSet_subset B V S hV hS g f h)) ≫
        (Artin.ContractionSituation.smallerBaseCompletionIso B V S hV hS g Y hY T').hom =
      (Artin.ContractionSituation.smallerBaseCompletionIso B V S hV hS g X hX T).hom ≫
        completionSheafRestrict B S hS f.left T T' h := by
  have hXV := isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX
  have := mono_completionSheafToAmbient B S hS Y.left
    (FormalSpace.isSheaf_comp_uliftFunctor B S hS hY) T'
  apply ObjectProperty.hom_ext
  rw [← cancel_mono (completionSheafToAmbient B S hS Y.left
    (FormalSpace.isSheaf_comp_uliftFunctor B S hS hY) T')]
  have R : ((Artin.ContractionSituation.smallerBaseCompletionIso B V S hV hS g X hX T).hom ≫
      completionSheafRestrict B S hS f.left T T' h).hom ≫
      completionSheafToAmbient B S hS Y.left (FormalSpace.isSheaf_comp_uliftFunctor B S hS hY) T' =
      FormalSpace.smallerBaseULiftMap B V S hV hS g
        (completionSheafToAmbient B V hV (smallerBaseInverse B V S hV hS g X)
          (FormalSpace.isSheaf_comp_uliftFunctor B V hV hXV)
          (smallerBaseInverseSet B V S hV hS g X T)) ≫
        (smallerBaseAmbientIso B V S hV hS g X).hom ≫
          Functor.whiskerRight f.left uliftFunctor.{u + 1} :=
    (congrArg
      ((Artin.ContractionSituation.smallerBaseCompletionIso B V S hV hS g X hX T).hom.hom ≫ ·)
      (completionSheafRestrict_comp_completionSheafToAmbient B S hS f.left T T' h
        (FormalSpace.isSheaf_comp_uliftFunctor B S hS hX)
        (FormalSpace.isSheaf_comp_uliftFunctor B S hS hY))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ Functor.whiskerRight f.left uliftFunctor.{u + 1})
          (smallerBaseCompletionIso_hom_comp_completionSheafToAmbient B V S hV hS g X hX T)).trans
          (Category.assoc _ _ _)))
  refine (smallerBaseSheafFunctor_map_comp_completionSheafToAmbient
    B V S hV hS g Y hY T' _).trans (Eq.trans ?_ R.symm)
  rw [completionSheafRestrict_comp_completionSheafToAmbient B V hV
    ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) _ _
    (smallerBaseInverseSet_subset B V S hV hS g f h)
    (FormalSpace.isSheaf_comp_uliftFunctor B V hV hXV)
    (FormalSpace.isSheaf_comp_uliftFunctor B V hV
      (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g Y hY)),
    ← FormalSpace.smallerBaseULiftMap_comp_assoc, smallerBaseAmbientIso_hom_naturality]

end SmallerBase

end AlgebraicGeometry.Space

end
