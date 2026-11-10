module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.RingTheory.SpreadingOut.Smooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. A
morphism over one stage which is locally of finite presentation and becomes smooth over the limit
is smooth after base change to some later stage.

## Main definitions

* `AlgebraicGeometry.baseChangeAffineAlgebraDiagram`,
  `AlgebraicGeometry.baseChangeAffineAlgebraCocone` and
  `AlgebraicGeometry.baseChangeAffineAlgebraPresentation`: the coordinate algebras of the base
  changes of an affine scheme over a stage, presented as a filtered colimit.

## Main results

* `AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange` descends smoothness from
  the inverse limit to a finite stage.

## Implementation notes

Schemes over the chosen stage and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` means that `i` is a later stage than `i₀`
in the cofiltered indexing category. The source uses a directed indexing set; the categorical
formulation applies to a cofiltered category in the same universe as the schemes, as in Mathlib's
theory of cofiltered limits with affine transition morphisms. This ensures that the filtered
colimits of affine coordinate rings used in the source are computed on underlying sets. A
categorical limit in `Scheme.{u}` for an index category larger than universe `u` need not have
this property.

## References

* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Smoothness on affine charts -/

/-- On affine schemes smoothness of a morphism is smoothness of the map of global section
rings. -/
private lemma smooth_iff_appTop_of_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : Smooth f ↔ f.appTop.hom.Smooth :=
  HasRingHomProperty.iff_of_isAffine (P := @Smooth)

/-- A pushout square of commutative rings identifies its right-hand map with the inclusion of the
left factor into the tensor product, so smoothness transfers between them. -/
private lemma smooth_of_isPushout_tensor {R S B C : Type u} [CommRing R] [CommRing S]
    [CommRing B] [CommRing C] [Algebra R S] [Algebra R B] (β : S →+* C) (γ : B →+* C)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom β) (CommRingCat.ofHom γ))
    (hs : (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B).Smooth) : β.Smooth := by
  let H₀ := CommRingCat.isPushout_tensorProduct R S B
  let e := H₀.isoIsPushout _ _ H
  have hcomp : e.hom.hom.comp Algebra.TensorProduct.includeLeftRingHom = β :=
    congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of C ↦ f.hom)
      (H₀.inl_isoIsPushout_hom _ _ H)
  rw [← hcomp]
  exact hs.comp (RingHom.Smooth.of_bijective e.commRingCatIsoToRingEquiv.bijective)

/-- The converse direction of `AlgebraicGeometry.smooth_of_isPushout_tensor`. -/
private lemma smooth_tensor_of_isPushout {R S B C : Type u} [CommRing R] [CommRing S]
    [CommRing B] [CommRing C] [Algebra R S] [Algebra R B] (β : S →+* C) (γ : B →+* C)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom β) (CommRingCat.ofHom γ)) (hs : β.Smooth) :
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B).Smooth := by
  let H₀ := CommRingCat.isPushout_tensorProduct R S B
  let e := H₀.isoIsPushout _ _ H
  have hcomp : e.inv.hom.comp β = Algebra.TensorProduct.includeLeftRingHom :=
    congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of (S ⊗[R] B) ↦ f.hom)
      (H₀.inl_isoIsPushout_inv _ _ H)
  rw [← hcomp]
  exact hs.comp (RingHom.Smooth.of_bijective e.symm.commRingCatIsoToRingEquiv.bijective)

/-- For a base change of affine schemes along an affine morphism, smoothness of the base-changed
morphism is smoothness of the inclusion of the left factor into the tensor product of the
coordinate rings. -/
private lemma smooth_baseChange_iff_tensor {S T : Scheme.{u}} (g : T ⟶ S) (X Y : Over S)
    (f : X ⟶ Y) [IsAffine X.left] [IsAffine Y.left] [IsAffineHom g]
    [Algebra Γ(Y.left, ⊤) Γ(X.left, ⊤)] [Algebra Γ(Y.left, ⊤) Γ(pullback g Y.hom, ⊤)]
    (hX : algebraMap Γ(Y.left, ⊤) Γ(X.left, ⊤) = f.left.appTop.hom)
    (hY : algebraMap Γ(Y.left, ⊤) Γ(pullback g Y.hom, ⊤) = (pullback.snd g Y.hom).appTop.hom) :
    Smooth ((Over.pullback g).map f).left ↔
      (Algebra.TensorProduct.includeLeftRingHom :
        Γ(pullback g Y.hom, ⊤) →+*
          Γ(pullback g Y.hom, ⊤) ⊗[Γ(Y.left, ⊤)] Γ(X.left, ⊤)).Smooth := by
  have : MorphismProperty.RespectsIso (@Smooth) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have H := isPushout_appTop_of_isPullback (baseChangeMap_isPullback g X Y f)
  have H' : IsPushout
      (CommRingCat.ofHom (algebraMap Γ(Y.left, ⊤) Γ(pullback g Y.hom, ⊤)))
      (CommRingCat.ofHom (algebraMap Γ(Y.left, ⊤) Γ(X.left, ⊤)))
      (CommRingCat.ofHom (baseChangeMap g X Y f).appTop.hom)
      (CommRingCat.ofHom (pullback.snd g X.hom).appTop.hom) := by
    rw [hX, hY]
    convert H using 1 <;> rfl
  rw [← baseChangeMap_prop_iff (@Smooth) g X Y f, smooth_iff_appTop_of_affine]
  exact ⟨smooth_tensor_of_isPushout _ _ H', smooth_of_isPushout_tensor _ _ H'⟩

/-- Smoothness of the tensor-product map out of a base algebra is smoothness of the inclusion of
the left factor. -/
private lemma smooth_tensorMap_ofId_iff_includeLeft {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] :
    (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).toRingHom.Smooth ↔
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B).Smooth := by
  let e := Algebra.TensorProduct.rid R R A
  have heq : (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).comp e.toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B) := by
    ext
    simp [e, Algebra.TensorProduct.rid_tmul]
  have hcomp : (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).toRingHom =
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B).comp
        e.toRingEquiv.toRingHom := congrArg AlgHom.toRingHom heq.symm
  have hcomp' : (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) =
      (Algebra.TensorProduct.map (AlgHom.id R A)
        (Algebra.ofId R B)).toRingHom.comp e.symm.toRingEquiv.toRingHom := by
    rw [hcomp]
    ext a
    simp [e, Algebra.TensorProduct.rid_tmul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hcomp']
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective e.symm.toRingEquiv.bijective) h
  · rw [hcomp]
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective e.toRingEquiv.bijective) h

/-- Smoothness of the inclusion of the left factor of a tensor product transfers along an
algebra isomorphism of that factor. -/
private lemma smooth_includeLeft_of_algEquiv {R A S B : Type u} [CommRing R] [CommRing A]
    [CommRing S] [CommRing B] [Algebra R A] [Algebra R S] [Algebra R B] (e : A ≃ₐ[R] S)
    (h : (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B).Smooth) :
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B).Smooth := by
  let eT := Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[R] B)
  have hq : (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B) =
      eT.toRingEquiv.toRingHom.comp
        ((Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B).comp
          e.symm.toRingEquiv.toRingHom) := by
    ext s
    simp [eT, Algebra.TensorProduct.congr_apply]
  rw [hq]
  exact RingHom.Smooth.comp
    (RingHom.Smooth.comp (RingHom.Smooth.of_bijective e.symm.toRingEquiv.bijective) h)
    (RingHom.Smooth.of_bijective eT.toRingEquiv.bijective)

/-- Smoothness of the inclusion of the left factor of a tensor product is invariant under an
algebra isomorphism of that factor. -/
private lemma smooth_includeLeft_congr {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S]
    [CommRing B] [Algebra R A] [Algebra R S] [Algebra R B] (e : A ≃ₐ[R] S) :
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B).Smooth ↔
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B).Smooth :=
  ⟨smooth_includeLeft_of_algEquiv e, smooth_includeLeft_of_algEquiv e.symm⟩

/-! ### The coordinate algebras of a limit of affine schemes over a spectrum -/

/-- The coordinate algebras of a limiting cone of affine schemes over the spectrum of a ring form
a colimiting cocone of algebras. -/
noncomputable def isColimit_affineOverSpecCone {J : Type u} [Category.{u} J]
    [IsConnected J] {R : Type u} [CommRing R] (E : J ⥤ Over (Spec (.of R))) (c : Cone E)
    (hc : IsLimit c) (hE : ∀ j : J, IsAffine (E.obj j).left) :
    IsColimit (coconeLeftOpOfCone ((algΓ (.of R)).mapCone c)) := by
  apply isColimitCoconeLeftOpOfCone
  have hΓ : IsLimit ((Over.post Scheme.Γ.rightOp).mapCone c) := by
    apply isLimitOfReflects (Over.forget _)
    have (j : J) : IsAffine ((E ⋙ Over.forget _).obj j) := hE j
    let hBase : IsLimit ((Over.forget _).mapCone c) := isLimitOfPreserves (Over.forget _) hc
    have : IsAffine (((Over.forget _).mapCone c).pt) := Scheme.isAffine_of_isLimit _ hBase
    exact isLimitOfPreserves Scheme.Γ.rightOp hBase
  let e := (Scheme.ΓSpecIso (.of R)).inv.op
  have : IsIso e := inferInstance
  have : (Over.map e).IsEquivalence := inferInstance
  have : PreservesLimits (Over.map e) := inferInstance
  have : (Over.mapIso (asIso e)).functor.IsEquivalence :=
    (Over.mapIso (asIso e)).isEquivalence_functor
  have : PreservesLimitsOfSize.{u, u} (Over.mapIso (asIso e)).functor := inferInstance
  have : PreservesLimitsOfShape J (Over.mapIso (asIso e)).functor := inferInstance
  have : PreservesLimit (E ⋙ Over.post Scheme.Γ.rightOp) (Over.mapIso (asIso e)).functor :=
    (inferInstance : PreservesLimitsOfShape J (Over.mapIso (asIso e)).functor).preservesLimit
  have hMap : IsLimit ((Over.map e).mapCone ((Over.post Scheme.Γ.rightOp).mapCone c)) :=
    Classical.choice ((show PreservesLimit (E ⋙ Over.post Scheme.Γ.rightOp)
      (Over.mapIso (asIso e)).functor from inferInstance).preserves hΓ)
  have hUnder : IsLimit ((Over.opEquivOpUnder _).functor.mapCone
      ((Over.map e).mapCone ((Over.post Scheme.Γ.rightOp).mapCone c))) :=
    isLimitOfPreserves (Over.opEquivOpUnder _).functor hMap
  exact isLimitOfPreserves (commAlgCatEquivUnder _).inverse.op hUnder

variable {I : Type u} [Category.{u} I]

/-- The diagram of coordinate algebras of the base changes of an affine scheme over a stage. -/
noncomputable def baseChangeAffineAlgebraDiagram (D : I ⥤ Scheme.{u}) (i₀ : I)
    (Y : Over (D.obj i₀)) [IsAffine Y.left] : (Over i₀)ᵒᵖ ⥤ CommAlgCat.{u} Γ(Y.left, ⊤) :=
  ((Over.post D ⋙ Over.pullback Y.hom) ⋙
    (Over.map Y.left.isoSpec.hom ⋙ algΓ (CommRingCat.of Γ(Y.left, ⊤)))).leftOp

/-- The cocone on `AlgebraicGeometry.baseChangeAffineAlgebraDiagram` whose point is the coordinate
algebra of the base change to the limit. -/
noncomputable def baseChangeAffineAlgebraCocone (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (Y : Over (D.obj i₀)) [IsAffine Y.left] :
    Cocone (baseChangeAffineAlgebraDiagram D i₀ Y) :=
  coconeLeftOpOfCone ((Over.map Y.left.isoSpec.hom ⋙
    algΓ (CommRingCat.of Γ(Y.left, ⊤))).mapCone
      ((Over.pullback Y.hom).mapCone ((Over.conePost D i₀).obj c)))

/-- The coordinate algebra of the base change to the limit is the filtered colimit of the
coordinate algebras of the base changes to the later stages. -/
noncomputable def isColimit_baseChangeAffineAlgebraCocone [IsCofiltered I] (D : I ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (Y : Over (D.obj i₀)) [IsAffine Y.left] :
    IsColimit (baseChangeAffineAlgebraCocone D c i₀ Y) := by
  have : IsConnected (Over i₀) := IsCofiltered.isConnected (C := Over i₀)
  let E : Over i₀ ⥤ Over (Spec (.of Γ(Y.left, ⊤))) :=
    Over.post D ⋙ Over.pullback Y.hom ⋙ Over.map Y.left.isoSpec.hom
  let cY := (Over.pullback Y.hom).mapCone ((Over.conePost D i₀).obj c)
  let cSpec := (Over.map Y.left.isoSpec.hom).mapCone cY
  have hcSpec : IsLimit cSpec :=
    isLimitOfPreserves (Over.map Y.left.isoSpec.hom)
      (isLimitOfPreserves (Over.pullback Y.hom) (Over.isLimitConePost i₀ hc))
  have hE (j : Over i₀) : IsAffine (E.obj j).left := by
    change IsAffine (pullback (D.map j.hom) Y.hom)
    infer_instance
  exact isColimit_affineOverSpecCone E cSpec hcSpec hE

/-- The colimit presentation of the coordinate algebra of the base change to the limit. -/
noncomputable def baseChangeAffineAlgebraPresentation [IsCofiltered I] (D : I ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (Y : Over (D.obj i₀)) [IsAffine Y.left] :
    ColimitPresentation (Over i₀)ᵒᵖ (baseChangeAffineAlgebraCocone D c i₀ Y).pt where
  diag := baseChangeAffineAlgebraDiagram D i₀ Y
  ι := (baseChangeAffineAlgebraCocone D c i₀ Y).ι
  isColimit := isColimit_baseChangeAffineAlgebraCocone D c hc i₀ Y

/-- The structure map of the coordinate algebra of the base change of `Y` to the stage `j` is
the map on global sections induced by the second projection of the fibre product. -/
@[simp]
lemma baseChangeAffineAlgebraDiagram_algebraMap (D : I ⥤ Scheme.{u}) (i₀ : I)
    (Y : Over (D.obj i₀)) [IsAffine Y.left] (j : Over i₀) :
    (algebraMap Γ(Y.left, ⊤) ((baseChangeAffineAlgebraDiagram D i₀ Y).obj (.op j))) =
      (pullback.snd (D.map j.hom) Y.hom).appTop.hom := by
  change ((Scheme.ΓSpecIso Γ(Y.left, ⊤)).inv ≫
    (pullback.snd (D.map j.hom) Y.hom ≫ Y.left.toSpecΓ).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The structure map of the coordinate algebra of the base change of `Y` to the limit is the
map on global sections induced by the second projection of the fibre product. -/
@[simp]
lemma baseChangeAffineAlgebraCocone_algebraMap (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (Y : Over (D.obj i₀)) [IsAffine Y.left] :
    (algebraMap Γ(Y.left, ⊤) (baseChangeAffineAlgebraCocone D c i₀ Y).pt) =
      (pullback.snd (c.π.app i₀) Y.hom).appTop.hom := by
  change ((Scheme.ΓSpecIso Γ(Y.left, ⊤)).inv ≫
    (pullback.snd (c.π.app i₀) Y.hom ≫ Y.left.toSpecΓ).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The underlying ring of the colimit coordinate algebra is the ring of global sections of the
base change to the limit. -/
noncomputable def baseChangeAffineAlgebraCocone_ringEquiv (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i₀ : I) (Y : Over (D.obj i₀)) [IsAffine Y.left] :
    (baseChangeAffineAlgebraCocone D c i₀ Y).pt ≃+* Γ(pullback (c.π.app i₀) Y.hom, ⊤) :=
  RingEquiv.refl _

/-- The underlying ring of a stage's coordinate algebra is the ring of global sections of the base
change to that stage. -/
noncomputable def baseChangeAffineAlgebraDiagram_ringEquiv (D : I ⥤ Scheme.{u}) (i₀ : I)
    (Y : Over (D.obj i₀)) [IsAffine Y.left] (j : Over i₀) :
    (baseChangeAffineAlgebraDiagram D i₀ Y).obj (.op j) ≃+*
      Γ(pullback (D.map j.hom) Y.hom, ⊤) :=
  RingEquiv.refl _

/-! ### The affine case -/

/-- Affine source and target suffice for the algebraic descent of smoothness; the ambient base
scheme itself can be arbitrary. -/
@[sga "3 VIB 10.1" "special case"]
private lemma exists_smooth_baseChange_of_affine_source_target [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X Y : Over (D.obj i₀)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f.left]
    (h : Smooth ((Over.pullback (c.π.app i₀)).map f).left) :
    ∃ j : Over i₀, Smooth ((Over.pullback (D.map j.hom)).map f).left := by
  let R := Γ(Y.left, ⊤)
  let B := Γ(X.left, ⊤)
  let : Algebra R B := f.left.appTop.hom.toAlgebra
  let φ : R →ₐ[R] B := Algebra.ofId R B
  have hφ : φ.toRingHom.FinitePresentation := finitePresentation_appTop_of_affine f.left
  let A := (baseChangeAffineAlgebraCocone D c i₀ Y).pt
  let pres := baseChangeAffineAlgebraPresentation D c hc i₀ Y
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  let : Algebra R Γ(pullback (c.π.app i₀) Y.hom, ⊤) :=
    (pullback.snd (c.π.app i₀) Y.hom).appTop.hom.toAlgebra
  let eAalg : A ≃ₐ[R] Γ(pullback (c.π.app i₀) Y.hom, ⊤) :=
    AlgEquiv.ofRingEquiv (f := baseChangeAffineAlgebraCocone_ringEquiv D c i₀ Y) fun r ↦
      RingHom.congr_fun (baseChangeAffineAlgebraCocone_algebraMap D c i₀ Y) r
  obtain ⟨j, hj⟩ := RingHom.Smooth.exists_baseChange_smooth_of_colimitPresentation pres φ hφ
    (smooth_tensorMap_ofId_iff_includeLeft.2 ((smooth_includeLeft_congr (B := B) eAalg).2
      ((smooth_baseChange_iff_tensor (c.π.app i₀) X Y f rfl rfl).1 h)))
  let j' := j.unop
  let : Algebra R Γ(pullback (D.map j'.hom) Y.hom, ⊤) :=
    (pullback.snd (D.map j'.hom) Y.hom).appTop.hom.toAlgebra
  let eAjalg : (pres.diag.obj j) ≃ₐ[R] Γ(pullback (D.map j'.hom) Y.hom, ⊤) :=
    AlgEquiv.ofRingEquiv (f := baseChangeAffineAlgebraDiagram_ringEquiv D i₀ Y j') fun r ↦
      RingHom.congr_fun (baseChangeAffineAlgebraDiagram_algebraMap D i₀ Y j') r
  exact ⟨j', (smooth_baseChange_iff_tensor (D.map j'.hom) X Y f rfl rfl).2
    ((smooth_includeLeft_congr (B := B) eAjalg).1 (smooth_tensorMap_ofId_iff_includeLeft.1 hj))⟩

/-! ### Descending smoothness -/

/-- Smoothness can be cancelled along a postcomposed open immersion. -/
private theorem Smooth.hasOfPostcompProperty_isOpenImmersion :
    MorphismProperty.HasOfPostcompProperty (@Smooth : MorphismProperty Scheme.{u})
      @IsOpenImmersion := by
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
  intro A B q W hq
  have : Smooth q := hq
  infer_instance

/-- Local finite presentation can be cancelled along a postcomposed open immersion. -/
private theorem LocallyOfFinitePresentation.hasOfPostcompProperty_isOpenImmersion :
    MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion := by
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
  intro A B q W hq
  have : LocallyOfFinitePresentation q := hq
  infer_instance

/-- **Stacks Project, Tag 0C0C.** If a locally finitely presented morphism over a stage of a
cofiltered inverse system becomes smooth over the limit, it becomes smooth at some later
stage. -/
@[stacks 0C0C, ega "IV 17.7.8" "(ii) smooth", ega "IV 17.12.6" "f smooth ⇒ ∃λ"]
theorem exists_smooth_baseChange_of_smooth_limitBaseChange
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (hc : IsLimit c)
    [Smooth ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      Smooth ((Over.pullback (D.map g)).map f₀).left := by
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  have := Smooth.hasOfPostcompProperty_isOpenImmersion.{u}
  have := LocallyOfFinitePresentation.hasOfPostcompProperty_isOpenImmersion.{u}
  obtain ⟨C, hCfinite, hCaffine, V, b, p, hVaffine, hb, hp⟩ :=
    exists_finite_affine_charts f₀.left
  have : Finite C.I₀ := hCfinite
  have (j : C.I₀) : IsAffine (C.X j) := hCaffine j
  have (j : C.I₀) : IsAffine (V j) := hVaffine j
  have (j : C.I₀) : IsOpenImmersion (b j) := hb j
  let UX (j : C.I₀) : Over (D.obj i₀) := Over.mk (C.f j ≫ X₀.hom)
  let VY (j : C.I₀) : Over (D.obj i₀) := Over.mk (b j ≫ Y₀.hom)
  let a (j : C.I₀) : UX j ⟶ X₀ := Over.homMk (C.f j)
  let b₀ (j : C.I₀) : VY j ⟶ Y₀ := Over.homMk (b j)
  let p₀ (j : C.I₀) : UX j ⟶ VY j := Over.homMk (p j) (by
    change p j ≫ (b j ≫ Y₀.hom) = C.f j ≫ X₀.hom
    rw [← Category.assoc, hp, Category.assoc, Over.w])
  have (j : C.I₀) : IsAffine (UX j).left := hCaffine j
  have (j : C.I₀) : IsAffine (VY j).left := hVaffine j
  have hoa (j : C.I₀) : IsOpenImmersion (a j).left := C.map_prop j
  have hob (j : C.I₀) : IsOpenImmersion (b₀ j).left := hb j
  have hp₀ (j : C.I₀) : p₀ j ≫ b₀ j = a j ≫ f₀ := by
    ext
    exact hp j
  have hfp (j : C.I₀) : LocallyOfFinitePresentation (p₀ j).left := by
    have := hoa j
    have : LocallyOfFinitePresentation ((p₀ j).left ≫ (b₀ j).left) := by
      rw [show (p₀ j).left ≫ (b₀ j).left = (a j).left ≫ f₀.left from hp j]
      infer_instance
    exact MorphismProperty.HasOfPostcompProperty.of_postcomp _ _ (hob j) this
  have hchart : ∀ j : C.I₀, ∃ (i : I) (g : i ⟶ i₀),
      Smooth ((Over.pullback (D.map g)).map (p₀ j)).left := by
    intro j
    have := hoa j
    have := hob j
    have := hfp j
    obtain ⟨j', hj'⟩ := exists_smooth_baseChange_of_affine_source_target D c hc i₀
      (UX j) (VY j) (p₀ j) (prop_overPullback_chart (@Smooth) (c.π.app i₀) X₀ Y₀ (UX j) (VY j)
        f₀ (a j) (b₀ j) (p₀ j) (hp₀ j) inferInstance)
    exact ⟨j'.left, j'.hom, hj'⟩
  obtain ⟨i', g, hg⟩ := common_stage_of_finite_prop (@Smooth) D i₀ UX VY p₀ hchart
  exact ⟨i', g, prop_overPullback_of_charts (@Smooth) (fun q hq => by have := hq; infer_instance)
    (D.map g) X₀ Y₀ f₀ UX VY a b₀ p₀ hp₀ C.exists_eq hg⟩

end AlgebraicGeometry
