module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification.IdealBasis
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The stages of a finite type algebra system and their colimit

For a finite type algebra system over an ideal basis, this file builds the stages over the base
formal space, the diagram of their spectra, the induced map from the colimit of the stages to
the base and the identification of each stage as a base change of that colimit. It also defines
the morphisms of finite type algebra systems and their category, and records the fppf covering
facts used afterwards. It is part of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteTypeClassification`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open CartesianColimit

universe u v w

namespace FiniteTypeAlgebraSystem

attribute [local instance] bigFppfOver_subcanonical

attribute [local instance] Sheaf.sheafifiedYoneda_full Sheaf.sheafifiedYoneda_faithful

attribute [local instance] idealBasisFunctor_final

theorem contains_spec_systemStage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (i : I) :
    B.Contains (Spec (CommRingCat.of (P.B.obj (Opposite.op i)))) := by
  let K := idealBasisIndex J i
  let T := Q.diagram.obj K
  have hT : B.Contains ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).obj T) := by
    change _ < B.cutoff
    exact T.1.left.property
  have hbase : (Spec (CommRingCat.of (A ⧸ K.1))).size < B.cutoff := by
    rw [← Scheme.size_congr (Q.quotientIso K)]
    exact hT
  let : Algebra (A ⧸ K.1) (P.B.obj (Opposite.op i)) :=
    (P.algebraMap i).toAlgebra
  have hft : Algebra.FiniteType (A ⧸ K.1) (P.B.obj (Opposite.op i)) :=
    RingHom.finiteType_algebraMap.mp (P.finiteType i)
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit _ _ hbase

noncomputable def systemStageBaseMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (i : I) :
    Spec (CommRingCat.of (P.B.obj (Opposite.op i))) ⟶
      B.inclusion.obj (B.obj hS) := by
  let K := idealBasisIndex J i
  let T := Q.diagram.obj K
  let specMap :
      Spec (CommRingCat.of (P.B.obj (Opposite.op i))) ⟶
        Spec (CommRingCat.of (A ⧸ J.ideal i)) :=
    Spec.map (CommRingCat.ofHom (P.algebraMap i))
  exact specMap ≫ (Q.quotientIso K).inv ≫
    B.inclusion.map ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj T).hom

noncomputable def systemStageSchemeMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
  (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    Spec (CommRingCat.of (P.B.obj (Opposite.op i))) ⟶
      Spec (CommRingCat.of (P.B.obj (Opposite.op j))) :=
  Spec.map (P.B.map (homOfLE h).op)

theorem systemStageSchemeMap_algebraMap_compat
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    systemStageSchemeMap P h ≫
        Spec.map (CommRingCat.ofHom (P.algebraMap j)) =
      Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫
        Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h))) := by
  let t : CommRingCat.of (P.B.obj (Opposite.op j)) ⟶
      CommRingCat.of (P.B.obj (Opposite.op i)) := P.B.map (homOfLE h).op
  let aᵢ : CommRingCat.of (A ⧸ J.ideal i) ⟶
      CommRingCat.of (P.B.obj (Opposite.op i)) := CommRingCat.ofHom (P.algebraMap i)
  let aⱼ : CommRingCat.of (A ⧸ J.ideal j) ⟶
      CommRingCat.of (P.B.obj (Opposite.op j)) := CommRingCat.ofHom (P.algebraMap j)
  let q : CommRingCat.of (A ⧸ J.ideal j) ⟶
      CommRingCat.of (A ⧸ J.ideal i) :=
    CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h))
  have hcomp : aⱼ ≫ t = q ≫ aᵢ := CommRingCat.hom_ext (P.compatible h)
  calc
    _ = Spec.map (aⱼ ≫ t) := by
      dsimp [systemStageSchemeMap, t, aⱼ]
      exact (Spec.map_comp aⱼ t).symm
    _ = Spec.map (q ≫ aᵢ) := by rw [hcomp]
    _ = _ := by rw [Spec.map_comp]

theorem quotientPresentation_transition_inv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (Q : WeakIdealColimitPresentation B S hS A X)
    {K L : WeakIdeals A} (f : K ⟶ L) :
    Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show L.1 ≤ K.1 from leOfHom f))) ≫
      (Q.quotientIso L).inv =
        (Q.quotientIso K).inv ≫
          (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (Q.diagram.map f) := by
  apply (cancel_mono (Q.quotientIso L).hom).1
  calc
    _ = Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show L.1 ≤ K.1 from leOfHom f))) := by simp
    _ = (Q.quotientIso K).inv ≫
        ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (Q.diagram.map f) ≫
          (Q.quotientIso L).hom) := by
            rw [Q.quotientIso_natural f]
            simp
    _ = _ := by simp

theorem quotientPresentation_isThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (Q : WeakIdealColimitPresentation B S hS A X)
    {K L : WeakIdeals A} (f : K ⟶ L) :
    Stacks.Thickenings.IsThickening ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      (Q.diagram.map f)) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor f.le))
  have hq : Stacks.Thickenings.IsThickening q := quotient_specMap_isThickening K.2 L.2 f.le
  have : IsClosedImmersion q := hq.1
  have : Surjective q := ⟨hq.2⟩
  have he : (AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map (Q.diagram.map f) =
      (Q.quotientIso K).hom ≫ q ≫ (Q.quotientIso L).inv := by
    rw [show q ≫ _ = _ from quotientPresentation_transition_inv B S hS A Q f,
      Iso.hom_inv_id_assoc]
  rw [he]
  exact ⟨inferInstance, Scheme.Hom.surjective _⟩

noncomputable def systemStageObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (i : I) : AlgebraicGeometry.BigAffineFppf B S hS := by
  let K := idealBasisIndex J i
  let U : B.Schemes := B.obj (contains_spec_systemStage B S hS A P Q i)
  let fS : B.inclusion.obj U ⟶
      B.inclusion.obj (B.obj hS) :=
    systemStageBaseMap B S hS A P Q i
  let Uover : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk fS)
  refine ⟨Uover, ?_⟩
  change IsAffine (Spec (CommRingCat.of (P.B.obj (Opposite.op i))))
  infer_instance

/-- A pushout of a quotient homomorphism is the quotient by the extended kernel. -/
theorem surjective_and_ker_eq_of_isPushout
    {R S T U : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
    {a : S ⟶ U} {b : T ⟶ U} (h : IsPushout f g a b)
    (hf : Function.Surjective f.hom) :
    Function.Surjective b.hom ∧
      RingHom.ker b.hom = (RingHom.ker f.hom).map g.hom := by
  let K := (RingHom.ker f.hom).map g.hom
  let q : T ⟶ CommRingCat.of (T ⧸ K) := CommRingCat.ofHom (Ideal.Quotient.mk K)
  let a' : S ⟶ CommRingCat.of (T ⧸ K) := CommRingCat.ofHom
    (f.hom.liftOfSurjective hf ⟨q.hom.comp g.hom, by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.hom hx)⟩)
  have hw : f ≫ a' = g ≫ q := CommRingCat.hom_ext (RingHom.liftOfSurjective_comp _ _ _)
  have hq : IsPushout f g a' q := isPushout_of_surjective_of_ker_eq f g a' q hw hf
    (Ideal.Quotient.mk_surjective) (Ideal.mk_ker)
  let e := h.isoIsPushout S T hq
  have hb : b ≫ e.hom = q := h.inr_isoIsPushout_hom S T hq
  constructor
  · rw [← h.inr_isoIsPushout_inv S T hq]
    exact (ConcreteCategory.bijective_of_isIso e.inv).2.comp Ideal.Quotient.mk_surjective
  · have he := RingHom.ker_comp_of_injective b.hom
      (ConcreteCategory.bijective_of_isIso e.hom).1
    rw [← he]
    change RingHom.ker ((b ≫ e.hom).hom) = K
    rw [hb]
    exact Ideal.mk_ker

/-- Cartesian squares of affine spectra give precisely the quotient transition axioms. -/
noncomputable def algebraSystemOfCartesianSpecDiagram
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I)
    (R : Iᵒᵖ ⥤ CommRingCat.{u})
    (a : ∀ i, A ⧸ J.ideal i →+* R.obj (Opposite.op i))
    (hft : ∀ i, (a i).FiniteType)
    (hcart : ∀ ⦃i j : I⦄ (h : i ≤ j),
      IsPullback (Spec.map (CommRingCat.ofHom (a i)))
        (Spec.map (R.map (homOfLE h).op))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h))))
        (Spec.map (CommRingCat.ofHom (a j)))) :
    FiniteTypeAlgebraSystem A I J := by
  have hpush (i j : I) (h : i ≤ j) :
      IsPushout (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h)))
        (CommRingCat.ofHom (a j)) (CommRingCat.ofHom (a i))
        (R.map (homOfLE h).op) := by
    have hcart' : IsPullback (R.map (homOfLE h).op).op
        (CommRingCat.ofHom (a i)).op (CommRingCat.ofHom (a j)).op
        (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h))).op :=
      IsPullback.of_map_of_faithful Scheme.Spec (hcart h).flip
    exact hcart'.unop
  have hquot (i j : I) (h : i ≤ j) :=
    surjective_and_ker_eq_of_isPushout (hpush i j h) (by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk _ b, Ideal.Quotient.factor_mk (J.antitone h) b⟩)
  refine
    { B := R
      algebraMap := a
      finiteType := hft
      compatible := fun {i j} h => ?_
      transition_surjective := fun {i j} h => (hquot i j h).1
      transition_ker := fun {i j} h => ?_ }
  · exact congrArg CommRingCat.Hom.hom (hpush _ _ h).w.symm
  · simpa only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker, Ideal.map_map]
      using (hquot _ _ h).2

/-- Global sections recover an algebra system from cartesian finite type affine schemes. -/
noncomputable def algebraSystemOfAffineSchemeDiagram
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] (J : IdealBasis A I)
    (D : I ⥤ Scheme.{u}) (hD : ∀ i, IsAffine (D.obj i))
    (a : ∀ i, D.obj i ⟶ Spec (CommRingCat.of (A ⧸ J.ideal i)))
    (hft : ∀ i, LocallyOfFiniteType (a i))
    (hcart : ∀ ⦃i j : I⦄ (h : i ≤ j),
      IsPullback (a i) (D.map (homOfLE h))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h)))) (a j)) :
    FiniteTypeAlgebraSystem A I J := by
  letI : ∀ i, IsAffine (D.obj i) := hD
  let R := D.op ⋙ Scheme.Γ
  let b (i : I) : A ⧸ J.ideal i →+* R.obj (Opposite.op i) :=
    (Scheme.Spec.preimage ((D.obj i).isoSpec.inv ≫ a i)).unop.hom
  have hb (i : I) : Spec.map (CommRingCat.ofHom (b i)) =
      (D.obj i).isoSpec.inv ≫ a i := Scheme.Spec.map_preimage _
  have ht {i j : I} (g : i ⟶ j) : Spec.map (R.map g.op) =
      (D.obj i).isoSpec.inv ≫ D.map g ≫ (D.obj j).isoSpec.hom := by
    change Spec.map (D.map g).appTop = _
    rw [← Scheme.isoSpec_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  refine algebraSystemOfCartesianSpecDiagram J R b (fun i => ?_) (fun {i j} h => ?_)
  · have : LocallyOfFiniteType (a i) := hft i
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})
      (φ := CommRingCat.ofHom (b i))).mp
    have hfi : LocallyOfFiniteType ((D.obj i).isoSpec.inv ≫ a i) := inferInstance
    rw [hb]
    exact hfi
  · apply (hcart h).of_iso (D.obj i).isoSpec (Iso.refl _)
      (D.obj j).isoSpec (Iso.refl _)
    · rw [hb]
      simp
    · rw [ht]
      simp
    · simp
    · rw [hb]
      simp

/-- The reduction condition is the pushout property of the transition square
of rings. -/
private theorem transition_isPushout
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    IsPushout
      (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h)))
      (CommRingCat.ofHom (P.algebraMap j))
      (CommRingCat.ofHom (P.algebraMap i)) (P.B.map (homOfLE h).op) := by
  apply isPushout_of_surjective_of_ker_eq
  · exact CommRingCat.hom_ext (P.compatible h).symm
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.factor_mk (J.antitone h) a⟩
  · exact P.transition_surjective h
  · simpa only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker,
      Ideal.map_map] using P.transition_ker h

/-- Passing to spectra identifies the transition square with a fibre square. -/
private theorem transition_isPullback
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (P.algebraMap i)))
      (systemStageSchemeMap P h)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (J.antitone h))))
      (Spec.map (CommRingCat.ofHom (P.algebraMap j))) :=
  ((transition_isPushout P h).op.map Scheme.Spec).flip

private theorem systemStage_finiteType
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J) (i : I) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (P.algebraMap i))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (P.algebraMap i))) :=
  ⟨HasRingHomProperty.Spec_iff.mpr (P.finiteType i), inferInstance⟩

theorem systemStageSchemeMap_base
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    {i j : I} (h : i ≤ j) :
    systemStageSchemeMap P h ≫ systemStageBaseMap B S hS A P Q j =
      systemStageBaseMap B S hS A P Q i := by
  let f := (idealBasisFunctor J).map (homOfLE h)
  have hw := congrArg (fun g => B.inclusion.map g)
    (Over.w ((AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map (Q.diagram.map f)))
  dsimp only [systemStageBaseMap]
  rw [← Category.assoc, systemStageSchemeMap_algebraMap_compat, Category.assoc]
  refine congrArg (fun k => Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫ k) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ _)
    (quotientPresentation_transition_inv B S hS A Q f)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  congr 1

noncomputable def systemStageMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    {i j : I} (h : i ≤ j) :
    systemStageObject B S hS A P Q i ⟶ systemStageObject B S hS A P Q j := by
  refine ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk (systemStageSchemeMap P h)) ?_)
  apply ObjectProperty.hom_ext
  exact systemStageSchemeMap_base B S hS A P Q h

/-- The spectra of the algebra system form a diagram over the base scheme. -/
noncomputable def systemDiagram
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    I ⥤ AlgebraicGeometry.BigAffineFppf B S hS where
  obj := systemStageObject B S hS A P Q
  map f := systemStageMap B S hS A P Q f.le
  map_id i := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (P.B.map (𝟙 (Opposite.op i))) = 𝟙 _
    rw [P.B.map_id, Spec.map_id]
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (P.B.map (f ≫ g).op) = _
    rw [op_comp, P.B.map_comp, Spec.map_comp]
    rfl

private theorem systemDiagram_isThickening
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    {i j : I} (f : i ⟶ j) :
    Stacks.Thickenings.IsThickening ((AlgebraicGeometry.BigAffineFppf.toScheme B S hS).map
      ((systemDiagram B S hS A P Q).map f)) := by
  change Stacks.Thickenings.IsThickening (Spec.map (P.B.map f.op))
  exact transition_specMap_isThickening P f.le

/-- The algebra structure maps give a morphism to the base quotient diagram. -/
noncomputable def systemDiagramToBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    systemDiagram B S hS A P Q ⟶ idealBasisFunctor J ⋙ Q.diagram where
  app i := ObjectProperty.homMk (Over.homMk
    (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫
        (Q.quotientIso (idealBasisIndex J i)).inv)) (by
          apply ObjectProperty.hom_ext
          rfl))
  naturality i j f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change systemStageSchemeMap P f.le ≫
        (Spec.map (CommRingCat.ofHom (P.algebraMap j)) ≫
          (Q.quotientIso (idealBasisIndex J j)).inv) =
      (Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫
          (Q.quotientIso (idealBasisIndex J i)).inv) ≫ _
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ (Q.quotientIso (idealBasisIndex J j)).inv)
      (systemStageSchemeMap_algebraMap_compat P f.le)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => Spec.map (CommRingCat.ofHom (P.algebraMap i)) ≫ k)
      (quotientPresentation_transition_inv B S hS A Q
        ((idealBasisFunctor J).map f))).trans ?_
    exact (Category.assoc _ _ _).symm

private theorem systemDiagramToBase_equifibered
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (Functor.whiskerRight (systemDiagramToBase B S hS A P Q)
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS)).Equifibered := by
  intro i j f
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have : T.Faithful := by dsimp [T, AlgebraicGeometry.BigFppfOver.toScheme]; infer_instance
  have : ReflectsLimitsOfShape WalkingCospan T := by
    dsimp [T, AlgebraicGeometry.BigFppfOver.toScheme, AlgebraicGeometry.BigFppfOver.forget]
    infer_instance
  apply IsPullback.of_map_of_faithful T
  apply (transition_isPullback P f.le).flip.of_iso
    (Iso.refl _) (Iso.refl _)
    (Q.quotientIso (idealBasisIndex J i)).symm
    (Q.quotientIso (idealBasisIndex J j)).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact quotientPresentation_transition_inv B S hS A Q
      ((idealBasisFunctor J).map f)

noncomputable def systemSheafMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :=
  Functor.whiskerRight (systemDiagramToBase B S hS A P Q)
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))

theorem systemSheafMap_equifibered
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    (systemSheafMap B S hS A P Q).Equifibered := by
  have : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) := by
    dsimp [Sheaf.sheafifiedYoneda]
    infer_instance
  exact (systemDiagramToBase_equifibered B S hS A P Q).whiskerRight
    (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS))

/-- Cofinality identifies the colimit over the selected basis with the base
formal space. -/
noncomputable def basisColimitIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (J : IdealBasis A I)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    colimit (idealBasisFunctor J ⋙ Q.diagram ⋙
      AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) ≅ X :=
  Functor.Final.colimitIso (idealBasisFunctor J) _ ≪≫ Q.colimitIso.symm

/-- The compatible structural morphisms induce a map from the colimit to `X`. -/
noncomputable def systemColimitMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [IsDirected I (· ≤ ·)] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) :
    colimit (systemDiagram B S hS A P Q ⋙
      AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) ⟶ X :=
  colim.map (systemSheafMap B S hS A P Q) ≫ (basisColimitIso B S hS A J Q).hom

/-- Each stage is recovered as a base change of the colimit. -/
private theorem systemColimitMap_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X) (i : I) :
    IsPullback
      (colimit.ι (systemDiagram B S hS A P Q ⋙
        AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) i)
      ((systemSheafMap B S hS A P Q).app i)
      (systemColimitMap B S hS A P Q)
      (colimit.ι (idealBasisFunctor J ⋙ Q.diagram ⋙
        AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) i ≫
          (basisColimitIso B S hS A J Q).hom) := by
  have : IsConnected (Under i) := IsFiltered.isConnected _
  apply (equifibered_colimit_isPullback (systemSheafMap B S hS A P Q)
    (systemSheafMap_equifibered B S hS A P Q) i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (basisColimitIso B S hS A J Q)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

theorem systemColimitMap_baseChange_stage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    {X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {J : IdealBasis A I} (P : FiniteTypeAlgebraSystem A I J)
    (Q : WeakIdealColimitPresentation B S hS A X)
    (i : I) (U : AlgebraicGeometry.BigFppfOver B S hS)
    (u : U ⟶ (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj
      (Q.diagram.obj (idealBasisIndex J i))) :
    ∃ (V : AlgebraicGeometry.BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).obj V ⟶
        colimit (systemDiagram B S hS A P Q ⋙
          AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)))
      (q : V ⟶ U),
      IsPullback p
        ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map q)
        (systemColimitMap B S hS A P Q)
        ((Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)).map u ≫
          colimit.ι (idealBasisFunctor J ⋙ Q.diagram ⋙
            AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)) i ≫
              (basisColimitIso B S hS A J Q).hom) ∧
      IsAffineHom ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFiniteType ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map q) := by
  have : (_root_.AlgebraicGeometry.schemeSizeBelow B.cutoff).IsClosedUnderLimitsOfShape
      WalkingCospan := by
    refine ⟨?_⟩
    intro Z hZ
    obtain ⟨p⟩ := hZ
    let f := p.diag.map WalkingCospan.Hom.inl
    let g := p.diag.map WalkingCospan.Hom.inr
    have hp := IsPullback.of_isLimit_cone p.isLimit
    let e : Z ≅ pullback f g := hp.isoPullback
    change Z.size < B.cutoff
    rw [Scheme.size_congr e]
    exact Scheme.size_pullback_lt f g
      (p.prop_diag_obj WalkingCospan.left) (p.prop_diag_obj WalkingCospan.right)
  let E := Sheaf.sheafifiedYoneda (AlgebraicGeometry.BigFppfOver.topology B S hS)
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let a := (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).map
    ((systemDiagramToBase B S hS A P Q).app i)
  have hft : LocallyOfFiniteType (T.map a) := by
    have h1 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (P.algebraMap i))) :=
      (systemStage_finiteType P i).1
    have h2 : LocallyOfFiniteType (Q.quotientIso (idealBasisIndex J i)).inv := inferInstance
    exact MorphismProperty.comp_mem _ _ _ h1 h2
  have ha : IsAffineHom (T.map a) := by
    have h1 : IsAffineHom (Spec.map (CommRingCat.ofHom (P.algebraMap i))) := inferInstance
    have h2 : IsAffineHom (Q.quotientIso (idealBasisIndex J i)).inv := inferInstance
    exact (inferInstance : MorphismProperty.IsMultiplicative (@IsAffineHom.{u})).comp_mem
      _ _ h1 h2
  have : PreservesLimitsOfShape WalkingCospan E := by
    dsimp [E, Sheaf.sheafifiedYoneda]
    infer_instance
  let p := E.map (pullback.fst a u) ≫ colimit.ι (systemDiagram B S hS A P Q ⋙
    AlgebraicGeometry.BigAffineFppf.inclusion B S hS ⋙ E) i
  have hp := ((IsPullback.of_hasPullback a u).map E).paste_horiz
    (systemColimitMap_isPullback B S hS A P Q i)
  have hq := (IsPullback.of_hasPullback a u).map T
  exact ⟨pullback a u, p, pullback.snd a u, hp, MorphismProperty.of_isPullback hq ha,
    MorphismProperty.of_isPullback hq hft⟩

/-- The kernel and surjectivity axioms identify each later stage modulo the
earlier base ideal with the earlier stage. -/
private noncomputable def transitionQuotientEquiv
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) :
    ((P.B.obj (Opposite.op j)) ⧸
      (J.ideal i).map ((P.algebraMap j).comp (Ideal.Quotient.mk (J.ideal j))))
      ≃+* (P.B.obj (Opposite.op i)) := by
  let f : P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i) :=
    (P.B.map (homOfLE h).op).hom
  exact (Ideal.quotEquivOfEq (P.transition_ker h).symm).trans
    (f.quotientKerEquivOfSurjective (P.transition_surjective h))

private theorem transitionQuotientEquiv_mk
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) (b : P.B.obj (Opposite.op j)) :
    transitionQuotientEquiv P h
      (Ideal.Quotient.mk _ b) = (P.B.map (homOfLE h).op).hom b := by
  simp [transitionQuotientEquiv]

/-- Basis indices defining the same ideal give isomorphic ring stages. -/
private noncomputable def transitionRingEquiv_of_ideal_eq
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P : FiniteTypeAlgebraSystem A I J)
    {i j : I} (h : i ≤ j) (hij : J.ideal i = J.ideal j) :
    P.B.obj (Opposite.op j) ≃+* P.B.obj (Opposite.op i) := by
  let f : P.B.obj (Opposite.op j) →+* P.B.obj (Opposite.op i) :=
    (P.B.map (homOfLE h).op).hom
  have hker : RingHom.ker f = ⊥ := by
    rw [P.transition_ker h]
    rw [hij, ← Ideal.map_map (Ideal.Quotient.mk (J.ideal j)) (P.algebraMap j),
      Ideal.map_quotient_self, Ideal.map_bot]
  exact RingEquiv.ofBijective f
    ⟨(RingHom.injective_iff_ker_eq_bot f).2 hker,
      P.transition_surjective h⟩

/-- A compatible family of homomorphisms of finite type algebra systems. -/
structure Hom {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    (P Q : FiniteTypeAlgebraSystem A I J) where
  /-- The natural transformation between the underlying inverse systems of rings. -/
  nat : P.B ⟶ Q.B
  /-- The components are compatible with the structure homomorphisms. -/
  base : ∀ i, (nat.app (Opposite.op i)).hom.comp (P.algebraMap i) = Q.algebraMap i

/-- A morphism of finite type algebra systems is determined by its underlying natural
transformation, the compatibility with the structure homomorphisms being a proposition. -/
theorem Hom.ext_nat {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I}
    {P Q : FiniteTypeAlgebraSystem A I J} {f g : Hom P Q}
    (h : f.nat = g.nat) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Finite type algebra systems over a fixed weak ideal basis form a category, whose morphisms are
the compatible families of homomorphisms `Hom`. -/
instance {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : Type v} [Preorder I] {J : IdealBasis A I} :
    Category (FiniteTypeAlgebraSystem A I J) where
  Hom := Hom
  id P := ⟨𝟙 P.B, by intro i; rfl⟩
  comp f g := ⟨f.nat ≫ g.nat, by
    intro i
    simpa only [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.comp_assoc,
      f.base i] using g.base i⟩
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

private theorem singleton_mem_bigFppf_topology
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X Y : B.Schemes} (f : Y ⟶ X)
    (hs : Surjective (B.inclusion.map f)) (he : Etale (B.inclusion.map f)) :
    Sieve.generate (Presieve.singleton f) ∈ B.topology X := by
  have hEt : Presieve.singleton (B.inclusion.map f) ∈
      Scheme.etalePrecoverage (B.inclusion.obj X) := by
    let : Surjective (B.inclusion.map f) := hs
    exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})
      (B.inclusion.map f)).2 ⟨Scheme.Hom.surjective _, he⟩
  let E : Covering B.Schemes := ⟨X, PreZeroHypercover.singleton f⟩
  have hE : _root_.AlgebraicGeometry.IsFppfCovering E := by
    change (PreZeroHypercover.singleton f).presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj X)
    simpa only [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton] using
      AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage _ hEt
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative E hE
  have hpre : E.2.presieve₀ ∈ B.precoverage X := by
    obtain ⟨hX, hComb⟩ := hEquiv
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  simpa [E, PreZeroHypercover.presieve₀_singleton] using
    (Precoverage.generate_mem_toGrothendieck hpre)

private theorem isLocallySurjective_of_surjective_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hs : (MorphismProperty.relative (uliftYoneda.{u + 1})
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f)
    (he : (MorphismProperty.relative (uliftYoneda.{u + 1})
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS))) f) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) f := by
  constructor
  intro T y
  let ξ : (uliftYoneda.{u + 1}).obj T ⟶ G := uliftYonedaEquiv.symm y
  let q := hs.rep.snd ξ
  have hbase := singleton_mem_bigFppf_topology B q.left
    (hs.property_snd ξ) (he.property ξ (hs.rep.fst ξ) q (hs.rep.isPullback ξ))
  have hcover : Sieve.generate (Presieve.singleton q) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS T := by
    change Sieve.generate (Presieve.singleton q) ∈ B.topology.over (B.obj hS) T
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact hbase
  apply (AlgebraicGeometry.BigFppfOver.topology B S hS).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨⟩
  refine ⟨uliftYonedaEquiv (hs.rep.fst ξ), ?_⟩
  have hw := congrArg uliftYonedaEquiv (hs.rep.isPullback ξ).w
  have hn := uliftYonedaEquiv_naturality ξ q.op
  exact (uliftYonedaEquiv_comp _ _).symm.trans (hw.trans
    (by simpa only [q, Quiver.Hom.unop_op, ξ, Equiv.apply_symm_apply] using hn.symm))

private lemma small_sections_of_representable_cover
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
    (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type (u + 1)}
    (hF : Presheaf.IsSheaf J F) {U : C} (a : (uliftYoneda.{u + 1}).obj U ⟶ F)
    [Presheaf.IsLocallySurjective J a] (T : C) : Small.{u} (F.obj (Opposite.op T)) := by
  let E := equivSmallModel.{u} C
  let encode : F.obj (Opposite.op T) →
      (V : SmallModel.{u} C) → (E.inverse.obj V ⟶ T) → (E.inverse.obj V ⟶ U) → Prop :=
    fun x V g t ↦ a.app _ ⟨t⟩ = F.map g.op x
  apply small_of_injective (f := encode)
  intro x y h
  apply hF.isSeparated _ _ (Presheaf.imageSieve_mem J a x) x y
  intro V g hg
  obtain ⟨t, ht⟩ := hg
  change ULift (V ⟶ U) at t
  let e := E.unitIso.app V
  have hx : encode x (E.functor.obj V) (e.inv ≫ g) (e.inv ≫ t.down) := by
    dsimp [encode]
    rw [F.map_comp, types_comp_apply, ← ht]
    exact a.naturality_apply e.inv.op t
  have hy : encode y (E.functor.obj V) (e.inv ≫ g) (e.inv ≫ t.down) := by
    rw [← h]
    exact hx
  have hxy : F.map e.inv.op (F.map g.op x) = F.map e.inv.op (F.map g.op y) := by
    simpa only [encode, op_comp, F.map_comp, types_comp_apply] using hx.symm.trans hy
  have hinj : Function.Injective (F.map e.inv.op) :=
    CategoryTheory.injective_of_mono (F.map e.inv.op)
  exact hinj hxy

private lemma relativelyRepresentable_of_fullyFaithful_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (L : D ⥤ E) [L.Full] [L.Faithful]
    {X Y : D} (f : X ⟶ Y)
    (hf : (G ⋙ L).relativelyRepresentable (L.map f)) :
    G.relativelyRepresentable f := by
  intro U g
  obtain ⟨V, q, p, hp⟩ := hf (L.map g)
  refine ⟨V, q, L.preimage p, ?_⟩
  apply IsPullback.of_map_of_faithful L
  simpa only [Functor.map_preimage, Functor.comp_obj, Functor.comp_map] using hp

private lemma relative_of_fullyFaithful_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (L : D ⥤ E) [L.Full] [L.Faithful]
    [PreservesLimitsOfShape WalkingCospan L]
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y)
    (hf : P.relative (G ⋙ L) (L.map f)) : P.relative G f := by
  refine ⟨relativelyRepresentable_of_fullyFaithful_map G L f hf.rep, ?_⟩
  intro U V g p q hp
  exact hf.property (L.map g) (L.map p) q (hp.map L)

end FiniteTypeAlgebraSystem

end AlgebraicGeometry.FormalSpace

end
