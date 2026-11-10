module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductFunctorial
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealProductColimit
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdicProduct

/-!
# The inclusions of a finite coproduct of formal spectra

Let `S` be a scheme contained in a big fppf site `B`, and let `A k` be a finite family of weakly
admissible linearly topologized rings, each carrying a quotient system `E k`. The coproduct of
the formal spectra `Spf (A k)` is the formal spectrum of the product ring `∏ A k`:
`AlgebraicGeometry.FormalSpace.sigmaWeakIdealColimitPresentation` presents it over `∏ A k`, and
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.formalSpectrumIso` turns that
presentation into an isomorphism with the formal spectrum of the induced quotient system.

This file identifies the inclusions of the coproduct under that isomorphism: the inclusion of
the `k`-th summand is the formal spectrum of the projection `∏ A k → A k`. That is the shape in
which a finite product of rings enters the proof of **Stacks 0ANG**, where axiom (3) of
Situation 0CBA is applied to a finite disjoint union of affine formal algebraic spaces.

## Main definitions

* `AlgebraicGeometry.FormalSpace.sigmaFormalSpectrumPresentation`: the weak-ideal presentation
  of the coproduct of the formal spectra over the product ring.
* `AlgebraicGeometry.FormalSpace.sigmaFormalSpectrumIso`: the coproduct of the formal spectra,
  identified with the formal spectrum of the product ring.
* `AlgebraicGeometry.FormalSpace.piProjContinuousHom`: the projection `∏ A k → A k`, as a
  continuous homomorphism over `S` between the quotient systems.

## Main results

* `AlgebraicGeometry.FormalSpace.ι_sigmaFormalSpectrumIso_hom`: the inclusion of the `k`-th
  summand, read through `sigmaFormalSpectrumIso`, is the formal spectrum of the `k`-th
  projection.

These are statements about the site and about products of rings, not results of the Stacks
project, so they carry no `@[stacks]` registration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits TopologicalRing.pi_isLinearTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {K : Type u} [Finite K] (A : K → Type u) [∀ k, CommRing (A k)]
  [∀ k, TopologicalSpace (A k)] [∀ k, IsTopologicalRing (A k)]
  [∀ k, IsLinearTopology (A k) (A k)]
  (hA : ∀ k, TopologicalRing.IsWeaklyAdmissible (A k))
  (E : ∀ k, QuotientSystem B S hS (A k))

/-- The weak-ideal presentation of the coproduct of the formal spectra of a finite family of
weakly admissible rings, over the product of the rings. -/
def sigmaFormalSpectrumPresentation :
    WeakIdealColimitPresentation B S hS (∀ k, A k) (∐ fun k ↦ formalSpectrum (E k)) :=
  sigmaWeakIdealColimitPresentation B S hS A hA (fun k ↦ formalSpectrum (E k))
    fun k ↦ (E k).weakIdealColimitPresentation

/-- The coproduct of the formal spectra of a finite family of weakly admissible rings,
identified with the formal spectrum of the product ring for the quotient system induced by
`AlgebraicGeometry.FormalSpace.sigmaFormalSpectrumPresentation`. -/
def sigmaFormalSpectrumIso :
    (∐ fun k ↦ formalSpectrum (E k)) ≅
      formalSpectrum (sigmaFormalSpectrumPresentation B S hS A hA E).quotientSystem :=
  (sigmaFormalSpectrumPresentation B S hS A hA E).formalSpectrumIso

omit [∀ (k : K), TopologicalSpace (A k)] [∀ (k : K), IsTopologicalRing (A k)]
  [∀ (k : K), IsLinearTopology (A k) (A k)] in
/-- The ring-level computation behind the inclusions: the quotient map of the `k`-th projection
`∏ A k → A k` at a pair of compatible ideals factors through the quotient of the product by an
ideal, the product of the quotients of the factors and the canonical quotient map of the
`k`-th factor. -/
private theorem quotientMap_evalRingHom_eq (k : K) (J : Ideal (∀ k, A k)) (L : Ideal (A k))
    (h : J ≤ L.comap (Pi.evalRingHom A k)) (hJk : J.map (Pi.evalRingHom A k) ≤ L) :
    Ideal.quotientMap L (Pi.evalRingHom A k) h =
      ((Ideal.Quotient.factor hJk).comp
          (Pi.evalRingHom (fun k ↦ A k ⧸ J.map (Pi.evalRingHom A k)) k)).comp
        (quotPiEvalEquiv A J : _ →+* _) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
  simp [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

/-- The scheme-level computation behind the inclusions: the morphism of quotient spectra
induced by the `k`-th projection is the `k`-th inclusion of the stage of the presentation of
the coproduct, read through the identification of that stage with the spectrum of the
quotient of the product ring. -/
private theorem spec_quotientMap_evalRingHom (k : K)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex (∀ k, A k))
    (L : TopologicalRing.WeakIdealOfDefinitionIndex (A k))
    (h : J.1 ≤ L.1.comap (Pi.evalRingHom A k))
    (hJk : OrderDual.toDual L ⟶ (weakIdealsPiProj A hA k).obj (OrderDual.toDual J)) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (Pi.evalRingHom A k) h)) =
      (BigAffineFppf.toScheme B S hS).map ((E k).diagram.map hJk) ≫
        (BigAffineFppf.toScheme B S hS).map (BigAffineFppf.sigmaIncl B S hS
          (fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj (OrderDual.toDual J))) k) ≫
        ((sigmaFormalSpectrumPresentation B S hS A hA E).quotientIso
          (OrderDual.toDual J)).hom := by
  have hJk' : (OrderDual.toDual J).1.map (Pi.evalRingHom A k) ≤ L.1 := leOfHom hJk
  have h' : (OrderDual.toDual J).1 ≤ L.1.comap (Pi.evalRingHom A k) := h
  have e1 : (sigmaFormalSpectrumPresentation B S hS A hA E).quotientIso (OrderDual.toDual J) =
      sigmaWeakIdealQuotientIso B S hS A hA _
        (fun k ↦ (E k).weakIdealColimitPresentation.quotientIso) (OrderDual.toDual J) := rfl
  have e3 : (BigAffineFppf.toScheme B S hS).map ((E k).diagram.map hJk) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJk')) := rfl
  have e2 : (BigAffineFppf.toScheme B S hS).map (BigAffineFppf.sigmaIncl B S hS
        (fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj (OrderDual.toDual J))) k) ≫
      (BigAffineFppf.sigmaObjIsoSpecPi B S hS (Equiv.refl K)
        (fun k ↦ .of (A k ⧸ (OrderDual.toDual J).1.map (Pi.evalRingHom A k)))
        (fun k ↦ (E k).weakIdealColimitPresentation.quotientIso
          ((weakIdealsPiProj A hA k).obj (OrderDual.toDual J)))).hom =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom
        (fun k ↦ (A k ⧸ (OrderDual.toDual J).1.map (Pi.evalRingHom A k) : Type u)) k)) :=
    BigAffineFppf.toScheme_map_sigmaIncl_sigmaObjIsoSpecPi_hom B S hS
      (Equiv.refl K)
      (A := fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj (OrderDual.toDual J)))
      (fun k ↦ .of (A k ⧸ (OrderDual.toDual J).1.map (Pi.evalRingHom A k)))
      (fun k ↦ (E k).weakIdealColimitPresentation.quotientIso
        ((weakIdealsPiProj A hA k).obj (OrderDual.toDual J))) k
  have hring : Ideal.quotientMap L.1 (Pi.evalRingHom A k) h' =
      ((Ideal.Quotient.factor hJk').comp (Pi.evalRingHom
          (fun k ↦ (A k ⧸ (OrderDual.toDual J).1.map (Pi.evalRingHom A k) : Type u)) k)).comp
        (quotPiEvalEquiv A (OrderDual.toDual J).1 : _ →+* _) :=
    quotientMap_evalRingHom_eq A k (OrderDual.toDual J).1 L.1 h' hJk'
  have hlhs : Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (Pi.evalRingHom A k) h)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (Pi.evalRingHom A k) h')) := rfl
  have key : Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (Pi.evalRingHom A k) h')) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJk')) ≫
        (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom
          (fun k ↦ (A k ⧸ (OrderDual.toDual J).1.map (Pi.evalRingHom A k) : Type u)) k))) ≫
        Spec.map (CommRingCat.ofHom (quotPiEvalEquiv A (OrderDual.toDual J).1 : _ →+* _)) := by
    rw [Category.id_comp, hring, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp,
      Spec.map_comp, Category.assoc]
  rw [e1, sigmaWeakIdealQuotientIso_hom, e3, hlhs, key, ← e2]
  exact congrArg (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJk')) ≫ ·)
    (Category.assoc _ _ _)

/-- A morphism of the big affine fppf category over `S` is a morphism over `S`. -/
private theorem toScheme_map_comp_overHom {X Y : BigAffineFppf B S hS} (f : X ⟶ Y) :
    (BigAffineFppf.toScheme B S hS).map f ≫
        B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj Y)) =
      B.inclusion.map (Over.hom ((BigAffineFppf.inclusion B S hS).obj X)) :=
  (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (Over.w ((BigAffineFppf.inclusion B S hS).map f)))

/-- The compatibility with the structure morphisms to `S` of the `k`-th projection of a finite
product of rings, between the quotient system induced by
`AlgebraicGeometry.FormalSpace.sigmaFormalSpectrumPresentation` and the `k`-th quotient
system. -/
theorem piProj_overS (k : K)
    (J : TopologicalRing.WeakIdealOfDefinitionIndex (∀ k, A k))
    (L : TopologicalRing.WeakIdealOfDefinitionIndex (A k))
    (h : J.1 ≤ L.1.comap (Pi.evalRingHom A k)) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (Pi.evalRingHom A k) h)) ≫
        (sigmaFormalSpectrumPresentation B S hS A hA E).quotientSystem.overS J =
      (E k).overS L := by
  have hJk : OrderDual.toDual L ⟶ (weakIdealsPiProj A hA k).obj (OrderDual.toDual J) :=
    homOfLE (Ideal.map_le_iff_le_comap.mpr h)
  rw [spec_quotientMap_evalRingHom B S hS A hA E k J L h hJk,
    WeakIdealColimitPresentation.quotientSystem_overS]
  exact (Category.assoc _ _ _).trans <|
    (congrArg ((BigAffineFppf.toScheme B S hS).map ((E k).diagram.map hJk) ≫ ·)
      ((Category.assoc _ _ _).trans
        (congrArg ((BigAffineFppf.toScheme B S hS).map (BigAffineFppf.sigmaIncl B S hS
          (fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj (OrderDual.toDual J))) k) ≫ ·)
          (Iso.hom_inv_id_assoc _ _)))).trans <|
    (congrArg ((BigAffineFppf.toScheme B S hS).map ((E k).diagram.map hJk) ≫ ·)
      (toScheme_map_comp_overHom B S hS _)).trans (toScheme_map_comp_overHom B S hS _)

/-- The `k`-th projection of a finite product of weakly admissible rings, as a continuous
homomorphism over `S` from the quotient system induced by
`AlgebraicGeometry.FormalSpace.sigmaFormalSpectrumPresentation` to the `k`-th quotient
system. -/
def piProjContinuousHom (k : K) :
    ContinuousHom (sigmaFormalSpectrumPresentation B S hS A hA E).quotientSystem (E k) where
  toRingHom := Pi.evalRingHom A k
  continuous := continuous_apply k
  overS := piProj_overS B S hS A hA E k

/-- The ring homomorphism underlying `AlgebraicGeometry.FormalSpace.piProjContinuousHom` is the
`k`-th evaluation `Pi.evalRingHom A k`. -/
@[simp]
theorem piProjContinuousHom_toRingHom (k : K) :
    (piProjContinuousHom B S hS A hA E k).toRingHom = Pi.evalRingHom A k :=
  rfl

/-- The inclusions of the coproduct of a finite family of sheaves presented by weak ideals,
read through `AlgebraicGeometry.FormalSpace.sigmaWeakIdealColimitIso`: on the stage of the
`k`-th member at the projection of a weak ideal of definition `J` of the product, the `k`-th
inclusion is the `k`-th inclusion of the coproduct of affines forming the stage at `J`. -/
theorem ι_sigmaWeakIdealColimitIso_hom
    (D : ∀ k, WeakIdeals (A k) ⥤ BigAffineFppf B S hS) (Z : K → FppfSheaf B S hS)
    (hZ : ∀ k, Z k ≅ colimit (D k ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (k : K) (J : WeakIdeals (∀ k, A k)) :
    colimit.ι (D k ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ((weakIdealsPiProj A hA k).obj J) ≫
      (hZ k).inv ≫ Sigma.ι Z k ≫ (sigmaWeakIdealColimitIso B S hS A hA D Z hZ).hom =
    (BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (BigAffineFppf.sigmaIncl B S hS
          (fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J)) k) ≫
      colimit.ι (sigmaWeakIdealDiagram B S hS A hA D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) J := by
  let hfin : ∀ k, (weakIdealsPiProj A hA k).Final := final_weakIdealsPiProj A hA
  dsimp only [sigmaWeakIdealColimitIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [HasColimit.ι_isoOfNatIso_inv_assoc, Discrete.natIso_inv_app, Iso.trans_inv, Iso.trans_inv,
    Iso.symm_inv, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.Final.ι_colimitIso_inv_assoc, HasColimit.ι_isoOfNatIso_inv_assoc,
    sigmaWeakIdealSheafFamilyObjIso_inv_app]
  refine (Category.id_comp _).trans ?_
  rw [colimitFlipCompColimIsoColimitCompColim_ι_ι_inv_assoc, HasColimit.ι_isoOfNatIso_hom]
  exact ι_sigmaWeakIdealStageIso_hom_assoc B S hS A hA D J k _

/-- **The inclusions of a finite coproduct of formal spectra are the formal spectra of the
projections.** Under the identification
`AlgebraicGeometry.FormalSpace.sigmaFormalSpectrumIso` of the coproduct of the formal spectra
of a finite family of weakly admissible rings with the formal spectrum of their product, the
inclusion of the `k`-th summand is the formal spectrum of the `k`-th projection. -/
theorem ι_sigmaFormalSpectrumIso_hom (k : K) :
    Sigma.ι (fun k ↦ formalSpectrum (E k)) k ≫ (sigmaFormalSpectrumIso B S hS A hA E).hom =
      formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_pi A hA)
        (piProjContinuousHom B S hS A hA E k) := by
  let hfin : ∀ k, (weakIdealsPiProj A hA k).Final := final_weakIdealsPiProj A hA
  let G := BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  suffices key : ∀ J : WeakIdeals (∀ k, A k),
      formalSpectrumInclusion (E k) ((weakIdealsPiProj A hA k).obj J) ≫
          Sigma.ι (fun k ↦ formalSpectrum (E k)) k ≫ (sigmaFormalSpectrumIso B S hS A hA E).hom =
        formalSpectrumInclusion (E k) ((weakIdealsPiProj A hA k).obj J) ≫
          formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_pi A hA)
            (piProjContinuousHom B S hS A hA E k) by
    refine (cancel_epi (Functor.Final.colimitIso (weakIdealsPiProj A hA k)
      (formalSpectrumDiagram (E k))).hom).1 (colimit.hom_ext fun J ↦ ?_)
    exact (Functor.Final.ι_colimitIso_hom_assoc _ _ _ _).trans
      ((key J).trans (Functor.Final.ι_colimitIso_hom_assoc _ _ _ _).symm)
  intro J
  set P := sigmaFormalSpectrumPresentation B S hS A hA E
  have hstage : BigAffineFppf.sigmaIncl B S hS
        (fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj J)) k ≫ (P.stageIso J).hom =
      (piProjContinuousHom B S hS A hA E k).stageMap (OrderDual.ofDual J)
        (OrderDual.ofDual ((weakIdealsPiProj A hA k).obj J)) Ideal.le_comap_map := by
    apply (BigAffineFppf.toScheme B S hS).map_injective
    have hs := spec_quotientMap_evalRingHom B S hS A hA E k (OrderDual.ofDual J)
      (OrderDual.ofDual ((weakIdealsPiProj A hA k).obj J)) Ideal.le_comap_map (𝟙 _)
    have h0 := (congrArg (BigAffineFppf.toScheme B S hS).map ((E k).diagram.map_id
      (OrderDual.toDual (OrderDual.ofDual ((weakIdealsPiProj A hA k).obj J))))).trans
      ((BigAffineFppf.toScheme B S hS).map_id _)
    exact ((BigAffineFppf.toScheme B S hS).map_comp _ _).trans
      (((congrArg _ (P.toScheme_map_stageIso_hom J)).trans (Category.id_comp _).symm).trans
        ((congrArg (· ≫ _) h0.symm).trans hs.symm))
  have hl : formalSpectrumInclusion (E k) ((weakIdealsPiProj A hA k).obj J) ≫
      Sigma.ι (fun k ↦ formalSpectrum (E k)) k ≫ P.colimitIso.hom =
      G.map (BigAffineFppf.sigmaIncl B S hS
        (fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj J)) k) ≫
        colimit.ι (P.diagram ⋙ G) J :=
    (congrArg (formalSpectrumInclusion (E k) ((weakIdealsPiProj A hA k).obj J) ≫ ·)
      (Category.id_comp _).symm).trans
    (ι_sigmaWeakIdealColimitIso_hom B S hS A hA (fun k ↦ (E k).diagram)
      (fun k ↦ formalSpectrum (E k)) (fun k ↦ (E k).weakIdealColimitPresentation.colimitIso) k J)
  have hr := formalSpectrumMap_spec (TopologicalRing.isWeaklyAdmissible_pi A hA)
    (piProjContinuousHom B S hS A hA E k) (OrderDual.ofDual J)
    (OrderDual.ofDual ((weakIdealsPiProj A hA k).obj J)) Ideal.le_comap_map
  have hn := HasColimit.ι_isoOfNatIso_hom (Functor.isoWhiskerRight P.diagramIso G) J
  have hG : G.map (BigAffineFppf.sigmaIncl B S hS
        (fun k ↦ (E k).diagram.obj ((weakIdealsPiProj A hA k).obj J)) k) ≫
      G.map (P.stageIso J).hom =
      G.map ((piProjContinuousHom B S hS A hA E k).stageMap (OrderDual.ofDual J)
        (OrderDual.ofDual ((weakIdealsPiProj A hA k).obj J)) Ideal.le_comap_map) :=
    (G.map_comp _ _).symm.trans (congrArg G.map hstage)
  refine ((reassoc_of% hl) _).trans (Eq.trans ?_ hr.symm)
  refine (congrArg (G.map _ ≫ ·) hn).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hG)

end AlgebraicGeometry.FormalSpace

end
