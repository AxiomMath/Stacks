module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Fubini
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealProductDiagram

/-!
# The weak-ideal presentation of a finite product of weakly admissible rings

Let `A k` be a finite family of weakly admissible linearly topologized rings, each presented as
in `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` by a diagram `D k` of affine
schemes over `S` indexed by its weak ideals of definition. The colimit of the sheaves of
`AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram` is the coproduct of the presented sheaves,
and the coproduct is presented by weak ideals over the product ring `∏ A k`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.sigmaWeakIdealSheafFlipIso`: the diagram of sheaves of
  `AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram`, identified with the stagewise colimit
  over the family of the reindexed diagrams of sheaves of the members.
* `AlgebraicGeometry.FormalSpace.sigmaWeakIdealColimitIso`: the coproduct of a finite family of
  sheaves presented by weak ideals, identified with the colimit of the sheaves of
  `AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram`.
* `AlgebraicGeometry.FormalSpace.sigmaWeakIdealColimitPresentation`: the weak-ideal presentation
  of the coproduct of a finite family of presented sheaves, over the product of their rings.

## Main results

* `AlgebraicGeometry.FormalSpace.final_weakIdealsPiProj`: the projection of the weak ideals of
  definition of a finite product of weakly admissible rings to those of a factor is final.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section Final

variable {K : Type u} [Finite K] (A : K → Type u) [∀ k, CommRing (A k)]
  [∀ k, TopologicalSpace (A k)] [∀ k, IsTopologicalRing (A k)]
  [∀ k, IsLinearTopology (A k) (A k)]
  (hA : ∀ k, TopologicalRing.IsWeaklyAdmissible (A k))

/-- **The projection of the weak ideals of definition of a finite product of weakly admissible
linearly topologized rings to those of a factor is final.** -/
theorem final_weakIdealsPiProj (k : K) : (weakIdealsPiProj A hA k).Final := by
  classical
  let : IsDirectedOrder (WeakIdeals (∀ k, A k)) := isDirectedOrder_weakIdeals (∀ k, A k)
  refine (Monotone.final_functor_iff
    (monotone_weakIdealOfDefinitionPiProj A hA k).dual).mpr fun J ↦ ?_
  set I : ∀ i, Ideal (A i) :=
    Function.update (fun i ↦ (hA i).1.choose) k (OrderDual.ofDual J).1 with hI
  have hIk : I k = (OrderDual.ofDual J).1 := Function.update_self (f := _) k _
  have hIdef : ∀ i, TopologicalRing.IsWeakIdealOfDefinition (I i) := by
    intro i
    rcases eq_or_ne i k with rfl | h
    · rw [hIk]
      exact (OrderDual.ofDual J).2
    · rw [hI, Function.update_of_ne h]
      exact (hA i).1.choose_spec
  refine ⟨OrderDual.toDual
    ⟨Ideal.pi I, TopologicalRing.isWeakIdealOfDefinition_idealPi A I hIdef⟩, ?_⟩
  show (Ideal.pi I).map (Pi.evalRingHom A k) ≤ (OrderDual.ofDual J).1
  rw [Ideal.map_evalRingHom_pi, hIk]

end Final

/-! ### The colimit of the weak-ideal diagram of a finite product -/

section Sigma

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {K : Type u} [Finite K] (A : K → Type u) [∀ k, CommRing (A k)]
  [∀ k, TopologicalSpace (A k)] [∀ k, IsTopologicalRing (A k)]
  [∀ k, IsLinearTopology (A k) (A k)]
  (hA : ∀ k, TopologicalRing.IsWeaklyAdmissible (A k))
  (D : ∀ k, WeakIdeals (A k) ⥤ BigAffineFppf B S hS)

attribute [local instance] sheaf_hasColimits

/-- The family of diagrams of fppf sheaves of a finite family of weak-ideal diagrams, reindexed
to the weak ideals of definition of the product ring: a functor out of the discrete category on
the index of the family whose value at `k` is the `k`-th member, reindexed along
`AlgebraicGeometry.FormalSpace.weakIdealsPiProj`, followed by the sheafified Yoneda embedding. -/
noncomputable def sigmaWeakIdealSheafFamily :
    Discrete K ⥤ (WeakIdeals (∀ k, A k) ⥤ FppfSheaf B S hS) :=
  (Discrete.functor fun k ↦ weakIdealsPiProj A hA k ⋙ D k) ⋙
    (Functor.whiskeringRight (WeakIdeals (∀ k, A k)) (BigAffineFppf B S hS)
      (FppfSheaf B S hS)).obj
      (BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))

/-- The member of `AlgebraicGeometry.FormalSpace.sigmaWeakIdealSheafFamily` at `k`, identified
with the reindexed `k`-th diagram of sheaves; the identification is the identity at every
stage. -/
noncomputable def sigmaWeakIdealSheafFamilyObjIso (k : Discrete K) :
    (sigmaWeakIdealSheafFamily B S hS A hA D).obj k ≅
      weakIdealsPiProj A hA k.as ⋙ D k.as ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- The components of the inverse of
`AlgebraicGeometry.FormalSpace.sigmaWeakIdealSheafFamilyObjIso` are identities. -/
@[simp]
theorem sigmaWeakIdealSheafFamilyObjIso_inv_app (k : Discrete K) (J : WeakIdeals (∀ k, A k)) :
    (sigmaWeakIdealSheafFamilyObjIso B S hS A hA D k).inv.app J = 𝟙 _ :=
  rfl

/-- **The sheaf of a stage of the weak-ideal diagram of a finite product is the coproduct of the
sheaves of the corresponding stages of the members.** -/
noncomputable def sigmaWeakIdealStageIsColimit (J : WeakIdeals (∀ k, A k)) :
    IsColimit ((Cocone.precompose (Discrete.natIsoFunctor
        (F := (sigmaWeakIdealSheafFamily B S hS A hA D).flip.obj J)).hom).obj
      (Cofan.mk ((BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          (BigAffineFppf.sigmaObj B S hS
            fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J)))
        fun k ↦ (BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (BigAffineFppf.sigmaIncl B S hS
            (fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J)) k))) :=
  (IsColimit.precomposeHomEquiv _ _).symm
    (Cofan.isColimitMapCoconeEquiv _ _ _
      (isColimitOfPreserves (BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (BigAffineFppf.isColimitSigmaCofan B S hS
          fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J))))

/-- The stage of the diagram of sheaves of
`AlgebraicGeometry.FormalSpace.sigmaWeakIdealDiagram`, identified with the colimit over the
family of the stages of the members. -/
noncomputable def sigmaWeakIdealStageIso (J : WeakIdeals (∀ k, A k)) :
    colimit ((sigmaWeakIdealSheafFamily B S hS A hA D).flip.obj J) ≅
      (BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (BigAffineFppf.sigmaObj B S hS
          fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J)) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (sigmaWeakIdealStageIsColimit B S hS A hA D J)

/-- The coprojection of the `k`-th member followed by
`AlgebraicGeometry.FormalSpace.sigmaWeakIdealStageIso` is the image under the sheafified Yoneda
embedding of the `k`-th summand inclusion of the finite coproduct of affines. -/
@[reassoc]
theorem ι_sigmaWeakIdealStageIso_hom (J : WeakIdeals (∀ k, A k)) (k : K) :
    colimit.ι ((sigmaWeakIdealSheafFamily B S hS A hA D).flip.obj J) ⟨k⟩ ≫
        (sigmaWeakIdealStageIso B S hS A hA D J).hom =
      (BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (BigAffineFppf.sigmaIncl B S hS
          (fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J)) k) := by
  have h0 : colimit.ι ((sigmaWeakIdealSheafFamily B S hS A hA D).flip.obj J) ⟨k⟩ ≫
      (sigmaWeakIdealStageIso B S hS A hA D J).hom =
        (Discrete.natIsoFunctor
            (F := (sigmaWeakIdealSheafFamily B S hS A hA D).flip.obj J)).hom.app ⟨k⟩ ≫
          (BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            (BigAffineFppf.sigmaIncl B S hS
              (fun k ↦ (D k).obj ((weakIdealsPiProj A hA k).obj J)) k) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
      (sigmaWeakIdealStageIsColimit B S hS A hA D J) ⟨k⟩
  rw [h0]
  refine Eq.trans (eq_whisker ?_ _) (Category.id_comp _)
  simp

/-- **The diagram of sheaves of the weak-ideal diagram of a finite product is the stagewise
colimit over the family of the diagrams of sheaves of the members.** -/
noncomputable def sigmaWeakIdealSheafFlipIso :
    (sigmaWeakIdealSheafFamily B S hS A hA D).flip ⋙ colim ≅
      sigmaWeakIdealDiagram B S hS A hA D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) :=
  NatIso.ofComponents (sigmaWeakIdealStageIso B S hS A hA D) (by
    intro J J' f
    refine colimit.hom_ext fun ⟨k⟩ ↦ ?_
    refine Eq.trans (ι_colimMap_assoc
      ((sigmaWeakIdealSheafFamily B S hS A hA D).flip.map f) ⟨k⟩ _) ?_
    refine Eq.trans (whisker_eq _ (ι_sigmaWeakIdealStageIso_hom B S hS A hA D J' k)) ?_
    refine Eq.trans ?_ (ι_sigmaWeakIdealStageIso_hom_assoc B S hS A hA D J k _).symm
    exact ((((BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _).symm.trans
      (congrArg (BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (BigAffineFppf.sigmaIncl_sigmaMap B S hS
          (fun i ↦ (D i).map ((weakIdealsPiProj A hA i).map f)) k))).trans
      ((BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp _ _)).symm)

/-- **The coproduct of a finite family of fppf sheaves presented by the weak ideals of definition
of weakly admissible rings is the colimit of the weak-ideal diagram of the product ring.** -/
noncomputable def sigmaWeakIdealColimitIso (Z : K → FppfSheaf B S hS)
    (hZ : ∀ k, Z k ≅ colimit (D k ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    (∐ Z) ≅ colimit (sigmaWeakIdealDiagram B S hS A hA D ⋙
      BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
  letI : ∀ k, (weakIdealsPiProj A hA k).Final := final_weakIdealsPiProj A hA
  have e3 : sigmaWeakIdealSheafFamily B S hS A hA D ⋙ colim ≅ Discrete.functor Z :=
    Discrete.natIso fun k ↦
      HasColimit.isoOfNatIso (sigmaWeakIdealSheafFamilyObjIso B S hS A hA D k) ≪≫
        Functor.Final.colimitIso (weakIdealsPiProj A hA k.as)
          (D k.as ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≪≫
        (hZ k.as).symm
  (HasColimit.isoOfNatIso e3).symm ≪≫
    (colimitFlipCompColimIsoColimitCompColim (sigmaWeakIdealSheafFamily B S hS A hA D)).symm ≪≫
      HasColimit.isoOfNatIso (sigmaWeakIdealSheafFlipIso B S hS A hA D)

/-- **The weak-ideal presentation of a finite coproduct of fppf sheaves presented by weak ideals,
over the product of their rings.** -/
noncomputable def sigmaWeakIdealColimitPresentation (Z : K → FppfSheaf B S hS)
    (P : ∀ k, WeakIdealColimitPresentation B S hS (A k) (Z k)) :
    WeakIdealColimitPresentation B S hS (∀ k, A k) (∐ Z) where
  diagram := sigmaWeakIdealDiagram B S hS A hA fun k ↦ (P k).diagram
  quotientIso := sigmaWeakIdealQuotientIso B S hS A hA _ fun k ↦ (P k).quotientIso
  quotientIso_natural := sigmaWeakIdealQuotientIso_natural B S hS A hA _ _
    fun k ↦ (P k).quotientIso_natural
  colimitIso := sigmaWeakIdealColimitIso B S hS A hA _ Z fun k ↦ (P k).colimitIso

end Sigma

end AlgebraicGeometry.FormalSpace

end
