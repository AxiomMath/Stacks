module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.UliftYonedaCoproduct

/-!
# A presentation of a finite coproduct of fppf sheaves over a product of index preorders

Given presentations of finitely many fppf sheaves `Z i` as colimits of affine objects of the big
fppf site along thickenings, indexed by directed preorders `Idx i`, the coproduct `∐ Z` is
presented in the same way over the product preorder `CategoryTheory.PiOrder Idx`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_piOrder_presentation_sigma`: the presentation of `∐ Z`
  over `CategoryTheory.PiOrder Idx`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

/-! ### Products of directed preorders -/

namespace CategoryTheory

namespace PiOrder

variable {Ix : Type w} {Idx : Ix → Type v} [∀ i, Preorder (Idx i)]

/-- A product of finitely many countable preorders is countable. -/
instance [Finite Ix] [∀ i, Countable (Idx i)] : Countable (PiOrder Idx) :=
  Function.Injective.countable (f := fun x : PiOrder Idx ↦ x.val)
    fun x y h ↦ by cases x; cases y; subst h; rfl

end PiOrder

end CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [FinitaryExtensive C] {ι : Type*} [Finite ι]
  {X Y : ι → C} {A Bv : C} {lam : ∀ i, X i ⟶ A} {sig : ∀ i, Y i ⟶ Bv}

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {ι : Type v} [Finite ι] [Small.{u} ι] {X Y : ι → Scheme.{u}}

namespace BigAffineFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type w} [Finite I] [Small.{u} I] (A : I → BigAffineFppf B S hS)

end BigAffineFppf

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A finite coproduct of affine formal algebraic spaces -/

/-- **The combined presentation of a finite coproduct.** Given presentations
`Z i ≅ colim_{Idx i} D i` of finitely many fppf sheaves by affine schemes along thickenings,
the coproduct `∐ Z` is presented by affine schemes along thickenings over the product
`K = ∏ᵢ Idx i` of the index preorders, which is again nonempty and directed. -/
theorem exists_piOrder_presentation_sigma {I : Type (u + 1)} [Finite I]
    (Z : I → FppfSheaf B S hS) {Idx : I → Type (u + 1)} [∀ i, Preorder (Idx i)]
    [∀ i, Nonempty (Idx i)] [∀ i, IsDirectedOrder (Idx i)]
    (D : ∀ i, Idx i ⥤ BigAffineFppf B S hS)
    (hthick : ∀ (i : I) ⦃j k : Idx i⦄ (f : j ⟶ k),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map ((D i).map f)))
    (hiso : ∀ i, Nonempty (Z i ≅ colimit (D i ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ E : PiOrder Idx ⥤ BigAffineFppf B S hS,
      (∀ ⦃k k' : PiOrder Idx⦄ (h : k ⟶ k'),
        Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map h))) ∧
        Nonempty ((∐ Z) ≅ colimit (E ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let : Small.{u} I := Countable.toSmall.{u} I
  let J := BigFppfOver.topology B S hS
  let G := BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  let T : Discrete I ⥤ (PiOrder Idx ⥤ BigAffineFppf B S hS) :=
    Discrete.functor fun i ↦ PiOrder.proj i ⋙ D i
  let E : PiOrder Idx ⥤ BigAffineFppf B S hS := T.flip ⋙ colim
  let Stage : PiOrder Idx → I → BigAffineFppf B S hS := fun k i ↦ (T.flip.obj k).obj ⟨i⟩
  have cof : ∀ k : PiOrder Idx, IsColimit ((Cocone.precompose
      (Discrete.natIsoFunctor (F := T.flip.obj k)).hom).obj
      (Cofan.mk (BigAffineFppf.sigmaObj B S hS (Stage k))
        (BigAffineFppf.sigmaIncl B S hS (Stage k)))) := fun k ↦
    (IsColimit.precomposeHomEquiv _ _).symm (BigAffineFppf.isColimitSigmaCofan B S hS (Stage k))
  let eK : ∀ k : PiOrder Idx, colimit (T.flip.obj k) ≅
      BigAffineFppf.sigmaObj B S hS (Stage k) := fun k ↦
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (T.flip.obj k)) (cof k)
  have heK : ∀ (k : PiOrder Idx) (i : I), colimit.ι (T.flip.obj k) ⟨i⟩ ≫ (eK k).hom =
      BigAffineFppf.sigmaIncl B S hS (Stage k) i := by
    intro k i
    have h0 : colimit.ι (T.flip.obj k) ⟨i⟩ ≫ (eK k).hom =
        (Discrete.natIsoFunctor (F := T.flip.obj k)).hom.app ⟨i⟩ ≫
          BigAffineFppf.sigmaIncl B S hS (Stage k) i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (T.flip.obj k)) (cof k) ⟨i⟩
    rw [h0]
    simp
  have hthickE : ∀ ⦃k k' : PiOrder Idx⦄ (h : k ⟶ k'),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map h)) := by
    intro k k' h
    set ψ : BigAffineFppf.sigmaObj B S hS (Stage k) ⟶
        BigAffineFppf.sigmaObj B S hS (Stage k') := (eK k).inv ≫ E.map h ≫ (eK k').hom with hψdef
    have hψ : ∀ i, colimit.ι (T.flip.obj k) ⟨i⟩ ≫ E.map h ≫ (eK k').hom =
        (D i).map ((PiOrder.proj i).map h) ≫
          BigAffineFppf.sigmaIncl B S hS (Stage k') i := by
      intro i
      rw [show E.map h = colimMap (T.flip.map h) from rfl, ← Category.assoc, ι_colimMap,
        Category.assoc, heK k' i]
      rfl
    have hψ' : ∀ i, BigAffineFppf.sigmaIncl B S hS (Stage k) i ≫ ψ =
        (D i).map ((PiOrder.proj i).map h) ≫
          BigAffineFppf.sigmaIncl B S hS (Stage k') i := by
      intro i
      calc BigAffineFppf.sigmaIncl B S hS (Stage k) i ≫ ψ
          = (colimit.ι (T.flip.obj k) ⟨i⟩ ≫ (eK k).hom) ≫ ψ := by rw [heK k i]
        _ = colimit.ι (T.flip.obj k) ⟨i⟩ ≫ E.map h ≫ (eK k').hom := by
            rw [hψdef, Category.assoc, Iso.hom_inv_id_assoc]
        _ = _ := hψ i
    have hψthick : Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map ψ) :=
      Stacks.Thickenings.isThickening_of_cofan
        (BigAffineFppf.isColimitToSchemeSigmaCofan B S hS (Stage k))
        (BigAffineFppf.isColimitToSchemeSigmaCofan B S hS (Stage k'))
        (fun i ↦ (BigAffineFppf.toScheme B S hS).map ((D i).map ((PiOrder.proj i).map h)))
        (fun i ↦ by rw [← Functor.map_comp, hψ' i, Functor.map_comp])
        (fun i ↦ hthick i _)
    have hE : E.map h = (eK k).hom ≫ ψ ≫ (eK k').inv := by
      rw [hψdef]; simp
    rw [hE, Functor.map_comp, Functor.map_comp]
    refine ⟨?_, ?_⟩
    · have := hψthick.1
      infer_instance
    · have : AlgebraicGeometry.Surjective ((BigAffineFppf.toScheme B S hS).map ψ) :=
        ⟨hψthick.2⟩
      exact (((BigAffineFppf.toScheme B S hS).map (eK k).hom) ≫
        ((BigAffineFppf.toScheme B S hS).map ψ) ≫
        ((BigAffineFppf.toScheme B S hS).map (eK k').inv)).surjective
  let W : Discrete I ⥤ (PiOrder Idx ⥤ FppfSheaf B S hS) :=
    T ⋙ (Functor.whiskeringRight (PiOrder Idx) (BigAffineFppf B S hS)
      (FppfSheaf B S hS)).obj G
  have e1 : E ⋙ G ≅ W.flip ⋙ colim :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft T.flip (preservesColimitNatIso G) ≪≫
        (Functor.associator _ _ _).symm
  have hfin : ∀ i : I, (PiOrder.proj (Idx := Idx) i).Final := fun i ↦ PiOrder.final_proj i
  have e3 : W ⋙ colim ≅ Discrete.functor Z :=
    Discrete.natIso fun i ↦
      Functor.Final.colimitIso (PiOrder.proj i.as) (D i.as ⋙ G) ≪≫ (hiso i.as).some.symm
  exact ⟨E, hthickE, ⟨(HasColimit.isoOfNatIso e1 ≪≫
    colimitFlipCompColimIsoColimitCompColim W ≪≫ HasColimit.isoOfNatIso e3).symm⟩⟩

end FormalSpace

end AlgebraicGeometry

end
