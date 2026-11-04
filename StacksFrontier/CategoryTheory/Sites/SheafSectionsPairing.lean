module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-!
# Pairings of sheaves of sets on sections, along functors preserving binary products

For two finite-product-preserving functors `Φ ≅ Φ''` between categories of sheaves of sets, the
composite of the inverse product comparison of `Φ` with `Φ` of a pairing `q : P ⨯ Q ⟶ N` is carried
by the isomorphism to the same composite for `Φ''`, after the product of the two components. For
`Φ''` restriction along a continuous functor `F`, that composite is, on a pair of local sections
over `U`, the pairing `q` itself over `F U`.

## Main results

* `CategoryTheory.Limits.preservesLimitPair_iso_inv_map_comp_natIso`: an isomorphism of
  product-preserving functors carries the inverse product comparison followed by the image of a
  pairing to the same composite for the other functor.
* `Stacks.SheafSections.sectionsFunctor_map_pairing_natIso`: the same statement on a pair of local
  sections of sheaves of sets.
* `Stacks.SheafSections.sectionsFunctor_map_pairing_sheafPushforwardContinuous`: for restriction
  along a continuous functor `F`, the pairing on local sections over `U` is `q` over `F U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

/-- An isomorphism of product-preserving functors carries the inverse product comparison followed
by the image of a pairing to the same composite for the other functor, after the product of its
components. -/
theorem preservesLimitPair_iso_inv_map_comp_natIso {D E : Type*} [Category D] [Category E]
    [HasFiniteProducts D] [HasFiniteProducts E] {Φ Φ'' : D ⥤ E}
    [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ''] (ε : Φ ≅ Φ'') {P Q N : D}
    (q : P ⨯ Q ⟶ N) :
    ((PreservesLimitPair.iso Φ P Q).inv ≫ Φ.map q) ≫ ε.hom.app N =
      prod.map (ε.hom.app P) (ε.hom.app Q) ≫ (PreservesLimitPair.iso Φ'' P Q).inv ≫ Φ''.map q := by
  rw [Category.assoc, ε.hom.naturality q, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.eq_comp_inv, Category.assoc, PreservesLimitPair.iso_hom,
    prodComparison_natural_of_natTrans, ← Category.assoc, ← PreservesLimitPair.iso_hom,
    Iso.inv_hom_id, Category.id_comp]


end CategoryTheory.Limits

namespace Stacks.SheafSections

section Sets

universe w u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}

/-- The image of a product of two morphisms of sheaves of sets on a pair of local sections. -/
theorem sectionsFunctor_map_prodMap_prodObjMk {U : Cᵒᵖ} {P P' Q Q' : Sheaf J (Type w)}
    (α : P ⟶ P') (β : Q ⟶ Q') (x : (Sheaf.sectionsFunctor J U).obj P)
    (y : (Sheaf.sectionsFunctor J U).obj Q) :
    (Sheaf.sectionsFunctor J U).map (prod.map α β) (Functor.prodObjMk x y) =
      Functor.prodObjMk ((Sheaf.sectionsFunctor J U).map α x)
        ((Sheaf.sectionsFunctor J U).map β y) := by
  rw [Functor.map_prodMap_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

/-- An isomorphism `ε : Φ ≅ Φ''` of product-preserving functors of sheaves of sets carries the
value on a pair of local sections of the pairing `Φ(P) ⨯ Φ(Q) ≅ Φ(P ⨯ Q) ⟶ Φ(N)` to the value of
the same pairing for `Φ''` on the pair of transported sections. -/
theorem sectionsFunctor_map_pairing_natIso
    {Φ Φ'' : Sheaf J' (Type w) ⥤ Sheaf J (Type w)}
    [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ''] (ε : Φ ≅ Φ'')
    {P Q N : Sheaf J' (Type w)} (q : P ⨯ Q ⟶ N) (U : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J U).obj (Φ.obj P))
    (y : (Sheaf.sectionsFunctor J U).obj (Φ.obj Q)) :
    (Sheaf.sectionsFunctor J U).map (ε.hom.app N)
        ((Sheaf.sectionsFunctor J U).map ((PreservesLimitPair.iso Φ P Q).inv ≫ Φ.map q)
          (Functor.prodObjMk x y)) =
      (Sheaf.sectionsFunctor J U).map ((PreservesLimitPair.iso Φ'' P Q).inv ≫ Φ''.map q)
        (Functor.prodObjMk ((Sheaf.sectionsFunctor J U).map (ε.hom.app P) x)
          ((Sheaf.sectionsFunctor J U).map (ε.hom.app Q) y)) := by
  rw [← FunctorToTypes.map_comp_apply, Limits.preservesLimitPair_iso_inv_map_comp_natIso,
    FunctorToTypes.map_comp_apply, sectionsFunctor_map_prodMap_prodObjMk]

/-- For restriction of sheaves of sets along a continuous functor `F`, the pairing
`F_*P ⨯ F_*Q ≅ F_*(P ⨯ Q) ⟶ F_*N` on a pair of local sections over `U` is the pairing `q` on the
same pair of sections over `F U`. -/
theorem sectionsFunctor_map_pairing_sheafPushforwardContinuous
    (F : C ⥤ C') [F.IsContinuous J J']
    [PreservesFiniteProducts (F.sheafPushforwardContinuous (Type w) J J')]
    {P Q N : Sheaf J' (Type w)} (q : P ⨯ Q ⟶ N) (U : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J U).obj ((F.sheafPushforwardContinuous (Type w) J J').obj P))
    (y : (Sheaf.sectionsFunctor J U).obj ((F.sheafPushforwardContinuous (Type w) J J').obj Q)) :
    (Sheaf.sectionsFunctor J U).map
        ((PreservesLimitPair.iso (F.sheafPushforwardContinuous (Type w) J J') P Q).inv ≫
          (F.sheafPushforwardContinuous (Type w) J J').map q)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} J U)
          (A := (F.sheafPushforwardContinuous (Type w) J J').obj P)
          (B := (F.sheafPushforwardContinuous (Type w) J J').obj Q) x y) =
      (Sheaf.sectionsFunctor J' (F.op.obj U)).map q
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} J' (F.op.obj U)) (A := P) (B := Q)
          x y) := by
  rw [FunctorToTypes.map_comp_apply]
  congr 1
  refine Functor.prodObjMk_ext (P := Sheaf.sectionsFunctor.{w} J' (F.op.obj U)) ?_ ?_
  · have h1 : (Sheaf.sectionsFunctor J U).map
        ((PreservesLimitPair.iso (F.sheafPushforwardContinuous (Type w) J J') P Q).inv ≫
          (F.sheafPushforwardContinuous (Type w) J J').map prod.fst)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} J U) x y) = x := by
      rw [PreservesLimitPair.iso_inv_fst, Functor.map_fst_prodObjMk]
    exact (FunctorToTypes.map_comp_apply _ _ _ _).symm.trans
      (h1.trans
        (Functor.map_fst_prodObjMk (P := Sheaf.sectionsFunctor.{w} J' (F.op.obj U)) x y).symm)
  · have h1 : (Sheaf.sectionsFunctor J U).map
        ((PreservesLimitPair.iso (F.sheafPushforwardContinuous (Type w) J J') P Q).inv ≫
          (F.sheafPushforwardContinuous (Type w) J J').map prod.snd)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} J U) x y) = y := by
      rw [PreservesLimitPair.iso_inv_snd, Functor.map_snd_prodObjMk]
    exact (FunctorToTypes.map_comp_apply _ _ _ _).symm.trans
      (h1.trans
        (Functor.map_snd_prodObjMk (P := Sheaf.sectionsFunctor.{w} J' (F.op.obj U)) x y).symm)

end Sets

end Stacks.SheafSections



end
