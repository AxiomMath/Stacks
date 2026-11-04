module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.PushforwardSquareMate
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism

/-!
# Beck–Chevalley for the degreewise square of a morphism between simplicial sites

Let `h` be a morphism between simplicial sites in the cocontinuous case and `n` a simplicial
degree. The total morphism of topoi `h_{total}`, the degreewise morphism `h_n` and the two
component morphisms `g_n`, `g'_n` of degree `n` form the commutative square of Stacks 0D96, as
witnessed by the isomorphism `totalComponentPushforwardIso` of composite direct images. Its mate
along the adjunctions `g_n^{-1} ⊣ g_{n,*}` and `g'^{-1}_n ⊣ g'_{n,*}` is a comparison

`(g'_n)^{-1} ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^{-1}`

of functors on sheaves of sets, and this file proves that it is invertible.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalComponentPushforwardMate`: the mate.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.isIso_totalComponentPushforwardMate`:
  the mate is an isomorphism.

## Implementation notes

The inverse images of the component morphisms are the sheaf pullbacks `(i^p -)^#` of
Stacks 00XL, with their adjunction. The component inclusion `i` is also continuous, so its
restriction is a second left adjoint of `i_*`; the mate along the two choices differ by the
comparisons of left adjoints (`CategoryTheory.mateEquiv_symm_natTrans_app_leftAdjointUniq`), and
along restriction it is the base change of right Kan extensions of the square of component
inclusions (`CategoryTheory.sheafPushforwardCocontinuousSquareMate_app_hom`). That square is
Guitart exact (`CategoryTheory.Grothendieck.guitartExact_ιCompMap`), which is the whole content.

The mate is a different 2-cell from `totalPushforwardRestrictIso`, which is constructed directly
from the base change of right Kan extensions; the point here is that the canonical comparison
attached to the commutative square, the one the source writes as an equality, is invertible.

## References

* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.CocontinuousSimplicialSite.Morphism

variable {C C' : CocontinuousSimplicialSite.{u}}

/-- The canonical comparison `(g'_n)^{-1} ∘ h_{total,*} ⟶ h_{n,*} ∘ g_n^{-1}` of sheaves of sets:
the mate of the square of direct images of Stacks 0D96 along the adjunctions of the two
component morphisms of degree `n`. -/
abbrev totalComponentPushforwardMate (h : Morphism C C') (n : SimplexCategory) :=
  (mateEquiv (SimplicialSiteSituation.componentMorphism
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).adj
      (SimplicialSiteSituation.componentMorphism
        (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).adj).symm
    (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv)

/-- **The Beck–Chevalley property of the degreewise square of Stacks 0D96.** The mate of the
square of direct images along the two component morphisms of simplicial degree `n` is an
isomorphism: the canonical comparison `(g'_n)^{-1} h_{total,*} ⟶ h_{n,*} g_n^{-1}` of sheaves
of sets is invertible. -/
theorem isIso_totalComponentPushforwardMate (h : Morphism C C') (n : SimplexCategory) :
    IsIso (totalComponentPushforwardMate h n).natTrans := by
  let v := (h.hom.app (Opposite.op n)).toFunctor
  let i := Grothendieck.ι C.underlying (Opposite.op n)
  let i' := Grothendieck.ι C'.underlying (Opposite.op n)
  let Jn := topologyOfCoverings (C.coverage (Opposite.op n))
  let Jn' := topologyOfCoverings (C'.coverage (Opposite.op n))
  let K := SimplicialCoverings.totalTopology C.underlying C.coverage
  let K' := SimplicialCoverings.totalTopology C'.underlying C'.coverage
  let : v.IsCocontinuous Jn Jn' := h.isCocontinuous (Opposite.op n)
  let : i.IsCocontinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  let : i'.IsCocontinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  let : i.IsContinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  let : i'.IsContinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  let := h.totalFunctor_isCocontinuous
  have hq : i ⋙ h.totalFunctor = v ⋙ i' := h.ι_comp_totalFunctor (Opposite.op n)
  have hw : (TwoSquare.mk _ _ _ _ (eqToHom hq) : TwoSquare i v h.totalFunctor i') =
      (Grothendieck.ιCompMap h.hom (Opposite.op n)).hom := by
    ext X
    simp [Grothendieck.ιCompMap]
    rfl
  have : (TwoSquare.mk _ _ _ _ (eqToHom hq) : TwoSquare i v h.totalFunctor i').GuitartExact := by
    rw [hw]; exact Grothendieck.guitartExact_ιCompMap h.hom (Opposite.op n)
  have := isIso_sheafPushforwardCocontinuousSquareMate Jn Jn' K K' i i' v h.totalFunctor hq
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  unfold totalComponentPushforwardMate
  let adj :=
    (SimplicialSiteSituation.componentMorphism (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).adj
  let adj' :=
    (SimplicialSiteSituation.componentMorphism (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).adj
  let e := adj.leftAdjointUniq (i.sheafAdjunctionCocontinuous (Type u) Jn K)
  let e' := adj'.leftAdjointUniq (i'.sheafAdjunctionCocontinuous (Type u) Jn' K')
  rw [mateEquiv_symm_natTrans_app_leftAdjointUniq adj (i.sheafAdjunctionCocontinuous (Type u) Jn K)
    adj' (i'.sheafAdjunctionCocontinuous (Type u) Jn' K')
    (TwoSquare.mk _ _ _ _ (h.totalComponentPushforwardIso n).inv) F]
  have : IsIso (e'.hom.app (h.totalMorphism.pushforward.obj F)) := (e'.app _).isIso_hom
  have : IsIso (e.inv.app F) := (e.app F).isIso_inv
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
    (NatIso.isIso_app_of_isIso
      (sheafPushforwardCocontinuousSquareMate Jn Jn' K K' i i' v h.totalFunctor hq).natTrans F)
    inferInstance)

end CategoryTheory.CocontinuousSimplicialSite.Morphism

end
