module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitDescentTransfer

/-!
# Descending an object along a single morphism through a fibrewise fully faithful transformation

Let `τ : F ⟶ G` be a strong transformation of pseudofunctors from `LocallyDiscrete Cᵒᵖ` to `Cat`,
and let `f : X ⟶ S` be a morphism with chosen fibre products `X ×_S X` and `X ×_S X ×_S X`.
Suppose that `F` has effective descent along `{f}`, that isomorphisms of `G`-descent data along
`{f}` between canonical descent data come from isomorphisms over `S` (the comparison functor of
`G` along `{f}` is fully faithful), and that the components of `τ` over `X`, `X ×_S X` and
`X ×_S X ×_S X` are faithful, the one over `X ×_S X` also full.

Then **an object `N` of `G` over `S` whose inverse image to `X` comes from `F` comes from `F`
over `S`**: if `τ_X(M) ≅ f^* N` then `τ_S(L) ≅ N` for some `L` over `S`.

The proof is the usual one. The canonical descent datum of `N` is carried to `M` along the given
isomorphism; full faithfulness of `τ` over `X ×_S X` gives the gluing morphism of a pre-descent
datum on `M` relative to `{f}` for `F`, and faithfulness of `τ` over `X` and `X ×_S X ×_S X`
reflects the two descent conditions from the canonical datum of `N`. That datum descends to some
`L` over `S`; transporting along `τ`, the canonical datum of `τ_S(L)` is isomorphic to that of
`N`, and full faithfulness of the comparison functor of `G` turns this into `τ_S(L) ≅ N`.

This is the categorical core of the step "it suffices to construct a descent after replacing `Y`
by the members of an h covering" in the proof of Stacks Tag 0EXH, with `F` the stack of Stacks
Tag 0EXE over the base and `G` its inverse image along the given morphism `X ⟶ Y`.

## Main results

* `CategoryTheory.Pseudofunctor.SinglePreDatum.exists_app_obj_iso_of_map_obj_iso`: an object of
  `G` over `S` whose inverse image to `X` comes from `F` comes from `F` over `S`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public noncomputable section

universe v' u' v u

namespace CategoryTheory.Pseudofunctor

open Opposite Limits

variable {C : Type u} [Category.{v} C] {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  (τ : F.StrongTrans G) {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f)
  (sq₃ : ChosenPullback₃ sq sq sq)

namespace SinglePreDatum

/-- The pre-descent datum for `F` on `M` obtained from the canonical descent datum of `N` along
an isomorphism `τ_X(M) ≅ f^* N`, through full faithfulness of `τ` over `X ×_S X`. -/
def ofAppIsoCan [(τ.app (.mk (op sq.pullback))).toFunctor.Full] (N : G.obj (.mk (op S)))
    (M : F.obj (.mk (op X)))
    (e : (τ.app (.mk (op X))).toFunctor.obj M ≅ (G.map f.op.toLoc).toFunctor.obj N) :
    SinglePreDatum sq F where
  obj := M
  hom := (τ.app (.mk (op sq.pullback))).toFunctor.preimage
    ((τ.pullIso sq.p₁ M).hom ≫ ((can sq₃ N).ofIso e).hom ≫ (τ.pullIso sq.p₂ M).inv)

/-- The gluing morphism of the transport of `SinglePreDatum.ofAppIsoCan` along `τ` is that of the
canonical pre-descent datum of `N` carried to `τ_X(M)`. -/
lemma ofAppIsoCan_map_hom [(τ.app (.mk (op sq.pullback))).toFunctor.Full]
    (N : G.obj (.mk (op S))) (M : F.obj (.mk (op X)))
    (e : (τ.app (.mk (op X))).toFunctor.obj M ≅ (G.map f.op.toLoc).toFunctor.obj N) :
    ((ofAppIsoCan τ sq sq₃ N M e).map τ).hom = ((can sq₃ N).ofIso e).hom := by
  simp [ofAppIsoCan, StrongTrans.mapPullHom]

/-- The transport of `SinglePreDatum.ofAppIsoCan` along `τ` is the canonical pre-descent datum of
`N` carried to `τ_X(M)`. -/
lemma ofAppIsoCan_map [(τ.app (.mk (op sq.pullback))).toFunctor.Full]
    (N : G.obj (.mk (op S))) (M : F.obj (.mk (op X)))
    (e : (τ.app (.mk (op X))).toFunctor.obj M ≅ (G.map f.op.toLoc).toFunctor.obj N) :
    (ofAppIsoCan τ sq sq₃ N M e).map τ = (can sq₃ N).ofIso e :=
  congrArg (SinglePreDatum.mk _) (ofAppIsoCan_map_hom τ sq sq₃ N M e)

/-- The transport of `SinglePreDatum.ofAppIsoCan` along `τ` is isomorphic to the canonical
pre-descent datum of `N`. -/
def ofAppIsoCanMapIso [(τ.app (.mk (op sq.pullback))).toFunctor.Full]
    (N : G.obj (.mk (op S))) (M : F.obj (.mk (op X)))
    (e : (τ.app (.mk (op X))).toFunctor.obj M ≅ (G.map f.op.toLoc).toFunctor.obj N) :
    ((ofAppIsoCan τ sq sq₃ N M e).map τ).Iso (can sq₃ N) :=
  (Iso.ofEq (ofAppIsoCan_map τ sq sq₃ N M e)).trans (isoOfIso (can sq₃ N) e)

/-- **An object over `S` whose inverse image to `X` comes from `F` comes from `F` over `S`**,
given effective descent for `F` along `{f}`, full faithfulness of the comparison functor of `G`
along `{f}`, and faithfulness of `τ` over `X`, `X ×_S X` and `X ×_S X ×_S X`, with fullness over
`X ×_S X`. -/
theorem exists_app_obj_iso_of_map_obj_iso
    [(τ.app (.mk (op X))).toFunctor.Faithful]
    [(τ.app (.mk (op sq.pullback))).toFunctor.Full]
    [(τ.app (.mk (op sq.pullback))).toFunctor.Faithful]
    [(τ.app (.mk (op sq₃.pullback))).toFunctor.Faithful]
    (hF : (F.toDescentData (fun _ : PUnit.{1} ↦ f)).EssSurj)
    [(G.toDescentData (fun _ : PUnit.{1} ↦ f)).Full]
    [(G.toDescentData (fun _ : PUnit.{1} ↦ f)).Faithful]
    (N : G.obj (.mk (op S))) (M : F.obj (.mk (op X)))
    (e : (τ.app (.mk (op X))).toFunctor.obj M ≅ (G.map f.op.toLoc).toFunctor.obj N) :
    ∃ L : F.obj (.mk (op S)), Nonempty ((τ.app (.mk (op S))).toFunctor.obj L ≅ N) := by
  let D := ofAppIsoCan τ sq sq₃ N M e
  have hDτ : (D.map τ).IsDatum sq₃ :=
    (ofAppIsoCanMapIso τ sq sq₃ N M e).symm.isDatum (isDatum_can sq₃ N)
  have hD : D.IsDatum sq₃ :=
    { self := τ.mapPullHom_injective
        ((D.map_pull τ _ _ _ _ _).symm.trans (hDτ.self.trans τ.mapPullHom_id.symm))
      comp := τ.mapPullHom_injective (by
        rw [← τ.mapPullHom_comp, ← D.map_pull, ← D.map_pull, ← D.map_pull]
        exact hDτ.comp) }
  obtain ⟨L, ⟨ε⟩⟩ := hF.mem_essImage
    ((DescentData'.toDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).obj (D.toDescentData' hD))
  let ε' := (DescentData'.fromDescentDataFunctor F (sqF sq) (sq₃F sq sq₃)).mapIso ε ≪≫
    ((DescentData'.descentDataEquivalence F (sqF sq) (sq₃F sq sq₃)).unitIso.app
      (D.toDescentData' hD)).symm
  let isoL : (can sq₃ L).Iso D := isoOfIso' ε'
  let Ξ : (can sq₃ ((τ.app (.mk (op S))).toFunctor.obj L)).Iso (can sq₃ N) :=
    (canMapIso sq₃ τ L).symm.trans ((isoL.map τ).trans (ofAppIsoCanMapIso τ sq sq₃ N M e))
  refine ⟨L, ⟨(Functor.FullyFaithful.ofFullyFaithful
    (G.toDescentData (fun _ : PUnit.{1} ↦ f))).preimageIso
      { hom := descentDataHomOfIsMor sq₃ Ξ.e.hom Ξ.comm
        inv := descentDataHomOfIsMor sq₃ Ξ.symm.e.hom Ξ.symm.comm
        hom_inv_id := ?_, inv_hom_id := ?_ }⟩⟩
  all_goals
    ext ⟨⟩
    rw [DescentData.comp_hom, DescentData.id_hom]
    refine (congrArg₂ (· ≫ ·) (descentDataHomOfIsMor_hom sq₃ _ _)
      (descentDataHomOfIsMor_hom sq₃ _ _)).trans ?_
  exacts [Ξ.e.hom_inv_id, Ξ.e.inv_hom_id]

end SinglePreDatum

end CategoryTheory.Pseudofunctor

end
