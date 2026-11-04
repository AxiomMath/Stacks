module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionFiberGenerator

/-!
# The fibre comparison of the projection formula on a germ

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. This file computes
the fibre comparison `AlgebraicGeometry.SmallEtale.modProjectionFiberIso` of [Stacks, Tag 0GKF]
on the germ at a geometric point `ȳ` of `Y` of a pure tensor, and then on the germ of a
generator `(Z, a)` of `f_{p!}F` tensored with a section `t` of `G`: the answer is the germ of the
supported section `a ⊗ f^{-1}t`, which is also where the source's recipe sends it.

## Main results

* `AlgebraicGeometry.SmallEtale.moduleFiberStalksIso_hom_apply`,
  `AlgebraicGeometry.SmallEtale.modFiberStalksTensorIso_hom_apply` and
  `AlgebraicGeometry.SmallEtale.modProjectionFiberSummandsIso_hom_apply` — **the componentwise
  formulae for the three direct-sum legs of the fibre comparison**: two reindexings of a direct
  sum and the distributivity of a tensor product over it.
* `AlgebraicGeometry.SmallEtale.modProjectionFiberIso_hom_comp` — the fibre comparison with its
  first four legs exposed, the last two having been cancelled against the forward decomposition
  of the target's fibre.
* `AlgebraicGeometry.SmallEtale.modProjectionFiberIso_germ_tmul` — **the fibre comparison on the
  germ of a pure tensor**, componentwise.
* `AlgebraicGeometry.SmallEtale.modProjectionFiberIso_germ_generator` and
  `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorBilinear_germ_generator` — **the two sides
  of the projection formula agree on the germ of a generator tensored with a germ.**
* `AlgebraicGeometry.SmallEtale.exists_modFiniteSupportGenerator_sum` — Stacks 0F6J for the
  `Λ`-linear finite-support direct image: every section of `f_{p!}F` over a test object is a
  finite sum of generators.

## Implementation notes

The two reindexing legs are `DirectSum.congrLinearEquiv`s, so their componentwise formulae hold
by `rfl`; the distributivity leg is a `TensorProduct.directSumLeft`, whose componentwise formula
is Mathlib's `TensorProduct.directSumLeft_tmul`. Comparing the three of them is then a matter of
`DFinsupp.ext`.

The last two legs of `AlgebraicGeometry.SmallEtale.modProjectionFiberIso` are the inverses of
the forward decomposition of the fibre of `f_{p!}(F ⊗_Λ f^{-1}G)`, so the identity is proved
after post-composing with that decomposition, which cancels them. That cancellation is
`Stacks.iso_trans_tail_cancel`, an identity between abstract isomorphisms, because `simp` cannot
rewrite the nested `Iso.trans` of the chain: the intermediate objects agree with their spellings
in the chain only up to unfolding a definition.

Nothing here carries a `stacks` attribute: this is the germ computation behind
[Stacks, Tag 0GKF], which is proved in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso`.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F6J](https://stacks.math.columbia.edu/tag/0F6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped DirectSum

namespace Stacks

/-- **A chain of six isomorphisms, with its last two legs cancelled.** If the last two legs of
the chain are the inverses of two isomorphisms, post-composing with those two leaves the first
four legs. Isolated as a statement about abstract isomorphisms so that it applies to terms whose
types agree only up to unfolding a definition. -/
public theorem iso_trans_tail_cancel {C : Type*} [Category* C] {W P Q R S T U : C}
    (a : W ≅ P) (b : P ≅ Q) (c : Q ≅ R) (d : R ≅ S) (e : T ≅ S) (g : U ≅ T) :
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e.symm ≪≫ g.symm).hom ≫ g.hom ≫ e.hom =
      a.hom ≫ b.hom ≫ c.hom ≫ d.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end Stacks

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Componentwise formula for `moduleFiberStalksIso`. -/
public theorem moduleFiberStalksIso_hom_apply (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (z : ⨁ x : GeometricFiberPoint B f s,
      ((moduleEtaleStalkFunctor.{u, v, max (u + 1) v} B Λ X
        (x.toGeometricPoint B f s)).obj F : Type _))
    (x : GeometricFiberPoint B f s) :
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom z x =
      ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ X
        (x.toGeometricPoint B f s)).app F).hom (z x) :=
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Componentwise formula for `modFiberStalksTensorIso`. -/
public theorem modFiberStalksTensorIso_hom_apply (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (N : ModuleCat.{max (u + 1) v} Λ)
    (w : modFiberStalks.{u, v, max (u + 1) v} B Λ f s F) (n : N)
    (x : GeometricFiberPoint B f s) :
    (modFiberStalksTensorIso.{u, v} B Λ f s F N).hom (w ⊗ₜ[Λ] n) x = w x ⊗ₜ[Λ] n := by
  let : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact TensorProduct.directSumLeft_tmul Λ Λ w n x

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Componentwise formula for `modProjectionFiberSummandsIso`. -/
public theorem modProjectionFiberSummandsIso_hom_apply (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (z : ⨁ x : GeometricFiberPoint B f s,
      (((modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F ⊗
        (modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G :
          ModuleCat.{max (u + 1) v} Λ) : Type _))
    (x : GeometricFiberPoint B f s) :
    (modProjectionFiberSummandsIso.{u, v} B Λ f s F G).hom z x =
      (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).hom (z x) :=
  rfl

/-- The germ of a generator, read through both decompositions of the fibre, componentwise. -/
public theorem moduleFiberStalksIso_modFiniteSupportFiberIso_generator
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (s : GeometricPoint Y.obj)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      U.1).obj E) (x : GeometricFiberPoint B f s) :
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom
        ((modFiniteSupportFiberIso B Λ f F s).hom
          ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F)
            (modFiniteSupportGenerator B Λ f F U.1 E a))) x =
      modFiberComponent B Λ f F s U.1 U.2 E a x := by
  rw [modFiniteSupportFiberIso_generator B Λ f F s U E a]
  exact moduleEtaleStalkIso_fiberStalkComponent B Λ f F s U.1 U.2 E a x

/-- The fibre comparison, with its first four legs exposed: the last two are the inverses of
the forward decomposition of the target's fibre and cancel against it. -/
public theorem modProjectionFiberIso_hom_comp (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (modProjectionFiberIso.{u, v} B Λ f s F G).hom ≫
        (modFiniteSupportFiberIso B Λ f
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s).hom ≫
        (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom =
      (Functor.Monoidal.μIso
          ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).inv ≫
        (tensorIso (modFiniteSupportFiberIso B Λ f F s ≪≫
          moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F) (Iso.refl _)).hom ≫
        (modFiberStalksTensorIso.{u, v} B Λ f s F
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom ≫
        (modProjectionFiberSummandsIso.{u, v} B Λ f s F G).hom := by
  dsimp only [modProjectionFiberIso]
  exact Stacks.iso_trans_tail_cancel _ _ _ _ _ _

/-- **The fibre comparison on the germ of a pure tensor**, componentwise: in the summand at a
point `x̄` of the geometric fibre the germ of `p ⊗ t` goes to the summandwise comparison applied
to the `x̄`-component of the germ of `p` tensored with the germ of `t`. -/
public theorem modProjectionFiberIso_germ_tmul (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (p : ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op U.1))
    (t : G.obj.obj (op U.1)) (x : GeometricFiberPoint B f s) :
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom
        ((modFiniteSupportFiberIso B Λ f
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s).hom
          ((modProjectionFiberIso.{u, v} B Λ f s F G).hom
            ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj)
              (p ⊗ₜ[Λ] t)))) x =
      (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).hom
        ((moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom
            ((modFiniteSupportFiberIso B Λ f F s).hom
              ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
                ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) p)) x ⊗ₜ[Λ]
          (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2 G.obj t) := by
  have hδ : (Functor.Monoidal.μIso
        ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).inv
      ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) (p ⊗ₜ[Λ] t)) =
      (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) p ⊗ₜ[Λ]
        (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2 G.obj t :=
    ConcreteCategory.congr_hom
      ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber_δ U.1 U.2
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj) (p ⊗ₜ[Λ] t)
  have h : ((modFiberStalksTensorIso.{u, v} B Λ f s F
          ((modStalkFunctor.{u, v, max (u + 1) v} B Λ Y s).obj G)).hom
        ((tensorIso (modFiniteSupportFiberIso B Λ f F s ≪≫
            moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F) (Iso.refl _)).hom
          ((Functor.Monoidal.μIso
              ((geometricPointSitePoint B Y.obj Y.property s).presheafFiber)
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj).inv
            ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj)
              (p ⊗ₜ[Λ] t))))) x =
      (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s F).hom
          ((modFiniteSupportFiberIso B Λ f F s).hom
            ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) p)) x ⊗ₜ[Λ]
        (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2 G.obj t := by
    rw [hδ]
    exact modFiberStalksTensorIso_hom_apply B Λ f s F _ _ _ x
  refine Eq.trans (DFunLike.congr_fun
    (ConcreteCategory.congr_hom (modProjectionFiberIso_hom_comp B Λ f s F G)
      ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj)
        (p ⊗ₜ[Λ] t))) x) ?_
  exact congrArg (fun z => (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).hom z) h

/-- **The fibre comparison on the germ of a generator tensored with a germ**, componentwise:
the germ of `(Z, a) ⊗ t` goes to the germ of the supported section `a ⊗ f^{-1}t`. -/
public theorem modProjectionFiberIso_germ_generator (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      U.1).obj E) (t : G.obj.obj (op U.1)) (x : GeometricFiberPoint B f s) :
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom
        ((modFiniteSupportFiberIso B Λ f
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s).hom
          ((modProjectionFiberIso.{u, v} B Λ f s F G).hom
            ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
              ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj)
              (modFiniteSupportGenerator B Λ f F U.1 E a ⊗ₜ[Λ] t)))) x =
      modFiberComponent B Λ f (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s U.1 U.2 E
        (tensorSupportedSectionsHom B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f U.1) (modPullbackUnitSection B Λ f G U.1 t) E.1
          (finiteSupport_isLocallyClosed B f U.1 E) a) x := by
  rw [modProjectionFiberIso_germ_tmul B Λ f s F G U _ t x,
    moduleFiberStalksIso_modFiniteSupportFiberIso_generator B Λ f F s U E a x]
  exact modProjectionFiberSummandIso_germ B Λ f s F G U.1 U.2 E a t x

/-- **The projection map on the germ of a generator tensored with a germ**, componentwise: the
recipe `(Z, a) ⊗ t ↦ (Z, a ⊗ f^{-1}t)` lands on the same germ. -/
public theorem modFiniteSupportTensorBilinear_germ_generator (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      U.1).obj E) (t : G.obj.obj (op U.1)) (x : GeometricFiberPoint B f s) :
    (moduleFiberStalksIso.{u, v, max (u + 1) v} B Λ f s
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).hom
        ((modFiniteSupportFiberIso B Λ f
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s).hom
          ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber U.1 U.2
            ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
              (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G))
            (modFiniteSupportTensorBilinear B Λ f F G U.1
              (modFiniteSupportGenerator B Λ f F U.1 E a ⊗ₜ[Λ] t)))) x =
      modFiberComponent B Λ f (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s U.1 U.2 E
        (tensorSupportedSectionsHom B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f U.1) (modPullbackUnitSection B Λ f G U.1 t) E.1
          (finiteSupport_isLocallyClosed B f U.1 E) a) x := by
  rw [show modFiniteSupportTensorBilinear B Λ f F G U.1
        (modFiniteSupportGenerator B Λ f F U.1 E a ⊗ₜ[Λ] t) =
      modFiniteSupportGenerator B Λ f (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) U.1 E
        (tensorSupportedSectionsHom B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f U.1) (modPullbackUnitSection B Λ f G U.1 t) E.1
          (finiteSupport_isLocallyClosed B f U.1 E) a) from
    ConcreteCategory.congr_hom (modFiniteSupportTensorHom_generator B Λ f F G U.1 t E) a]
  exact moduleFiberStalksIso_modFiniteSupportFiberIso_generator B Λ f
    (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s U E _ x

/-- **Stacks 0F6J for the `Λ`-linear finite-support direct image.** Every section of `f_{p!}F`
over a test object is a finite sum of generators. -/
public theorem exists_modFiniteSupportGenerator_sum
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ) (V : SmallEtale B Y.obj Y.property)
    (w : ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F).obj (op V)) :
    ∃ (n : ℕ) (Z : Fin n → FiniteSupport B f V)
      (a : ∀ i, (finiteSupportDiagram B f
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V).obj (Z i)),
      w = ∑ i, modFiniteSupportGenerator B Λ f F V (Z i) (a i) := by
  obtain ⟨n, Z, a, ha⟩ := exists_finiteSupport_sum B f
    ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V
    (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).2.obj_eq
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) w)
  refine ⟨n, Z, a, ?_⟩
  have hid : eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).2.obj_eq
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) ≫
      eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).2.obj_eq
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V).symm = 𝟙 _ := by
    rw [eqToHom_trans, eqToHom_refl]
  refine Eq.trans (show w = eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).2.obj_eq
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V).symm
        (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).2.obj_eq
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) w)
        from (ConcreteCategory.congr_hom hid w).symm) ?_
  rw [ha]
  exact map_sum (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).2.obj_eq
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V).symm).hom
    (fun i => colimit.ι (finiteSupportDiagram B f
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V) (Z i) (a i)) Finset.univ

end AlgebraicGeometry.SmallEtale

end
