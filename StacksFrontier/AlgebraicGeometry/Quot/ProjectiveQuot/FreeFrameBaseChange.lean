module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.TwistPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FreeDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImageEpiFibre
public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackFreeIso

/-!
# The free frame of `π_*(𝒪^{⊕ r}(m))` commutes with base change

`AlgebraicGeometry.ProjectiveQuot.pushforwardTwistFreeModuleIso` identifies `π_*(𝒪^{⊕ r}(m))`
on `T` with the free module `𝒪_T^{⊕ N}`, `N = freeRank n r m`, on the degree-`m` monomials in
`r` copies. For `g : T' ⟶ T` the pullback of this frame, followed by the base-change morphism
`g^* π_* ⟶ π'_* (ℙⁿ_g)^*` and the identification `(ℙⁿ_g)^*(𝒪^{⊕ r}(m)) ≅ 𝒪^{⊕ r}(m)`, is the
frame over `T'` (`AlgebraicGeometry.ProjectiveQuot.pushforwardTwistFreeModuleIso_baseChange`).
On each basis vector this is the stability of the monomial `T^e` under base change
(`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.toPushforwardTwistOver_baseChange`)
together with that of the left unit constraint
(`AlgebraicGeometry.ProjectiveQuot.pullback_map_tensorLeftUnitor_hom_twistingSheaf`).

This is what makes the point of the Grassmannian attached to `K ∈ Quot^P(T)` in the proof of
Stacks 0DPA natural in `T`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.ιFree_pushforwardTwistFreeModuleIso_inv`: the frame on a
  basis vector.
* `AlgebraicGeometry.ProjectiveQuot.pullback_map_ι_twistFreeModuleIso_inv`.
* `AlgebraicGeometry.ProjectiveQuot.pushforwardTwistFreeModuleIso_baseChange`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)

universe u

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveQuot

/-- A functor preserving a coproduct carries each coproduct inclusion to the inclusion. -/
@[reassoc]
theorem map_ι_comp_preservesCoproduct_iso_hom {C : Type*} [Category* C] {D : Type*} [Category* D]
    (G : C ⥤ D) {J : Type*} (f : J → C) [HasCoproduct f] [HasCoproduct fun j => G.obj (f j)]
    [PreservesColimit (Discrete.functor f) G] (j : J) :
    G.map (Sigma.ι f j) ≫ (PreservesCoproduct.iso G f).hom = Sigma.ι (fun j => G.obj (f j)) j := by
  rw [← cancel_mono (PreservesCoproduct.iso G f).inv, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

variable {n r : ℕ}

/-- The identification `𝒪^{⊕ r}(d) ≅ 𝒪(d)^{⊕ r}` on the `j`-th summand. -/
theorem ι_twistFreeModuleIso_inv (T : Scheme.{u}) (d : ℤ) (j : Fin r) :
    Sigma.ι (fun _ : Fin r => twistingSheaf n T d) j ≫ (twistFreeModuleIso n r T d).inv =
      (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T d)).inv ≫
        (twistFunctor n T d).map
          (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j) := by
  rw [twistFreeModuleIso, Iso.trans_inv]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Sigma.ι_mapIso_inv _ j)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (ι_comp_sigmaComparison _ _ j)

/-- The identification `(ℙⁿ_g)^* 𝒪^{⊕ r} ≅ 𝒪^{⊕ r}` on the `j`-th summand. -/
theorem pullback_map_ι_freeModulePullbackIso_hom {T' T : Scheme.{u}} (g : T' ⟶ T) (j : Fin r) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j) ≫
        (freeModulePullbackIso n r g).hom =
      (Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)).hom ≫
        Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T')) j := by
  rw [freeModulePullbackIso, Iso.trans_hom, map_ι_comp_preservesCoproduct_iso_hom_assoc,
    Sigma.ι_mapIso_hom]

/-- A map of index types acts on the basis vectors of a free module. -/
theorem ιFree_freeFunctor_map {X : Scheme.{u}} {I J : Type u} (φ : I ⟶ J) (i : I) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ SheafOfModules.freeFunctor.map φ =
      SheafOfModules.ιFree (φ i) := by
  simp

/-- **The frame of `π_*(𝒪^{⊕ r}(m))` on a basis vector**: the monomial `T^e` in the `j`-th
summand, for `(j, e) = freeRankEquiv n r m i`. -/
theorem ιFree_pushforwardTwistFreeModuleIso_inv (T : Scheme.{u}) (m : ℕ)
    (i : ULift.{u} (Fin (freeRank.{u} n r m))) :
    SheafOfModules.ιFree i ≫ (pushforwardTwistFreeModuleIso (n := n) (r := r) T m).inv =
      monomialBasisHom n T (m : ℤ) (freeRankEquiv n r m i).2 ≫
        toPushforwardTwistOver n T (m : ℤ) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map
          (Sigma.ι (fun _ : Fin r => twistingSheaf n T (m : ℤ)) (freeRankEquiv n r m i).1 ≫
            (twistFreeModuleIso n r T m).inv) := by
  rw [pushforwardTwistFreeModuleIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (ιFree_freeFunctor_map _ i)).trans
      (Sigma.ι_comp_desc _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Sigma.ι_mapIso_inv _ _)).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (ι_comp_sigmaComparison _ _ _)).trans ?_
  exact (Functor.map_comp _ _ _).symm

/-- Inverting the two outer isomorphisms of a commutative square. -/
theorem inv_comp_eq_comp_inv_of_hom_comp {C : Type*} [Category* C] {W X Y Z : C} (e : W ≅ X)
    (e' : Y ≅ Z) (v : X ⟶ Z) (p : W ⟶ Y) (h : e.hom ≫ v = p ≫ e'.hom) :
    e.inv ≫ p = v ≫ e'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The bookkeeping of `pullback_map_ι_twistFreeModuleIso_inv`, in an arbitrary category. -/
theorem chain_of_five {C : Type*} [Category* C] {A B D E F G H K : C}
    (x : A ⟶ E) (a1 : A ⟶ B) (a2 : B ⟶ E) (b : E ⟶ F) (c : F ⟶ G) (bO : B ⟶ D) (k : D ⟶ F)
    (p : D ⟶ H) (q : H ⟶ G) (v : A ⟶ K) (l : K ⟶ H) (y : K ⟶ G)
    (H0 : x = a1 ≫ a2) (H1 : a2 ≫ b = bO ≫ k) (H2 : k ≫ c = p ≫ q)
    (H3 : a1 ≫ bO ≫ p = v ≫ l) (H4 : y = l ≫ q) :
    x ≫ b ≫ c = v ≫ y := by
  rw [H0, H4, Category.assoc, reassoc_of% H1, H2, ← reassoc_of% H3]

/-- The left unit constraint of `𝒪(d)` and the base change, in the inverse direction. -/
theorem pullback_map_tensorLeftUnitor_inv_twistingSheaf {T' T : Scheme.{u}} (g : T' ⟶ T)
    (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T d)).inv ≫
        (twistPullbackIso g d (Scheme.unitModule (projectiveSpaceOver n T))).inv ≫
        twistMap d (Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)).hom =
      (twistingSheafPullbackIso n g d).hom ≫
        (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T' d)).inv :=
  inv_comp_eq_comp_inv_of_hom_comp
    ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).mapIso
      (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T d)))
    (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T' d)) _ _
    (pullback_map_tensorLeftUnitor_hom_twistingSheaf (n := n) g d)

/-- **The twisted free module on one summand, under base change.** The pullback of the inclusion
`𝒪(d) ⟶ 𝒪^{⊕ r}(d)` of the `j`-th summand, read through the base-change isomorphisms, is the
inclusion of the `j`-th summand over `T'`. -/
theorem pullback_map_ι_twistFreeModuleIso_inv {T' T : Scheme.{u}} (g : T' ⟶ T) (d : ℤ)
    (j : Fin r) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (Sigma.ι (fun _ : Fin r => twistingSheaf n T d) j ≫ (twistFreeModuleIso n r T d).inv) ≫
        (twistPullbackIso g d (freeModule n r T)).inv ≫
        twistMap d (freeModulePullbackIso n r g).hom =
      (twistingSheafPullbackIso n g d).hom ≫
        Sigma.ι (fun _ : Fin r => twistingSheaf n T' d) j ≫ (twistFreeModuleIso n r T' d).inv := by
  have hnat := twistPullbackIso_hom_naturality g d
    (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j)
  have key (S : Scheme.{u}) :
      Sigma.ι (fun _ : Fin r => twistingSheaf n S d) j ≫ (twistFreeModuleIso n r S d).inv =
        (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n S d)).inv ≫
          twistMap d (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n S)) j) :=
    (ι_twistFreeModuleIso_inv S d j).trans
      (congrArg (_ ≫ ·) (twistMap_eq_twistFunctor_map d _).symm)
  have H0 := (congrArg (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (key T)).trans
    (Functor.map_comp _ _ _)
  have H1 := inv_comp_eq_comp_inv_of_hom_comp
    (twistPullbackIso g d (Scheme.unitModule (projectiveSpaceOver n T)))
    (twistPullbackIso g d (freeModule n r T)) _ _ hnat.symm
  have H2 : twistMap d ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) j)) ≫
        twistMap d (freeModulePullbackIso n r g).hom =
      twistMap d (Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)).hom ≫
        twistMap d (Sigma.ι (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T')) j) := by
    rw [twistMap_eq_twistFunctor_map, twistMap_eq_twistFunctor_map, twistMap_eq_twistFunctor_map,
      twistMap_eq_twistFunctor_map, ← Functor.map_comp, ← Functor.map_comp,
      pullback_map_ι_freeModulePullbackIso_hom]
  exact chain_of_five _ _ _ _ _ _ _ _ _ _ _ _ H0 H1.symm H2
    (pullback_map_tensorLeftUnitor_inv_twistingSheaf (n := n) g d) (key T')

/-- The bookkeeping of `pushforwardTwistFreeModuleIso_baseChange`, in an arbitrary category. -/
theorem chain_of_frames {C : Type*} [Category* C] {A A' B B' D E F G H K : C}
    (x : A ⟶ E) (gm : A ⟶ B) (gt : B ⟶ D) (gp : D ⟶ E) (bcF : E ⟶ F) (pΦ : F ⟶ G)
    (bcL : D ⟶ H) (pφ : H ⟶ F) (pO : H ⟶ K) (pφ' : K ⟶ G) (iso : B ⟶ B') (t' : B' ⟶ K)
    (u : A ⟶ A') (m' : A' ⟶ B') (y : A' ⟶ G)
    (H0 : x = gm ≫ gt ≫ gp) (H1 : gp ≫ bcF = bcL ≫ pφ) (H2 : pφ ≫ pΦ = pO ≫ pφ')
    (H3a : gt ≫ bcL ≫ pO = iso ≫ t') (H3b : gm ≫ iso = u ≫ m') (H4 : y = m' ≫ t' ≫ pφ') :
    x ≫ bcF ≫ pΦ = u ≫ y := by
  rw [H0, H4, Category.assoc, Category.assoc, reassoc_of% H1, H2, ← Category.assoc bcL,
    ← Category.assoc gt, H3a, Category.assoc, ← Category.assoc gm, H3b, Category.assoc]

/-- Morphisms out of the pullback of a free module are determined on the summands. -/
theorem pullback_free_hom_ext {X Y : Scheme.{u}} (g : X ⟶ Y) (N : ℕ) {M : X.Modules}
    {φ ψ : (Scheme.Modules.pullback g).obj
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin N))) ⟶ M}
    (h : ∀ i, (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i) ≫ φ =
      (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i) ≫ ψ) : φ = ψ := by
  have : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  rw [← cancel_epi (Grassmannian.pullbackFreeIso g N).inv]
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ fun i => ?_
  have hi := Grassmannian.pullback_map_ιFree_comp_pullbackFreeIso_hom g N i
  have hi' := (inv_comp_eq_comp_inv_of_hom_comp (Scheme.Modules.pullbackUnitIso g)
    (Grassmannian.pullbackFreeIso g N) _ _ hi.symm).symm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) hi').trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h i)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) hi'.symm).trans
        (Category.assoc _ _ _))))))

variable (n r) in
/-- **The free frame of `π_*(𝒪^{⊕ r}(m))` commutes with base change.** For `g : T' ⟶ T` the
pullback of the frame `𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))`, followed by the base-change morphism and the
identification `(ℙⁿ_g)^*(𝒪^{⊕ r}(m)) ≅ 𝒪^{⊕ r}(m)`, is the frame over `T'` read through
`g^* 𝒪_T^{⊕ N} ≅ 𝒪_{T'}^{⊕ N}`. -/
theorem pushforwardTwistFreeModuleIso_baseChange {T' T : Scheme.{u}} (g : T' ⟶ T) (m : ℕ) :
    (Scheme.Modules.pullback g).map (pushforwardTwistFreeModuleIso (n := n) (r := r) T m).inv ≫
        (baseChangeNatTrans (isPullback_projectiveSpaceOverMap n g).w).app
          (twist (m : ℤ) (freeModule n r T)) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n T' ↘ T')).map
          ((twistPullbackIso g (m : ℤ) (freeModule n r T)).inv ≫
            twistMap (m : ℤ) (freeModulePullbackIso n r g).hom) =
      (Grassmannian.pullbackFreeIso g (freeRank.{u} n r m)).hom ≫
        (pushforwardTwistFreeModuleIso (n := n) (r := r) T' m).inv := by
  refine pullback_free_hom_ext g _ fun i => ?_
  have hi := Grassmannian.pullback_map_ιFree_comp_pullbackFreeIso_hom g (freeRank.{u} n r m) i
  have H0 := (Functor.map_comp (Scheme.Modules.pullback g) _ _).symm.trans
    ((congrArg (Scheme.Modules.pullback g).map
      (ιFree_pushforwardTwistFreeModuleIso_inv T m i)).trans
      ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))))
  have H1 := ((baseChangeNatTrans (isPullback_projectiveSpaceOverMap n g).w).naturality
    (Sigma.ι (fun _ : Fin r => twistingSheaf n T (m : ℤ)) (freeRankEquiv n r m i).1 ≫
      (twistFreeModuleIso n r T m).inv))
  have H2 := ((Functor.map_comp (Scheme.Modules.pushforward
      (projectiveSpaceOver n T' ↘ T')) _ _).symm.trans
    ((congrArg (Scheme.Modules.pushforward (projectiveSpaceOver n T' ↘ T')).map
      (pullback_map_ι_twistFreeModuleIso_inv (n := n) (r := r) g (m : ℤ)
        (freeRankEquiv n r m i).1)).trans
      (Functor.map_comp _ _ _)))
  have H3a := toPushforwardTwistOver_baseChange n g (m : ℤ)
  have H3b := pullback_map_monomialBasisHom_comp_pullbackBaseDegreeSheafIso_hom n g (m : ℤ)
    (freeRankEquiv n r m i).2
  refine (chain_of_frames (C := T'.Modules) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H2 H3a H3b
    (by exact ιFree_pushforwardTwistFreeModuleIso_inv T' m i)).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hi.symm).trans (Category.assoc _ _ _))

end AlgebraicGeometry.ProjectiveQuot

end
