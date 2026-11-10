module

public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.SheavesOverSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# Relocalization at a morphism of semi-representable objects

Let `(C, J)` be a site and `f : K ⟶ L` a morphism of semi-representable objects of `C`, given by
a map `α : K.I → L.I` of index sets together with morphisms `f_i : K.obj i ⟶ L.obj (α i)`. It
induces a relocalization morphism of sites `C / K ⟶ C / L`, whose inverse image functor
`f^{-1} : Sh(C / L) ⥤ Sh(C / K)` is componentwise inverse image along
`Over.map f_i : C / K.obj i ⥤ C / L.obj (α i)`.

Stacks 0D87 part (3) asserts that under the equivalences of part (1), `f^{-1}` corresponds to base
change along `F(K)^♯ ⟶ F(L)^♯`, i.e. `(G ⟶ F(L)^♯) ↦ (G ×_{F(L)^♯} F(K)^♯ ⟶ F(K)^♯)`.

Following the source, this is Stacks 04IL applied to each re-localization morphism
`C / K.obj i ⟶ C / L.obj (α i)`, assembled over the index set. The assembling step is the content
of `assembleOverPullbackIso`: for a van Kampen coproduct, assembling a family of slices commutes
with base change along a morphism of the coproducts that is compatible with the injections.

## Main definitions

* `CategoryTheory.SemiRepresentable.formalCoproductSheafificationMap`: the morphism
  `F(K)^♯ ⟶ F(L)^♯` induced by a morphism of semi-representable objects.
* `CategoryTheory.SemiRepresentable.componentwiseRelocalization`: the relocalization inverse image
  functor `f^{-1} : Sh(C / L) ⥤ Sh(C / K)` in the componentwise presentations.

## Main results

* `CategoryTheory.SemiRepresentable.assembleOverAdjunction`: assembling the slices over the
  summands of a van Kampen coproduct is left adjoint to componentwise base change along the
  injections.
* `CategoryTheory.SemiRepresentable.assembleOverPullbackIso`: assembling commutes with base change
  along a morphism of van Kampen coproducts.
* `CategoryTheory.SemiRepresentable.sliceHasWeakSheafify`: a localized site of a site with weak
  sheafification has weak sheafification.
* `SemiRepresentable.componentwiseRelocalization_comp_sheafEquivalence_iso_pullback`: under the
  identifications `sheafEquivalence`, relocalization along `f : K ⟶ L` is base change along
  `F(K)^♯ ⟶ F(L)^♯`.

## Implementation notes

The four `assembleOver` results are stated for an arbitrary category with pullbacks and
coproducts, since that is the generality in which `assembleOver` itself and its unit isomorphism
`assembleOverCompPullbackIso` are available; only `sliceHasWeakSheafify` onwards is about sites.

`sliceHasWeakSheafify` is the one input of part (3) that the Stacks source does not mention: the
statement of part (3) names `Sh(C / K.obj i)` and the inverse-image functors between the localized
sites, so those sites must have sheafification, and the source takes that for granted. It is
obtained from Stacks 00Y1: `Sh(C / U) ≌ Sh(C) / h_U^♯` carries the sheafification of `Sh(C)` and
the slice adjunctions over to a left adjoint of the inclusion of sheaves on `C / U`.

The coefficient universe and the instance hypotheses are those of part (1): `HasWeakSheafify` for
the constructions, and `HasSheafify` together with
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` wherever the equivalence of part (1)
is named. See the implementation notes of
`StacksFrontier.CategoryTheory.Sites.SemiRepresentable.SheavesOverSheafification`.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 04IL](https://stacks.math.columbia.edu/tag/04IL)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SemiRepresentable

universe u v w u' v'

/-! ### Assembling the slices over a van Kampen coproduct, and base change -/

section Assemble

variable {D : Type u} [Category.{v} D] [HasPullbacks D] [HasCoproducts.{w} D]

/-- **Assembling is left adjoint to componentwise base change along the injections.** This is the
adjunction underlying `isEquivalence_assembleOver`: `assembleOverCompPullbackIso` is its unit, and
`assembleOver` is an equivalence, so componentwise base change is its quasi-inverse. -/
noncomputable def assembleOverAdjunction {I : Type w} {X : I → D}
    (c : Cocone (Discrete.functor X)) (hVK : IsVanKampenColimit c) :
    assembleOver c ⊣ Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩) := by
  have := isEquivalence_assembleOver c hVK
  exact (assembleOver c).asEquivalence.toAdjunction.ofNatIsoRight <|
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (assembleOver c).inv (assembleOverCompPullbackIso c hVK).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (assembleOver c).asEquivalence.counitIso _ ≪≫
      Functor.leftUnitor _

/-- Componentwise base change along the injections of a van Kampen coproduct is an equivalence.
This is `overCoproductEquivalence` read off `assembleOverAdjunction`. -/
theorem isEquivalence_piPullbackCocone {I : Type w} {X : I → D}
    (c : Cocone (Discrete.functor X)) (hVK : IsVanKampenColimit c) :
    (Functor.pi' fun i => Over.pullback (c.ι.app ⟨i⟩)).IsEquivalence :=
  have := isEquivalence_assembleOver c hVK
  (assembleOverAdjunction c hVK).isEquivalence_right_of_isEquivalence_left

/-- **Assembling commutes with base change.** Let `c` and `d` be van Kampen coproducts, let
`g : I → J`, `a i : X i ⟶ Y (g i)` and `f : c.pt ⟶ d.pt` be compatible with the injections. Then
base changing an assembled family along `f` is the same as base changing each summand along `a i`
and assembling.

Both sides become the same functor after composing with componentwise base change along `c`'s
injections — on the left because base change along `c.ι.app ⟨i⟩ ≫ f = a i ≫ d.ι.app ⟨g i⟩` may be
computed either way, on the right because `assembleOverCompPullbackIso` cancels — and that functor
is an equivalence, hence in particular fully faithful. -/
noncomputable def assembleOverPullbackIso {I J : Type w} {X : I → D} {Y : J → D}
    (c : Cocone (Discrete.functor X)) (hVKc : IsVanKampenColimit c)
    (d : Cocone (Discrete.functor Y)) (hVKd : IsVanKampenColimit d)
    (g : I → J) (a : (i : I) → X i ⟶ Y (g i)) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, c.ι.app ⟨i⟩ ≫ f = a i ≫ d.ι.app ⟨g i⟩) :
    assembleOver d ⋙ Over.pullback f ≅
      (Functor.pi' fun i : I =>
        Pi.eval (fun j : J => Over (Y j)) (g i) ⋙ Over.pullback (a i)) ⋙ assembleOver c := by
  let Bc : Over c.pt ⥤ (∀ i : I, Over (X i)) :=
    Functor.pi' (fun i : I => Over.pullback (c.ι.app ⟨i⟩))
  let Bd : Over d.pt ⥤ (∀ j : J, Over (Y j)) :=
    Functor.pi' (fun j : J => Over.pullback (d.ι.app ⟨j⟩))
  let Ac := assembleOver c
  let Ad := assembleOver d
  let Q : ((j : J) → Over (Y j)) ⥤ ((i : I) → Over (X i)) :=
    Functor.pi' (fun i : I => Pi.eval (fun j : J => Over (Y j)) (g i) ⋙ Over.pullback (a i))
  let hleft : (Ad ⋙ Over.pullback f) ⋙ Bc ≅ Q := by
    refine NatIso.pi' fun i => ?_
    let ci := c.ι.app ⟨i⟩
    let dj := d.ι.app ⟨g i⟩
    let evalY := Pi.eval (fun j : J => Over (Y j)) (g i)
    let evalX := Pi.eval (fun i : I => Over (X i)) i
    have hEvalX : Bc ⋙ evalX = Over.pullback ci := by dsimp [Bc, evalX, ci]
    calc
      ((Ad ⋙ Over.pullback f) ⋙ Bc) ⋙ evalX ≅ Ad ⋙ Over.pullback f ⋙ Over.pullback ci :=
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (Ad ⋙ Over.pullback f) (eqToIso hEvalX)
      _ ≅ Ad ⋙ (Over.pullback f ⋙ Over.pullback ci) :=
        (Functor.associator Ad (Over.pullback f) (Over.pullback ci)).symm
      _ ≅ Ad ⋙ Over.pullback (ci ≫ f) :=
        Functor.isoWhiskerLeft Ad (Over.pullbackComp ci f).symm
      _ ≅ Ad ⋙ Over.pullback (a i ≫ dj) :=
        Functor.isoWhiskerLeft Ad (eqToIso (congrArg (fun k => Over.pullback k) (hf i)))
      _ ≅ Ad ⋙ Over.pullback dj ⋙ Over.pullback (a i) :=
        Functor.isoWhiskerLeft Ad (Over.pullbackComp (a i) dj)
      _ ≅ (Ad ⋙ Over.pullback dj) ⋙ Over.pullback (a i) := (Functor.associator _ _ _).symm
      _ ≅ evalY ⋙ Over.pullback (a i) :=
        Functor.isoWhiskerRight ((Functor.associator Ad Bd evalY).symm ≪≫
          Functor.isoWhiskerRight (assembleOverCompPullbackIso d hVKd) evalY ≪≫
            Functor.leftUnitor evalY) (Over.pullback (a i))
  let hright : (Q ⋙ Ac) ⋙ Bc ≅ Q :=
    Functor.associator Q Ac Bc ≪≫
      Functor.isoWhiskerLeft Q (assembleOverCompPullbackIso c hVKc)
  have : Bc.IsEquivalence := isEquivalence_piPullbackCocone c hVKc
  exact Functor.fullyFaithfulCancelRight Bc (hleft ≪≫ hright.symm)

end Assemble

/-! ### Sheafification on a localized site -/

variable {C : Type u} [Category.{v} C]

/-- The product of a family indexed by `PUnit` is the category itself. -/
noncomputable def singletonPiEquivalence (D : Type u') [Category.{v'} D] :
    ((_ : PUnit) → D) ≌ D where
  functor := Pi.eval (fun _ : PUnit => D) PUnit.unit
  inverse := Functor.pi' (fun _ : PUnit => 𝟭 D)
  unitIso := NatIso.ofComponents (fun X => Pi.isoMk (fun i => by
    cases i
    exact Iso.refl _)) (by
      intro X Y f
      ext i
      cases i
      exact (Category.comp_id (f PUnit.unit)).trans (Category.id_comp (f PUnit.unit)).symm)
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _

/-- **A localized site of a site with weak sheafification has weak sheafification.**

By Stacks 00Y1, `Sh(C / U) ≌ Sh(C) / h_U^♯`. On the other side, presheaves on `C / U` are
presheaves on `C` over `h_U` (`OverShriek.presheafEquivalence`), sheafification of `Sh(C)` induces
a left adjoint on slices (`Over.postAdjunctionLeft`), and base change along `h_U ⟶ h_U^♯` is right
adjoint to postcomposition. Composing the three adjunctions exhibits a left adjoint of a functor
that `OverShriek.sheafFiberFunctor` identifies with the inclusion of sheaves into presheaves. -/
theorem sliceHasWeakSheafify (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]
    [J.WEqualsLocallyBijective (Type v)] (U : C) :
    HasWeakSheafify (J.over U) (Type v) := by
  let E := CategoryTheory.OverShriek.presheafEquivalence (U := U)
  let F := CategoryTheory.OverShriek.sheafEquivalence (U := U) J
  let P := presheafToSheaf J (Type v)
  let I := sheafToPresheaf J (Type v)
  let η := toSheafify J (yoneda.obj U)
  let L := E.functor ⋙ Over.post P ⋙ F.inverse
  let R := F.functor ⋙ Over.post I ⋙ Over.pullback η ⋙ E.inverse
  let h₀ : (E.functor ⋙ Over.post P) ⊣ (Over.post I ⋙ Over.pullback η ⋙ E.inverse) :=
    E.toAdjunction.comp (Over.postAdjunctionLeft (sheafificationAdjunction J (Type v)))
  have h : L ⊣ R := h₀.comp F.symm.toAdjunction
  have hBase : Over.post I ⋙ Over.pullback η ⋙ E.inverse ≅
      CategoryTheory.OverShriek.sheafFiberUnderlying (U := U) J := by
    let pfEquiv (T : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)))
        (W : (Over U)ᵒᵖ) :
        (CategoryTheory.OverShriek.fiber (𝟙 (yoneda.obj U))
          (pullback.snd ((Over.post (sheafToPresheaf J (Type v))).obj T).hom
            (toSheafify J (yoneda.obj U)))).obj W ≃
        (CategoryTheory.OverShriek.fiber (toSheafify J (yoneda.obj U))
          ((Over.post (sheafToPresheaf J (Type v))).obj T).hom).obj W := by
      let φ := ((Over.post (sheafToPresheaf J (Type v))).obj T).hom
      let X := op W.unop.left
      let eval := (evaluation Cᵒᵖ (Type v)).obj X
      let ePB := (asIso (pullbackComparison eval φ η)).toEquiv.trans
        (Types.pullbackIsoPullback (eval.map φ) (eval.map η)).toEquiv
      have hePB (y : eval.obj (pullback φ η)) :
          (ePB y).val = ((pullback.fst φ η).app X y, (pullback.snd φ η).app X y) :=
        Prod.ext (by exact congr_arg (fun t => t y) (pullbackComparison_comp_fst eval φ η))
          (by exact congr_arg (fun t => t y) (pullbackComparison_comp_snd eval φ η))
      have hcond (y : eval.obj (pullback φ η)) :
          φ.app X ((pullback.fst φ η).app X y) =
            η.app X ((pullback.snd φ η).app X y) := by
        simpa using congrArg (fun t => t.app X y)
          (pullback.condition (f := φ) (g := η))
      have hpair (y : eval.obj (pullback φ η)) (b : (yoneda.obj U).obj X)
          (hb : (pullback.snd φ η).app X y = b) :
          φ.app X ((pullback.fst φ η).app X y) = η.app X b :=
        (hcond y).trans (congrArg (η.app X) hb)
      refine {
        toFun := fun x => ?_
        invFun := fun x => ?_
        left_inv := ?_
        right_inv := ?_ }
      · exact ⟨(pullback.fst φ η).app X x.1, hpair x.1 W.unop.hom x.2⟩
      · refine ⟨ePB.symm ⟨⟨x.1, W.unop.hom⟩, ?_⟩, ?_⟩
        · change φ.app X x.1 = η.app X W.unop.hom
          exact x.2
        · have hInv : (asIso (pullbackComparison eval φ η)).inv ≫
              eval.map (pullback.snd φ η) = pullback.snd (eval.map φ) (eval.map η) := by
            rw [← pullbackComparison_comp_snd]
            simp
          change ((asIso (pullbackComparison eval φ η)).inv ≫
            eval.map (pullback.snd φ η))
              ((Types.pullbackIsoPullback (eval.map φ) (eval.map η)).inv
                ⟨⟨x.1, W.unop.hom⟩, by exact x.2⟩) = W.unop.hom
          rw [hInv]
          simp
      · intro x
        apply Subtype.ext
        apply ePB.injective
        rw [ePB.apply_symm_apply]
        apply Subtype.ext
        rw [hePB]
        exact Prod.ext rfl x.2.symm
      · intro x
        apply Subtype.ext
        have h := hePB (ePB.symm ⟨⟨x.1, W.unop.hom⟩, x.2⟩)
        rw [ePB.apply_symm_apply] at h
        exact (congrArg (·.1) h).symm
    refine NatIso.ofComponents (fun T => ?_) ?_
    · refine NatIso.ofComponents (fun W => Equiv.toIso (pfEquiv T W)) ?_
      intro W W' k
      ext x
      apply Subtype.ext
      let φ := ((Over.post I).obj T).hom
      change (pullback.fst φ η).app (op W'.unop.left)
          ((pullback φ η).map k.unop.left.op x.1) =
        ((Over.post I).obj T).left.map k.unop.left.op
          ((pullback.fst φ η).app (op W.unop.left) x.1)
      exact NatTrans.naturality_apply (pullback.fst φ η) k.unop.left.op x.1
    · intro T T' g
      ext W x
      apply Subtype.ext
      let φ := ((Over.post I).obj T).hom
      let φ' := ((Over.post I).obj T').hom
      let k := (Over.post I).map g
      change (pullback.fst φ' η).app (op W.unop.left)
          (((Over.pullback η).map k).left.app (op W.unop.left) x.1) =
        k.left.app (op W.unop.left)
          ((pullback.fst φ η).app (op W.unop.left) x.1)
      have hSq :
          pullback.lift (pullback.fst φ η ≫ k.left) (pullback.snd φ η)
              (by
                rw [Category.assoc, Over.w k]
                exact pullback.condition) ≫
              pullback.fst φ' η = pullback.fst φ η ≫ k.left :=
        pullback.lift_fst _ _ _
      have h2 := congrArg (fun q => q.app (op W.unop.left) x.1) hSq
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h2
      dsimp [Over.pullback]
      exact h2
  have hUnderlying : CategoryTheory.OverShriek.sheafFiberUnderlying (U := U) J ≅
      CategoryTheory.OverShriek.sheafFiberFunctor J ⋙
        sheafToPresheaf (J.over U) (Type v) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have hFiber : F.functor ⊣ CategoryTheory.OverShriek.sheafFiberFunctor J :=
    h₀.restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf (J.over U) (Type v))
      (Functor.FullyFaithful.id _)
      (by rfl)
      (hBase ≪≫ hUnderlying)
  have : ∀ X, IsIso (hFiber.unit.app X) := fun _ => inferInstance
  have hR : R ≅ sheafToPresheaf (J.over U) (Type v) := by
    dsimp [R]
    calc
      F.functor ⋙ Over.post I ⋙ Over.pullback η ⋙ E.inverse ≅
          F.functor ⋙ CategoryTheory.OverShriek.sheafFiberUnderlying (U := U) J :=
        Functor.isoWhiskerLeft F.functor hBase
      _ ≅ F.functor ⋙ CategoryTheory.OverShriek.sheafFiberFunctor J ⋙
          sheafToPresheaf (J.over U) (Type v) :=
        Functor.isoWhiskerLeft F.functor hUnderlying
      _ ≅ sheafToPresheaf (J.over U) (Type v) :=
        Functor.isoWhiskerRight (asIso hFiber.unit).symm
          (sheafToPresheaf (J.over U) (Type v)) ≪≫ Functor.leftUnitor _
  exact ⟨L, ⟨h.ofNatIsoRight hR⟩⟩

/-- **Stacks 00XS for `Over.forget U`**: restriction `j_U^{-1} : Sh(C) ⥤ Sh(C / U)` has a left
adjoint. This is `sheafFunctorToOverForgetAdjunction` for the one-element semi-representable
object `K = {U}`, read through `singletonPiEquivalence`. -/
theorem sliceRestrictionIsRightAdjoint (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)] (U : C) [HasWeakSheafify (J.over U) (Type v)] :
    ((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint := by
  let K : FormalCoproduct.{v} C := ⟨PUnit, fun _ => U⟩
  let e := singletonPiEquivalence (Sheaf (J.over U) (Type v))
  have hR : componentwiseRestriction J K ⋙ e.functor ≅
      (Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J := by
    dsimp [e, singletonPiEquivalence, componentwiseRestriction, K]
    rfl
  exact ((e.symm.toAdjunction.comp (sheafFunctorToOverForgetAdjunction J K)).ofNatIsoRight
    hR).isRightAdjoint

/-- **Stacks 00XS for `Over.map f`**: relocalization inverse image
`Sh(C / U) ⥤ Sh(C / V)` has a left adjoint, namely the sheafification of the presheaf level
relocalization lower shriek of Stacks 04IK. -/
theorem relocalizationRestrictionIsRightAdjoint (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)] {V U : C} (f : V ⟶ U)
    [HasWeakSheafify (J.over V) (Type v)] [HasWeakSheafify (J.over U) (Type v)] :
    ((Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint := by
  let iV := sheafToPresheaf (J.over V) (Type v)
  let I := sheafToPresheaf (J.over U) (Type v)
  let P := presheafToSheaf (J.over U) (Type v)
  let Λ := CategoryTheory.OverShriek.relocalizePresheafFunctor f
  let res := CategoryTheory.OverShriek.relocalizeRestrict f
  let L := iV ⋙ (Λ ⋙ P)
  let R := (Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)
  have adj₀ : Λ ⋙ P ⊣ I ⋙ res :=
    (CategoryTheory.OverShriek.relocalizeAdjunction f).comp
      (sheafificationAdjunction (J.over U) (Type v))
  have hR : R ⋙ iV ≅ I ⋙ res := by
    simpa [R, I, res, GrothendieckTopology.overPullback] using
      (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
        (Over.map f) (Type v) (J.over V) (J.over U))
  exact (adj₀.restrictFullyFaithful (fullyFaithfulSheafToPresheaf (J.over V) (Type v))
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor L).symm hR.symm).isRightAdjoint

/-! ### Stacks 0D87 part (3) -/

variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- The morphism `F(K)^♯ ⟶ F(L)^♯` of associated sheaves induced by a morphism `f : K ⟶ L` of
semi-representable objects. -/
noncomputable def formalCoproductSheafificationMap {K L : FormalCoproduct.{v} C} (f : K ⟶ L) :
    formalCoproductSheafification J K ⟶ formalCoproductSheafification J L :=
  (presheafToSheaf J (Type v)).map ((FormalCoproduct.yoneda (C := C)).map f)

/-- `formalCoproductSheafificationMap` is compatible with the sheafified coproduct injections.
It is `CategoryTheory.Limits.Sigma.ι_desc` for `F(f) : ∐ i, h_{K.obj i} ⟶ ∐ j, h_{L.obj j}`
after sheafification, and it is the compatibility `assembleOverPullbackIso` consumes. -/
theorem formalCoproductSheafificationι_comp_map {K L : FormalCoproduct.{v} C} (f : K ⟶ L)
    (i : K.I) :
    formalCoproductSheafificationι J K i ≫ formalCoproductSheafificationMap J f =
      (presheafToSheaf J (Type v)).map (yoneda.map (f.φ i)) ≫
        formalCoproductSheafificationι J L (f.f i) :=
  ((presheafToSheaf J (Type v)).map_comp _ _).symm.trans
    ((congrArg (presheafToSheaf J (Type v)).map
      (Sigma.ι_comp_desc (fun j => yoneda.map (f.φ j) ≫
        Sigma.ι (fun j : L.I => yoneda.obj (L.obj j)) (f.f j)) i)).trans
      ((presheafToSheaf J (Type v)).map_comp _ _))

/-- Relocalization inverse image `f^{-1} : Sh(C / L) ⥤ Sh(C / K)` along a morphism `f : K ⟶ L` of
semi-representable objects, in the componentwise presentations: on the component indexed by `i` it
selects the component `f.f i` and takes inverse image along
`Over.map (f.φ i) : C / K.obj i ⥤ C / L.obj (f.f i)`. -/
def componentwiseRelocalization {K L : FormalCoproduct.{v} C} (f : K ⟶ L) :
    SheafOverFormalCoproduct J L ⥤ SheafOverFormalCoproduct J K :=
  Functor.pi' fun i =>
    Pi.eval (fun j => Sheaf (J.over (L.obj j)) (Type v)) (f.f i) ⋙
      (Over.map (f.φ i)).sheafPushforwardContinuous
        (Type v) (J.over (K.obj i)) (J.over (L.obj (f.f i)))

section

variable [HasSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]

/-- **Stacks 0D87 part (3).** Under the identifications of part (1), the relocalization inverse
image `f^{-1} : Sh(C / L) ⥤ Sh(C / K)` along a morphism `f : K ⟶ L` of semi-representable objects
is base change along `F(K)^♯ ⟶ F(L)^♯`: an object `G ⟶ F(L)^♯` is sent to
`G ×_{F(L)^♯} F(K)^♯ ⟶ F(K)^♯`.

Following the source, this is Stacks 04IL applied to each re-localization morphism
`C / K.obj i ⟶ C / L.obj (f.f i)` — that is `hComponent` — and then assembled over the index set
by `assembleOverPullbackIso`, which is where the van Kampen property of the coproduct
`F(K)^♯ = ∐ i, h_{K.obj i}^♯` is used. -/
@[stacks 0D87 "(3): f^{-1} corresponds to base change along F(K)^sharp to F(L)^sharp"]
theorem componentwiseRelocalization_comp_sheafEquivalence_iso_pullback
    {K L : FormalCoproduct.{v} C} (f : K ⟶ L) :
    Nonempty
      (componentwiseRelocalization J f ⋙ (sheafEquivalence J K).functor ≅
        (sheafEquivalence J L).functor ⋙
          Over.pullback (formalCoproductSheafificationMap J f)) := by
  classical
  let _ (U : C) : HasWeakSheafify (J.over U) (Type v) := sliceHasWeakSheafify J U
  let _ (U : C) :
      ((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint :=
    sliceRestrictionIsRightAdjoint J U
  let _ (V U : C) (g : V ⟶ U) :
      ((Over.map g).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint :=
    relocalizationRestrictionIsRightAdjoint J g
  let Hₖ : K.I → Sheaf J (Type v) := fun i =>
    (presheafToSheaf J (Type v)).obj (yoneda.obj (K.obj i))
  let Hₗ : L.I → Sheaf J (Type v) := fun j =>
    (presheafToSheaf J (Type v)).obj (yoneda.obj (L.obj j))
  let cₖ := sheafComponentCocone J K
  let cₗ := sheafComponentCocone J L
  let a : (i : K.I) → Hₖ i ⟶ Hₗ (f.f i) := fun i =>
    (presheafToSheaf J (Type v)).map (yoneda.map (f.φ i))
  let P := formalCoproductSheafificationMap J f
  let Q : ((j : L.I) → Over (Hₗ j)) ⥤ ((i : K.I) → Over (Hₖ i)) :=
    Functor.pi' fun i =>
      Pi.eval (fun j : L.I => Over (Hₗ j)) (f.f i) ⋙ Over.pullback (a i)
  let hAssembly := assembleOverPullbackIso cₖ (isVanKampenColimit_sheafComponentCocone J K) cₗ
    (isVanKampenColimit_sheafComponentCocone J L) f.f a P
    (formalCoproductSheafificationι_comp_map J f)
  let Fₖ : SheafOverFormalCoproduct J K ⥤ ((i : K.I) → Over (Hₖ i)) :=
    Functor.pi fun i => CategoryTheory.OverShriek.sheafFunctorToOver (J := J) (U := K.obj i)
  let Fₗ : SheafOverFormalCoproduct J L ⥤ ((j : L.I) → Over (Hₗ j)) :=
    Functor.pi fun j => CategoryTheory.OverShriek.sheafFunctorToOver (J := J) (U := L.obj j)
  let T := componentwiseRelocalization J f
  let hComponent : T ⋙ Fₖ ≅ Fₗ ⋙ Q := by
    refine NatIso.pi' fun i => ?_
    exact Functor.isoWhiskerLeft
      (Pi.eval (fun j : L.I => Sheaf (J.over (L.obj j)) (Type v)) (f.f i))
      (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso (f.φ i) J)
  exact ⟨(Functor.isoWhiskerLeft T
      (Functor.isoWhiskerLeft Fₖ (assembleOverSheafComponentCoconeIso J K))).symm ≪≫
    (Functor.associator T Fₖ (assembleOver cₖ)).symm ≪≫
    Functor.isoWhiskerRight hComponent (assembleOver cₖ) ≪≫
    Functor.associator Fₗ Q (assembleOver cₖ) ≪≫
    Functor.isoWhiskerLeft Fₗ hAssembly.symm ≪≫
    (Functor.associator Fₗ (assembleOver cₗ) (Over.pullback P)).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft Fₗ (assembleOverSheafComponentCoconeIso J L))
      (Over.pullback P)⟩

end

end CategoryTheory.SemiRepresentable

end
