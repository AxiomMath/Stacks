module

public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekTautological
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullRestrictionTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03EE is natural in the object

Let `(C, J)` be a small site and `g : U ⟶ V` a morphism of `C`. Stacks 03EE identifies
`j_{U!}j_U^{-1}` with `h_U^# × -` (`CategoryTheory.OverShriek.overShriekOverPullbackNatIso`), and
`j_U = Over.map g ⋙ j_V`, so the relocalization functor `r_g = Over.map g` produces a transition
`j_{U!}j_U^{-1} ⟶ j_{V!}j_V^{-1}`, the shriek transition of
`StacksFrontier/CategoryTheory/Sites/SemiRepresentable/PushPullRestrictionTransition.lean`. This
file proves that the two instances of Stacks 03EE carry that transition to `h_g^# × -`, i.e. that
Stacks 03EE is natural in the object as well as in the sheaf.

A map into a binary product is its two projections, so the statement splits in two. The `prod.snd`
halves are the counits of `j_! ⊣ j^{-1}`
(`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd`) and the shriek
transition is a map over the identity, so that half is immediate. The `prod.fst` halves are the
adjuncts of the tautological sections
(`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_fst`), and that half is the
work: it is done abstractly, for a triangle of adjunctions and any two *constant* families of maps
compatible along the triangle, and then instantiated.

## Main results

* `Stacks.CategoryTheory.homEquiv_leftAdjointUniq_hom_app_comp` and
  `Stacks.CategoryTheory.comp_homEquiv_apply`: the two hom-set computations the abstract step
  rests on — uniqueness of a left adjoint followed by a map, and the adjunct of a composite
  adjunction.
* `Stacks.CategoryTheory.homEquiv_restrictionLeftAdjointIso_hom_app_comp`: the adjunct of
  `Stacks.CategoryTheory.restrictionLeftAdjointIso` followed by a map.
* `Stacks.CategoryTheory.shriekTransition_comp_constant`: **the abstract `prod.fst` step.** The
  shriek transition of a triangle carries the adjunct of a constant family `t` to the adjunct of
  a constant family `t'` followed by `w`, as soon as restricting `t` along the relocalization and
  transporting it along the triangle's comparison gives `t'` followed by `w`.
* `CategoryTheory.SemiRepresentable.overMapPullbackIso_hom_app`: the one-object relocalization
  comparison is the identity.
* `CategoryTheory.SemiRepresentable.overMapPullback_tautologicalSection`: the tautological
  sections at `U` and at `V` agree along `g`. This is the only concrete input of the `prod.fst`
  half.
* `CategoryTheory.SemiRepresentable.overShriekTransition_comp_prod_fst` and
  `.overShriekTransition_comp_prod_snd`: the two halves.
* `CategoryTheory.SemiRepresentable.overShriekTransition_comp_overShriekOverPullbackNatIso_app`
  and `.overShriekTransition_comp_overShriekOverPullbackNatIso`: **Stacks 03EE is natural in the
  object**, componentwise and as transformations.
* `CategoryTheory.SemiRepresentable.pushPullContraMap_eq_restrictionTransition`: **Stacks 0D7X is
  natural in the object, in restriction-transition form.** The conjugate of `h_g^# × -` under the
  two push-pull adjunctions is the restriction transition of the one-object relocalization
  triangle. This is the form the naturality of Stacks 0D86 in the semi-representable object is
  stated in.

## Implementation notes

The abstract step is stated for a *family* of maps `t : ∀ W, W ⟶ P.obj Y'` together with the
hypothesis that it is constant (`m ≫ t W' = t W`) rather than for a map out of a terminal object.
Nothing below needs terminal objects, and the tautological section is defined directly as such a
family, so introducing one would only add a transport.

The two frictions of this corner that bite here: `CategoryTheory.Iso.trans` is
`implicit_reducible`, so `simp` cannot unfold a component of a composite of isomorphisms — which
is why `overMapPullbackIso_hom_app` is proved by `show` and not by `simp` (a `simp only` unfolding
of `CategoryTheory.Functor.sheafPushforwardContinuousComp'` stalls at exactly the `≪≫`); and
`CategoryTheory.Limits.prod.functor` is semireducible, which is why the last proof is a term-mode
chain rather than `simp`.

## References

* [Stacks Project, Tag 03EE](https://stacks.math.columbia.edu/tag/03EE)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.CategoryTheory

open CategoryTheory

variable {A : Type u₁} {B : Type u₂} {D : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D]
  {P : A ⥤ B} {P' : A ⥤ D} {R : B ⥤ D}
  {Pl : B ⥤ A} {Pl' : D ⥤ A} {Rl : D ⥤ B}

/-- **Uniqueness of a left adjoint, in the hom-set form.** For two adjunctions with the same
right adjoint, the adjunct of the canonical comparison followed by a map is the adjunct of that
map under the second adjunction. -/
@[sga "4 IV 3.1.1" "partial"]
theorem homEquiv_leftAdjointUniq_hom_app_comp {L₁ L₂ : A ⥤ B} {Rr : B ⥤ A} (adj₁ : L₁ ⊣ Rr)
    (adj₂ : L₂ ⊣ Rr) (W : A) (Y : B) (f : L₂.obj W ⟶ Y) :
    adj₁.homEquiv W Y ((Adjunction.leftAdjointUniq adj₁ adj₂).hom.app W ≫ f) =
      adj₂.homEquiv W Y f := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit]

/-- The adjunct, under `Rl ⊣ R` followed by `Pl ⊣ P`, of a map out of `Pl.obj (Rl.obj W)`. -/
theorem comp_homEquiv_apply {Q : A ⥤ B} (rcont : Rl ⊣ R) (cont : Pl ⊣ Q) (W : D) (Y : A)
    (f : Pl.obj (Rl.obj W) ⟶ Y) :
    (rcont.comp cont).homEquiv W Y f =
      rcont.unit.app W ≫ R.map (cont.homEquiv (Rl.obj W) Y f) := by
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Category.assoc, Functor.comp_map,
    ← Functor.map_comp]
  exact congrArg (fun m => rcont.unit.app W ≫ R.map m)
    (Adjunction.homEquiv_unit cont (Rl.obj W) Y f).symm

/-- **The comparison of the left adjoints of a triangle, in the hom-set form.** The adjunct under
`cont' : Pl' ⊣ P'` of `restrictionLeftAdjointIso` followed by a map `f` is the adjunct of `f`
under `rcont` and `cont`, transported along `eL`. -/
theorem homEquiv_restrictionLeftAdjointIso_hom_app_comp (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P)
    (cont' : Pl' ⊣ P') (rcont : Rl ⊣ R) (W : D) (Y : A) (f : Pl.obj (Rl.obj W) ⟶ Y) :
    cont'.homEquiv W Y
        ((restrictionLeftAdjointIso eL cont cont' rcont).hom.app W ≫ f) =
      (rcont.unit.app W ≫ R.map (cont.homEquiv (Rl.obj W) Y f)) ≫ eL.hom.app Y := by
  have h := homEquiv_leftAdjointUniq_hom_app_comp (cont'.ofNatIsoRight eL.symm)
    (rcont.comp cont) W Y f
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom,
    comp_homEquiv_apply rcont cont W Y f] at h
  rw [← h, Category.assoc, eL.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- **The shriek transition against a constant family of maps.** Let `t` and `t'` be families of
maps into `P.obj Y'` and `P'.obj Y` which are constant, i.e. unchanged by precomposition, and let
`w : Y ⟶ Y'`. If restricting `t` along `R` and transporting along `eL` gives `t'` followed by
`P'.map w`, then the shriek transition carries the adjunct of `t` to the adjunct of `t'`
followed by `w`.

This is the abstract form of the `U`-to-`V` compatibility of the `prod.fst` component of
Stacks 03EE: there `t` and `t'` are the tautological sections of `h_V^#` over `C/V` and of
`h_U^#` over `C/U`, and `w` is `h_g^#`. -/
theorem shriekTransition_comp_constant (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P) (cont' : Pl' ⊣ P')
    (rcont : Rl ⊣ R) {Y Y' : A} (w : Y ⟶ Y')
    (t : ∀ W : B, W ⟶ P.obj Y') (t' : ∀ W : D, W ⟶ P'.obj Y)
    (ht : ∀ {W W' : B} (m : W ⟶ W'), m ≫ t W' = t W)
    (ht' : ∀ {W W' : D} (m : W ⟶ W'), m ≫ t' W' = t' W)
    (hc : ∀ W : B, R.map (t W) ≫ eL.hom.app Y' = t' (R.obj W) ≫ P'.map w) (X : A) :
    (shriekTransition eL cont cont' rcont).app X ≫
        Pl.map (t (P.obj X)) ≫ cont.counit.app Y' =
      (Pl'.map (t' (P'.obj X)) ≫ cont'.counit.app Y) ≫ w := by
  have hf : Pl.map (rcont.counit.app (P.obj X)) ≫ Pl.map (t (P.obj X)) ≫ cont.counit.app Y' =
      Pl.map (t (Rl.obj (R.obj (P.obj X)))) ≫ cont.counit.app Y' := by
    rw [← Category.assoc, ← Functor.map_comp,
      ht (W := Rl.obj (R.obj (P.obj X))) (W' := P.obj X) (rcont.counit.app (P.obj X))]
  have hmid : cont'.homEquiv (R.obj (P.obj X)) Y'
        ((restrictionLeftAdjointIso eL cont cont' rcont).hom.app (R.obj (P.obj X)) ≫
          Pl.map (t (Rl.obj (R.obj (P.obj X)))) ≫ cont.counit.app Y') =
      t' (R.obj (P.obj X)) ≫ P'.map w := by
    rw [homEquiv_restrictionLeftAdjointIso_hom_app_comp, homEquiv_map_comp_counit,
      Category.assoc, hc (Rl.obj (R.obj (P.obj X))), ← Category.assoc,
      ht' (W := R.obj (P.obj X)) (W' := R.obj (Rl.obj (R.obj (P.obj X))))
        (rcont.unit.app (R.obj (P.obj X)))]
  have hlhs : cont'.homEquiv (P'.obj X) Y'
        ((shriekTransition eL cont cont' rcont).app X ≫
          Pl.map (t (P.obj X)) ≫ cont.counit.app Y') = t' (P'.obj X) ≫ P'.map w := by
    rw [shriekTransition_app, Category.assoc, Category.assoc, hf,
      Adjunction.homEquiv_naturality_left]
    exact (congrArg (fun m => eL.inv.app X ≫ m) hmid).trans
      ((Category.assoc _ _ _).symm.trans
        (eq_whisker (ht' (W := P'.obj X) (W' := R.obj (P.obj X)) (eL.inv.app X)) (P'.map w)))
  have hrhs : cont'.homEquiv (P'.obj X) Y'
        ((Pl'.map (t' (P'.obj X)) ≫ cont'.counit.app Y) ≫ w) =
      t' (P'.obj X) ≫ P'.map w := by
    rw [Adjunction.homEquiv_naturality_right]
    exact congrArg (fun m => m ≫ P'.map w)
      (homEquiv_map_comp_counit cont' (t' (P'.obj X)))
  exact (cont'.homEquiv (P'.obj X) Y').injective (hlhs.trans hrhs.symm)

end Stacks.CategoryTheory

namespace CategoryTheory.SemiRepresentable

open CategoryTheory.OverShriek

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) {U V : C} (g : U ⟶ V)

/-- The one-object relocalization comparison is the identity: the underlying functors satisfy
`Over.map g ⋙ Over.forget V = Over.forget U` on the nose, which is why
`CategoryTheory.SemiRepresentable.overMapPullbackIso` is
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` at `Iso.refl`. -/
theorem overMapPullbackIso_hom_app (Z : Sheaf J (Type u)) :
    (overMapPullbackIso J g).hom.app Z = 𝟙 ((J.overPullback (Type u) U).obj Z) := by
  apply Sheaf.hom_ext
  show Functor.whiskerRight (NatTrans.op (𝟙 (Over.map g ⋙ Over.forget V)))
      ((sheafToPresheaf J (Type u)).obj Z) = 𝟙 (((J.overPullback (Type u) U).obj Z).obj)
  rw [NatTrans.op_id, Functor.whiskerRight_id']
  rfl

/-- **The tautological sections at `U` and at `V` agree along `g : U ⟶ V`.** Restricting the
tautological section of `h_V^#` along the relocalization functor `Over.map g` and transporting it
by the one-object relocalization comparison gives the tautological section of `h_U^#` followed by
`h_g^#`: over the object `A →φ U` of `C/U` both are the image of `φ ≫ g` under the sheafification
unit of `h_V`, on the left because `Over.map g` sends `A →φ U` to `A →{φ ≫ g} V`, on the right by
naturality of the sheafification unit along `h_g`. -/
theorem overMapPullback_tautologicalSection (W : Sheaf (J.over V) (Type u)) :
    ((Over.map g).sheafPushforwardContinuous (Type u) (J.over U) (J.over V)).map
          (tautologicalSection V J W) ≫
        (overMapPullbackIso J g).hom.app ((presheafToSheaf J (Type u)).obj (yoneda.obj V)) =
      tautologicalSection U J
          (((Over.map g).sheafPushforwardContinuous (Type u) (J.over U) (J.over V)).obj W) ≫
        (localizationPullback U J).map
          ((presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g)) := by
  rw [overMapPullbackIso_hom_app]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun A => ?_)
  ext x
  exact congrArg (fun m => m A.unop.hom)
    (NatTrans.congr_app
      ((sheafificationAdjunction J (Type u)).unit.naturality ((yoneda (C := C)).map g))
      (op A.unop.left))

/-- The shriek transition of the one-object relocalization triangle of `g : U ⟶ V`:
`j_{U!}j_U^{-1} ⟶ j_{V!}j_V^{-1}`. -/
abbrev overShriekTransition :
    OverShriek.localizationPullback U J ⋙ OverShriek.localizationShriek U J ⟶
      OverShriek.localizationPullback V J ⋙ OverShriek.localizationShriek V J :=
  Stacks.CategoryTheory.shriekTransition (overMapPullbackIso J g)
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J)
    ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)
    ((Over.map g).sheafAdjunctionContinuous (Type u) (J.over U) (J.over V))

/-- **The `prod.fst` half of the naturality of Stacks 03EE in the object.** The shriek transition
of `g : U ⟶ V` carries the projection onto `h_V^#` to the projection onto `h_U^#` followed by
`h_g^#`.

Both projections are adjuncts of tautological sections
(`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_fst`), so this is
`Stacks.CategoryTheory.shriekTransition_comp_constant` at the two of them; the hypothesis it needs
is `overMapPullback_tautologicalSection`. -/
theorem overShriekTransition_comp_prod_fst (X : Sheaf J (Type u)) :
    (overShriekTransition J g).app X ≫
        (OverShriek.overShriekOverPullbackNatIso V J).hom.app X ≫ prod.fst =
      ((OverShriek.overShriekOverPullbackNatIso U J).hom.app X ≫ prod.fst) ≫
        (presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g) := by
  rw [OverShriek.overShriekOverPullbackNatIso_hom_app_prod_fst,
    OverShriek.overShriekOverPullbackNatIso_hom_app_prod_fst]
  exact Stacks.CategoryTheory.shriekTransition_comp_constant (overMapPullbackIso J g)
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J)
    ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)
    ((Over.map g).sheafAdjunctionContinuous (Type u) (J.over U) (J.over V))
    ((presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g))
    (tautologicalSection V J) (tautologicalSection U J)
    (fun {_ _} m => comp_tautologicalSection V J m)
    (fun {_ _} m => comp_tautologicalSection U J m)
    (overMapPullback_tautologicalSection J g) X

/-- **The `prod.snd` half of the naturality of Stacks 03EE in the object.** Both projections onto
the sheaf are the counit of `j_! ⊣ j^{-1}`
(`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd`), and the shriek
transition is a map over the identity
(`Stacks.CategoryTheory.shriekTransition_comp_counit`). -/
theorem overShriekTransition_comp_prod_snd (X : Sheaf J (Type u)) :
    (overShriekTransition J g).app X ≫
        (OverShriek.overShriekOverPullbackNatIso V J).hom.app X ≫ prod.snd =
      (OverShriek.overShriekOverPullbackNatIso U J).hom.app X ≫ prod.snd := by
  rw [OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd,
    OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd]
  exact Stacks.CategoryTheory.shriekTransition_comp_counit (overMapPullbackIso J g)
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J)
    ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)
    ((Over.map g).sheafAdjunctionContinuous (Type u) (J.over U) (J.over V)) X

/-- **Stacks 03EE is natural in the object, componentwise.** For `g : U ⟶ V` the shriek
transition `j_{U!}j_U^{-1} ⟶ j_{V!}j_V^{-1}` is carried by the two instances of Stacks 03EE to
`h_g^# × -`. A map into a binary product is its two projections, and the two projections are
`overShriekTransition_comp_prod_fst` and `overShriekTransition_comp_prod_snd`. -/
theorem overShriekTransition_comp_overShriekOverPullbackNatIso_app (X : Sheaf J (Type u)) :
    (overShriekTransition J g).app X ≫
        (OverShriek.overShriekOverPullbackNatIso V J).hom.app X =
      (OverShriek.overShriekOverPullbackNatIso U J).hom.app X ≫
        prod.map ((presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g)) (𝟙 X) := by
  refine prod.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((overShriekTransition_comp_prod_fst J g X).trans
        ((Category.assoc _ _ _).trans
          ((congrArg
              (fun m => (OverShriek.overShriekOverPullbackNatIso U J).hom.app X ≫ m)
              (prod.map_fst ((presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g))
                (𝟙 X)).symm).trans
            (Category.assoc _ _ _).symm)))
  · exact (Category.assoc _ _ _).trans
      ((overShriekTransition_comp_prod_snd J g X).trans
        ((congrArg
            (fun m => (OverShriek.overShriekOverPullbackNatIso U J).hom.app X ≫ m)
            ((Category.comp_id (prod.snd :
                (presheafToSheaf J (Type u)).obj (yoneda.obj U) ⨯ X ⟶ X)).symm.trans
              (prod.map_snd ((presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g))
                (𝟙 X)).symm)).trans
          (Category.assoc _ _ _).symm))

/-- **Stacks 03EE is natural in the object.** The shriek transition of `g : U ⟶ V` is carried by
the two instances of Stacks 03EE to `h_g^# × -`. -/
theorem overShriekTransition_comp_overShriekOverPullbackNatIso :
    overShriekTransition J g ≫ (OverShriek.overShriekOverPullbackNatIso V J).hom =
      (OverShriek.overShriekOverPullbackNatIso U J).hom ≫
        prod.functor.map (sheafifiedYonedaMap J g) :=
  NatTrans.ext (funext fun X =>
    overShriekTransition_comp_overShriekOverPullbackNatIso_app J g X)

/-- **Stacks 0D7X is natural in the object, in restriction-transition form.** The conjugate
`CategoryTheory.SemiRepresentable.pushPullContraMap` of `h_g^# × -` under the two push-pull
adjunctions of Stacks 0D7X is the restriction transition of the one-object relocalization
triangle of `g : U ⟶ V`.

This is what identifies the abstract transition of
`StacksFrontier/CategoryTheory/Sites/SemiRepresentable/PushPullRestrictionTransition.lean` with
restriction along `g`: the conjugate of the shriek transition is the restriction transition
(`Stacks.CategoryTheory.conjugateEquiv_shriekTransition`), and the shriek transition corresponds
to `h_g^# × -` by `overShriekTransition_comp_overShriekOverPullbackNatIso`. -/
theorem pushPullContraMap_eq_restrictionTransition :
    pushPullContraMap J g =
      Stacks.CategoryTheory.restrictionTransition
        ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
        ((Over.forget U).sheafAdjunctionCocontinuous (Type u) (J.over U) J)
        ((Over.map g).sheafAdjunctionCocontinuous (Type u) (J.over U) (J.over V))
        (overMapPullbackIso J g) := by
  have h2 : (OverShriek.overShriekOverPullbackNatIso U J).hom ≫
        prod.functor.map (sheafifiedYonedaMap J g) ≫
          (OverShriek.overShriekOverPullbackNatIso V J).inv = overShriekTransition J g := by
    rw [← Category.assoc, ← overShriekTransition_comp_overShriekOverPullbackNatIso,
      Category.assoc, Iso.hom_inv_id]
    exact Category.comp_id _
  have h1 : pushPullContraMap J g =
      conjugateEquiv
        (((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J).comp
          ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J))
        (((Over.forget U).sheafAdjunctionCocontinuous (Type u) (J.over U) J).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J))
        ((OverShriek.overShriekOverPullbackNatIso U J).hom ≫
          prod.functor.map (sheafifiedYonedaMap J g) ≫
            (OverShriek.overShriekOverPullbackNatIso V J).inv) :=
    Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft
      (((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J).comp
        ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J))
      (((Over.forget U).sheafAdjunctionCocontinuous (Type u) (J.over U) J).comp
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J))
      (OverShriek.overShriekOverPullbackNatIso V J)
      (OverShriek.overShriekOverPullbackNatIso U J)
      (prod.functor.map (sheafifiedYonedaMap J g))
  rw [h1, h2]
  exact Stacks.CategoryTheory.conjugateEquiv_shriekTransition
    ((Over.forget V).sheafAdjunctionCocontinuous (Type u) (J.over V) J)
    ((Over.forget U).sheafAdjunctionCocontinuous (Type u) (J.over U) J)
    ((Over.map g).sheafAdjunctionCocontinuous (Type u) (J.over U) (J.over V))
    (overMapPullbackIso J g)
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (J.over V) J)
    ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)
    ((Over.map g).sheafAdjunctionContinuous (Type u) (J.over U) (J.over V))

end CategoryTheory.SemiRepresentable

end
