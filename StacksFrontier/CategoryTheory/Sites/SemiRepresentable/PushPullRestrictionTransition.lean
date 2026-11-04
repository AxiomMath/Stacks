module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.MateNatTrans
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.RelocalizationRestriction

/-!
# Restricting push-pull further along a morphism of semi-representable objects

Let `(C, J)` be a small site and `f : M ⟶ N` a morphism of semi-representable objects of `C`.
The componentwise localization functors satisfy `j_M = r_f ⋙ j_N`, where `r_f` is the
componentwise relocalization functor, so restriction along `j_N` followed by restriction along
`r_f` is restriction along `j_M`
(`CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso`). This file builds the
transformation this induces on the push-pull functors,
`j_{N,*} j_N^{-1} ⟶ j_{M,*} j_M^{-1}`, and identifies it by its mate.

## Main definitions

* `Stacks.CategoryTheory.restrictionTransition`: the construction in the abstract, for a triangle
  of adjunctions `P ⊣ Q`, `P' ⊣ Q'`, `R ⊣ S` together with an isomorphism `P ⋙ R ≅ P'`.
* `Stacks.CategoryTheory.restrictionRightAdjointIso`: the companion isomorphism `Q' ≅ S ⋙ Q` of
  right adjoints that the construction transports along.
* `Stacks.CategoryTheory.restrictionLeftAdjointIso` and `Stacks.CategoryTheory.shriekTransition`:
  the left-adjoint counterparts, for a triangle whose three right-hand functors themselves have
  left adjoints `Pl`, `Pl'`, `Rl`: the comparison `Pl' ≅ Rl ⋙ Pl`, and the transition
  `P' ⋙ Pl' ⟶ P ⋙ Pl` it produces together with the counit of `Rl ⊣ R`.
* `CategoryTheory.SemiRepresentable.pushPullRestrictionTransition`: the transition
  `j_{N,*} j_N^{-1} ⟶ j_{M,*} j_M^{-1}` itself.

## Main results

* `Stacks.CategoryTheory.restrictionTransition_mate`: **the mate formula.** The adjunct of the
  transition under `P' ⊣ Q'` is the counit of `P ⊣ Q` read through `R` and conjugated by the
  isomorphism `P ⋙ R ≅ P'`. Since taking mates is a bijection this *characterises* the
  transition, which is what `Stacks.CategoryTheory.restrictionTransition_eq_of_mate` records.
* `Stacks.CategoryTheory.restrictionTransition_eq_id`: the transition of a triangle whose
  relocalization is the identity is the identity.
* `Stacks.CategoryTheory.conjugateEquiv_shriekTransition`: **the two transitions are
  conjugate.** `P ⋙ Q` and `P' ⋙ Q'` are right adjoint to `P ⋙ Pl` and `P' ⋙ Pl'`, and under
  that adjointness the restriction transition is the shriek transition. This is what moves the
  transition to the side on which it is a counit, with no uniqueness-of-adjoints left in it.
* `Stacks.CategoryTheory.restrictionLeftAdjointIso_hom_app_counit` and
  `Stacks.CategoryTheory.shriekTransition_comp_counit`: the counit properties of the two, the
  second saying that the shriek transition is a map over the identity.
* `CategoryTheory.SemiRepresentable.pushPullRestrictionTransition_mate` and
  `.pushPullRestrictionTransition_id`: the two previous results for the transition at hand; the
  second says the transition is not degenerate.
* `CategoryTheory.SemiRepresentable.pushPullProductIso_mate`: **the mate of the product
  description of push-pull.** The adjunct of `pushPullProductIso` under the componentwise
  localization adjunction is the restriction of the push-pull counit to the components. This is
  the counit characterisation of that isomorphism, i.e. the form in which uniqueness of adjoints
  is usable in a diagram chase.
* `CategoryTheory.SemiRepresentable.componentLocalizationAdjunction_counit_app` and
  `.pushPullProductIso_mate_π`: the same two facts one component at a time — the counit of the
  componentwise localization adjunction at the index `i`, and the adjunct of `pushPullProductIso`
  followed by the projection onto the `i`-th factor, under the localization adjunction at `M_i`.

## Implementation notes

The topologies on the two component sites are parameters, each with a proof that it is the
componentwise localized topology, exactly as in
`CategoryTheory.SemiRepresentable.pushPullProductIso`: the intended consumer is the component
site of a simplicial semi-representable object, whose topology is only propositionally the
componentwise localized one.

Everything about the transition is proved through its mate. The mate is taken with
`CategoryTheory.Adjunction.mateNatTrans`, whose bijectivity turns the mate formula into a
characterisation; this is cleaner than unfolding
`CategoryTheory.Adjunction.rightAdjointUniq`, which the construction of the companion
isomorphism of right adjoints goes through.

`pushPullProductIso_mate` is proved from the same two facts: the triangle identity of the slice
equivalence and naturality of the push-pull counit. It is stated as an equation between maps
into the product rather than componentwise, so that no `CategoryTheory.Limits.Pi.hom_ext` is
needed at the point of use.

The shriek side exists for the same reason: on a localization triangle the restriction
transition is written through `CategoryTheory.Adjunction.rightAdjointUniq`, whereas its
conjugate is the counit of the relocalization, which is what the comparison with Stacks 03EE is
stated in terms of.

## References

* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.CategoryTheory

open CategoryTheory

variable {A : Type u₁} {B : Type u₂} {D : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D]
  {P : A ⥤ B} {Q : B ⥤ A} {P' : A ⥤ D} {Q' : D ⥤ A} {R : B ⥤ D} {S : D ⥤ B}

/-- The companion isomorphism of right adjoints of a triangle `P ⋙ R ≅ P'` of left adjoints:
`Q'` and `S ⋙ Q` are both right adjoint to `P'`, so they agree. -/
def restrictionRightAdjointIso (adj : P ⊣ Q) (adj' : P' ⊣ Q') (radj : R ⊣ S)
    (eL : P ⋙ R ≅ P') : Q' ≅ S ⋙ Q :=
  Adjunction.rightAdjointUniq adj' ((adj.comp radj).ofNatIsoLeft eL)

/-- **The restriction transition of a triangle of adjunctions.** Given `adj : P ⊣ Q`,
`adj' : P' ⊣ Q'`, `radj : R ⊣ S` and an isomorphism `eL : P ⋙ R ≅ P'`, the unit of `radj`
produces a transformation `P ⋙ Q ⟶ P ⋙ R ⋙ S ⋙ Q`, which `eL` and the companion isomorphism
of right adjoints carry to `P' ⋙ Q'`. -/
def restrictionTransition (adj : P ⊣ Q) (adj' : P' ⊣ Q') (radj : R ⊣ S)
    (eL : P ⋙ R ≅ P') : P ⋙ Q ⟶ P' ⋙ Q' :=
  Functor.whiskerLeft P (Functor.whiskerRight radj.unit Q) ≫
    Functor.whiskerRight eL.hom (S ⋙ Q) ≫
      Functor.whiskerLeft P' (restrictionRightAdjointIso adj adj' radj eL).inv

/-- The component of `restrictionTransition` at an object, with the three whiskerings
evaluated. -/
theorem restrictionTransition_app (adj : P ⊣ Q) (adj' : P' ⊣ Q') (radj : R ⊣ S)
    (eL : P ⋙ R ≅ P') (X : A) :
    (restrictionTransition adj adj' radj eL).app X =
      Q.map (radj.unit.app (P.obj X)) ≫ Q.map (S.map (eL.hom.app X)) ≫
        (restrictionRightAdjointIso adj adj' radj eL).inv.app (P'.obj X) :=
  rfl

/-- **The mate formula.** The adjunct of the restriction transition under `adj' : P' ⊣ Q'` is
the counit of `adj : P ⊣ Q`, pushed through `R` and conjugated by the comparison
`eL : P ⋙ R ≅ P'` of the two left adjoints. -/
theorem restrictionTransition_mate (adj : P ⊣ Q) (adj' : P' ⊣ Q') (radj : R ⊣ S)
    (eL : P ⋙ R ≅ P') (X : A) :
    P'.map ((restrictionTransition adj adj' radj eL).app X) ≫ adj'.counit.app (P'.obj X) =
      eL.inv.app (Q.obj (P.obj X)) ≫ R.map (adj.counit.app (P.obj X)) ≫ eL.hom.app X := by
  have hcounit : P'.map ((restrictionRightAdjointIso adj adj' radj eL).inv.app (P'.obj X)) ≫
      adj'.counit.app (P'.obj X) =
      eL.inv.app (Q.obj (S.obj (P'.obj X))) ≫
        R.map (adj.counit.app (S.obj (P'.obj X))) ≫ radj.counit.app (P'.obj X) := by
    rw [restrictionRightAdjointIso, Adjunction.rightAdjointUniq_inv_app,
      Adjunction.rightAdjointUniq_hom_app_counit]
    simp
  rw [restrictionTransition_app, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, hcounit, ← Category.assoc (P'.map (Q.map (radj.unit.app (P.obj X)))),
    ← Functor.map_comp, ← Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc R,
    Adjunction.counit_naturality adj (radj.unit.app (P.obj X) ≫ S.map (eL.hom.app X))]
  simp [Adjunction.counit_naturality]

/-- **The mate formula characterises the restriction transition.** A transformation whose
adjunct is the one of `restrictionTransition_mate` is the restriction transition, because taking
mates is a bijection. -/
theorem restrictionTransition_eq_of_mate (adj : P ⊣ Q) (adj' : P' ⊣ Q') (radj : R ⊣ S)
    (eL : P ⋙ R ≅ P') (τ : P ⋙ Q ⟶ P' ⋙ Q')
    (h : ∀ X : A, P'.map (τ.app X) ≫ adj'.counit.app (P'.obj X) =
      eL.inv.app (Q.obj (P.obj X)) ≫ R.map (adj.counit.app (P.obj X)) ≫ eL.hom.app X) :
    τ = restrictionTransition adj adj' radj eL := by
  refine (adj'.mateNatTrans_bijective (P ⋙ Q) P').1 ?_
  ext X
  rw [Adjunction.mateNatTrans_app, Adjunction.mateNatTrans_app, h X,
    restrictionTransition_mate]

section Identity

variable {R₀ S₀ : B ⥤ B}

/-- **A triangle whose relocalization is the identity has the identity transition.** If `R₀` is
isomorphic to the identity by an isomorphism `ρ` whose whiskering by `P` is the comparison `eL`,
then the restriction transition of the triangle is the identity. -/
theorem restrictionTransition_eq_id (adj : P ⊣ Q) (radj : R₀ ⊣ S₀) {ρ : R₀ ≅ 𝟭 B}
    {eL : P ⋙ R₀ ≅ P} (hρ : ∀ X : A, eL.hom.app X = ρ.hom.app (P.obj X)) :
    restrictionTransition adj adj radj eL = 𝟙 (P ⋙ Q) := by
  have hρinv : ∀ X : A, eL.inv.app X = ρ.inv.app (P.obj X) := fun X => by
    rw [← cancel_mono (eL.hom.app X), Iso.inv_hom_id_app, hρ X, Iso.inv_hom_id_app]
    rfl
  refine (restrictionTransition_eq_of_mate adj adj radj eL _ (fun X => ?_)).symm
  have hnat : R₀.map (adj.counit.app (P.obj X)) ≫ ρ.hom.app (P.obj X) =
      ρ.hom.app (P.obj (Q.obj (P.obj X))) ≫ adj.counit.app (P.obj X) :=
    ρ.hom.naturality (adj.counit.app (P.obj X))
  rw [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, hρ X,
    hρinv (Q.obj (P.obj X)), hnat, ← Category.assoc, ρ.inv_hom_id_app]
  simp

end Identity

section Shriek

variable {Pl : B ⥤ A} {Pl' : D ⥤ A} {Rl : D ⥤ B}

/-- **The comparison of the left adjoints of a triangle.** If `eL : P ⋙ R ≅ P'` and `P`, `P'`,
`R` have left adjoints `Pl`, `Pl'`, `Rl`, then `Pl'` and `Rl ⋙ Pl` are both left adjoint to
`P ⋙ R`, hence agree. -/
def restrictionLeftAdjointIso (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P) (cont' : Pl' ⊣ P')
    (rcont : Rl ⊣ R) : Pl' ≅ Rl ⋙ Pl :=
  Adjunction.leftAdjointUniq (cont'.ofNatIsoRight eL.symm) (rcont.comp cont)

/-- **The shriek transition of a triangle**, the left-adjoint counterpart of
`restrictionTransition`: the comparison of the left adjoints followed by the counit of
`rcont : Rl ⊣ R`. -/
def shriekTransition (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P) (cont' : Pl' ⊣ P') (rcont : Rl ⊣ R) :
    P' ⋙ Pl' ⟶ P ⋙ Pl :=
  Functor.whiskerRight eL.inv Pl' ≫
    Functor.whiskerLeft (P ⋙ R) (restrictionLeftAdjointIso eL cont cont' rcont).hom ≫
      Functor.whiskerLeft P (Functor.whiskerRight rcont.counit Pl)

/-- The component of `shriekTransition` at an object, with the three whiskerings evaluated. -/
theorem shriekTransition_app (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P) (cont' : Pl' ⊣ P')
    (rcont : Rl ⊣ R) (W : A) :
    (shriekTransition eL cont cont' rcont).app W =
      Pl'.map (eL.inv.app W) ≫
        (restrictionLeftAdjointIso eL cont cont' rcont).hom.app (R.obj (P.obj W)) ≫
          Pl.map (rcont.counit.app (P.obj W)) :=
  rfl

/-- **The defining property of `restrictionLeftAdjointIso`.** It is a comparison of two left
adjoints of `P ⋙ R`, so it carries the counit of `rcont` and `cont` to the counit of `cont'`
transported along `eL`. -/
theorem restrictionLeftAdjointIso_hom_app_counit (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P)
    (cont' : Pl' ⊣ P') (rcont : Rl ⊣ R) (X : A) :
    (restrictionLeftAdjointIso eL cont cont' rcont).hom.app (R.obj (P.obj X)) ≫
        Pl.map (rcont.counit.app (P.obj X)) ≫ cont.counit.app X =
      Pl'.map (eL.hom.app X) ≫ cont'.counit.app X := by
  have h := Adjunction.leftAdjointUniq_hom_app_counit (cont'.ofNatIsoRight eL.symm)
    (rcont.comp cont) X
  rwa [Adjunction.comp_counit_app] at h

/-- **The shriek transition is compatible with the two counits.** Following it by the counit of
`cont : Pl ⊣ P` gives the counit of `cont' : Pl' ⊣ P'`; that is, the transition is a map over the
identity. -/
theorem shriekTransition_comp_counit (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P) (cont' : Pl' ⊣ P')
    (rcont : Rl ⊣ R) (X : A) :
    (shriekTransition eL cont cont' rcont).app X ≫ cont.counit.app X = cont'.counit.app X := by
  rw [shriekTransition_app]
  simp only [Category.assoc]
  rw [restrictionLeftAdjointIso_hom_app_counit, ← Functor.map_comp_assoc, eL.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The restriction transition is the conjugate of the shriek transition.** For a triangle
`eL : P ⋙ R ≅ P'` whose three right-hand functors have left adjoints, `P ⋙ Q` and `P' ⋙ Q'` are
right adjoint to `P ⋙ Pl` and `P' ⋙ Pl'`, and under that adjointness `restrictionTransition`
corresponds to `shriekTransition`.

This is what moves the transition to the side on which it is computable: on the left-adjoint side
the transition is a counit, with no `CategoryTheory.Adjunction.rightAdjointUniq` in it. -/
theorem conjugateEquiv_shriekTransition (adj : P ⊣ Q) (adj' : P' ⊣ Q') (radj : R ⊣ S)
    (eL : P ⋙ R ≅ P') (cont : Pl ⊣ P) (cont' : Pl' ⊣ P') (rcont : Rl ⊣ R) :
    conjugateEquiv (adj.comp cont) (adj'.comp cont')
        (shriekTransition eL cont cont' rcont) =
      restrictionTransition adj adj' radj eL := by
  refine (eq_conjugateEquiv _ _ _ _ (fun X => ?_)).symm
  have hrc : Rl.map (R.map (adj.counit.app (P.obj X))) ≫ rcont.counit.app (P.obj X) =
      rcont.counit.app (P.obj (Q.obj (P.obj X))) ≫ adj.counit.app (P.obj X) :=
    Adjunction.counit_naturality rcont (adj.counit.app (P.obj X))
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app, Functor.comp_map,
    ← Functor.map_comp_assoc, restrictionTransition_mate, shriekTransition_app,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    ← restrictionLeftAdjointIso_hom_app_counit eL cont cont' rcont X]
  simp only [Functor.comp_obj, Category.assoc]
  have hnu : Pl'.map (R.map (adj.counit.app (P.obj X))) ≫
        (restrictionLeftAdjointIso eL cont cont' rcont).hom.app (R.obj (P.obj X)) ≫
          Pl.map (rcont.counit.app (P.obj X)) ≫ cont.counit.app X =
      (restrictionLeftAdjointIso eL cont cont' rcont).hom.app
            (R.obj (P.obj (Q.obj (P.obj X)))) ≫
          Pl.map (Rl.map (R.map (adj.counit.app (P.obj X)))) ≫
            Pl.map (rcont.counit.app (P.obj X)) ≫ cont.counit.app X :=
    NatTrans.naturality_assoc _ _ _
  rw [hnu, ← Functor.map_comp_assoc Pl, hrc, Functor.map_comp, Category.assoc]

end Shriek

end Stacks.CategoryTheory

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open Stacks.CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

section

variable {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
  (Jm : GrothendieckTopology (ComponentOver M)) (hJm : Jm = componentwiseTopology J M)
  (Jn : GrothendieckTopology (ComponentOver N)) (hJn : Jn = componentwiseTopology J N)
  [(componentOverForget M).IsContinuous Jm J] [(componentOverForget M).IsCocontinuous Jm J]
  [(componentOverForget N).IsContinuous Jn J] [(componentOverForget N).IsCocontinuous Jn J]
  [(componentOverMap f).IsContinuous Jm Jn] [(componentOverMap f).IsCocontinuous Jm Jn]

/-- **Restricting push-pull further along `f : M ⟶ N`.** The canonical transformation
`j_{N,*} j_N^{-1} ⟶ j_{M,*} j_M^{-1}` attached to a morphism of semi-representable objects: it
is the unit of the relocalization adjunction of `r_f`, transported along the identification of
restriction along `j_N` followed by restriction along `r_f` with restriction along `j_M`. -/
def pushPullRestrictionTransition :
    (componentOverForget N).sheafPushforwardContinuous (Type u) Jn J ⋙
        (componentOverForget N).sheafPushforwardCocontinuous (Type u) Jn J ⟶
      (componentOverForget M).sheafPushforwardContinuous (Type u) Jm J ⋙
        (componentOverForget M).sheafPushforwardCocontinuous (Type u) Jm J :=
  restrictionTransition ((componentOverForget N).sheafAdjunctionCocontinuous (Type u) Jn J)
    ((componentOverForget M).sheafAdjunctionCocontinuous (Type u) Jm J)
    ((componentOverMap f).sheafAdjunctionCocontinuous (Type u) Jm Jn)
    (relocalizationForgetPushforwardIso J f Jm hJm Jn hJn)

/-- **The mate of the push-pull restriction transition.** Its adjunct under the push-pull
adjunction of `j_M` is the counit of the push-pull adjunction of `j_N`, restricted along `r_f`
and conjugated by `relocalizationForgetPushforwardIso`. -/
theorem pushPullRestrictionTransition_mate (X : Sheaf J (Type u)) :
    ((componentOverForget M).sheafPushforwardContinuous (Type u) Jm J).map
          ((pushPullRestrictionTransition J f Jm hJm Jn hJn).app X) ≫
        ((componentOverForget M).sheafAdjunctionCocontinuous (Type u) Jm J).counit.app
          (((componentOverForget M).sheafPushforwardContinuous (Type u) Jm J).obj X) =
      (relocalizationForgetPushforwardIso J f Jm hJm Jn hJn).inv.app
          (((componentOverForget N).sheafPushforwardCocontinuous (Type u) Jn J).obj
            (((componentOverForget N).sheafPushforwardContinuous (Type u) Jn J).obj X)) ≫
        ((componentOverMap f).sheafPushforwardContinuous (Type u) Jm Jn).map
            (((componentOverForget N).sheafAdjunctionCocontinuous (Type u) Jn J).counit.app
              (((componentOverForget N).sheafPushforwardContinuous (Type u) Jn J).obj X)) ≫
          (relocalizationForgetPushforwardIso J f Jm hJm Jn hJn).hom.app X :=
  restrictionTransition_mate _ _ _ _ X

end

/-- **The push-pull restriction transition of an identity is the identity**: the transition is
not degenerate. The relocalization functor of `𝟙 M` is the identity
(`CategoryTheory.SemiRepresentable.componentOverMap_id`), and restriction along it is the
identity on sheaves by the same equation, which is the transport the statement needs. -/
theorem pushPullRestrictionTransition_id (M : FormalCoproduct.{u} C)
    (Jm : GrothendieckTopology (ComponentOver M)) (hJm : Jm = componentwiseTopology J M)
    [(componentOverForget M).IsContinuous Jm J] [(componentOverForget M).IsCocontinuous Jm J]
    [(componentOverMap (𝟙 M)).IsContinuous Jm Jm]
    [(componentOverMap (𝟙 M)).IsCocontinuous Jm Jm] :
    pushPullRestrictionTransition J (𝟙 M) Jm hJm Jm hJm =
      𝟙 ((componentOverForget M).sheafPushforwardContinuous (Type u) Jm J ⋙
        (componentOverForget M).sheafPushforwardCocontinuous (Type u) Jm J) := by
  subst hJm
  refine restrictionTransition_eq_id _ _
    (ρ := Functor.sheafPushforwardContinuousId' (eqToIso (componentOverMap_id M)) (Type u)
      (componentwiseTopology J M)) (fun X => ?_)
  rw [relocalizationForgetPushforwardIso_eq]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun Z => ?_)
  have key : (eqToIso (componentOverMap_comp_componentOverForget (𝟙 M))).inv.app Z.unop =
      (componentOverForget M).map ((eqToIso (componentOverMap_id M)).inv.app Z.unop) := by
    simp only [eqToIso.inv, eqToHom_app, eqToHom_map]
  exact congrArg (fun m => X.obj.map (Quiver.Hom.op m)) key

/-! ### The counit characterisation of the product description of push-pull -/

/-- **The counit of the componentwise localization adjunction, componentwise.** At the component
indexed by `i` it is the projection of the product of the componentwise pushforwards onto its
`i`-th factor, restricted to `C/M_i`, followed by the counit of the localization adjunction at
`M_i`.

The adjunction is built from the family of the one-object ones by a hom-set bijection
(`CategoryTheory.SemiRepresentable.componentLocalizationAdjunction`), so this is that bijection
read at the identity. -/
theorem componentLocalizationAdjunction_counit_app (M : FormalCoproduct.{u} C)
    (Z : (i : M.I) → Sheaf (J.over (M.obj i)) (Type u)) (i : M.I) :
    (componentLocalizationAdjunction J M).counit.app Z i =
      (localizationPullback (M.obj i) J).map
          (Pi.π (fun j : M.I => (localizationPushforward (M.obj j) J).obj (Z j)) i) ≫
        (localizationAdjunction J (M.obj i)).counit.app (Z i) :=
  (localizationAdjunction J (M.obj i)).homEquiv_counit _ _ _

/-- **The mate of the product description of push-pull.** The adjunct of
`CategoryTheory.SemiRepresentable.pushPullProductIso` under the componentwise localization
adjunction is the counit of push-pull along `j_M`, read through the product description of
sheaves on `C/M`.

This is uniqueness of adjoints in the form a diagram chase can use: because taking adjuncts is
a bijection, the equation determines `pushPullProductIso`. -/
theorem pushPullProductIso_mate (M : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) :
    (Functor.pi' fun i : M.I => localizationPullback (M.obj i) J).map
          ((pushPullProductIso J M (componentwiseTopology J M) rfl).hom.app X) ≫
        (componentLocalizationAdjunction J M).counit.app
          ((Functor.pi' fun i : M.I => localizationPullback (M.obj i) J).obj X) =
      (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
        (((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
            (componentwiseTopology J M) J).counit.app
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) := by
  show (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
        (((componentOverForget M).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J M) J).map
          ((pushPullProductIso J M (componentwiseTopology J M) rfl).hom.app X)) ≫
      (componentLocalizationAdjunction J M).counit.app
        ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) = _
  have hkey : (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).map
            ((componentPushforwardSliceIso J M).inv.app
              ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
                (((componentOverForget M).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J M) J).obj X)))) ≫
        (componentLocalizationAdjunction J M).counit.app
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).obj X)) =
      (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
          (((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
              (componentwiseTopology J M) J).counit.app
            ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.inverse.obj
              ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
                (((componentOverForget M).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J M) J).obj X)))) ≫
        (formalCoproductSliceSheavesEquivalence J M (Type u)).1.counit.app
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).obj X)) :=
    componentPushforwardSliceIso_inv_app_counit J M _
  have hnat : ((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).map
          (((componentOverForget M).sheafPushforwardCocontinuous (Type u)
              (componentwiseTopology J M) J).map
            ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.unitIso.hom.app
              (((componentOverForget M).sheafPushforwardContinuous (Type u)
                (componentwiseTopology J M) J).obj X))) ≫
        ((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
            (componentwiseTopology J M) J).counit.app
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.inverse.obj
            ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
              (((componentOverForget M).sheafPushforwardContinuous (Type u)
                (componentwiseTopology J M) J).obj X))) =
      ((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
            (componentwiseTopology J M) J).counit.app
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X) ≫
        (formalCoproductSliceSheavesEquivalence J M (Type u)).1.unitIso.hom.app
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X) :=
    Adjunction.counit_naturality _ _
  have htri : (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
        ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.unitIso.hom.app
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) ≫
      (formalCoproductSliceSheavesEquivalence J M (Type u)).1.counit.app
        ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) = 𝟙 _ :=
    (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor_unit_comp _
  calc _ = _ :=
        congrArg (fun m => (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).map m) ≫ _)
          (pushPullProductIso_hom_app J M X)
    _ = _ :=
        congrArg
          (fun m => (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map m ≫ _)
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).map_comp _ _)
    _ = _ :=
        congrArg (· ≫ _)
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map_comp _ _)
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (_ ≫ ·) hkey
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ :=
        congrArg (· ≫ _)
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map_comp _ _).symm
    _ = _ :=
        congrArg
          (fun m => (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map m ≫ _)
          hnat
    _ = _ :=
        congrArg (· ≫ _)
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map_comp _ _)
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (_ ≫ ·) htri
    _ = _ := Category.comp_id _

/-- **The mate of the product description of push-pull, one component at a time.** The adjunct,
under the localization adjunction at `M_i`, of `pushPullProductIso` followed by the projection
onto the `i`-th factor is the `i`-th component of the restriction of the push-pull counit of
`j_M` to the component sites.

This is `CategoryTheory.SemiRepresentable.pushPullProductIso_mate` with the product of the
localization adjunctions replaced by the one at `M_i`; the passage between the two is
`componentLocalizationAdjunction_counit_app`. It is the form a chase at a single component
uses. -/
theorem pushPullProductIso_mate_π (M : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) (i : M.I) :
    ((localizationAdjunction J (M.obj i)).homEquiv
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
                (componentwiseTopology J M) J ⋙
              (componentOverForget M).sheafPushforwardCocontinuous (Type u)
                (componentwiseTopology J M) J).obj X)
          ((localizationPullback (M.obj i) J).obj X)).symm
        ((pushPullProductIso J M (componentwiseTopology J M) rfl).hom.app X ≫
          Pi.π (fun j : M.I => (localizationPullback (M.obj j) J ⋙
            localizationPushforward (M.obj j) J).obj X) i) =
      (restrictSheaf J M (Type u)).map
        (((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
            (componentwiseTopology J M) J).counit.app
          (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) i :=
  ((localizationAdjunction J (M.obj i)).homEquiv_counit _ _ _).trans
    ((congrArg (· ≫ (localizationAdjunction J (M.obj i)).counit.app
          ((localizationPullback (M.obj i) J).obj X))
        ((localizationPullback (M.obj i) J).map_comp
          ((pushPullProductIso J M (componentwiseTopology J M) rfl).hom.app X)
          (Pi.π (fun j : M.I => (localizationPullback (M.obj j) J ⋙
            localizationPushforward (M.obj j) J).obj X) i))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => (localizationPullback (M.obj i) J).map
              ((pushPullProductIso J M (componentwiseTopology J M) rfl).hom.app X) ≫ m)
            (componentLocalizationAdjunction_counit_app J M
              (fun j : M.I => (localizationPullback (M.obj j) J).obj X) i).symm).trans
          (congrFun (pushPullProductIso_mate J M X) i))))

end CategoryTheory.SemiRepresentable

end
