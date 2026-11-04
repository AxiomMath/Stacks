module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Localization of the small pro-étale site

For a weakly étale morphism `j : U ⟶ X`, the slice of the small pro-étale site of `X` over `U`
is canonically the small pro-étale site of `U`. Under this identification, localization
restriction is restriction along `j`.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetalePostcompose` sends an object of the small pro-étale site
  of `U` to its composite over `X`.
* `AlgebraicGeometry.ProEtale.localizationEquivalence` is the canonical equivalence from the
  small pro-étale site of `U` to the slice of the small pro-étale site of `X` over `U`.

## Main results

* `AlgebraicGeometry.ProEtale.localizationEquivalence_forget` identifies the composite of the
  equivalence with the slice forgetful functor as postcomposition by `j`; precomposition on
  sheaves is thus localization restriction.
* `AlgebraicGeometry.ProEtale.localizationEquivalence_inducedTopology` identifies the small
  pro-étale topology of `U` with the localized topology.
* `AlgebraicGeometry.ProEtale.proetalePostcompose_isContinuous` is continuity of
  postcomposition for the small pro-étale topologies.

## Implementation notes

The morphism `U ⟶ X` is packaged as an object `j` of `X.ProEt`, so that the slice is
`Over j`. The arrow-to-`U` equation `localizationEquivalence_obj_over_hom` pins the
equivalence over `U`, rather than merely identifying its composite over `X`.

Mathlib knows that weakly étale morphisms are multiplicative, but the parent
`MorphismProperty.IsStableUnderComposition` is not reachable by instance search from
`MorphismProperty.IsMultiplicative`, so it is recorded here.

## References

* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

/-- Weakly étale morphisms are stable under composition. -/
instance weaklyEtale_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Composition with a weakly étale morphism on small pro-étale sites. -/
def proetalePostcompose {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map (P := (@WeaklyEtale : MorphismProperty Scheme.{u}))
    ⊤ (inferInstance : WeaklyEtale j)

variable {X : Scheme.{u}} (j : X.ProEt)

/-- The canonical equivalence between the site of a weakly étale `U ⟶ X`
and the localization of the site of `X` at `U`. -/
noncomputable def localizationEquivalence : j.left.ProEt ≌ Over j := by
  let F : j.left.ProEt ⥤ Over j := Over.lift (proetalePostcompose j.hom)
    { app := fun V => MorphismProperty.Over.homMk V.hom
      naturality := by
        intro V W f
        apply MorphismProperty.Comma.Hom.ext'
        apply CommaMorphism.ext
        · exact f.w
        · simp }
  let Gobj : Over j → j.left.ProEt := fun V => by
    have hcomp : V.hom.left ≫ j.hom = V.left.hom := V.hom.w
    letI : WeaklyEtale (V.hom.left ≫ j.hom) := by rw [hcomp]; exact V.left.prop
    letI : WeaklyEtale j.hom := j.prop
    letI : WeaklyEtale V.hom.left := WeaklyEtale.of_comp V.hom.left j.hom
    exact Scheme.ProEt.mk V.hom.left
  let G : Over j ⥤ j.left.ProEt := {
    obj := Gobj
    map := fun {V W} f => by
      apply (Scheme.ProEt.forgetFullyFaithful j.left).preimage
      refine Over.homMk f.left.left ?_
      change f.left.left ≫ W.hom.left = V.hom.left
      exact congrArg (fun g : V.left ⟶ j => g.left) f.w
    map_id := by
      intro V
      apply (Scheme.ProEt.forgetFullyFaithful j.left).map_injective
      apply (Over.forget j.left).map_injective
      rfl
    map_comp := by
      intro V W Z f g
      apply (Scheme.ProEt.forgetFullyFaithful j.left).map_injective
      apply (Over.forget j.left).map_injective
      rfl }
  let counit : ∀ V : Over j, (G ⋙ F).obj V ≅ V := fun V => by
    let eOver : (Scheme.ProEt.forget X).obj (((G ⋙ F).obj V).left) ≅
        (Scheme.ProEt.forget X).obj V.left :=
      Over.isoMk (Iso.refl V.left.left) V.hom.w.symm
    let e := (Scheme.ProEt.forgetFullyFaithful X).preimageIso eOver
    exact Over.isoMk e (by
      apply (Scheme.ProEt.forgetFullyFaithful X).map_injective
      apply (Over.forget X).map_injective
      rfl)
  exact {
    functor := F
    inverse := G
    unitIso := NatIso.ofComponents
      (fun V => MorphismProperty.Over.isoMk (Iso.refl V.left) (by
        change 𝟙 V.left ≫ V.hom = V.hom
        simp))
      (by
        intro V W f
        apply MorphismProperty.Comma.Hom.ext'
        rfl)
    counitIso := NatIso.ofComponents
      counit
      (by
        intro V W f
        apply (Over.forget j).map_injective
        apply MorphismProperty.Comma.Hom.ext'
        apply CommaMorphism.ext <;> rfl)
    functor_unitIso_comp := by
      intro V
      apply (Over.forget j).map_injective
      apply MorphismProperty.Comma.Hom.ext'
      rfl }

/-- The localization equivalence keeps the underlying source scheme. -/
lemma localizationEquivalence_obj_left (V : j.left.ProEt) :
    ((localizationEquivalence j).functor.obj V).left.left = V.left :=
  rfl

/-- The slice arrow of the canonical localization equivalence is precisely
the original structure morphism to `U`, not merely an arrow with the same
composite to `X`. -/
lemma localizationEquivalence_obj_over_hom (V : j.left.ProEt) :
    HEq ((localizationEquivalence j).functor.obj V).hom.left V.hom :=
  HEq.rfl

/-- Under localization, the structural morphism to `X` is the composite
of the structural morphism to `U` with `U ⟶ X`. This is the objectwise
identification of localization restriction with restriction along `j`. -/
lemma localizationEquivalence_obj_hom (V : j.left.ProEt) :
    HEq ((localizationEquivalence j).functor.obj V).left.hom
      (V.hom ≫ j.hom) :=
  HEq.rfl

/-- On morphisms, localization restriction is the same map of underlying
schemes as restriction along `j`. -/
lemma localizationEquivalence_map_left {V W : j.left.ProEt} (f : V ⟶ W) :
    HEq (((localizationEquivalence j).functor.map f).left).left f.left :=
  HEq.rfl

/-- Forgetting from the localized site after the canonical equivalence is
postcomposition by `j`. Consequently localization restriction on presheaves
and sheaves is restriction along `j`. -/
lemma localizationEquivalence_forget :
    (localizationEquivalence j).functor ⋙ Over.forget j =
      proetalePostcompose j.hom :=
  rfl

/-- The canonical equivalence identifies pro-étale coverings in the
localization with pro-étale coverings over `U`. -/
lemma localizationEquivalence_inducedTopology :
    Scheme.ProEt.topology j.left =
      (localizationEquivalence j).functor.inducedTopology
        ((Scheme.ProEt.topology X).over j) := by
  let e := localizationEquivalence j
  have hS (S : Scheme.{u}) : Scheme.ProEt.topology S =
      (Scheme.ProEt.forget S).restrictedTopology (Scheme.proetaleTopology.over S) := by
    rw [Scheme.ProEt.topology, Scheme.ProEt.precoverage]
    exact MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      Scheme.proetalePrecoverage Scheme.proetalePrecoverage_le_precoverage_weaklyEtale
  have hcomp : e.functor ⋙ Over.forget j ⋙ Scheme.ProEt.forget X ⋙ Over.forget X =
      Scheme.ProEt.forget j.left ⋙ Over.forget j.left :=
    congrArg (· ⋙ Scheme.ProEt.forget X ⋙ Over.forget X) (localizationEquivalence_forget j)
  ext V S
  rw [hS j.left, Functor.mem_restrictedTopology_iff,
    Functor.mem_inducedTopology_iff_of_isCoverDense]
  conv_rhs => rw [GrothendieckTopology.mem_over_iff]
  rw [hS X, Functor.mem_restrictedTopology_iff]
  conv_lhs => rw [GrothendieckTopology.mem_over_iff]
  conv_rhs => rw [GrothendieckTopology.mem_over_iff]
  have hsieve :
      Sieve.overEquiv ((Scheme.ProEt.forget j.left).obj V)
          (S.functorPushforward (Scheme.ProEt.forget j.left)) =
        Sieve.overEquiv ((Scheme.ProEt.forget X).obj (e.functor.obj V).left)
          ((Sieve.overEquiv (e.functor.obj V) (S.functorPushforward e.functor)).functorPushforward
            (Scheme.ProEt.forget X)) := by
    change Sieve.functorPushforward (Over.forget j.left)
        (S.functorPushforward (Scheme.ProEt.forget j.left)) =
      Sieve.functorPushforward (Over.forget X)
        (Sieve.functorPushforward (Scheme.ProEt.forget X)
          (Sieve.functorPushforward (Over.forget j) (S.functorPushforward e.functor)))
    simp only [← Sieve.functorPushforward_comp]
    cases hcomp
    rfl
  rw [hsieve]
  rfl

/-- Composition with a weakly étale morphism is continuous for the small
pro-étale topologies. -/
theorem proetalePostcompose_isContinuous {U X : Scheme.{u}}
    (j : U ⟶ X) [WeaklyEtale j] :
    (proetalePostcompose j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) := by
  let e := localizationEquivalence (Scheme.ProEt.mk j)
  have : e.functor.IsContinuous
      (Scheme.ProEt.topology U)
      ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk j)) := by
    change (localizationEquivalence (Scheme.ProEt.mk j)).functor.IsContinuous
      (Scheme.ProEt.topology (Scheme.ProEt.mk j).left) _
    rw [localizationEquivalence_inducedTopology]
    infer_instance
  exact Functor.isContinuous_comp e.functor (Over.forget (Scheme.ProEt.mk j))
    (Scheme.ProEt.topology U) ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk j))
    (Scheme.ProEt.topology X)

end AlgebraicGeometry.ProEtale

end
