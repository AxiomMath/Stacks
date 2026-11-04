module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TransitionCocycle
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The unit and cocycle laws for the transition of component modules

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
The transition `f_φ^*ℱₘ ⟶ ℱₙ` of the restrictions of a sheaf of `O`-modules, which is the mate
of the direct-image transition under the pullback-pushforward adjunction, is a pseudofunctorial
datum: the transition attached to an identity simplex map is the canonical identification of
`f_𝟙^*` with the identity, and the transition attached to a composite is the composite of the
two transitions, compared by the pullback compositor. These are the two laws that make a
cartesian module into a descent datum, and they are the module half of Stacks 09WF; for sheaves
of sets they are `CategoryTheory.SimplicialSiteSituation.fiberTransition_id` and
`.fiberTransition_comp`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesIdIso`: the identification
  `f_𝟙^* ≅ 𝟭` of the pullback of modules along the transition of an identity simplex map with
  the identity functor.

## Main results

* `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_id`: the unit law.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_comp`: the cocycle law.

## Implementation notes

Both laws are instances of one piece of adjunction bookkeeping, stated here as the private
lemmas `leftAdjointUniq_homEquiv_comp` and `homEquiv_symm_comp`: the mate of a composite of
direct-image comparisons is the composite of the mates, the comparison of the two left adjoints
being the one that uniqueness of a left adjoint produces. That is exactly the shape in which
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` — hence
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso` — and
`AlgebraicGeometry.RingedToposHom.pullbackModulesIsoId` are built, so no comparison is chosen
here and none is extracted from an existence statement.

What is left after that reduction is the same law for *direct* images of modules,
`restrictTransitionModules_comp`, and there the content is the already-proved law for sheaves of
sets: a morphism of sheaves of modules is determined by its sections, every comparison occurring
in the statement is the identity or the geometric compositor of Stacks 09WE on sections, and the
equation of sections is
`CategoryTheory.SimplicialSiteSituation.restrictTransition_comp` read at one section. Descending
all the way to sections is deliberate. The same equation taken at the level of morphisms of
sheaves of modules forces the elaborator to identify the two spellings
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf (S.totalRingSheaf O) n` and
`Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O` of the
structure sheaf of a component — equal by `rfl`, but only after unfolding the category of
sheaves of modules over each — and that exhausts its heartbeats; at sections the two carriers
are the same type and nothing has to be unfolded.

For the same reason the pullback compositor is handed to the abstract lemma through the
`rfl`-equation `transitionPullbackModulesCompIso_eq` rather than by unification, and the
comparison is substituted into the goal with `congrArg` at an explicitly given motive rather
than with `rw`, whose motive is formed over the whole goal and does not typecheck across the
two spellings.

The structure sheaf is a sheaf of *commutative* rings, which is the level at which this
development has ringed topoi and the pullback of modules, where the source says "rings".

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The unit law -/

/-- The structure map of the transition morphism of ringed topoi of an identity simplex map is,
on underlying sheaves of sets, the inverse of the unit comparison of direct images of
Stacks 09WE.

This is the hypothesis that `AlgebraicGeometry.RingedToposHom.pullbackModulesIsoId` consumes;
it is public because it occurs in the body of an exposed `def`. -/
theorem transitionFSharpId (n : SimplexCategory) :
    (S.componentRingedTopos O n).forgetRing.map (S.transitionRingedToposHom O (𝟙 n)).fSharp =
      (S.pushforwardId n).symm.hom.app
        ((S.componentRingedTopos O n).forgetRing.obj (S.componentRingedTopos O n).O) :=
  (S.transitionRingedToposHom_forgetFSharp O (𝟙 n)).trans
    ((Iso.comp_hom_eq_id ((S.pushforwardId n).app _)).mp
      (S.restrictTransition_id n ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)))

/-- **Stacks 09WE, on pullbacks of modules.** The identification `f_𝟙^* ≅ 𝟭` of the pullback of
sheaves of modules along the transition morphism of ringed topoi of an identity simplex map with
the identity functor.

Both functors are left adjoint to the identity, the left-hand side through the unit comparison
of direct images of Stacks 09WE, so this is uniqueness of a left adjoint. -/
noncomputable def transitionPullbackModulesIdIso (n : SimplexCategory) :
    (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules ≅
      𝟭 (SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :=
  (S.transitionRingedToposHom O (𝟙 n)).pullbackModulesIsoId (S.pushforwardId n).symm
    (S.transitionFSharpId O n)

/-- **Stacks 09WF for sheaves of modules: the unit law.** The transition of the restrictions of
a sheaf of `O`-modules attached to an identity simplex map is the canonical identification of
`f_𝟙^*` with the identity functor. -/
@[stacks 09WF "the unit law for the transition of modules"]
theorem fiberTransitionModules_id (n : SimplexCategory)
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    S.fiberTransitionModules O (𝟙 n) M =
      (S.transitionPullbackModulesIdIso O n).hom.app
        ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) := by
  let E := (S.transitionRingedToposHom O (𝟙 n)).pushforwardModulesIsoId
    (S.pushforwardId n).symm (S.transitionFSharpId O n)
  let A := (S.transitionRingedToposHom O (𝟙 n)).pullbackAdjPushforwardModules.ofNatIsoRight E.symm
  have hR := Adjunction.homEquiv_leftAdjointUniq_hom_app A
    (Adjunction.id (C := SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)))
    ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M)
  have h1 := Adjunction.homEquiv_ofNatIsoRight_apply
    (S.transitionRingedToposHom O (𝟙 n)).pullbackAdjPushforwardModules E.symm
    (S.fiberTransitionModules O (𝟙 n) M)
  have h2 := congrArg (fun t => t ≫ E.symm.hom.app
      ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M))
    (S.fiberTransitionModules_adj O (𝟙 n) M)
  refine (A.homEquiv _ _).injective (Eq.trans (h1.trans (h2.trans ?_)) hR.symm)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact congrArg (fun t => (Sheaf.sectionsFunctor (S.componentTopology n) V).map t x)
    (S.restrictTransition_id n (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))

/-! ### The cocycle law -/

/-- Transposing a composite whose first factor compares two left adjoints of one functor. -/
private theorem leftAdjointUniq_homEquiv_comp {A : Type*} [Category A] {B : Type*} [Category B]
    {P P' : A ⥤ B} {Q : B ⥤ A} (adj : P ⊣ Q) (adj' : P' ⊣ Q) {X : A} {Y : B}
    (g : P'.obj X ⟶ Y) :
    adj.homEquiv X Y ((Adjunction.leftAdjointUniq adj adj').hom.app X ≫ g) =
      adj'.homEquiv X Y g := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]

/-- The mates of a composite of comparisons of right adjoints compose: a cocycle of
direct-image comparisons transposes to a cocycle of the left adjoints, compared by the
isomorphism that uniqueness of a left adjoint produces. -/
private theorem homEquiv_symm_comp {A : Type*} [Category A] {B : Type*} [Category B]
    {C : Type*} [Category C] {L₁ : A ⥤ B} {R₁ : B ⥤ A} (adjψ : L₁ ⊣ R₁)
    {L₂ : B ⥤ C} {R₂ : C ⥤ B} (adjφ : L₂ ⊣ R₂) {L : A ⥤ C} {R : C ⥤ A} (adjχ : L ⊣ R)
    (τ : R₂ ⋙ R₁ ≅ R) {X : A} {Z : B} {Y : C} (uψ : X ⟶ R₁.obj Z) (uφ : Z ⟶ R₂.obj Y)
    (uχ : X ⟶ R.obj Y) (hu : (uψ ≫ R₁.map uφ) ≫ τ.hom.app Y = uχ) :
    (adjχ.homEquiv X Y).symm uχ =
      (Adjunction.leftAdjointUniq (adjχ.ofNatIsoRight τ.symm) (adjψ.comp adjφ)).hom.app X ≫
        L₂.map ((adjψ.homEquiv X Z).symm uψ) ≫ (adjφ.homEquiv Z Y).symm uφ := by
  refine ((adjχ.ofNatIsoRight τ.symm).homEquiv X Y).injective ?_
  rw [leftAdjointUniq_homEquiv_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Iso.symm_hom, ← hu,
    Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The direct-image transition of component modules, read through the four-field morphism of
ringed topoi that the pullback of modules is constructed over, is the mate of the pullback
transition for that reading of the adjunction. -/
private theorem fiberTransitionModules_adj_toModulesHom {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((pullbackAdjPushforwardModules
          (S.transitionRingedToposHom O φ).toModulesHom).homEquiv _ _)
        (S.fiberTransitionModules O φ M) =
      S.restrictTransitionModulesApp O φ M ≫
        (S.transitionRingedToposHom O φ).toModulesPushforwardIso.inv.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) :=
  (Iso.eq_comp_inv (((S.transitionRingedToposHom O φ).toModulesPushforwardIso).app _)).mpr
    ((Adjunction.homEquiv_ofNatIsoRight_apply
      (pullbackAdjPushforwardModules (S.transitionRingedToposHom O φ).toModulesHom)
      (S.transitionRingedToposHom O φ).toModulesPushforwardIso
      (S.fiberTransitionModules O φ M)).symm.trans (S.fiberTransitionModules_adj O φ M))

/-- The pullback transition is the inverse transpose of the direct-image transition. -/
private theorem homEquiv_symm_restrictTransitionModulesApp {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((pullbackAdjPushforwardModules
          (S.transitionRingedToposHom O φ).toModulesHom).homEquiv
        ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj M)
        ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M)).symm
      (S.restrictTransitionModulesApp O φ M ≫
        (S.transitionRingedToposHom O φ).toModulesPushforwardIso.inv.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M)) =
      S.fiberTransitionModules O φ M :=
  (Equiv.symm_apply_eq _).mpr (S.fiberTransitionModules_adj_toModulesHom O φ M).symm

/-- The pullback compositor of Stacks 09WE is the isomorphism of left adjoints attached to the
comparison of direct images of modules. One definitional step, supplied on its own so that the
abstract lemma it feeds does not have to recover it by unification. -/
private theorem transitionPullbackModulesCompIso_eq {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    S.transitionPullbackModulesCompIso O ψ φ =
      Adjunction.leftAdjointUniq
        ((pullbackAdjPushforwardModules
            (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom).ofNatIsoRight
          (S.transitionPushforwardModulesCompIso O ψ φ).symm)
        ((pullbackAdjPushforwardModules (S.transitionRingedToposHom O ψ).toModulesHom).comp
          (pullbackAdjPushforwardModules (S.transitionRingedToposHom O φ).toModulesHom)) :=
  rfl

/-- **Stacks 09WF for sheaves of modules, on direct images: the cocycle law.** The direct-image
transition attached to a composite simplex map is the composite of the two transitions, compared
by the comparison of direct images of Stacks 09WE.

On sections every comparison here is the identity or the geometric compositor, and the equation
is the one for sheaves of sets. -/
private theorem restrictTransitionModules_comp {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((S.restrictTransitionModulesApp O ψ M ≫
            (S.transitionRingedToposHom O ψ).toModulesPushforwardIso.inv.app
              ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj M)) ≫
          (pushforwardModules (S.transitionRingedToposHom O ψ).toModulesHom).map
            (S.restrictTransitionModulesApp O φ M ≫
              (S.transitionRingedToposHom O φ).toModulesPushforwardIso.inv.app
                ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M))) ≫
        (S.transitionPushforwardModulesCompIso O ψ φ).hom.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) =
      S.restrictTransitionModulesApp O (ψ ≫ φ) M ≫
        (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesPushforwardIso.inv.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) n).obj M) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact congrArg (fun t => (Sheaf.sectionsFunctor (S.componentTopology l) V).map t x)
    (S.restrictTransition_comp ψ φ (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))

/-- **Stacks 09WF for sheaves of modules: the cocycle law.** The transition of the restrictions
of a sheaf of `O`-modules attached to a composite simplex map is the composite of the two
transitions, compared by the pullback compositor of Stacks 09WE. -/
@[stacks 09WF "the cocycle law for the transition of modules"]
theorem fiberTransitionModules_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    S.fiberTransitionModules O (ψ ≫ φ) M =
      (S.transitionPullbackModulesCompIso O ψ φ).hom.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) l).obj M) ≫
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
            (S.fiberTransitionModules O ψ M) ≫
          S.fiberTransitionModules O φ M := by
  refine Eq.trans ?_ (congrArg
    (fun e : (S.transitionRingedToposHom O (ψ ≫ φ)).toModulesHom.pullbackModules ≅
        (S.transitionRingedToposHom O ψ).toModulesHom.pullbackModules ⋙
          (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules =>
      e.hom.app ((S.componentModuleRestriction (S.totalRingSheaf O) l).obj M) ≫
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
            (S.fiberTransitionModules O ψ M) ≫
          S.fiberTransitionModules O φ M)
    (S.transitionPullbackModulesCompIso_eq O ψ φ)).symm
  rw [← S.homEquiv_symm_restrictTransitionModulesApp O ψ M,
    ← S.homEquiv_symm_restrictTransitionModulesApp O φ M,
    ← S.homEquiv_symm_restrictTransitionModulesApp O (ψ ≫ φ) M]
  exact homEquiv_symm_comp _ _ _ _ _ _ _ (S.restrictTransitionModules_comp O ψ φ M)

end CategoryTheory.SimplicialSiteSituation

end
