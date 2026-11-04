module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionCocycle

/-!
# Cartesian objects of `D(O)` are detected by the face maps (Stacks 07TG (4))

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total
site. An object `K` of the derived category of `O`-modules is cartesian when the derived
transition `Lf_φ^* K_m ⟶ K_n` of Stacks 0D9P is an isomorphism for every arrow `φ` of the
simplex category. This file shows that it suffices to test the face maps `δ i`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_faces`:
  **Stacks 07TG (4)**.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedComponentModuleTransition_id`: the unit
  law for the derived transitions — the derived transition of an identity simplex map is an
  isomorphism. This is the half of the pseudofunctoriality of `φ ↦ Lf_φ^*` that Stacks 0D9P
  does not record, its cocycle half being
  `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleTransition_comp`.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedTransitionComparison_id`: degreewise
  pullback along the transition of an identity simplex map is already its own left derived
  functor.

## Implementation notes

The simplex maps whose derived transition is invertible form a multiplicative class of
morphisms. Its composition law is the cocycle condition
`derivedComponentModuleTransition_comp` of Stacks 0D9P together with the invertibility of the
comparison of derived pullbacks, which is Stacks 0D6D
(`isIso_derivedTransitionCompComparison`). Its identity law is not recorded by Stacks 0D9P — a
simplicial system of the derived category of modules imposes the cocycle condition and nothing
else — and is proved here as `isIso_derivedComponentModuleTransition_id`.

That unit law reduces, by `CategoryTheory.isIso_liftedTransition`, to the invertibility of the
two inputs out of which `derivedComponentModuleTransition` is lifted:

* the degreewise transition, which at an identity simplex map is the identification
  `f_𝟙^* ≅ 𝟭` by the unit law of Stacks 09WF for modules
  (`CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_id`), and therefore induces
  an invertible transition of homotopy categories; and
* the canonical comparison `Lf_𝟙^* ⟶ f_𝟙^*`, which is invertible because `f_𝟙^*` is
  isomorphic to the identity functor, hence exact, hence inverts the quasi-isomorphisms: a
  comparison out of a left derived functor of a functor which inverts the weak equivalences is
  an isomorphism (`CategoryTheory.Functor.isIso_of_isLeftDerivedFunctor_of_inverts`). The
  invertibility is read off Mathlib's `Functor.mapDerivedCategoryFactorsh` for `f_𝟙^*`, so no
  comparison of homotopy categories with the identity functor is rebuilt.

## References

* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The unit law for the degreewise transition of component modules -/

/-- **Stacks 09WF for sheaves of modules: the unit law, as an invertibility statement.** The
pullback transition of the restrictions attached to an identity simplex map is an isomorphism,
being the identification of `f_𝟙^*` with the identity functor. -/
instance isIso_componentModuleTransition_id (n : SimplexCategory) :
    IsIso (S.componentModuleTransition O (𝟙 n)) := by
  have happ : ∀ M : SheafOfModules.{u} (S.totalRingSheaf O),
      IsIso ((S.componentModuleTransition O (𝟙 n)).app M) := by
    intro M
    rw [componentModuleTransition_app, fiberTransitionModules_id]
    exact ((S.transitionPullbackModulesIdIso O n).app _).isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- The same, read between the modules of the total and the component ringed topoi, which is
the reading `derivedComponentModuleTransition` is lifted from. -/
instance isIso_componentModulesTransition_id (n : SimplexCategory) :
    IsIso (S.componentModulesTransition O (𝟙 n)) :=
  S.isIso_componentModuleTransition_id O n

/-! ### Derived pullback along the transition of an identity simplex map -/

/-- **Stacks 09WE, on pullbacks of modules.** The identification `f_𝟙^* ≅ 𝟭` of Stacks 09WF,
with the identity functor read at the modules of the component ringed topos rather than at the
restriction of the total sheaf of rings. The two readings of that category agree by `rfl`, but
only after both sheaves of rings are computed, so — as for `componentModulesRestriction` — the
identification is paid once here and the instance below meets it nowhere. -/
def transitionPullbackModulesIdToposIso (n : SimplexCategory) :
    (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules ≅
      𝟭 ((S.componentRingedTopos O n).Modules) :=
  S.transitionPullbackModulesIdIso O n

/-- Pullback of sheaves of modules along the transition morphism of an identity simplex map
preserves finite limits: it is isomorphic to the identity functor. -/
instance preservesFiniteLimits_transitionPullbackModules_id (n : SimplexCategory) :
    PreservesFiniteLimits (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
  preservesFiniteLimits_of_natIso (S.transitionPullbackModulesIdToposIso O n).symm

/-- Pullback of sheaves of modules along the transition morphism of a simplex map preserves
finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_transitionPullbackModules {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules :=
  AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
    (S.transitionRingedToposHom O φ)

/-- **Degreewise pullback along the transition of an identity simplex map inverts the
quasi-isomorphisms.** It is isomorphic to the identity functor, hence exact, so after
localization it factors through the derived category by Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, and the localization functor inverts the
quasi-isomorphisms. -/
theorem isInvertedBy_pullbackOnHomotopy_transition_id (n : SimplexCategory) :
    (targetQuasiIso (S.componentRingedTopos O n)).IsInvertedBy
      (pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O (𝟙 n))) :=
  (MorphismProperty.IsInvertedBy.iff_of_iso _
    (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh).1
    (MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh _) _)

/-- **Degreewise pullback along the transition of an identity simplex map is already its own
left derived functor.** The canonical comparison `Lf_𝟙^* ⟶ f_𝟙^*` is an isomorphism, because
`f_𝟙^*` inverts the quasi-isomorphisms. -/
theorem isIso_derivedTransitionComparison_id (n : SimplexCategory) :
    IsIso (S.derivedTransitionComparison O (𝟙 n)) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (S.derivedTransitionPullback O (𝟙 n))
    (S.derivedTransitionComparison O (𝟙 n))
    (S.isInvertedBy_pullbackOnHomotopy_transition_id O n)

/-! ### The unit law for the derived transition, and the face criterion -/

/-- **The unit law for the derived transitions of Stacks 0D9P.** The derived transition
`Lg_n^* ⋙ Lf_𝟙^* ⟶ Lg_n^*` attached to an identity simplex map is an isomorphism.

Both inputs of the lifted transition are invertible: the degreewise transition by the unit law
of Stacks 09WF for modules, and the comparison of the derived pullback with the degreewise one
because the latter inverts the quasi-isomorphisms. -/
theorem isIso_derivedComponentModuleTransition_id (n : SimplexCategory) :
    IsIso (S.derivedComponentModuleTransition O (𝟙 n)) := by
  have := S.isIso_derivedTransitionComparison_id O n
  delta derivedComponentModuleTransition
  exact isIso_liftedTransition _ _ _ _ _

/-- **Stacks 07TG (4).** An object of the derived category of `O`-modules on the total site of
a simplicial site is cartesian if and only if the derived transition along every face map is an
isomorphism.

The simplex maps whose derived transition is invertible form a multiplicative class: the
identity law is `isIso_derivedComponentModuleTransition_id` and the composition law is the
cocycle condition `derivedComponentModuleTransition_comp` of Stacks 0D9P together with
Stacks 0D6D. Every arrow of the simplex category is a composite of faces and degeneracies, and
`SimplexCategory.δ_comp_σ_self` exhibits each degeneracy as the second factor of a composite
that is an identity, so no separate hypothesis on the degeneracies is needed. -/
@[stacks 07TG "face criterion for objects of D(O)"]
theorem isCartesianDerivedModule_iff_faces
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.IsCartesianDerivedModule O K ↔
      ∀ (k : ℕ) (i : Fin (k + 2)),
        IsIso ((S.derivedComponentModuleTransition O (SimplexCategory.δ i)).app K) := by
  refine ⟨fun h k i => h _, fun h => ?_⟩
  have hid : ∀ n : SimplexCategory,
      IsIso ((S.derivedComponentModuleTransition O (𝟙 n)).app K) := fun n =>
    have := S.isIso_derivedComponentModuleTransition_id O n
    inferInstance
  have hiff : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      IsIso ((S.derivedComponentModuleTransition O (ψ ≫ φ)).app K) ↔
        IsIso ((S.derivedTransitionPullback O φ).map
            ((S.derivedComponentModuleTransition O ψ).app K) ≫
          (S.derivedComponentModuleTransition O φ).app K) := by
    intro l m n ψ φ
    have := S.isIso_derivedTransitionCompComparison O ψ φ
    rw [← S.derivedComponentModuleTransition_comp O ψ φ K,
      isIso_comp_left_iff ((S.derivedTransitionCompComparison O ψ φ).app
        ((S.derivedComponentModuleRestriction O l).obj K))]
  let W : MorphismProperty SimplexCategory :=
    fun _ _ φ => IsIso ((S.derivedComponentModuleTransition O φ).app K)
  have : W.ContainsIdentities := ⟨hid⟩
  have : W.IsStableUnderComposition :=
    ⟨fun ψ φ (_ : IsIso _) (_ : IsIso _) => (hiff ψ φ).mpr inferInstance⟩
  have : W.IsMultiplicative := ⟨⟩
  have hδ : ∀ {k : ℕ} (i : Fin (k + 2)), W (SimplexCategory.δ i) := fun i => h _ i
  have hσ : ∀ {k : ℕ} (i : Fin (k + 1)), W (SimplexCategory.σ i) := by
    intro k i
    have : IsIso ((S.derivedComponentModuleTransition O (SimplexCategory.δ i.castSucc)).app K) :=
      hδ i.castSucc
    have key := (hiff (SimplexCategory.δ i.castSucc) (SimplexCategory.σ i)).mp
      (by rw [SimplexCategory.δ_comp_σ_self]; exact hid _)
    exact (isIso_comp_left_iff _ _).mp key
  have hW := SimplexCategory.morphismProperty_eq_top W hδ hσ
  intro m n φ
  exact show W φ by rw [hW]; trivial

end CategoryTheory.SimplicialSiteSituation

end
