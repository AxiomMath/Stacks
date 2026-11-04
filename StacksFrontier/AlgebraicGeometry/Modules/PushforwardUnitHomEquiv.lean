module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerPushforwardPullback

/-!
# Morphisms into a pushed-forward structure sheaf as morphisms of pullbacks

Let `g : G ⟶ S` be a morphism of schemes and `P` a module on `S`. By the pullback–pushforward
adjunction a morphism `P ⟶ g_* 𝒪_G` is the same thing as a morphism `g^* P ⟶ 𝒪_G`, and
`𝒪_G = g^* 𝒪_S`. So a morphism `P ⟶ g_* 𝒪_G` is a morphism `g^* P ⟶ g^* 𝒪_S` between pullbacks of
two modules on `S`: this is `Stacks.Algebraization.pullbackHomEquivPushforwardUnit`. In this form
it is a point of the system of morphisms between restrictions of `P` and `𝒪_S` that the
completion functor of [Stacks, Tag 0EK2] is stated with.

The identification is compatible with base change along a factorization `h ≫ g = g'`: following a
morphism `P ⟶ g_* 𝒪_G` by the canonical algebra map `g_* 𝒪_G ⟶ g'_* 𝒪_{G'}` corresponds to
pulling the morphism of pullbacks back along `h`
(`Stacks.Algebraization.pullbackHomEquivPushforwardUnit_comp`). This is the compatibility the
proof of [Stacks, Tag 0ELA] uses to read a compatible system of maps
`f_* 𝒪_U ⟶ 𝒪_{Y_n}` as an object of the target of the completion functor.

## Main definitions

* `Stacks.Algebraization.pullbackHomEquivPushforwardUnit` — `Hom(P, g_* 𝒪_G) ≃
  Hom(g^* P, g^* 𝒪_S)`.

## Main results

* `Stacks.Algebraization.underlyingModuleMap_pushforwardAlgebraMap_homMk` — the module map
  underlying the algebra map `g_* 𝒪_G ⟶ (h ≫ g)_* 𝒪_{G'}` is `g_*` of the unit map
  `𝒪_G ⟶ h_* 𝒪_{G'}`, followed by the composition isomorphism of pushforwards.
* `Stacks.Algebraization.pullbackHomEquivPushforwardUnit_comp` — compatibility with a
  factorization `h ≫ g = g'`.

## Implementation notes

The compatibility is the case `M = 𝒪_G`, `φ = 𝒪_G ⟶ h_* 𝒪_{G'}` of
`Stacks.Algebraization.pullbackHomEquivPushforward_comp`, combined with
`Scheme.Modules.pullbackUnitIso_homEquiv` and `Scheme.Modules.pullbackUnitIso_comp`, which
describe the identifications `h^* 𝒪_G ≅ 𝒪_{G'}` through the adjunction.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Algebraization

/-- **Morphisms into a pushed-forward structure sheaf are morphisms of pullbacks.** For
`g : G ⟶ S` and a module `P` on `S`, a morphism `P ⟶ g_* 𝒪_G` corresponds by adjunction to a
morphism `g^* P ⟶ 𝒪_G`, and `𝒪_G` is `g^* 𝒪_S`. -/
def pullbackHomEquivPushforwardUnit {S G : Scheme.{u}} (g : G ⟶ S) (P : S.Modules) :
    (P ⟶ (Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) ≃
      ((Scheme.Modules.pullback g).obj P ⟶
        (Scheme.Modules.pullback g).obj (Scheme.unitModule S)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv P _).symm.trans
    ((Iso.refl _).homCongr (Scheme.Modules.pullbackUnitIso g).symm)

/-- **The module map underlying the canonical algebra map of a factorization.** For `h : G' ⟶ G`
and `g : G ⟶ S`, the algebra map `g_* 𝒪_G ⟶ (h ≫ g)_* 𝒪_{G'}` attached to `h` as a morphism over
`S` is, on underlying modules, `g_*` of the unit map `𝒪_G ⟶ h_* 𝒪_{G'}` followed by the
composition isomorphism `g_* h_* ≅ (h ≫ g)_*`. -/
theorem underlyingModuleMap_pushforwardAlgebraMap_homMk {S G G' : Scheme.{u}} (g : G ⟶ S)
    (h : G' ⟶ G) :
    AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMap (Over.homMk h rfl : (Over.mk (h ≫ g) : Over S) ⟶ Over.mk g)) =
      (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit h) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app _ := by
  ext U x
  rfl

/-- `Stacks.Algebraization.pullbackHomEquivPushforwardUnit_comp` for the factorization
`h ≫ g = h ≫ g`, with the algebra map written out as module maps: the case
`M = 𝒪_G` of `Stacks.Algebraization.pullbackHomEquivPushforward_comp`. -/
theorem pullbackHomEquivPushforwardUnit_comp_aux {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (P : S.Modules)
    (β : P ⟶ (Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) :
    pullbackHomEquivPushforwardUnit (h ≫ g) P (β ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit h) ≫
        (Scheme.Modules.pushforwardComp h g).hom.app _) =
      pullbackHomMap P (Scheme.unitModule S) h rfl (pullbackHomEquivPushforwardUnit g P β) := by
  have hU : ∀ {G₀ : Scheme.{u}} (g₀ : G₀ ⟶ S) (Q : S.Modules)
      (γ : Q ⟶ (Scheme.Modules.pushforward g₀).obj (Scheme.unitModule G₀)),
      pullbackHomEquivPushforwardUnit g₀ Q γ =
        pullbackHomEquivPushforward g₀ Q _ γ ≫ (Scheme.Modules.pullbackUnitIso g₀).inv := by
    intro G₀ g₀ Q γ
    simp [pullbackHomEquivPushforwardUnit, pullbackHomEquivPushforward]
  have hh : pullbackHomEquivPushforward h _ _ (Scheme.Modules.unitToPushforwardUnit h) =
      (Scheme.Modules.pullbackUnitIso h).hom :=
    (Equiv.symm_apply_eq _).2 (Scheme.Modules.pullbackUnitIso_homEquiv h).symm
  have he : (Scheme.Modules.pullbackUnitIso h).hom ≫ (Scheme.Modules.pullbackUnitIso (h ≫ g)).inv =
      (Scheme.Modules.pullback h).map (Scheme.Modules.pullbackUnitIso g).inv ≫
        (Scheme.Modules.pullbackComp h g).hom.app (Scheme.unitModule S) := by
    rw [Iso.comp_inv_eq, ← Scheme.Modules.pullbackUnitIso_comp h g]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hU, pullbackHomEquivPushforward_comp_aux, hh, hU]
  simp only [pullbackHomMap, pullbackObjFactorIso, pullbackFactorIso, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, Iso.trans_inv, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp, he]

/-- **Compatibility with a factorization.** If `h ≫ g = g'`, following `β : P ⟶ g_* 𝒪_G` by the
canonical algebra map `g_* 𝒪_G ⟶ g'_* 𝒪_{G'}` corresponds, under
`Stacks.Algebraization.pullbackHomEquivPushforwardUnit`, to pulling the morphism
`g^* P ⟶ g^* 𝒪_S` attached to `β` back along `h`. -/
theorem pullbackHomEquivPushforwardUnit_comp {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (g' : G' ⟶ S) (hh : h ≫ g = g') (P : S.Modules)
    (β : P ⟶ (Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) :
    pullbackHomEquivPushforwardUnit g' P (β ≫ AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMap (Over.homMk h hh : (Over.mk g' : Over S) ⟶ Over.mk g))) =
      pullbackHomMap P (Scheme.unitModule S) h hh (pullbackHomEquivPushforwardUnit g P β) := by
  subst hh
  rw [underlyingModuleMap_pushforwardAlgebraMap_homMk]
  exact pullbackHomEquivPushforwardUnit_comp_aux g h P β

end Stacks.Algebraization

end
