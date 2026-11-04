module

public import StacksFrontier.AlgebraicGeometry.Modules.PushforwardUnitHomEquiv
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerPushforwardPullback

/-!
# Condition (4) of Tag 0EK2 read on morphisms into direct images of structure sheaves

Let `T` be a tower of schemes `Y_n ⟶ S` (`Stacks.Algebraization.InfinitesimalTower`), for example
the infinitesimal neighbourhoods of a closed subscheme read over an open neighbourhood. Condition
(4) of [Stacks, Tag 0EK2] for a pair `(P, 𝒪_S)` is stated with morphisms of pullbacks
`P|_W ⟶ 𝒪_S|_W` and `P|_{Y_n} ⟶ 𝒪_S|_{Y_n}`. Through
`Stacks.Algebraization.pullbackHomEquivPushforwardUnit` these are the morphisms
`P ⟶ (W ⟶ S)_* 𝒪_W` and `P ⟶ (Y_n ⟶ S)_* 𝒪_{Y_n}`, and restriction along a factorization becomes
composition with the restriction map of direct images. This file records the two halves of the
condition in that form, which is the form in which the proof of [Stacks, Tag 0ELA] uses it: a
compatible system of morphisms into the direct images on the `Y_n` comes from a morphism on a
neighbourhood, and two morphisms on a neighbourhood that agree on every `Y_n` agree on a smaller
neighbourhood.

## Main definitions

* `Stacks.Algebraization.pushforwardAlgebraRestriction`, `pushforwardUnitRestriction` — the
  restriction morphism `g_* 𝒪_G ⟶ g'_* 𝒪_{G'}` attached to a factorization `h ≫ g = g'`, of
  algebra sheaves and of modules.

## Main results

* `Stacks.Algebraization.TowerUnit.exists_hom` — compatible systems of morphisms into the direct
  images on the terms of the tower come from a morphism on a neighbourhood of the support.
* `Stacks.Algebraization.TowerUnit.eq_of_forall` — morphisms agreeing on every term agree after
  shrinking the neighbourhood.
* `Stacks.Algebraization.pushforwardUnitRestriction_comp_pullbackUnitIso_inv` — the restriction
  maps of direct images of structure sheaves are those of direct images of pullbacks of `𝒪_S`.

## Implementation notes

Both halves are the case `Q = 𝒪_S` of
`Stacks.Algebraization.InfinitesimalTower.exists_hom_pushforward` and
`Stacks.Algebraization.InfinitesimalTower.eq_of_forall_pushforward`, transported along the
identifications `𝒪_G ≅ g^* 𝒪_S` by `pushforwardUnitRestriction_comp_pullbackUnitIso_inv`. The
codomains are kept in the spelling `AlgebraSheaf.underlyingModule (pushforwardAlgebra _)`, which
is the one the multiplication of the algebra sheaf is stated with; the transport is written in
term mode because the two spellings are identified only up to unfolding.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Algebraization

/-! ### Restriction maps between direct images of structure sheaves -/

/-- The restriction morphism `g_* 𝒪_G ⟶ g'_* 𝒪_{G'}` of `𝒪_S`-algebras attached to a
factorization `h ≫ g = g'`: the canonical morphism of direct image algebras, with source and
target spelled through `g` and `g'` themselves. -/
def pushforwardAlgebraRestriction {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G) (g' : G' ⟶ S)
    (hh : h ≫ g = g') : pushforwardAlgebra g ⟶ pushforwardAlgebra g' :=
  pushforwardAlgebraMap (Over.homMk h hh : (Over.mk g' : Over S) ⟶ Over.mk g)

/-- The restriction map `g_* 𝒪_G ⟶ g'_* 𝒪_{G'}` of `𝒪_S`-modules underlying
`pushforwardAlgebraRestriction`. -/
abbrev pushforwardUnitRestriction {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G) (g' : G' ⟶ S)
    (hh : h ≫ g = g') :
    AlgebraSheaf.underlyingModule (pushforwardAlgebra g) ⟶
      AlgebraSheaf.underlyingModule (pushforwardAlgebra g') :=
  AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraRestriction g h g' hh)

/-- Restriction morphisms compose. -/
theorem pushforwardAlgebraRestriction_comp {S G G' G'' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (g' : G' ⟶ S) (hh : h ≫ g = g') (h' : G'' ⟶ G') (g'' : G'' ⟶ S) (hh' : h' ≫ g' = g'')
    (k : G'' ⟶ G) (hk : h' ≫ h = k) :
    pushforwardAlgebraRestriction g h g' hh ≫ pushforwardAlgebraRestriction g' h' g'' hh' =
      pushforwardAlgebraRestriction g k g''
        (show k ≫ g = g'' by rw [← hk, Category.assoc, hh, hh']) := by
  have e : (Over.homMk h' hh' : (Over.mk g'' : Over S) ⟶ Over.mk g') ≫
      (Over.homMk h hh : (Over.mk g' : Over S) ⟶ Over.mk g) =
        Over.homMk k (show k ≫ g = g'' by rw [← hk, Category.assoc, hh, hh']) :=
    Over.OverMorphism.ext hk
  rw [pushforwardAlgebraRestriction, pushforwardAlgebraRestriction, pushforwardAlgebraRestriction,
    ← e, pushforwardAlgebraMap_comp]

/-- Restriction maps compose. -/
theorem pushforwardUnitRestriction_comp {S G G' G'' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (g' : G' ⟶ S) (hh : h ≫ g = g') (h' : G'' ⟶ G') (g'' : G'' ⟶ S) (hh' : h' ≫ g' = g'')
    (k : G'' ⟶ G) (hk : h' ≫ h = k) :
    pushforwardUnitRestriction g h g' hh ≫ pushforwardUnitRestriction g' h' g'' hh' =
      pushforwardUnitRestriction g k g'' (show k ≫ g = g'' by rw [← hk, Category.assoc, hh, hh']) :=
  ((AlgebraSheaf.underlyingModuleFunctor S).map_comp _ _).symm.trans
    (congrArg AlgebraSheaf.underlyingModuleMap
      (pushforwardAlgebraRestriction_comp g h g' hh h' g'' hh' k hk))

/-- `Stacks.Algebraization.pullbackHomEquivPushforwardUnit` is the adjunction identification
`Stacks.Algebraization.pullbackHomEquivPushforward` followed by `𝒪_G ≅ g^* 𝒪_S`. -/
theorem pullbackHomEquivPushforwardUnit_eq {S G : Scheme.{u}} (g : G ⟶ S) (P : S.Modules)
    (β : P ⟶ (Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) :
    pullbackHomEquivPushforwardUnit g P β =
      pullbackHomEquivPushforward g P _ β ≫ (Scheme.Modules.pullbackUnitIso g).inv := by
  simp [pullbackHomEquivPushforwardUnit, pullbackHomEquivPushforward]

/-- **The restriction of direct images of structure sheaves is the restriction of direct images
of pullbacks of `𝒪_S`.** Under the identifications `𝒪_G ≅ g^* 𝒪_S` and `𝒪_{G'} ≅ g'^* 𝒪_S`,
`pushforwardUnitRestriction` is `Stacks.Algebraization.pushforwardPullbackRestriction` at the
module `𝒪_S`. -/
theorem pushforwardUnitRestriction_comp_pullbackUnitIso_inv {S G G' : Scheme.{u}} (g : G ⟶ S)
    (h : G' ⟶ G) (g' : G' ⟶ S) (hh : h ≫ g = g') :
    (pushforwardUnitRestriction g h g' hh :
        (Scheme.Modules.pushforward g).obj (Scheme.unitModule G) ⟶
          (Scheme.Modules.pushforward g').obj (Scheme.unitModule G')) ≫
        (Scheme.Modules.pushforward g').map (Scheme.Modules.pullbackUnitIso g').inv =
      (Scheme.Modules.pushforward g).map (Scheme.Modules.pullbackUnitIso g).inv ≫
        pushforwardPullbackRestriction g h g' hh (Scheme.unitModule S) := by
  apply (pullbackHomEquivPushforward g'
    ((Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) _).injective
  have hR : ∀ {G₀ : Scheme.{u}} (g₀ : G₀ ⟶ S) (P : S.Modules) {M N : G₀.Modules}
      (β : P ⟶ (Scheme.Modules.pushforward g₀).obj M) (e : M ⟶ N),
      pullbackHomEquivPushforward g₀ P N (β ≫ (Scheme.Modules.pushforward g₀).map e) =
        pullbackHomEquivPushforward g₀ P M β ≫ e :=
    fun g₀ P _ _ β e =>
      (Scheme.Modules.pullbackPushforwardAdjunction g₀).homEquiv_naturality_right_symm β e
  have hc := pullbackHomEquivPushforwardUnit_comp g h g' hh
    ((Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) (𝟙 _)
  have hr := pullbackHomEquivPushforward_pushforwardPullbackRestriction g h g' hh
    ((Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) (Scheme.unitModule S)
    ((Scheme.Modules.pushforward g).map (Scheme.Modules.pullbackUnitIso g).inv)
  have h1 := hR g ((Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) (𝟙 _)
    (Scheme.Modules.pullbackUnitIso g).inv
  rw [Category.id_comp] at h1
  have hid : (𝟙 ((Scheme.Modules.pushforward g).obj (Scheme.unitModule G)) ≫
      (pushforwardUnitRestriction g h g' hh :
        (Scheme.Modules.pushforward g).obj (Scheme.unitModule G) ⟶
          (Scheme.Modules.pushforward g').obj (Scheme.unitModule G'))) =
      pushforwardUnitRestriction g h g' hh := Category.id_comp _
  refine (hR g' _ _ _).trans ?_
  refine ((pullbackHomEquivPushforwardUnit_eq g' _ _).symm.trans ?_).trans hr.symm
  refine ((congrArg (pullbackHomEquivPushforwardUnit g' _) hid.symm).trans hc).trans ?_
  rw [h1, pullbackHomEquivPushforwardUnit_eq]

/-! ### Condition (4) of Tag 0EK2, read on morphisms into direct images -/

namespace TowerUnit

variable {S : Scheme.{u}} (T : InfinitesimalTower S)

/-- **Algebraization of a compatible system of morphisms into the direct images of the structure
sheaves of the terms of a tower.** If condition (4) of [Stacks, Tag 0EK2] holds for the pair
`(P, 𝒪_S)`, every compatible system of morphisms `P ⟶ (Y_n ⟶ S)_* 𝒪_{Y_n}` comes from a morphism
`P ⟶ (W ⟶ S)_* 𝒪_W` for some open `W` containing the support of the tower. -/
theorem exists_hom (P : S.Modules) (hP : T.IsHomsComplete P (Scheme.unitModule S))
    (α : ∀ n : ℕ, P ⟶ AlgebraSheaf.underlyingModule (pushforwardAlgebra (T.obj n).hom))
    (hα : ∀ (n m : ℕ) (h : n ≤ m),
      α m ≫ pushforwardUnitRestriction (T.obj m).hom (T.trans n m h).left
        (T.obj n).hom (Over.w (T.trans n m h)) = α n) :
    ∃ (W : S.Opens) (hW : T.support ⊆ W)
      (β : P ⟶ AlgebraSheaf.underlyingModule (pushforwardAlgebra W.ι)),
      ∀ n : ℕ, β ≫ pushforwardUnitRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
        (T.homToOpen_ι hW n) = α n := by
  have hcomp : ∀ (n m : ℕ) (h : n ≤ m),
      (α m ≫ (Scheme.Modules.pushforward (T.obj m).hom).map
          (Scheme.Modules.pullbackUnitIso (T.obj m).hom).inv) ≫
        pushforwardPullbackRestriction (T.obj m).hom (T.trans n m h).left (T.obj n).hom
          (Over.w (T.trans n m h)) (Scheme.unitModule S) =
      α n ≫ (Scheme.Modules.pushforward (T.obj n).hom).map
          (Scheme.Modules.pullbackUnitIso (T.obj n).hom).inv := by
    intro n m h
    exact (Category.assoc _ _ _).trans ((congrArg (fun t => α m ≫ t)
      (pushforwardUnitRestriction_comp_pullbackUnitIso_inv (T.obj m).hom (T.trans n m h).left
        (T.obj n).hom (Over.w (T.trans n m h))).symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (Scheme.Modules.pushforward (T.obj n).hom).map
        (Scheme.Modules.pullbackUnitIso (T.obj n).hom).inv) (hα n m h))))
  obtain ⟨W, hW, β, hβ⟩ := T.exists_hom_pushforward P (Scheme.unitModule S) hP _ hcomp
  refine ⟨W, hW, β ≫ (Scheme.Modules.pushforward W.ι).map
    (Scheme.Modules.pullbackUnitIso W.ι).hom, fun n => ?_⟩
  have hW' : (Scheme.Modules.pushforward W.ι).map (Scheme.Modules.pullbackUnitIso W.ι).hom ≫
      (Scheme.Modules.pushforward W.ι).map (Scheme.Modules.pullbackUnitIso W.ι).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  refine (cancel_mono ((Scheme.Modules.pushforward (T.obj n).hom).map
    (Scheme.Modules.pullbackUnitIso (T.obj n).hom).inv)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (β ≫ (Scheme.Modules.pushforward W.ι).map
    (Scheme.Modules.pullbackUnitIso W.ι).hom) ≫ t)
      (pushforwardUnitRestriction_comp_pullbackUnitIso_inv W.ι (T.homToOpen hW n) (T.obj n).hom
        (T.homToOpen_ι hW n))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => β ≫ t) ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ pushforwardPullbackRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
      (T.homToOpen_ι hW n) (Scheme.unitModule S)) hW').trans (Category.id_comp _)))).trans ?_
  exact hβ n

/-- **Two morphisms into the direct image of the structure sheaf of a neighbourhood that agree
on every term of a tower agree on a smaller neighbourhood**, granted condition (4) of
[Stacks, Tag 0EK2] for the pair `(P, 𝒪_S)`. -/
theorem eq_of_forall (P : S.Modules) (hP : T.IsHomsComplete P (Scheme.unitModule S))
    (W : S.Opens) (hW : T.support ⊆ W)
    (a b : P ⟶ AlgebraSheaf.underlyingModule (pushforwardAlgebra W.ι))
    (hab : ∀ n : ℕ, a ≫ pushforwardUnitRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
        (T.homToOpen_ι hW n) = b ≫ pushforwardUnitRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
        (T.homToOpen_ι hW n)) :
    ∃ (W' : S.Opens) (_ : T.support ⊆ W') (h : W' ≤ W),
      a ≫ pushforwardUnitRestriction W.ι (S.homOfLE h) W'.ι (S.homOfLE_ι h) =
        b ≫ pushforwardUnitRestriction W.ι (S.homOfLE h) W'.ι (S.homOfLE_ι h) := by
  have hι : ∀ {W₀ : S.Opens} {G₀ : Scheme.{u}} (k : G₀ ⟶ W₀.toScheme) (g₀ : G₀ ⟶ S)
      (hk : k ≫ W₀.ι = g₀) (c : P ⟶ AlgebraSheaf.underlyingModule (pushforwardAlgebra W₀.ι)),
      (c ≫ (Scheme.Modules.pushforward W₀.ι).map (Scheme.Modules.pullbackUnitIso W₀.ι).inv) ≫
          pushforwardPullbackRestriction W₀.ι k g₀ hk (Scheme.unitModule S) =
        (c ≫ pushforwardUnitRestriction W₀.ι k g₀ hk) ≫
          (Scheme.Modules.pushforward g₀).map (Scheme.Modules.pullbackUnitIso g₀).inv :=
    fun k g₀ hk c => (Category.assoc _ _ _).trans ((congrArg (fun t => c ≫ t)
      (pushforwardUnitRestriction_comp_pullbackUnitIso_inv _ k g₀ hk).symm).trans
        (Category.assoc _ _ _).symm)
  obtain ⟨W', hW', h, he⟩ := T.eq_of_forall_pushforward P (Scheme.unitModule S) hP W hW
    (a ≫ (Scheme.Modules.pushforward W.ι).map (Scheme.Modules.pullbackUnitIso W.ι).inv)
    (b ≫ (Scheme.Modules.pushforward W.ι).map (Scheme.Modules.pullbackUnitIso W.ι).inv)
    (fun n => (hι _ _ _ a).trans ((congrArg (fun t => t ≫
      (Scheme.Modules.pushforward (T.obj n).hom).map
        (Scheme.Modules.pullbackUnitIso (T.obj n).hom).inv) (hab n)).trans (hι _ _ _ b).symm))
  refine ⟨W', hW', h, (cancel_mono ((Scheme.Modules.pushforward W'.ι).map
    (Scheme.Modules.pullbackUnitIso W'.ι).inv)).1 ?_⟩
  exact (hι _ _ _ a).symm.trans (he.trans (hι _ _ _ b))

end TowerUnit

end Stacks.Algebraization

end
