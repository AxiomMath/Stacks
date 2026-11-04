module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Cosimplicial
public import StacksFrontier.AlgebraicTopology.StandardResolution.Basic
public import StacksFrontier.AlgebraicTopology.StandardResolution.Godement
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
import Mathlib.Topology.Sheaves.Sheafify
import StacksCore.Tactic.StacksAttribute

/-!
# The Godement resolution

Let `(X, O_X)` be a ringed space and let `f : X_disc ⟶ X` be the morphism of ringed spaces from
the points of `X` with the discrete topology. Applying `f_* f^*` repeatedly to a sheaf of
`O_X`-modules `F` gives the Godement complex
`f_* f^* F → f_* f^* f_* f^* F → ⋯`, functorial in `F`, augmented by `F`, and with every term a
flasque `O_X`-module.

## Main definitions

* `discreteRingedSpace`, `fromDiscrete`: the discrete ringed space `X_disc` on the points of `X`
  and the morphism `f : X_disc ⟶ X`.
* `godementComonad`, `godementSimplicial`, `godementCosimplicial`: the comonad `(f_* f^*)ᵒᵖ` on
  `Mod(𝒪_X)ᵒᵖ`, its standard resolution, and the opposite augmented cosimplicial object of
  endofunctors of `Mod(𝒪_X)`.
* `godementComplex`, `godementAugmentation`: the Godement complex as a functor
  `Mod(𝒪_X) ⥤ CochainComplex (Mod(𝒪_X)) ℕ` and its augmentation from `F ↦ F[0]`.

## Main results

* `godementComplexEvalIso`: the term of the Godement complex in degree `n` is the iterate
  `(f_* f^*)^(n+1)`, naturally in `F`.
* `isFlasque_iterate_modulePullbackPushforward`, `isFlasque_godementComplex`: each term
  `(f_* f^*)^(n+1) F` is flasque, because a sheaf on a discrete space is flasque and pushforward
  preserves flasqueness.
* `exists_functorial_flasque_godementComplex`: the functorial Godement complex, its terms
  identified with the iterates of `f_* f^*`, together with its augmentation and the flasqueness
  of every term.
* `fromDiscrete_stalkMap_bijective`: the germ map of `f : X_disc ⟶ X` on structure sheaves is
  bijective, because the structure sheaf of `X_disc` is the sheafification of the pullback of
  `𝒪_X` and `f` is the identity on points. This is what makes the construction compute stalks.

## Implementation notes

The cosimplicial object of the construction is the standard resolution of the comonad `f^* f_*`
on the opposite category, which the library provides only through the existence statement
`CategoryTheory.Godement.exists_augmented_standardResolution`. That resolution is named here by
`Exists.choose` (`godementSimplicial`), with `godementSimplicial_left_obj` and
`godementSimplicial_right` giving back the two pieces of its specification that the rest of the
file uses; everything downstream — the complex, its augmentation, the degreewise identification
of its terms — is then an honest definition rather than an existentially quantified one, which is
what a statement about the complex itself can be formulated against.

The exactness of the augmented complex and the stalkwise homotopy equivalence, clauses (3) and
(5) of [Stacks, Tag 0FKS], are proved in
`StacksFrontier/Topology/Sheaves/Cohomology/GodementResolution/StalkHomotopy.lean`, which is where
`fromDiscrete_stalkMap_bijective` is used.

## References

* [Stacks Project, Tag 0FKS](https://stacks.math.columbia.edu/tag/0FKS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open SSet Simplicial AlgebraicTopology
open scoped ZeroObject

universe u
universe v w

namespace AlgebraicGeometry.GodementResolution

/-! ### The discrete ringed space over `X` and the morphism `f`

The points of `X` carry a second, discrete topology; the type synonym `Discrete ↥X` holds it,
so that both topologies coexist. -/

/-- The discrete topology on the points of `X`, carried by the type synonym `Discrete ↥X`. It is
a local instance: it is the topology of `discreteRingedSpace X`, not a topology on every
discrete category. -/
local instance discreteTopology (X : RingedSpace.{u, u}) :
    TopologicalSpace (Discrete X) := ⊥

/-- The topology of `Discrete ↥X` is discrete. -/
local instance discreteTopology_isDiscrete (X : RingedSpace.{u, u}) :
    DiscreteTopology (Discrete X) := ⟨rfl⟩

/-- The identity on points, read as a continuous map from the discrete topology on the points
of `X` to `X`. -/
def discreteTo (X : RingedSpace.{u, u}) : TopCat.of (Discrete X) ⟶ X.carrier :=
  TopCat.ofHom ⟨fun x ↦ x.as, continuous_of_discreteTopology⟩

/-- `X_disc`: the points of `X` with the discrete topology, carrying the sheafification of the
pullback of `O_X` as its structure sheaf. -/
noncomputable def discreteRingedSpace (X : RingedSpace.{u, u}) :
    RingedSpace.{u, u} where
  carrier := TopCat.of (Discrete X)
  presheaf := ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of (Discrete X)))
    CommRingCat.{u}).obj
      ((TopCat.Presheaf.pullback CommRingCat.{u} (discreteTo X)).obj X.presheaf)).obj
  IsSheaf := ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of (Discrete X)))
    CommRingCat.{u}).obj
      ((TopCat.Presheaf.pullback CommRingCat.{u} (discreteTo X)).obj X.presheaf)).property

/-- The morphism of ringed spaces `f : X_disc ⟶ X` of the Godement construction: the identity on
points, with the unit of the pullback-pushforward adjunction followed by sheafification on
structure sheaves. -/
noncomputable def fromDiscrete (X : RingedSpace.{u, u}) :
    discreteRingedSpace X ⟶ X :=
  InducedCategory.homMk
    { base := discreteTo X
      c := (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (discreteTo X)).unit.app X.presheaf ≫
          (TopCat.Presheaf.pushforward CommRingCat.{u} (discreteTo X)).map
            (CategoryTheory.toSheafify _
              ((TopCat.Presheaf.pullback CommRingCat.{u} (discreteTo X)).obj X.presheaf)) }

/-- The space underlying `X_disc` is discrete. -/
instance discreteTopology_discreteRingedSpace (X : RingedSpace.{u, u}) :
    DiscreteTopology (discreteRingedSpace X) :=
  ⟨rfl⟩

/-- `f : X_disc ⟶ X` is a bijection on points. -/
theorem fromDiscrete_bijective (X : RingedSpace.{u, u}) :
    Function.Bijective (fromDiscrete X).hom.base :=
  ⟨fun ⟨_⟩ ⟨_⟩ h => by congr, fun x => ⟨(⟨x⟩ : Discrete X), rfl⟩⟩

/-- The point of `X_disc` lying over a point `x` of `X`. -/
def discretePoint (X : RingedSpace.{u, u}) (x : X) : discreteRingedSpace X := ⟨x⟩

/-- `f : X_disc ⟶ X` carries `discretePoint X x` to `x`. -/
@[simp]
theorem fromDiscrete_base_discretePoint (X : RingedSpace.{u, u}) (x : X) :
    (fromDiscrete X).hom.base (discretePoint X x) = x := rfl

/-- A morphism of presheafed spaces whose sheaf component factors as the unit of
`g^{-1} ⊣ g_*` followed by `g_*` of some `q : g^{-1} 𝒢 ⟶ ℱ` has an isomorphism for germ map at
`y` as soon as the stalk of `q` at `y` is an isomorphism: the germ map is then the composite of
`TopCat.Presheaf.stalkPullbackHom`, always an isomorphism, with the stalk of `q`.

The statement is about `PresheafedSpace.Hom.stalkMap` of a morphism between *variable*
presheafed spaces on purpose. Written for `f : X_disc ⟶ X` directly, the point `x` has type
`↥(discreteRingedSpace X).carrier`, and `rw` cannot unify it with the point variable of
`TopCat.Presheaf.germ_stalkPullbackHom` without unfolding the semireducible
`discreteRingedSpace`; here both the space and the point are atomic. -/
lemma isIso_stalkMap_of_c_eq_unit_comp
    {Y Z : AlgebraicGeometry.PresheafedSpace CommRingCat.{u}} (α : Y ⟶ Z)
    (q : (TopCat.Presheaf.pullback CommRingCat.{u} α.base).obj Z.presheaf ⟶ Y.presheaf)
    (hc : α.c = (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        α.base).unit.app Z.presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat.{u} α.base).map q)
    (y : Y) (hq : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map q)) :
    IsIso (α.stalkMap y) := by
  have hpb : IsIso (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} α.base Z.presheaf y) := by
    show IsIso (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} α.base Z.presheaf y).hom
    infer_instance
  have he : α.stalkMap y =
      TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} α.base Z.presheaf y ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map q := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hA : Z.presheaf.germ U (α.base y) hU ≫ α.stalkMap y =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} α.base).unit.app
            Z.presheaf).app (op U) ≫
          q.app (op ((Opens.map α.base).obj U)) ≫
            Y.presheaf.germ ((Opens.map α.base).obj U) y hU :=
      (PresheafedSpace.stalkMap_germ α U y hU).trans
        ((congrArg (· ≫ Y.presheaf.germ ((Opens.map α.base).obj U) y hU)
            (congrArg (fun t => t.app (op U)) hc)).trans
          (Category.assoc _ _ _))
    have hB : Z.presheaf.germ U (α.base y) hU ≫
        (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} α.base Z.presheaf y ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map q) =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} α.base).unit.app
            Z.presheaf).app (op U) ≫
          q.app (op ((Opens.map α.base).obj U)) ≫
            Y.presheaf.germ ((Opens.map α.base).obj U) y hU :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map q)
            (TopCat.Presheaf.germ_stalkPullbackHom CommRingCat.{u}
              α.base Z.presheaf y U hU)).trans
          ((Category.assoc _ _ _).trans
            (congrArg
              (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} α.base).unit.app
                Z.presheaf).app (op U) ≫ ·)
              (TopCat.Presheaf.stalkFunctor_map_germ ((Opens.map α.base).obj U) y hU q))))
    exact hA.trans hB.symm
  exact he ▸ IsIso.comp_isIso' hpb hq

/-- **The germ map of `f : X_disc ⟶ X` on structure sheaves is bijective.** The structure sheaf
of `X_disc` is the sheafification of the pullback of `𝒪_X`, and `f` is the identity on points:
taking the stalk at `x` of the pullback gives back the stalk of `𝒪_X` at `f x`
(`TopCat.Presheaf.stalkPullbackHom`) and sheafification does not change stalks
(`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`). So the germ map is a composite of two
isomorphisms.

This is what makes the Godement construction compute stalks: the pullback `f^* F` has stalk
`𝒪_{X_disc, x} ⊗_{𝒪_{X, f x}} F_{f x}`, which is `F_{f x}` precisely because this map is
bijective. -/
theorem fromDiscrete_stalkMap_bijective (X : RingedSpace.{u, u})
    (x : discreteRingedSpace X) :
    Function.Bijective ((fromDiscrete X).hom.stalkMap x) := by
  have : IsIso ((fromDiscrete X).hom.stalkMap x) :=
    isIso_stalkMap_of_c_eq_unit_comp (fromDiscrete X).hom
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of (Discrete X)))
        ((TopCat.Presheaf.pullback CommRingCat.{u} (discreteTo X)).obj X.presheaf))
      rfl x
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u} _)
  exact ConcreteCategory.bijective_of_isIso _

/-- The augmented cosimplicial object of `C` opposite to an augmented simplicial object of
`Cᵒᵖ`. -/
def dualAugmented {C : Type u} [Category.{u, u} C]
    (X : SimplicialObject.Augmented Cᵒᵖ) : CosimplicialObject.Augmented C := by
  let e := cosimplicialSimplicialEquiv C
  refine Comma.mk X.right.unop ((e.inverse.obj X.left).unop) ?_
  change ((Functor.const SimplexCategory).obj X.right.unop) ⟶ (e.inverse.obj X.left).unop
  exact (e.inverse.map X.hom).unop

/-- Every abelian sheaf on a discrete space is flasque: an open subset of an open set is a
direct summand of it, so restriction of sections is a split epimorphism. -/
private lemma flasque_of_discrete_sheaf {X : TopCat} [DiscreteTopology X]
    (F : TopCat.Sheaf AddCommGrpCat X) : F.IsFlasque := by
  constructor
  intro U V i
  let A : Opens X := unop V
  let B : Opens X := unop U
  have hle : A ≤ B := i.unop.le
  let W : Opens X := ⟨(B : Set X) \ (A : Set X), isOpen_discrete _⟩
  have hdisj : A ⊓ W = ⊥ := by
    ext x
    simp [W]
  have hunion : A ⊔ W = B := by
    ext x
    simp only [Opens.mem_sup, SetLike.mem_coe, W]
    exact ⟨fun h => h.elim (fun ha => hle ha) And.left,
      fun hb => (em (x ∈ A)).imp_right fun ha => ⟨hb, ha⟩⟩
  let L := F.isProductOfDisjoint A W hdisj
  let t := L.lift (BinaryFan.mk (𝟙 (F.obj.obj (op A)))
    (0 : F.obj.obj (op A) ⟶ F.obj.obj (op W)))
  have ht : t ≫ F.obj.map (homOfLE le_sup_left).op = 𝟙 (F.obj.obj (op A)) :=
    L.fac (BinaryFan.mk (𝟙 _) 0) ⟨WalkingPair.left⟩
  let r := t ≫ F.obj.map (eqToHom hunion.symm).op
  have hcomp : (eqToHom hunion.symm).op ≫ i = (homOfLE le_sup_left).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hr : r ≫ F.obj.map i = 𝟙 (F.obj.obj (op A)) := by
    dsimp [r]
    rw [Category.assoc, ← Functor.map_comp, hcomp, ht]
  exact SplitEpi.epi ⟨r, hr⟩

/-- Flasqueness is invariant under isomorphism of sheaves. -/
private lemma flasque_of_iso {X : TopCat} {F G : TopCat.Sheaf AddCommGrpCat X}
    (e : F ≅ G) (hF : TopCat.Sheaf.IsFlasque F) : TopCat.Sheaf.IsFlasque G := by
  constructor
  intro U V i
  have h (W : (Opens X)ᵒᵖ) : IsIso (e.hom.hom.app W) := ⟨⟨e.inv.hom.app W,
    congrArg (fun g => g.hom.app W) e.hom_inv_id, congrArg (fun g => g.hom.app W) e.inv_hom_id⟩⟩
  have h₂ : Epi (F.obj.map i ≫ e.hom.hom.app V) := inferInstance
  rw [e.hom.hom.naturality i] at h₂
  exact (CategoryTheory.epi_comp_iff_of_epi (e.hom.hom.app U) (G.obj.map i)).1 h₂

/-- Every positive iterate `(f_* f^*)^(n+1) F` of a morphism out of a discrete space is a flasque
sheaf of modules: a sheaf on a discrete space is flasque, and pushforward preserves flasqueness. -/
@[stacks 0FKS "each term f_* f^* ⋯ f_* f^* F is a flasque module",
  sga "4 XVII 4.2.3" "(i)",
  sga "4 XVII 4.2" "flasqueness of terms"]
theorem isFlasque_iterate_modulePullbackPushforward
    {Xdisc X : RingedSpace.{u, u}} (f : Xdisc ⟶ X) [DiscreteTopology Xdisc]
    (n : ℕ) (F : SheafOfModules.{u} (structureSheafRing X)) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (structureSheafRing X)).obj
      (((RingedSpaceModuleAdjunction.modulePullback f ⋙
        RingedSpaceModuleAdjunction.modulePushforward f).iterate (n + 1)).obj F)) := by
  let Odisc := structureSheafRing Xdisc
  let M := (((RingedSpaceModuleAdjunction.modulePullback f ⋙
    RingedSpaceModuleAdjunction.modulePushforward f).iterate n).obj F)
  have hdisc : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Odisc).obj
      ((RingedSpaceModuleAdjunction.modulePullback f).obj M)) :=
    flasque_of_discrete_sheaf _
  show TopCat.Sheaf.IsFlasque
    ((TopCat.Sheaf.pushforward AddCommGrpCat f.hom.base).obj
      ((SheafOfModules.toSheaf Odisc).obj ((RingedSpaceModuleAdjunction.modulePullback f).obj M)))
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque _ f.hom.base

/-- Iterating an endofunctor of `Dᵒᵖ` and then passing to the opposite functor is the same as
iterating the opposite functor. -/
lemma unop_iterate {D : Type v} [Category.{w, v} D]
    (F : Dᵒᵖ ⥤ Dᵒᵖ) (n : ℕ) :
    (F.iterate n).unop = F.unop.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (F.iterate n).unop ⋙ F.unop = F.unop.iterate n ⋙ F.unop
      rw [ih]

/-- The standard resolution of a comonad, read off from [Stacks, Tag 0G5N]: for a comonad
`(T, ε, δ)` on `D` there is an augmented simplicial object `S` of the category `D ⥤ D` of
endofunctors whose term in degree `n` is the power `T^{n+1}`, whose faces and degeneracies are
`Godement.face ε` and `Godement.degeneracy δ`, and whose augmentation object is `𝟭 D` with
augmentation `ε`.

The comonad identities are exactly the hypotheses of
`CategoryTheory.Godement.exists_augmented_standardResolution`; collecting them here lets the
resolution be named once, by `Exists.choose`, instead of being reintroduced by `obtain` in every
proof that uses it. -/
theorem exists_standardResolution {D : Type v} [Category.{w, v} D] (T : Comonad D) :
    ∃ (S : SimplicialObject.Augmented (D ⥤ D))
      (h : ∀ n : ℕ, S.left.obj (op ⦋n⦌) = (T : D ⥤ D).iterate (n + 1))
      (hS : S.right = 𝟭 D),
      (∀ (n : ℕ) (j : Fin (n + 2)), S.left.δ j =
        eqToHom (h (n + 1)) ≫ Godement.face T.ε (n + 1) j ≫ eqToHom (h n).symm) ∧
      (∀ (n : ℕ) (j : Fin (n + 1)), S.left.σ j =
        eqToHom (h n) ≫ Godement.degeneracy T.δ n j ≫ eqToHom (h (n + 1)).symm) ∧
      S.hom.app (op ⦋0⦌) = eqToHom (h 0) ≫ Godement.face T.ε 0 0 ≫ eqToHom hS.symm :=
  CategoryTheory.Godement.exists_augmented_standardResolution T.ε T.δ
    (by ext F; exact T.left_counit F) (by ext F; exact T.right_counit F)
    (by ext F; exact (T.coassoc F).symm)

/-- The functor to cochain complexes given by the alternating coface map complex of the
cosimplicial object of endofunctors underlying an augmented cosimplicial object. -/
noncomputable def resolutionComplex {C : Type v} [Category.{w, v} C]
    [Abelian C] (Q : CosimplicialObject.Augmented (C ⥤ C)) :
    C ⥤ CochainComplex C ℕ :=
  (HomologicalComplex.complexOfFunctorsToFunctorToComplex).obj
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj Q.right)

/-- The augmentation of a cosimplicial object composes to zero with the first differential of
its alternating coface map complex, the two cofaces out of degree `0` agreeing on it. -/
lemma resolutionAugmentationCondition {C : Type v} [Category.{w, v} C]
    [Preadditive C] (Q : CosimplicialObject.Augmented (C ⥤ C)) :
    Q.hom.app (.mk 0) ≫
      ((AlgebraicTopology.alternatingCofaceMapComplex (C ⥤ C)).obj Q.right).d 0 1 = 0 := by
  rw [show ((AlgebraicTopology.alternatingCofaceMapComplex (C ⥤ C)).obj Q.right).d 0 1 =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD Q.right 0 by
    show (CochainComplex.of _ _
      (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared Q.right)).d 0 (0 + 1) = _
    exact CochainComplex.of_d (fun n : ℕ ↦ Q.right.obj (.mk n))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD Q.right) 0]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul,
    CosimplicialObject.δ]
  have h (i : Fin 2) : Q.hom.app (.mk 0) ≫ Q.right.map (SimplexCategory.δ i) =
      Q.hom.app (.mk 1) := by
    simpa using (Q.hom.naturality (SimplexCategory.δ i)).symm
  calc
    _ = (Q.hom.app (.mk 0) ≫ Q.right.map (SimplexCategory.δ (0 : Fin 2))) +
        -(Q.hom.app (.mk 0) ≫ Q.right.map (SimplexCategory.δ (1 : Fin 2))) :=
          (Preadditive.comp_add _ _ _ _ _ _).trans (congrArg (_ + ·) (Preadditive.comp_neg _ _))
    _ = 0 := by rw [h 0, h 1, add_neg_cancel]

/-- The augmentation of `resolutionComplex Q` by the complex concentrated in degree `0`, for an
augmented cosimplicial object whose augmentation object is the identity functor. -/
noncomputable def resolutionAugmentation {C : Type v} [Category.{w, v} C]
    [Abelian C] (Q : CosimplicialObject.Augmented (C ⥤ C))
    (hL : Q.left = 𝟭 C) :
    (CochainComplex.single₀ C) ⟶ resolutionComplex Q := by
  let K := AlgebraicTopology.AlternatingCofaceMapComplex.obj Q.right
  let f₀ := eqToHom hL.symm ≫ Q.hom.app (.mk 0)
  have hf : f₀ ≫ K.d 0 1 = 0 := by
    change (eqToHom hL.symm ≫ Q.hom.app (.mk 0)) ≫ K.d 0 1 = 0
    have hbase : Q.hom.app (.mk 0) ≫ K.d 0 1 = 0 := resolutionAugmentationCondition Q
    calc
      _ = eqToHom hL.symm ≫ (Q.hom.app (.mk 0) ≫ K.d 0 1) := Category.assoc _ _ _
      _ = eqToHom hL.symm ≫ 0 := by rw [hbase]
      _ = 0 := comp_zero
  have hfAt (A : C) : f₀.app A ≫ ((resolutionComplex Q).obj A).d 0 1 = 0 := by
    change f₀.app A ≫ (K.d 0 1).app A = 0
    exact congrArg (fun z => z.app A) hf
  have hηAt (A : C) :
      (((CochainComplex.fromSingle₀Equiv ((resolutionComplex Q).obj A) A).symm
        ⟨f₀.app A, hfAt A⟩).f 0) = f₀.app A :=
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := (resolutionComplex Q).obj A) (X := A) (f := f₀.app A) (hf := hfAt A)
  refine { app := fun A => (CochainComplex.fromSingle₀Equiv _ A).symm ⟨f₀.app A, hfAt A⟩,
           naturality := ?_ }
  intro A B f
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
      hηAt B, hηAt A]
    simpa [resolutionComplex, HomologicalComplex.complexOfFunctorsToFunctorToComplex,
      HomologicalComplex.asFunctor, AlgebraicTopology.alternatingCofaceMapComplex_obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of,
      CochainComplex.of_X]
      using f₀.naturality f
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 A (n + 1)
      (by omega)).eq_of_src _ _

/-! ### The Godement complex and its augmentation

The construction is carried out in the opposite category: `f_* f^*` is a *comonad* on
`Mod(𝒪_X)`, so `(f_* f^*)ᵒᵖ` is the comonad `godementComonad X` on `Mod(𝒪_X)ᵒᵖ` whose standard
resolution (Stacks 0G5N) is an augmented *simplicial* object of endofunctors of `Mod(𝒪_X)ᵒᵖ`.
Passing to the opposite turns it into the augmented cosimplicial object
`godementCosimplicial X` of endofunctors of `Mod(𝒪_X)`, whose Moore cochain complex is the
Godement complex. -/

section GodementComplex

variable (X : RingedSpace.{u, u})

/-- The comonad on `Mod(𝒪_X)ᵒᵖ` whose standard resolution is the Godement construction: the
comonad of the opposite `(f_*)ᵒᵖ ⊣ (f^*)ᵒᵖ` of the adjunction `f^* ⊣ f_*` along the morphism
`f : X_disc ⟶ X`. Its underlying endofunctor is the opposite of `f_* f^*`. -/
noncomputable def godementComonad :
    Comonad (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ :=
  (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction (fromDiscrete X)).op.toComonad

/-- Godement's augmented simplicial object of endofunctors of `Mod(𝒪_X)ᵒᵖ`: the standard
resolution of the comonad `godementComonad X`. -/
noncomputable def godementSimplicial :
    SimplicialObject.Augmented
      ((SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
        (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ) :=
  (exists_standardResolution (godementComonad X)).choose

/-- The term of `godementSimplicial X` in degree `n` is the power `((f_* f^*)^{n+1})ᵒᵖ`. -/
theorem godementSimplicial_left_obj (n : ℕ) :
    (godementSimplicial X).left.obj (op ⦋n⦌) =
      (godementComonad X : _ ⥤ _).iterate (n + 1) :=
  (exists_standardResolution (godementComonad X)).choose_spec.choose n

/-- The augmentation object of `godementSimplicial X` is the identity functor. -/
theorem godementSimplicial_right :
    (godementSimplicial X).right = 𝟭 _ :=
  (exists_standardResolution (godementComonad X)).choose_spec.choose_spec.choose

/-- Godement's augmented cosimplicial object of endofunctors of `Mod(𝒪_X)`, opposite to
`godementSimplicial X`: its term in degree `n` is the iterate `(f_* f^*)^{n+1}` and its
augmentation object is the identity functor. -/
noncomputable def godementCosimplicial :
    CosimplicialObject.Augmented
      (SheafOfModules.{u} (structureSheafRing X) ⥤
        SheafOfModules.{u} (structureSheafRing X)) :=
  dualAugmented ((SimplicialObject.Augmented.whiskeringObj _ _
    (Functor.opUnopEquiv _ _).inverse).obj (godementSimplicial X))

/-- The augmentation object of `godementCosimplicial X` is the identity functor of
`Mod(𝒪_X)`: it is the opposite of the augmentation object `𝟭 Mod(𝒪_X)ᵒᵖ` of the standard
resolution. -/
theorem godementCosimplicial_left :
    (godementCosimplicial X).left =
      𝟭 (SheafOfModules.{u} (structureSheafRing X)) := by
  dsimp [godementCosimplicial, dualAugmented]
  rw [godementSimplicial_right]
  show Functor.unop (𝟭 (SheafOfModules.{u}
    (structureSheafRing X))ᵒᵖ) = _
  rfl

/-- **The Godement complex** of [Stacks, Tag 0FKS]: the functor sending a sheaf of
`𝒪_X`-modules `F` to the cochain complex
`f_* f^* F → f_* f^* f_* f^* F → ⋯`, the Moore cochain complex (the alternating coface map
complex) of the cosimplicial object `godementCosimplicial X` evaluated at `F`. Its term in
degree `n` is the iterate `(f_* f^*)^{n+1} F`, by `godementComplexEvalIso`. -/
noncomputable def godementComplex :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℕ :=
  resolutionComplex (godementCosimplicial X)

/-- **The augmentation of the Godement complex** of [Stacks, Tag 0FKS]: the morphism of
functors to cochain complexes from `F ↦ F[0]`, the complex concentrated in degree `0`, to
the Godement complex, given in degree `0` by the unit `F ⟶ f_* f^* F` of the adjunction
`f^* ⊣ f_*`. -/
noncomputable def godementAugmentation :
    CochainComplex.single₀ (SheafOfModules.{u} (structureSheafRing X)) ⟶
      godementComplex X :=
  resolutionAugmentation (godementCosimplicial X) (godementCosimplicial_left X)

/-- The term of the Godement complex in degree `n` is the iterate `(f_* f^*)^{n+1}`, naturally
in `F`. -/
noncomputable def godementComplexEvalIso (n : ℕ) :
    godementComplex X ⋙
        HomologicalComplex.eval
          (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℕ) n ≅
      (RingedSpaceModuleAdjunction.modulePullback (fromDiscrete X) ⋙
        RingedSpaceModuleAdjunction.modulePushforward (fromDiscrete X)).iterate (n + 1) := by
  apply eqToIso
  change ((godementSimplicial X).left.obj (op ⦋n⦌)).unop = _
  rw [congrArg (fun T : (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
    (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ => T.unop)
    (godementSimplicial_left_obj X n)]
  rw [unop_iterate (F := (godementComonad X).toFunctor)]
  rfl

/-- Every term of the Godement complex is a flasque `𝒪_X`-module: it is an iterate
`(f_* f^*)^{n+1} F`, and `isFlasque_iterate_modulePullbackPushforward` applies. -/
theorem isFlasque_godementComplex (F : SheafOfModules.{u}
    (structureSheafRing X)) (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (structureSheafRing X)).obj
        (((godementComplex X).obj F).X n)) :=
  flasque_of_iso
    (((SheafOfModules.toSheaf (structureSheafRing X)).mapIso
      ((godementComplexEvalIso X n).app F)).symm)
    (isFlasque_iterate_modulePullbackPushforward (fromDiscrete X) n F)

end GodementComplex

/-- **Stacks 0FKS**, the complex and its flasque terms. For a ringed space `(X, O_X)` there is a
functor `G` from sheaves of `O_X`-modules to cochain complexes, with an augmentation `η` from the
complex concentrated in degree `0`, whose term in degree `n` is the iterate
`(f_* f^*)^(n+1) F` along the morphism `f : X_disc ⟶ X` from the points of `X` with the discrete
topology, and each of whose terms is a flasque `O_X`-module. -/
@[stacks 0FKS "the functorial complex of flasque terms f_* f^* ⋯ f_* f^* F",
  sga "4 XVII 4.2.3" "(i)", sga "4 XVII 4.2" "functorial flasque terms"]
theorem exists_functorial_flasque_godementComplex (X : RingedSpace.{u, u}) :
    ∃ (G : SheafOfModules.{u} (structureSheafRing X) ⥤
        CochainComplex
          (SheafOfModules.{u} (structureSheafRing X)) ℕ)
      (_η : CochainComplex.single₀
          (SheafOfModules.{u} (structureSheafRing X)) ⟶ G)
      (_termIso : ∀ n,
        G ⋙ HomologicalComplex.eval
            (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℕ) n ≅
          (RingedSpaceModuleAdjunction.modulePullback (fromDiscrete X) ⋙
            RingedSpaceModuleAdjunction.modulePushforward (fromDiscrete X)).iterate (n + 1)),
      ∀ F n, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (structureSheafRing X)).obj
          ((G.obj F).X n)) :=
  ⟨godementComplex X, godementAugmentation X, godementComplexEvalIso X,
    isFlasque_godementComplex X⟩

end AlgebraicGeometry.GodementResolution
