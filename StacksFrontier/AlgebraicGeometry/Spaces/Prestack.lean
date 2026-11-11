module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.SheafHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.StronglyCartesian
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# The prestack of algebraic spaces over varying bases (Stacks 04UA)

Let `S` be a scheme contained in a big fppf site `B`. Stacks 04UA states that the projection
`AlgebraicGeometry.spacesProjection` from the category of algebraic spaces over varying base
schemes — the comma category of Stacks 04U8 — to the big fppf site of `S` satisfies conditions
(1) and (2) of Stacks 026F; the source states exactly these two conditions, and calls the
result a prestack.

Condition (1), that the projection is a fibred category, is the base change of an algebraic
space along a map of base schemes: the presheaf fibre product is again an algebraic space
(Stacks 02X2), its first projection makes it an object over the new base, and the comparison
map to it is the identity, so Stacks 04U9 says the resulting morphism is strongly cartesian.

Condition (2), that morphisms in each fibre form a sheaf, is fppf descent for morphisms of
algebraic spaces. An object of the fibre over `U` is the same thing as an algebraic space with
a map to the presheaf of points of `U`, hence — under the presheaf form of Stacks 00Y1,
`PSh(C/U) ≌ PSh(C)/h_U` — the same thing as a sheaf on the localized site `C/U`. Transporting
the fibre's hom-sets across that equivalence identifies the morphism presheaf of Stacks 02ZB
with the internal hom of two sheaves on `C/U`, and the internal hom of sheaves is a sheaf. The
length of the file is almost entirely the coherence of that identification: the comparison has
to be natural in the slice variable, which means reconciling the chosen pullbacks of the fibred
structure with the iterated-slice equivalence `(C/U)/T ≌ C/T`.

## Main results

* `AlgebraicGeometry.spacesProjection_isFibered`: **Stacks 04UA**, condition (1).
* `AlgebraicGeometry.spacesProjection_isMorSheaf`: **Stacks 04UA**, condition (2).

Together with effective descent these are the fields of `CategoryTheory.Functor.IsStack`.
The source does not assert effective descent for all algebraic spaces: Remark 04UB explains
that a descent datum glues to an algebraic space when set-theoretic size is ignored, the
obstruction being that an arbitrary disjoint union of algebraic spaces may leave the chosen
partial universe. The stack the source does assert is the finite-type one, Stacks 04UD,
`AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`.

## Implementation notes

Condition (2) is stated with the fibre structure supplied by condition (1), exactly as the
field of `CategoryTheory.Functor.IsStack` does, so the two can be used to build that structure
without restating the instance.

The sheaf attached to a fibre object is `CategoryTheory.OverShriek.fiber` of its structure map,
whose sheaf property follows from that of the underlying algebraic space and the separatedness
of the representable presheaf of the base.

## References

* [Stacks Project, Tag 04UA](https://stacks.math.columbia.edu/tag/04UA)
-/

@[expose] public section

-- Retained deliberately. Without it 28 proof steps in this file fail: the
-- unifier then refuses to see through the non-reducible definitions the argument is phrased
-- with -- `CategoryTheory.OverShriek.fiber`, `CategoryTheory.Over.iteratedSliceBackward`,
-- `CategoryTheory.Functor.pullbackFiberCompIso'` and `Functor.morPresheaf` -- so `change`,
-- `rw` and instance search all lose their targets. Making this file's own private defs
-- `@[reducible]` removes only 4 of the 28, because the definitions that need
-- unfolding are the imported ones, not these. Removing it therefore means restating a dozen
-- blocks of the argument against explicit unfolding lemmas that the library does not yet
-- provide; that belongs with those definitions, not here.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private abbrev SpacesObj :=
  Comma
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F))
    (yoneda : BigFppfOver B S hS ⥤
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

private def spacesFiberPresheaf
    {U : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) :
    (Over U)ᵒᵖ ⥤ Type u :=
  OverShriek.fiber (𝟙 (yoneda.obj U))
    (X.1.hom ≫ yoneda.map (eqToHom X.2))

private theorem spacesFiberPresheaf_isSheaf
    {U : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS |>.over U)
      (spacesFiberPresheaf B S hS X) := by
  let J := BigFppfOver.topology B S hS
  let F := (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
    IsAlgebraicSpace B S hS F)).obj X.1.left
  have hX : Presheaf.IsSheaf J F := X.1.left.property.isSheaf
  have hU : Presheaf.IsSheaf J (yoneda.obj U) :=
    (isAlgebraicSpace_yoneda B S hS U).isSheaf
  have hX' : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ F) :=
    (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J F hX
  have hU' : Presheaf.IsSheaf (J.over U) ((Over.forget U).op ⋙ yoneda.obj U) :=
    (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J (yoneda.obj U) hU
  rw [isSheaf_iff_isSheaf_of_type]
  exact OverShriek.isSheaf_fiber (K := J.over U) (𝟙 (yoneda.obj U))
    (X.1.hom ≫ yoneda.map (eqToHom X.2))
    ((isSheaf_iff_isSheaf_of_type (J.over U) _).1 hX')
    (((isSheaf_iff_isSheaf_of_type (J.over U) _).1 hU').isSeparated)

private noncomputable def overShriek_homEquiv
    {V : BigFppfOver B S hS}
    (A A' : Over (yoneda.obj V)) :
    (OverShriek.fiber (𝟙 (yoneda.obj V)) A.hom ⟶
      OverShriek.fiber (𝟙 (yoneda.obj V)) A'.hom) ≃ (A ⟶ A') := by
  let e := OverShriek.presheafEquivalence (U := V)
  exact (e.fullyFaithfulFunctor.homEquiv (X := e.inverse.obj A)
      (Y := e.inverse.obj A')).trans
    (Iso.homCongr ((OverShriek.presheafCounitIso (U := V)).app A)
      ((OverShriek.presheafCounitIso (U := V)).app A'))

private def spacesFiberOver
    {V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber V) :
    Over (yoneda.obj V) :=
  Over.mk (X.1.hom ≫ yoneda.map (eqToHom X.2))

private def spacesFiberOverHom
    {V : BigFppfOver B S hS}
    {X Y : (spacesProjection B S hS).Fiber V} (m : X ⟶ Y) :
    spacesFiberOver B S hS X ⟶ spacesFiberOver B S hS Y := by
  refine Over.homMk m.1.left.hom ?_
  have : (spacesProjection B S hS).IsHomLift (𝟙 V) m.1 := m.2
  have hm := IsHomLift.fac' (spacesProjection B S hS) (𝟙 V) m.1
  change m.1.right = eqToHom X.2 ≫ (𝟙 V) ≫ eqToHom Y.2.symm at hm
  have hm' : m.1.right = eqToHom X.2 ≫ eqToHom Y.2.symm := by
    simpa only [Category.comp_id, Category.id_comp] using hm
  have hcomma := m.1.w
  change m.1.left.hom ≫ Y.1.hom = X.1.hom ≫ yoneda.map m.1.right at hcomma
  change m.1.left.hom ≫ Y.1.hom ≫ yoneda.map (eqToHom Y.2) =
    X.1.hom ≫ yoneda.map (eqToHom X.2)
  calc
    m.1.left.hom ≫ Y.1.hom ≫ yoneda.map (eqToHom Y.2) =
        X.1.hom ≫ yoneda.map m.1.right ≫ yoneda.map (eqToHom Y.2) :=
          congrArg (fun k => k ≫ yoneda.map (eqToHom Y.2)) hcomma
    _ = X.1.hom ≫ yoneda.map (m.1.right ≫ eqToHom Y.2) := by
          rw [← Functor.map_comp]
    _ = X.1.hom ≫ yoneda.map (eqToHom X.2) := by rw [hm']; simp

private noncomputable def spacesFiberOverFunctor
    (V : BigFppfOver B S hS) :
    (spacesProjection B S hS).Fiber V ⥤ Over (yoneda.obj V) where
  obj := spacesFiberOver B S hS
  map := spacesFiberOverHom B S hS
  map_id X := by apply Over.OverMorphism.ext; rfl
  map_comp f g := by apply Over.OverMorphism.ext; rfl

private def spacesFiberOverInvHom
    {V : BigFppfOver B S hS}
    {X Y : (spacesProjection B S hS).Fiber V}
    (f : spacesFiberOver B S hS X ⟶ spacesFiberOver B S hS Y) : X ⟶ Y := by
  let b : X.1.right ⟶ Y.1.right := eqToHom X.2 ≫ eqToHom Y.2.symm
  let m : X.1 ⟶ Y.1 :=
    { left := ObjectProperty.homMk f.left
      right := b
      w := by
        have hw := f.w
        have hb : b ≫ eqToHom Y.2 = eqToHom X.2 := by simp [b]
        change f.left ≫ Y.1.hom = X.1.hom ≫ yoneda.map b
        apply (cancel_mono (yoneda.map (eqToHom Y.2))).1
        calc
          (f.left ≫ Y.1.hom) ≫ yoneda.map (eqToHom Y.2) =
              X.1.hom ≫ yoneda.map (eqToHom X.2) := hw
          _ = X.1.hom ≫ yoneda.map (b ≫ eqToHom Y.2) :=
                congrArg (fun t => X.1.hom ≫ yoneda.map t) hb.symm
          _ = (X.1.hom ≫ yoneda.map b) ≫ yoneda.map (eqToHom Y.2) := by
                rw [Functor.map_comp, Category.assoc] }
  have hm : (spacesProjection B S hS).IsHomLift (𝟙 V) m := by
    apply IsHomLift.of_fac (spacesProjection B S hS) (𝟙 V) m X.2 Y.2
    simp [m, b, spacesProjection]
  exact ⟨m, hm⟩

private noncomputable def spacesFiberOverHomEquiv
    {V : BigFppfOver B S hS}
    (X Y : (spacesProjection B S hS).Fiber V) :
    (X ⟶ Y) ≃ (spacesFiberOver B S hS X ⟶ spacesFiberOver B S hS Y) where
  toFun := spacesFiberOverHom B S hS
  invFun := spacesFiberOverInvHom B S hS
  left_inv := by
    intro m
    apply Functor.Fiber.hom_ext
    apply Comma.hom_ext
    · rfl
    · let : (spacesProjection B S hS).IsHomLift (𝟙 V) m.1 := m.2
      have hm := IsHomLift.fac' (spacesProjection B S hS) (𝟙 V) m.1
      change m.1.right = eqToHom X.2 ≫ eqToHom Y.2.symm at hm
      exact hm.symm
  right_inv := by
    intro f
    apply Over.OverMorphism.ext
    rfl

private noncomputable def spacesFiberHomEquiv
    {V : BigFppfOver B S hS}
    (X Y : (spacesProjection B S hS).Fiber V) :
    (X ⟶ Y) ≃ (spacesFiberPresheaf B S hS X ⟶ spacesFiberPresheaf B S hS Y) := by
  change (X ⟶ Y) ≃ (OverShriek.fiber (𝟙 (yoneda.obj V))
    (spacesFiberOver B S hS X).hom ⟶ OverShriek.fiber (𝟙 (yoneda.obj V))
      (spacesFiberOver B S hS Y).hom)
  exact (spacesFiberOverHomEquiv B S hS X Y).trans
    (overShriek_homEquiv B S hS (spacesFiberOver B S hS X)
      (spacesFiberOver B S hS Y)).symm

private noncomputable def presheafFiberPullbackIso
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : F ⟶ yoneda.obj U) :
    OverShriek.fiber (𝟙 (yoneda.obj V)) (pullback.fst (yoneda.map g) φ) ≅
      (Over.map g).op ⋙ OverShriek.fiber (𝟙 (yoneda.obj U)) φ := by
  classical
  refine NatIso.ofComponents (fun W => ?_) ?_
  · let e : ((pullback (yoneda.map g) φ).obj (op W.unop.left)) ≃
      Types.PullbackObj ((yoneda.map g).app (op W.unop.left)) (φ.app (op W.unop.left)) :=
      ((pullbackObjIso (yoneda.map g) φ (op W.unop.left)).trans
        (Types.pullbackIsoPullback ((yoneda.map g).app (op W.unop.left))
          (φ.app (op W.unop.left)))).toEquiv
    have hfst : ∀ s : {s : (pullback (yoneda.map g) φ).obj (op W.unop.left) //
        (pullback.fst (yoneda.map g) φ).app (op W.unop.left) s = W.unop.hom},
        (e s.1).1.1 = W.unop.hom := fun s => by
      have hh := congrArg (fun k => k s.1)
        (pullbackObjIso_hom_comp_fst (yoneda.map g) φ (op W.unop.left))
      calc
        (e s.1).1.1 = (pullback.fst ((yoneda.map g).app
            (op W.unop.left)) (φ.app (op W.unop.left)))
              ((pullbackObjIso (yoneda.map g) φ (op W.unop.left)).hom s.1) := by
          simp [e]
        _ = (pullback.fst (yoneda.map g) φ).app (op W.unop.left) s.1 := hh
        _ = W.unop.hom := s.2
    refine Equiv.toIso ?_
    refine {
      toFun := fun s =>
        ⟨(e s.1).1.2, by
          have hfst := hfst s
          calc
            φ.app (op W.unop.left) ((e s.1).1.2) =
                (yoneda.map g).app (op W.unop.left) ((e s.1).1.1) :=
                  (e s.1).2.symm
            _ = (yoneda.map g).app (op W.unop.left) W.unop.hom :=
                  congrArg _ hfst⟩
      invFun := fun s =>
        let z : Types.PullbackObj ((yoneda.map g).app (op W.unop.left))
            (φ.app (op W.unop.left)) := ⟨⟨W.unop.hom, s.1⟩, s.2.symm⟩
        ⟨e.symm z, by
          change (pullback.fst (yoneda.map g) φ).app (op W.unop.left) (e.symm z) =
            W.unop.hom
          calc
            (pullback.fst (yoneda.map g) φ).app (op W.unop.left) (e.symm z) =
                (pullback.fst ((yoneda.map g).app (op W.unop.left))
                  (φ.app (op W.unop.left)))
                    ((Types.pullbackIsoPullback ((yoneda.map g).app (op W.unop.left))
                      (φ.app (op W.unop.left))).inv z) := by
              calc
                _ = (pullback.fst ((yoneda.map g).app (op W.unop.left))
                    (φ.app (op W.unop.left)))
                      ((pullbackObjIso (yoneda.map g) φ (op W.unop.left)).hom (e.symm z)) :=
                    (congrArg (fun k => k (e.symm z))
                      (pullbackObjIso_hom_comp_fst (yoneda.map g) φ
                        (op W.unop.left))).symm
                _ = _ := by simp [e]
            _ = W.unop.hom := by simp [z]⟩
      left_inv := by
        intro s
        apply Subtype.ext
        apply e.injective
        simp only [Equiv.apply_symm_apply]
        apply Subtype.ext
        exact Prod.ext (hfst s).symm (by rfl)
      right_inv := by
        intro s
        apply Subtype.ext
        simp [e] }
  · intro W W' h
    ext s
    apply Subtype.ext
    change (pullback.snd ((yoneda.map g).app (op W'.unop.left))
          (φ.app (op W'.unop.left)))
        ((pullbackObjIso (yoneda.map g) φ (op W'.unop.left)).hom
          ((pullback (yoneda.map g) φ).map h.unop.left.op s.1)) =
      F.map h.unop.left.op
        ((pullback.snd ((yoneda.map g).app (op W.unop.left))
          (φ.app (op W.unop.left)))
          ((pullbackObjIso (yoneda.map g) φ (op W.unop.left)).hom s.1))
    have h₁ := congrArg (fun k => k
      (((pullback (yoneda.map g) φ).map h.unop.left.op) s.1))
      (pullbackObjIso_hom_comp_snd (yoneda.map g) φ (op W'.unop.left))
    have h₂ := congrArg (fun k => k s.1)
      (pullbackObjIso_hom_comp_snd (yoneda.map g) φ (op W.unop.left))
    calc
      (pullback.snd ((yoneda.map g).app (op W'.unop.left))
          (φ.app (op W'.unop.left)))
          ((pullbackObjIso (yoneda.map g) φ (op W'.unop.left)).hom
            ((pullback (yoneda.map g) φ).map h.unop.left.op s.1)) =
        (pullback.snd (yoneda.map g) φ).app (op W'.unop.left)
          ((pullback (yoneda.map g) φ).map h.unop.left.op s.1) := h₁
      _ = F.map h.unop.left.op
          ((pullback.snd (yoneda.map g) φ).app (op W.unop.left)
            s.1) :=
            NatTrans.naturality_apply (pullback.snd (yoneda.map g) φ)
              h.unop.left.op s.1
      _ = F.map h.unop.left.op
          ((pullback.snd ((yoneda.map g).app (op W.unop.left))
            (φ.app (op W.unop.left)))
            ((pullbackObjIso (yoneda.map g) φ (op W.unop.left)).hom s.1)) :=
              congrArg (F.map h.unop.left.op) h₂.symm

private noncomputable def spacesExplicitPullback
    {V : BigFppfOver B S hS}
    (A : SpacesObj B S hS) (g : V ⟶ A.right) : SpacesObj B S hS :=
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback (yoneda.map g) A.hom,
      isAlgebraicSpace_pullback B S hS (yoneda.map g) A.hom
        (isAlgebraicSpace_yoneda B S hS V) A.left.property
        (isAlgebraicSpace_yoneda B S hS A.right)⟩
  let p₁ : P ⟶ schemeSpace V :=
    ObjectProperty.homMk (pullback.fst (yoneda.map g) A.hom)
  ⟨P, V, p₁.hom⟩

private noncomputable def spacesExplicitPullbackMap
    {V : BigFppfOver B S hS}
    (A : SpacesObj B S hS) (g : V ⟶ A.right) :
    spacesExplicitPullback B S hS A g ⟶ A := by
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback (yoneda.map g) A.hom,
      isAlgebraicSpace_pullback B S hS (yoneda.map g) A.hom
        (isAlgebraicSpace_yoneda B S hS V) A.left.property
        (isAlgebraicSpace_yoneda B S hS A.right)⟩
  let p₂ : P ⟶ A.left :=
    ObjectProperty.homMk (pullback.snd (yoneda.map g) A.hom)
  refine ⟨p₂, g, ?_⟩
  change pullback.snd (yoneda.map g) A.hom ≫ A.hom =
    pullback.fst (yoneda.map g) A.hom ≫ yoneda.map g
  exact pullback.condition.symm

private theorem spacesExplicitPullbackMap_isStronglyCartesian
    {V : BigFppfOver B S hS}
    (A : SpacesObj B S hS) (g : V ⟶ A.right) :
    (spacesProjection B S hS).IsStronglyCartesian g
      (spacesExplicitPullbackMap B S hS A g) := by
  let D := spacesExplicitPullback B S hS A g
  let m := spacesExplicitPullbackMap B S hS A g
  change (spacesProjection B S hS).IsStronglyCartesian m.right m
  rw [spacesProjection_isStronglyCartesian_iff m]
  let c := pullback.lift D.hom m.left.hom m.w.symm
  have hc : c = 𝟙 D.left.obj := by
    apply pullback.hom_ext
    · simp [m, c, D, spacesExplicitPullback, spacesExplicitPullbackMap]
    · simp [m, c, D, spacesExplicitPullbackMap, spacesExplicitPullback]
  have hc' : ObjectProperty.homMk c = 𝟙 D.left := ObjectProperty.hom_ext _ hc
  change IsIso (ObjectProperty.homMk c : D.left ⟶ D.left)
  rw [hc']
  infer_instance

private noncomputable def spacesChosenPullbackIso
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (g : V ⟶ U) :
    Functor.pullbackFiber (spacesProjection B S hS) X g ≅
      ⟨spacesExplicitPullback B S hS X.1 (g ≫ eqToHom X.2.symm), by
        simp [spacesExplicitPullback, spacesProjection]⟩ := by
  rcases X with ⟨X0, rfl⟩
  change Functor.pullbackFiber (spacesProjection B S hS) ⟨X0, rfl⟩ g ≅
    ⟨spacesExplicitPullback B S hS X0 g, by
      simp [spacesExplicitPullback, spacesProjection]⟩
  let p := spacesProjection B S hS
  let φ := Functor.IsPreFibered.pullbackMap rfl g
  let ψ := spacesExplicitPullbackMap B S hS X0 g
  have hφ : p.IsCartesian g φ := Functor.IsPreFibered.pullbackMap.IsCartesian rfl g
  have hψ : p.IsCartesian g ψ :=
    letI : p.IsStronglyCartesian g ψ :=
      spacesExplicitPullbackMap_isStronglyCartesian B S hS X0 g
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p g ψ
  exact Functor.fiberIsoOfCartesian g φ ψ hφ hψ

private noncomputable def spacesFiberPresheafFunctor
    (V : BigFppfOver B S hS) :
    (spacesProjection B S hS).Fiber V ⥤ (Over V)ᵒᵖ ⥤ Type u :=
  spacesFiberOverFunctor B S hS V ⋙ OverShriek.fiberFunctor (𝟙 (yoneda.obj V))

-- The presheaf equivalence and its counit require deeper reduction here.
private lemma spacesFiberHomEquiv_eq_map
    {V : BigFppfOver B S hS}
    {X Y : (spacesProjection B S hS).Fiber V} (m : X ⟶ Y) :
    spacesFiberHomEquiv B S hS X Y m =
      (spacesFiberPresheafFunctor B S hS V).map m := by
  let E := OverShriek.presheafEquivalence (U := V)
  let FF := E.fullyFaithfulFunctor
  let A := spacesFiberOver B S hS X
  let A' := spacesFiberOver B S hS Y
  let c := OverShriek.presheafCounitIso (U := V)
  let φ := spacesFiberOverHom B S hS m
  have hn : OverShriek.presheafFunctorToOver.map
        ((OverShriek.fiberFunctor (𝟙 (yoneda.obj V))).map φ) ≫ c.hom.app A' =
      c.hom.app A ≫ φ := by
    simpa only [Functor.comp_map, Functor.id_map, A, A'] using
      c.hom.naturality φ
  have hn' : OverShriek.presheafFunctorToOver.map ((OverShriek.fiberFunctor
        (𝟙 (yoneda.obj V))).map φ) ≫ (c.app A').hom = (c.app A).hom ≫ φ := hn
  have hleft :
      OverShriek.presheafFunctorToOver.map (spacesFiberHomEquiv B S hS X Y m) =
        (Iso.homCongr (c.app A) (c.app A')).symm φ := by
    change OverShriek.presheafFunctorToOver.map
        (FF.preimage ((Iso.homCongr (c.app A) (c.app A')).symm φ)) = _
    exact FF.map_preimage _
  have hright :
      OverShriek.presheafFunctorToOver.map
          ((OverShriek.fiberFunctor (𝟙 (yoneda.obj V))).map φ) =
        (Iso.homCongr (c.app A) (c.app A')).symm φ := by
    apply (cancel_mono (c.app A').hom).1
    calc
      OverShriek.presheafFunctorToOver.map
          ((OverShriek.fiberFunctor (𝟙 (yoneda.obj V))).map φ) ≫
          (c.app A').hom = (c.app A).hom ≫ φ := hn'
      _ = ((Iso.homCongr (c.app A) (c.app A')).symm φ) ≫ (c.app A').hom := by
            simp [Iso.homCongr, Category.assoc]
  exact FF.map_injective (hleft.trans hright.symm)

private lemma spacesFiberHomEquiv_apply_val
    {V : BigFppfOver B S hS}
    {X Y : (spacesProjection B S hS).Fiber V} (m : X ⟶ Y)
    (T : Over V) (s : (spacesFiberPresheaf B S hS X).obj (op T)) :
    ((spacesFiberHomEquiv B S hS X Y m).app (op T) s).1 =
      m.1.left.hom.app (op T.left) s.1 := by
  rw [spacesFiberHomEquiv_eq_map]
  rfl


private noncomputable def spacesChosenPullbackPresheafIso
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (g : V ⟶ U) :
    spacesFiberPresheaf B S hS
        (Functor.pullbackFiber (spacesProjection B S hS) X g) ≅
      (Over.map g).op ⋙ spacesFiberPresheaf B S hS X := by
  classical
  rcases X with ⟨X0, rfl⟩
  let e := spacesChosenPullbackIso (B := B) (S := S) (hS := hS) ⟨X0, rfl⟩ g
  have e' := (spacesFiberPresheafFunctor B S hS V).mapIso e
  dsimp [spacesFiberPresheafFunctor, spacesFiberOverFunctor, spacesFiberOver,
    spacesFiberPresheaf, OverShriek.fiberFunctor] at e'
  exact e' ≪≫ presheafFiberPullbackIso B S hS g X0.hom

private lemma spacesChosenPullbackPresheafIso_apply_val
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U)
    (T : Over V)
    (s : (spacesFiberPresheaf B S hS
      (Functor.pullbackFiber (spacesProjection B S hS) X f)).obj (op T)) :
    ((spacesChosenPullbackPresheafIso B S hS X f).hom.app (op T) s).1 =
      (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T.left) s.1 := by
  rcases X with ⟨X0, rfl⟩
  let p := spacesProjection B S hS
  let φ := Functor.IsPreFibered.pullbackMap (p := spacesProjection B S hS) rfl f
  let ψ := spacesExplicitPullbackMap B S hS X0 f
  let e := spacesChosenPullbackIso B S hS ⟨X0, rfl⟩ f
  have hφ : p.IsCartesian f φ := by
    dsimp [φ, p]
    exact Functor.IsPreFibered.pullbackMap.IsCartesian rfl f
  have hψ : p.IsCartesian f ψ := by
    have : p.IsStronglyCartesian f ψ := by
      dsimp [p, ψ]
      exact spacesExplicitPullbackMap_isStronglyCartesian B S hS X0 f
    exact Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian p f ψ
  have hfac : e.hom.1.left.hom ≫ ψ.left.hom = φ.left.hom := by
    have hh := Functor.fiberIsoOfCartesian_hom_fac (p := p) (b := f) (a := X0)
      (z := Functor.pullbackFiber p ⟨X0, rfl⟩ f)
      (z' := ⟨spacesExplicitPullback B S hS X0 f, by
        rfl⟩) φ ψ hφ hψ
    exact congrArg (fun k => k.left.hom) hh
  have hfacApp := congrArg (fun k => k.app (op T.left) s.1) hfac
  change pullback.snd ((yoneda.map f).app (op T.left)) (X0.hom.app (op T.left))
      ((pullbackObjIso (yoneda.map f) X0.hom (op T.left)).hom
        ((spacesFiberOverHom B S hS e.hom).left.app (op T.left) s.1)) =
    (Functor.IsPreFibered.pullbackMap rfl f).left.hom.app (op T.left) s.1
  calc
    _ = (pullback.snd (yoneda.map f) X0.hom).app (op T.left)
          ((spacesFiberOverHom B S hS e.hom).left.app (op T.left) s.1) := by
      simpa [spacesFiberOverHom] using
        congrArg (fun k => k ((spacesFiberOverHom B S hS e.hom).left.app
          (op T.left) s.1))
          (pullbackObjIso_hom_comp_snd (yoneda.map f) X0.hom (op T.left))
    _ = (Functor.IsPreFibered.pullbackMap rfl f).left.hom.app (op T.left) s.1 := by
      have hleft : (spacesFiberOverHom B S hS e.hom).left.app (op T.left) =
          e.hom.1.left.hom.app (op T.left) := rfl
      have hψapp : ψ.left.hom.app (op T.left) =
          (pullback.snd (yoneda.map f) X0.hom).app (op T.left) := rfl
      rw [hleft]
      simp only [NatTrans.comp_app] at hfacApp
      rw [hψapp] at hfacApp
      exact hfacApp

private lemma spacesChosenPullbackPresheafIso_inv_apply_val
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U)
    (T : Over V)
    (s : ((Over.map f).op ⋙ spacesFiberPresheaf B S hS X).obj (op T)) :
    (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T.left)
        (((spacesChosenPullbackPresheafIso B S hS X f).inv.app (op T)) s).1 =
      s.1 := by
  calc
    _ = ((spacesChosenPullbackPresheafIso B S hS X f).hom.app (op T)
        ((spacesChosenPullbackPresheafIso B S hS X f).inv.app (op T) s)).1 := by
          symm
          exact spacesChosenPullbackPresheafIso_apply_val B S hS X f T
            ((spacesChosenPullbackPresheafIso B S hS X f).inv.app (op T) s)
    _ = s.1 := by
          have hh := congrArg (fun k => k s)
            ((spacesChosenPullbackPresheafIso B S hS X f).inv_hom_id_app (op T))
          exact congrArg Subtype.val hh

private lemma spacesChosenPullbackPresheafIso_natural
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    {X Y : (spacesProjection B S hS).Fiber U} (m : X ⟶ Y)
    (f : V ⟶ U) :
    (spacesFiberPresheafFunctor B S hS V).map
        (Functor.pullbackFiberHom m f) ≫
      (spacesChosenPullbackPresheafIso B S hS Y f).hom =
    (spacesChosenPullbackPresheafIso B S hS X f).hom ≫
      Functor.whiskerLeft (Over.map f).op
        ((spacesFiberPresheafFunctor B S hS U).map m) := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((spacesChosenPullbackPresheafIso B S hS Y f).hom.app T
      (((spacesFiberPresheafFunctor B S hS V).map
        (Functor.pullbackFiberHom m f)).app T s)).1 = _
  rw [spacesChosenPullbackPresheafIso_apply_val B S hS Y f T.unop
    (((spacesFiberPresheafFunctor B S hS V).map
      (Functor.pullbackFiberHom m f)).app T s)]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, CategoryTheory.comp_apply]
  have hX : ((spacesChosenPullbackPresheafIso B S hS X f).hom.app T s).1 =
      (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T.unop.left) s.1 := by
    simpa using spacesChosenPullbackPresheafIso_apply_val
      (B := B) (S := S) (hS := hS) (X := X) (f := f) (T := T.unop) s
  have hfac := congrArg (fun k => k.left.hom)
    (Functor.pullbackFiberHom_fac m f)
  have hfac' := congrArg (fun k => k.app (op T.unop.left) s.1) hfac
  have hfac'' :
      (Functor.IsPreFibered.pullbackMap Y.2 f).left.hom.app (op T.unop.left)
          ((Functor.IsCartesian.map (spacesProjection B S hS) f
              (Functor.IsPreFibered.pullbackMap Y.2 f)
              (Functor.IsPreFibered.pullbackMap X.2 f ≫
                Functor.Fiber.fiberInclusion.map m)).left.hom.app
            (op T.unop.left) s.1) =
        (Functor.Fiber.fiberInclusion.map m).left.hom.app (op T.unop.left)
          ((Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app
            (op T.unop.left) s.1) := by
    convert hfac' using 1 <;> rfl
  change (Functor.IsPreFibered.pullbackMap Y.2 f).left.hom.app (op T.unop.left)
      (((Functor.IsCartesian.map (spacesProjection B S hS) f
          (Functor.IsPreFibered.pullbackMap Y.2 f)
          (Functor.IsPreFibered.pullbackMap X.2 f ≫
            Functor.Fiber.fiberInclusion.map m)).left.hom.app
        (op T.unop.left) s.1)) =
    (Functor.Fiber.fiberInclusion.map m).left.hom.app (op T.unop.left)
      ((spacesChosenPullbackPresheafIso B S hS X f).hom.app T s).1
  rw [hX]
  exact hfac''


private def spacesOverMapCompNamed
    {U V W : BigFppfOver B S hS}
    (f : V ⟶ U) (g : W ⟶ V) (b : W ⟶ U) (h : g ≫ f = b) :
    (Over.map g).op ⋙ (Over.map f).op ≅ (Over.map b).op :=
  NatIso.ofComponents
    (fun T => by
      let A : Over U := (Over.map f).obj ((Over.map g).obj T.unop)
      let C : Over U := (Over.map b).obj T.unop
      change op A ≅ op C
      have hAC : A ≅ C := by
        refine Over.isoMk (Iso.refl A.left) ?_
        change T.unop.hom ≫ b = (T.unop.hom ≫ g) ≫ f
        rw [← h, Category.assoc]
      exact hAC.symm.op)
    (by
      intro T T' q
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      rfl)

private lemma spacesChosenPullbackPresheafIso_comp_named
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V W : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (f : V ⟶ U) (g : W ⟶ V)
    (b : W ⟶ U) (h : g ≫ f = b) :
    (spacesChosenPullbackPresheafIso B S hS
      (Functor.pullbackFiber (spacesProjection B S hS) X f) g).hom ≫
        (Functor.isoWhiskerLeft (Over.map g).op
          (spacesChosenPullbackPresheafIso B S hS X f)).hom =
      (spacesFiberPresheafFunctor B S hS W).map
          (Functor.pullbackFiberCompIso' X f g b h).hom ≫
    (spacesChosenPullbackPresheafIso B S hS X b).hom ≫
      (Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
        (spacesFiberPresheaf B S hS X)).hom := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  let T' := (Over.map g).obj T.unop
  let e₁ := spacesChosenPullbackPresheafIso B S hS
    (Functor.pullbackFiber (spacesProjection B S hS) X f) g
  let e₂ := spacesChosenPullbackPresheafIso B S hS X f
  let e₃ := spacesChosenPullbackPresheafIso B S hS X b
  let c := Functor.pullbackFiberCompIso' X f g b h
  let u := e₁.hom.app T s
  let z := (spacesFiberPresheafFunctor B S hS W).map c.hom |>.app T s
  let ag := (Functor.IsPreFibered.pullbackMap
    (Functor.pullbackFiber (spacesProjection B S hS) X f).2 g).left.hom.app
      (op T.unop.left)
  let af := (Functor.IsPreFibered.pullbackMap X.2 f).left.hom.app (op T'.left)
  let ac := (Functor.Fiber.fiberInclusion.map c.hom).left.hom.app (op T.unop.left)
  let agf := (Functor.IsPreFibered.pullbackMap X.2 b).left.hom.app (op T.unop.left)
  have hu : u.1 = ag s.1 := by
    simpa [u, e₁, ag] using
      spacesChosenPullbackPresheafIso_apply_val B S hS
        (Functor.pullbackFiber (spacesProjection B S hS) X f) g T.unop s
  have hv : (e₂.hom.app (op T') u).1 = af u.1 := by
    simpa [e₂, af] using
      spacesChosenPullbackPresheafIso_apply_val B S hS X f T' u
  have hz : z.1 = ac s.1 := by
    change ((OverShriek.fiberMap (𝟙 (yoneda.obj W))
      (spacesFiberOverHom B S hS c.hom)).app T s).1 = ac s.1
    rfl
  have hw : (e₃.hom.app T z).1 = agf z.1 := by
    simpa [e₃, agf] using spacesChosenPullbackPresheafIso_apply_val B S hS X b T.unop z
  have hd : ((Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
      (spacesFiberPresheaf B S hS X)).hom.app T (e₃.hom.app T z)).1 =
      (e₃.hom.app T z).1 := by
    cases h
    simp [spacesOverMapCompNamed, spacesFiberPresheaf, OverShriek.fiber, Over.isoMk]
  have hcomp := congrArg (fun k => k.left.hom.app (op T.unop.left) s.1)
    (Functor.pullbackFiberCompIso'_hom_fac X f g b h)
  have hcomp' : af (ag s.1) = agf (ac s.1) := by
    have hh := hcomp.symm
    simp only [Comma.comp_left,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      CategoryTheory.comp_apply] at hh
    change af (ag s.1) = agf (ac s.1) at hh
    exact hh
  change (e₂.hom.app (op T') u).1 =
    ((Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
      (spacesFiberPresheaf B S hS X)).hom.app T (e₃.hom.app T z)).1
  calc
    (e₂.hom.app (op T') u).1 = af u.1 := hv
    _ = af (ag s.1) := by rw [hu]
    _ = agf (ac s.1) := hcomp'
    _ = agf z.1 := by rw [hz]
    _ = (e₃.hom.app T z).1 := hw.symm
    _ = ((Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
      (spacesFiberPresheaf B S hS X)).hom.app T (e₃.hom.app T z)).1 := hd.symm

private lemma spacesChosenPullbackHom_comp_named
    [hFib : (spacesProjection B S hS).IsFibered]
    {U V W : BigFppfOver B S hS}
    {X Y : (spacesProjection B S hS).Fiber U}
    (f : V ⟶ U)
    (m : (Functor.pullbackFiber (spacesProjection B S hS) X f) ⟶
      (Functor.pullbackFiber (spacesProjection B S hS) Y f))
    (g : W ⟶ V) (b : W ⟶ U)
    (h : g ≫ f = b) :
    let cX := Functor.pullbackFiberCompIso' X f g b h
    let cY := Functor.pullbackFiberCompIso' Y f g b h
    let eXf := spacesChosenPullbackPresheafIso B S hS X f
    let eYf := spacesChosenPullbackPresheafIso B S hS Y f
    let eXb := spacesChosenPullbackPresheafIso B S hS X b
    let eYb := spacesChosenPullbackPresheafIso B S hS Y b
    let m₂ := cX.inv ≫ Functor.pullbackFiberHom m g ≫ cY.hom
    (Iso.homCongr eXb eYb (spacesFiberHomEquiv B S hS
      (Functor.pullbackFiber (spacesProjection B S hS) X b)
      (Functor.pullbackFiber (spacesProjection B S hS) Y b) m₂)) ≫
      (Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
        (spacesFiberPresheaf B S hS Y)).hom =
    (Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
      (spacesFiberPresheaf B S hS X)).hom ≫
      Functor.whiskerLeft (Over.map g).op
        (Iso.homCongr eXf eYf
          (spacesFiberHomEquiv B S hS
            (Functor.pullbackFiber (spacesProjection B S hS) X f)
            (Functor.pullbackFiber (spacesProjection B S hS) Y f)
            m)) := by
  let cX := Functor.pullbackFiberCompIso' X f g b h
  let cY := Functor.pullbackFiberCompIso' Y f g b h
  let eXf := spacesChosenPullbackPresheafIso B S hS X f
  let eYf := spacesChosenPullbackPresheafIso B S hS Y f
  let eXb := spacesChosenPullbackPresheafIso B S hS X b
  let eYb := spacesChosenPullbackPresheafIso B S hS Y b
  let DX := spacesChosenPullbackPresheafIso B S hS
    (Functor.pullbackFiber (spacesProjection B S hS) X f) g
  let DY := spacesChosenPullbackPresheafIso B S hS
    (Functor.pullbackFiber (spacesProjection B S hS) Y f) g
  let SX := Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
    (spacesFiberPresheaf B S hS X)
  let SY := Functor.isoWhiskerRight (spacesOverMapCompNamed B S hS f g b h).symm
    (spacesFiberPresheaf B S hS Y)
  let G := (Over.map g).op
  let iX := DX ≪≫ Functor.isoWhiskerLeft G eXf
  let jX := (spacesFiberPresheafFunctor B S hS W).mapIso cX ≪≫ eXb ≪≫ SX
  let m₂ := cX.inv ≫ Functor.pullbackFiberHom m g ≫ cY.hom
  have hcompX := spacesChosenPullbackPresheafIso_comp_named B S hS X f g b h
  have hcompY := spacesChosenPullbackPresheafIso_comp_named B S hS Y f g b h
  have hnat := spacesChosenPullbackPresheafIso_natural B S hS m g
  have hcompX' : iX.hom = jX.hom := by
    simpa [iX, jX, DX, eXf, eXb, SX, G] using hcompX
  have hcompXinv : iX.inv = jX.inv := (Iso.inv_eq_inv iX jX).2 hcompX'
  have hXmove' : SX.inv ≫ eXb.inv ≫
      (spacesFiberPresheafFunctor B S hS W).map cX.inv =
        G.whiskerLeft eXf.inv ≫ DX.inv := by
    simpa [iX, jX, DX, eXf, eXb, SX, G] using hcompXinv.symm
  have hXmove : eXb.inv ≫ (spacesFiberPresheafFunctor B S hS W).map cX.inv =
      SX.hom ≫ Functor.whiskerLeft G eXf.inv ≫ DX.inv := by
    calc
      eXb.inv ≫ (spacesFiberPresheafFunctor B S hS W).map cX.inv =
          SX.hom ≫ SX.inv ≫ eXb.inv ≫
            (spacesFiberPresheafFunctor B S hS W).map cX.inv := by simp
      _ = SX.hom ≫ Functor.whiskerLeft G eXf.inv ≫ DX.inv := by
          rw [hXmove']
  have hnat' : (spacesFiberPresheafFunctor B S hS W).map
        (Functor.pullbackFiberHom m g) ≫ DY.hom =
      DX.hom ≫ Functor.whiskerLeft G
        ((spacesFiberPresheafFunctor B S hS V).map m) := by
    simpa [DX, DY, G] using hnat
  have hnat'' : DX.inv ≫
      (spacesFiberPresheafFunctor B S hS W).map (Functor.pullbackFiberHom m g) ≫ DY.hom =
      Functor.whiskerLeft G ((spacesFiberPresheafFunctor B S hS V).map m) := by
    calc
      DX.inv ≫ (spacesFiberPresheafFunctor B S hS W).map
          (Functor.pullbackFiberHom m g) ≫ DY.hom =
          DX.inv ≫ ((spacesFiberPresheafFunctor B S hS W).map
            (Functor.pullbackFiberHom m g) ≫ DY.hom) := by simp
      _ = DX.inv ≫ (DX.hom ≫ Functor.whiskerLeft G
            ((spacesFiberPresheafFunctor B S hS V).map m)) := by rw [hnat']
      _ = Functor.whiskerLeft G
            ((spacesFiberPresheafFunctor B S hS V).map m) := by simp
  have hnatComp :
      (SX.hom ≫ Functor.whiskerLeft G eXf.inv ≫ DX.inv) ≫
        (spacesFiberPresheafFunctor B S hS W).map (Functor.pullbackFiberHom m g) ≫
        (DY.hom ≫ Functor.whiskerLeft G eYf.hom) =
      SX.hom ≫ Functor.whiskerLeft G
        (eXf.inv ≫ (spacesFiberPresheafFunctor B S hS V).map m ≫ eYf.hom) := by
    calc
      _ = SX.hom ≫ Functor.whiskerLeft G eXf.inv ≫
          (DX.inv ≫ (spacesFiberPresheafFunctor B S hS W).map
            (Functor.pullbackFiberHom m g) ≫ DY.hom) ≫
          Functor.whiskerLeft G eYf.hom := by simp [Category.assoc]
      _ = SX.hom ≫ Functor.whiskerLeft G eXf.inv ≫
          Functor.whiskerLeft G ((spacesFiberPresheafFunctor B S hS V).map m) ≫
          Functor.whiskerLeft G eYf.hom := by rw [hnat'']
      _ = SX.hom ≫ Functor.whiskerLeft G
          (eXf.inv ≫ (spacesFiberPresheafFunctor B S hS V).map m ≫ eYf.hom) := by
            simp [← Functor.whiskerLeft_comp]
  have hcompY' : (spacesFiberPresheafFunctor B S hS W).map cY.hom ≫ eYb.hom ≫ SY.hom =
      DY.hom ≫ Functor.whiskerLeft G eYf.hom := by
    simpa [SY, DY, eYf, eYb] using hcompY.symm
  dsimp [Iso.homCongr]
  rw [spacesFiberHomEquiv_eq_map]
  calc
    eXb.inv ≫ (spacesFiberPresheafFunctor B S hS W).map m₂ ≫ eYb.hom ≫ SY.hom =
        (eXb.inv ≫ (spacesFiberPresheafFunctor B S hS W).map cX.inv) ≫
          (spacesFiberPresheafFunctor B S hS W).map (Functor.pullbackFiberHom m g) ≫
          ((spacesFiberPresheafFunctor B S hS W).map cY.hom ≫ eYb.hom ≫ SY.hom) := by
            simp [m₂, Functor.map_comp, Category.assoc]
    _ = (SX.hom ≫ Functor.whiskerLeft G eXf.inv ≫ DX.inv) ≫
          (spacesFiberPresheafFunctor B S hS W).map (Functor.pullbackFiberHom m g) ≫
          (DY.hom ≫ Functor.whiskerLeft G eYf.hom) := by rw [hXmove, hcompY']
    _ = SX.hom ≫ Functor.whiskerLeft G
          (eXf.inv ≫ (spacesFiberPresheafFunctor B S hS V).map m ≫ eYf.hom) := hnatComp
    _ = SX.hom ≫ Functor.whiskerLeft G
          (Iso.homCongr eXf eYf (spacesFiberHomEquiv B S hS
            (Functor.pullbackFiber (spacesProjection B S hS) X f)
            (Functor.pullbackFiber (spacesProjection B S hS) Y f)
            m)) := by
      simp [Iso.homCongr, spacesFiberHomEquiv_eq_map]

universe v w

private lemma app_eq_conj {D : Type v} [Category.{w} D]
    {P Q : Dᵒᵖ ⥤ Type u} (α : P ⟶ Q) {W₁ W₂ : D} (e : W₁ ≅ W₂)
    {x : P.obj (op W₁) ⟶ P.obj (op W₂)} {y : Q.obj (op W₂) ⟶ Q.obj (op W₁)}
    (hx : x = P.map e.inv.op) (hy : y = Q.map e.hom.op) :
    α.app (op W₁) = x ≫ α.app (op W₂) ≫ y := by
  subst hx hy
  exact (NatTrans.naturality_1 α e.op).symm

private def iteratedSliceBackwardMapIso {U : BigFppfOver B S hS}
    {T T' : Over U} (q : T' ⟶ T) (V : Over T'.left) :
    (Over.map q).obj ((Over.iteratedSliceBackward T').obj V) ≅
      (Over.iteratedSliceBackward T).obj ((Over.map q.left).obj V) :=
  show
    (Over.mk ((Over.homMk V.hom :
      (Over.mk (V.hom ≫ T'.hom) : Over U) ⟶ T') ≫ q) : Over T) ≅
      Over.mk (Over.homMk (V.hom ≫ q.left) :
        (Over.mk ((V.hom ≫ q.left) ≫ T.hom) : Over U) ⟶ T)
    from Over.isoMk
      (show (Over.mk (V.hom ≫ T'.hom) : Over U) ≅
          Over.mk ((V.hom ≫ q.left) ≫ T.hom) from
        Over.isoMk (Iso.refl V.left) (by simp))
      (by ext; simp)

private noncomputable def spacesHomEquivIteratedSlice
    {U : BigFppfOver B S hS}
    (M N : (Over U)ᵒᵖ ⥤ Type u) (T : Over U) :
    ((Over.forget T).op ⋙ M ⟶ (Over.forget T).op ⋙ N) ≃
      ((Over.map T.hom).op ⋙ M ⟶ (Over.map T.hom).op ⋙ N) := by
  haveI : (Over.iteratedSliceBackward T).IsEquivalence :=
    (Over.iteratedSliceEquiv T).isEquivalence_inverse
  let W := (Functor.whiskeringLeft (Over T.left)ᵒᵖ (Over T)ᵒᵖ (Type u)).obj
    (Over.iteratedSliceBackward T).op
  let FF := Functor.FullyFaithful.ofFullyFaithful W
  have hfun : (Over.iteratedSliceBackward T).op ⋙ (Over.forget T).op =
      (Over.map T.hom).op := congrArg (fun F => F.op)
        (Over.iteratedSliceBackward_forget T)
  simpa [W, ← Functor.assoc, hfun] using
    FF.homEquiv (X := (Over.forget T).op ⋙ M) (Y := (Over.forget T).op ⋙ N)

private lemma spacesHomEquivIteratedSlice_app
    {U : BigFppfOver B S hS}
    {M N : (Over U)ᵒᵖ ⥤ Type u} (T : Over U)
    (α : (Over.map T.hom).op ⋙ M ⟶ (Over.map T.hom).op ⋙ N)
    (W' : (Over T.left)ᵒᵖ) :
    ((spacesHomEquivIteratedSlice B S hS M N T).symm α).app
        ((Over.iteratedSliceBackward T).op.obj W') =
      α.app W' := by
  classical
  have : (Over.iteratedSliceBackward T).IsEquivalence :=
    (Over.iteratedSliceEquiv T).isEquivalence_inverse
  let W := (Functor.whiskeringLeft (Over T.left)ᵒᵖ (Over T)ᵒᵖ (Type u)).obj
    (Over.iteratedSliceBackward T).op
  let FF := Functor.FullyFaithful.ofFullyFaithful W
  have hfun : (Over.iteratedSliceBackward T).op ⋙ (Over.forget T).op =
      (Over.map T.hom).op := congrArg (fun F => F.op)
        (Over.iteratedSliceBackward_forget T)
  have h := (spacesHomEquivIteratedSlice B S hS M N T).right_inv α
  have h' := congrArg (fun n => n.app W') h
  change ((spacesHomEquivIteratedSlice B S hS M N T).symm α).app
      ((Over.iteratedSliceBackward T).op.obj W') = α.app W' at h'
  exact h'

private lemma spacesHomEquivIteratedSlice_app_any
    {U : BigFppfOver B S hS}
    {M N : (Over U)ᵒᵖ ⥤ Type u} (T : Over U)
    (α : (Over.map T.hom).op ⋙ M ⟶ (Over.map T.hom).op ⋙ N)
    (A : (Over T)ᵒᵖ) :
    ((spacesHomEquivIteratedSlice B S hS M N T).symm α).app A =
      ((Over.forget T).op ⋙ M).map
          ((Over.iteratedSliceEquiv T).unitIso.app A.unop).inv.op ≫
        α.app ((Over.iteratedSliceForward T).op.obj A) ≫
      ((Over.forget T).op ⋙ N).map
          ((Over.iteratedSliceEquiv T).unitIso.app A.unop).hom.op := by
  let e := ((Over.iteratedSliceEquiv T).unitIso.app A.unop).symm
  let η := (spacesHomEquivIteratedSlice B S hS M N T).symm α
  let P := (Over.forget T).op ⋙ M
  let Q := (Over.forget T).op ⋙ N
  have h := app_eq_conj η e.symm (x := P.map e.hom.op) (y := Q.map e.inv.op) rfl rfl
  have hcan := spacesHomEquivIteratedSlice_app (B := B) (S := S) (hS := hS)
    (M := M) (N := N) T α
    ((Over.iteratedSliceForward T).op.obj A)
  have hcan' : η.app (op ((Over.iteratedSliceBackward T).obj
      ((Over.iteratedSliceForward T).obj A.unop))) =
      α.app ((Over.iteratedSliceForward T).op.obj A) := by
    simpa [Over.iteratedSliceBackward, Over.iteratedSliceForward,
      Over.iteratedSliceEquiv] using hcan
  rw [← hcan']
  simpa [e, P, Q, Over.iteratedSliceEquiv] using h

private theorem typeHom_comp_apply {A B C : Type u} (f : A ⟶ B) (g : B ⟶ C)
    (x : A) : (f ≫ g).hom' x = g.hom' (f.hom' x) := rfl

private noncomputable def spacesMorSectionEquiv
    [hFib : (spacesProjection B S hS).IsFibered]
    {U : BigFppfOver B S hS}
    (X Y : (spacesProjection B S hS).Fiber U) (T : Over U) :
    (Functor.morPresheaf (spacesProjection B S hS) X Y).obj (op T) ≃
      (presheafHom (spacesFiberPresheaf B S hS X) (spacesFiberPresheaf B S hS Y)).obj (op T) := by
  let X' := Functor.pullbackFiber (spacesProjection B S hS) X T.hom
  let Y' := Functor.pullbackFiber (spacesProjection B S hS) Y T.hom
  let eX := spacesChosenPullbackPresheafIso B S hS X T.hom
  let eY := spacesChosenPullbackPresheafIso B S hS Y T.hom
  change (X' ⟶ Y') ≃ _
  exact (spacesFiberHomEquiv B S hS X' Y').trans
    ((Iso.homCongr eX eY).trans
      (spacesHomEquivIteratedSlice B S hS (spacesFiberPresheaf B S hS X)
        (spacesFiberPresheaf B S hS Y) T).symm)

set_option maxHeartbeats 400000 in
-- The objects component of this natural isomorphism is checked against the expected type of
-- `NatIso.ofComponents`, which unfolds `Functor.morPresheaf`, `presheafHom` and
-- `OverShriek.fiber` down to the iterated-slice coherence maps; that one unification exceeds
-- the default budget. 250000 heartbeats fail and 300000 suffice, so this is the default
-- raised once with headroom, not an open-ended ceiling.
private noncomputable def spacesMorPresheafIso
    [hFib : (spacesProjection B S hS).IsFibered]
    {U : BigFppfOver B S hS}
    (X Y : (spacesProjection B S hS).Fiber U) :
    Functor.morPresheaf (spacesProjection B S hS) X Y ≅
      presheafHom (spacesFiberPresheaf B S hS X) (spacesFiberPresheaf B S hS Y) :=
  NatIso.ofComponents
    (fun T => (spacesMorSectionEquiv B S hS X Y T.unop).toIso)
    (by
      intro T₁ T₂ q
      ext m
      change spacesMorSectionEquiv B S hS X Y T₂.unop
          ((Functor.morPresheaf (spacesProjection B S hS) X Y).map q m) =
        (presheafHom (spacesFiberPresheaf B S hS X)
          (spacesFiberPresheaf B S hS Y)).map q
          (spacesMorSectionEquiv B S hS X Y T₁.unop m)
      rw [Functor.morPresheaf_map_apply, Functor.morRestrict_eq_pullbackFiberHom]
      let W := (Functor.whiskeringLeft (Over (unop T₂).left)ᵒᵖ
        (Over (unop T₂))ᵒᵖ (Type u)).obj
          (Over.iteratedSliceBackward (unop T₂)).op
      have : (Over.iteratedSliceBackward (unop T₂)).IsEquivalence :=
        (Over.iteratedSliceEquiv (unop T₂)).isEquivalence_inverse
      let FF := Functor.FullyFaithful.ofFullyFaithful W
      apply FF.map_injective
      apply NatTrans.ext
      funext W'
      apply ConcreteCategory.hom_ext
      intro s'
      simp only [W, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
      let T₂' := unop T₂
      let eX₂ := spacesChosenPullbackPresheafIso B S hS X T₂'.hom
      let eY₂ := spacesChosenPullbackPresheafIso B S hS Y T₂'.hom
      let cX := Functor.pullbackFiberCompIso' X (unop T₁).hom
        (Over.Hom.left q.unop) T₂'.hom (Over.w q.unop)
      let cY := Functor.pullbackFiberCompIso' Y (unop T₁).hom
        (Over.Hom.left q.unop) T₂'.hom (Over.w q.unop)
      let m₂ := cX.inv ≫ Functor.pullbackFiberHom m (Over.Hom.left q.unop) ≫ cY.hom
      let α₂ := (Iso.homCongr eX₂ eY₂)
        ((spacesFiberHomEquiv B S hS
          (Functor.pullbackFiber (spacesProjection B S hS) X T₂'.hom)
          (Functor.pullbackFiber (spacesProjection B S hS) Y T₂'.hom)) m₂)
      let f₁ := (unop T₁).hom
      let g₁ := Over.Hom.left q.unop
      let eX₁ := spacesChosenPullbackPresheafIso B S hS X f₁
      let eY₁ := spacesChosenPullbackPresheafIso B S hS Y f₁
      let α₁ := Iso.homCongr eX₁ eY₁
        (spacesFiberHomEquiv B S hS
          (Functor.pullbackFiber (spacesProjection B S hS) X f₁)
          (Functor.pullbackFiber (spacesProjection B S hS) Y f₁) m)
      let α := (spacesHomEquivIteratedSlice B S hS
        (spacesFiberPresheaf B S hS X) (spacesFiberPresheaf B S hS Y)
        (unop T₁)).symm
          (eX₁.inv ≫ spacesFiberHomEquiv B S hS
            (Functor.pullbackFiber (spacesProjection B S hS) X f₁)
            (Functor.pullbackFiber (spacesProjection B S hS) Y f₁) m ≫ eY₁.hom)
      have hAlpha : α = (spacesHomEquivIteratedSlice B S hS
          (spacesFiberPresheaf B S hS X) (spacesFiberPresheaf B S hS Y)
          (unop T₁)).symm
        ((spacesChosenPullbackPresheafIso B S hS X (unop T₁).hom).inv ≫
          spacesFiberHomEquiv B S hS
            (Functor.pullbackFiber (spacesProjection B S hS) X (unop T₁).hom)
            (Functor.pullbackFiber (spacesProjection B S hS) Y (unop T₁).hom) m ≫
          (spacesChosenPullbackPresheafIso B S hS Y (unop T₁).hom).hom) := rfl
      have hsec : spacesMorSectionEquiv B S hS X Y T₁.unop m = α := rfl
      let SX := Functor.isoWhiskerRight
        (spacesOverMapCompNamed B S hS f₁ g₁ T₂'.hom (Over.w q.unop)).symm
        (spacesFiberPresheaf B S hS X)
      let SY := Functor.isoWhiskerRight
        (spacesOverMapCompNamed B S hS f₁ g₁ T₂'.hom (Over.w q.unop)).symm
        (spacesFiberPresheaf B S hS Y)
      have hbridge := spacesChosenPullbackHom_comp_named (B := B) (S := S)
        (hS := hS) (X := X) (Y := Y) f₁ m g₁ T₂'.hom (Over.w q.unop)
      have hα₂ : α₂ ≫ SY.hom = SX.hom ≫
          Functor.whiskerLeft (Over.map g₁).op α₁ := by
        simpa [α₂, α₁, SX, SY, eX₂, eY₂, eX₁, eY₁, m₂, cX, cY] using hbridge
      change (((spacesHomEquivIteratedSlice B S hS (spacesFiberPresheaf B S hS X)
        (spacesFiberPresheaf B S hS Y) T₂').symm α₂).app
        ((Over.iteratedSliceBackward T₂').op.obj W')) s' = _
      rw [spacesHomEquivIteratedSlice_app (B := B) (S := S) (hS := hS)
        (M := spacesFiberPresheaf B S hS X) (N := spacesFiberPresheaf B S hS Y)
        (T := T₂')]
      have hApp := congrArg (fun η => η.app W' s') hα₂
      simp only [NatTrans.comp_app, CategoryTheory.comp_apply,
        Functor.whiskerLeft_app] at hApp
      have hAppVal := congrArg Subtype.val hApp
      have hround := congrArg (fun k => k (α₂.app W' s')) (SY.hom_inv_id_app W')
      calc
        α₂.app W' s' = SY.inv.app W' (SY.hom.app W' (α₂.app W' s')) := hround.symm
        _ = SY.inv.app W'
              ((Functor.whiskerLeft (Over.map g₁).op α₁).app W'
                (SX.hom.app W' s')) := by
          rw [hApp]
          simp only [Functor.whiskerLeft_app]
          rfl
        _ = _ := by
          apply Subtype.ext
          rw [hsec]
          have hpresheafHomApp :
              ((((presheafHom (spacesFiberPresheaf B S hS X)
                (spacesFiberPresheaf B S hS Y)).map q).hom' α).app
                  ((Over.iteratedSliceBackward (unop T₂)).op.obj W')).hom' s' =
                (α.app ((Over.map q.unop).op.obj
                  ((Over.iteratedSliceBackward (unop T₂)).op.obj W'))).hom' s' := by
            rfl
          have hpresheafAppVal := congrArg Subtype.val hpresheafHomApp
          let κ :=
            (Over.iteratedSliceEquiv (unop T₁)).functor.mapIso
              (iteratedSliceBackwardMapIso (B := B) (S := S) (hS := hS)
                q.unop W'.unop) ≪≫
            (Over.iteratedSliceEquiv (unop T₁)).counitIso.app
              ((Over.map g₁).obj (unop W'))
          let A := (Over.map q.unop).obj
            ((Over.iteratedSliceBackward T₂').obj W'.unop)
          let η := (Over.iteratedSliceEquiv (unop T₁)).unitIso.app A
          let ζ := ((spacesOverMapCompNamed B S hS f₁ g₁ T₂'.hom
            (Over.w q.unop)).app W').unop
          let ηU := (Over.forget (unop T₁)).mapIso η
          let δU := (Over.map f₁).mapIso κ
          have hζ : ηU.hom ≫ δU.hom = ζ.hom := by
            apply Over.OverMorphism.ext
            rfl
          have hIso : ηU ≪≫ δU = ζ := Iso.ext hζ
          have hζinv : δU.inv ≫ ηU.inv = ζ.inv := by
            have hh := congrArg Iso.inv hIso
            simpa only [Iso.trans_inv] using hh
          have hκ := α₁.naturality κ.hom.op
          have hκinv := α₁.naturality κ.inv.op
          have hκAt := congrArg (fun η => η (SX.hom.app W' s')) hκ
          have hκinvAt := congrArg (fun η => η (SX.hom.app W' s')) hκinv
          have hκAt' := hκAt
          simp [κ, SX, spacesOverMapCompNamed, iteratedSliceBackwardMapIso,
            Over.iteratedSliceBackward, Over.iteratedSliceForward,
            Over.iteratedSliceEquiv, Over.isoMk, Over.homMk,
            spacesFiberPresheaf, OverShriek.fiber,
            id_apply] at hκAt'
          change ((SY.inv.app W'
              ((Functor.whiskerLeft (Over.map g₁).op α₁).app W'
                (SX.hom.app W' s'))).val) =
            (((presheafHom (spacesFiberPresheaf B S hS X)
              (spacesFiberPresheaf B S hS Y)).map q α).app
                ((Over.iteratedSliceBackward (unop T₂)).op.obj W') s').val
          calc
            (SY.inv.app W'
                ((Functor.whiskerLeft (Over.map g₁).op α₁).app W'
                  (SX.hom.app W' s'))).val =
                ((α.app ((Over.map q.unop).op.obj
                  ((Over.iteratedSliceBackward (unop T₂)).op.obj W'))).hom' s').val := by
              rw [hAlpha]
              rw [spacesHomEquivIteratedSlice_app_any]
              simp only [Comma.snd_obj, ObjectProperty.ι_obj, Functor.op_obj, Over.map_obj_left,
                yoneda_obj_obj, NatTrans.comp_app, yoneda_map_app, types_comp_apply,
                TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, NatTrans.id_app, Over.map_obj_hom,
                types_id_apply, spacesFiberPresheaf, OverShriek.fiber, spacesOverMapCompNamed,
                Functor.comp_obj, Over.isoMk, Iso.op_symm, id_eq, Functor.isoWhiskerRight_inv,
                Iso.symm_inv, Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Iso.symm_hom,
                Iso.op_inv, Quiver.Hom.unop_op, CostructuredArrow.isoMk_inv_left, Iso.refl_inv,
                op_id, CategoryTheory.Functor.map_id, id_apply, TypeCat.ofHom_apply,
                Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, NatIso.ofComponents_inv_app,
                Iso.op_hom, CostructuredArrow.isoMk_hom_left, Iso.refl_hom,
                Over.iteratedSliceBackward, Over.homMk, Over.mk_left, Over.forget_obj, Over.mk_hom,
                Functor.id_obj, Over.iteratedSliceEquiv, Over.iteratedSliceForward,
                CostructuredArrow.homMk_left, Over.comp_left, NatIso.ofComponents.app,
                Functor.comp_map, Functor.op_map, Over.forget_map, Category.assoc, SY, SX]
              calc
                _ = _ := by
                  simpa [α₁, Iso.homCongr] using congrArg Subtype.val hκAt'.symm
                _ = _ := by
                  simp only [typeHom_comp_apply]
                  rfl
            _ = (((presheafHom (spacesFiberPresheaf B S hS X)
                (spacesFiberPresheaf B S hS Y)).map q α).app
                  ((Over.iteratedSliceBackward (unop T₂)).op.obj W') s').val :=
              hpresheafAppVal.symm
    )

/-- The projection from algebraic spaces over schemes is a fibred category. -/
@[stacks 04UA "condition (1)"]
theorem spacesProjection_isFibered :
    (spacesProjection B S hS).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro A V g
  exact ⟨_, _, spacesExplicitPullbackMap_isStronglyCartesian B S hS A g⟩

/-- Morphisms of algebraic spaces over a fixed scheme satisfy fppf descent. -/
@[stacks 04UA "condition (2)"]
theorem spacesProjection_isMorSheaf :
    haveI : (spacesProjection B S hS).IsFibered :=
      spacesProjection_isFibered B S hS
    ∀ (U : BigFppfOver B S hS)
      (X Y : (spacesProjection B S hS).Fiber U),
      (spacesProjection B S hS).IsMorSheaf
        (BigFppfOver.topology B S hS) U X Y := by
  intro U X Y
  let J := BigFppfOver.topology B S hS
  let FX : Sheaf (J.over U) (Type u) :=
    ⟨spacesFiberPresheaf B S hS X, spacesFiberPresheaf_isSheaf B S hS X⟩
  let FY : Sheaf (J.over U) (Type u) :=
    ⟨spacesFiberPresheaf B S hS Y, spacesFiberPresheaf_isSheaf B S hS Y⟩
  have hHom : Presheaf.IsSheaf (J.over U) (presheafHom FX.obj FY.obj) :=
    Presheaf.IsSheaf.hom FX.obj FY.obj FY.property
  unfold Functor.IsMorSheaf
  have : (spacesProjection B S hS).IsFibered :=
    spacesProjection_isFibered B S hS
  exact (Presheaf.isSheaf_of_iso_iff (spacesMorPresheafIso B S hS X Y)).2 hHom

end AlgebraicGeometry

end
