module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalCocycle
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Full faithfulness of pullback to a cofiltered limit, from the pinned form of Tag 01ZR (2)

Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact schemes with affine
transition morphisms.  Assume [Stacks Project, Tag 01ZR] (2) for `D` in the form the tag states
it — a morphism between the pullbacks to the limit of two finitely presented modules on a stage
is, after passing to a later stage, the base change of a morphism there *through the canonical
identification*.  This file deduces that two finitely presented modules on a stage whose
pullbacks to the limit are isomorphic are already isomorphic over some later stage.

That is the `hFullyFaithful` input of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit_of_descent`,
and **no reflection of isomorphisms is needed for it.**  The implementation notes of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/Invertible.lean` record that the route "descend the
isomorphism and its inverse separately and multiply" fails for the *existentially pinned* form
of Tag 01ZR (2), because two applications of fullness produce unrelated identifications of the
same object and the composite acquires an uncontrolled automorphism.  With the canonically pinned
form that obstruction disappears: the two identifications are then the same canonical one, the
composites of the two descended morphisms have the identity as their canonical base change, and
Tag 01ZR (3) makes them the identity over a later stage.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.HasCanonicalDescent`: [Stacks Project, Tag 01ZR] (2)
  for a diagram and a cone on it, in the canonically pinned form.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_of_hasCanonicalDescent`: an
  isomorphism between the pullbacks to the limit of two finitely presented modules on a stage is
  the base change of a morphism at a later stage which is *itself* an isomorphism after one
  further step.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_iso_of_hasCanonicalDescent`: the
  `hFullyFaithful` input, in the exact shape
  `exists_isInvertible_pullback_iso_of_isLimit_of_descent` takes it.
* `Stacks.AlgebraicGeometry.ModuleLimits.hasCanonicalDescent_upToIso`: the canonically pinned
  form implies the weaker up-to-an-arbitrary-identification form that
  `exists_isFinitePresentation_pullback_iso_of_upToIso_map` takes, so Tag 01ZR (1) in the general
  quasi-compact quasi-separated case follows from the same single input.

## Implementation notes

The cofiltered index category is used three times and each use is recorded here, because the
bookkeeping is the whole content of the argument.  First, the two stages produced by fullness for
`φ.hom` and for `φ.inv` are brought under one object and the two resulting morphisms to the
original stage are *equalised*, so that both descended morphisms are morphisms of pullbacks along
one and the same transition morphism; `CategoryTheory.IsCofilteredOrEmpty.cone_maps` is what does
that, and without it the two morphisms cannot even be composed.  Second, Tag 01ZR (3) is applied
to each of the two composites separately and the two stages it returns are brought under one
object.  Third, the two transition morphisms to the common stage obtained that way are equalised
again, because only then do both identities hold along a single morphism.

The transport of a descended morphism to a later stage is
`Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_stage_iff`, used in the direction
`mpr`; it takes the factorisation of the transition morphism as a hypothesis, so `D.map_comp` is
supplied directly and no isomorphism is transported by hand.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The pinned form of Tag 01ZR (2) as a property of a diagram and a cone -/

/-- **[Stacks Project, Tag 01ZR] (2)** for the diagram `D` and the cone `c`, in the form the tag
states it: a morphism between the pullbacks to `c.pt` of two finitely presented modules on a
stage is, after passing to a later stage, the base change of a morphism there through the
canonical identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom`. -/
def HasCanonicalDescent {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) : Prop :=
  ∀ (i : I) (F G : (D.obj i).Modules), F.IsFinitePresentation → G.IsFinitePresentation →
    ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G,
    ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
      (Scheme.Modules.pullback (D.map e)).obj G),
      IsCanonicalBaseChange (c.π.app j) (D.map e) (c.π.app i) (c.w e) φj φ

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The canonically pinned form of [Stacks Project, Tag 01ZR] (2) implies the form in which the
descended morphism is only required to agree with the given one through *some* pair of
isomorphisms, which is the `hmap` hypothesis of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_upToIso_map`.
The canonical identification is the pair of isomorphisms. -/
theorem hasCanonicalDescent_upToIso (hmap : HasCanonicalDescent D c) (i : I)
    (F G : (D.obj i).Modules) (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation)
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
      (Scheme.Modules.pullback (D.map e)).obj G)
      (iF : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj F) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj F)
      (iG : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj G) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ := by
  obtain ⟨j, e, φj, hφj⟩ := hmap i F G hF hG φ
  exact ⟨j, e, φj, canIso (c.π.app j) (D.map e) (c.π.app i) (c.w e) F,
    canIso (c.π.app j) (D.map e) (c.π.app i) (c.w e) G, hφj⟩

variable (hc : IsLimit c) [∀ i : I, CompactSpace (D.obj i)]

include hc in
/-- **The faithfulness step.**  Two morphisms of finitely presented modules at a stage with the
same canonical base change to the limit already have equal pullbacks over a later stage.  This
is `Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_eq_of_isCanonicalBaseChange` followed by
[Stacks Project, Tag 01ZR] (3). -/
theorem exists_pullback_map_eq_of_isCanonicalBaseChange {i j : I} (e : j ⟶ i)
    (F G : (D.obj i).Modules)
    (χ₁ χ₂ : (Scheme.Modules.pullback (D.map e)).obj F ⟶
      (Scheme.Modules.pullback (D.map e)).obj G)
    [((Scheme.Modules.pullback (D.map e)).obj F).IsFinitePresentation]
    [((Scheme.Modules.pullback (D.map e)).obj G).IsFinitePresentation]
    {φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G}
    (h₁ : IsCanonicalBaseChange (c.π.app j) (D.map e) (c.π.app i) (c.w e) χ₁ φ)
    (h₂ : IsCanonicalBaseChange (c.π.app j) (D.map e) (c.π.app i) (c.w e) χ₂ φ) :
    ∃ (k : I) (f : k ⟶ j), (Scheme.Modules.pullback (D.map f)).map χ₁ =
      (Scheme.Modules.pullback (D.map f)).map χ₂ :=
  exists_pullback_map_eq_of_isLimit' D c hc j _ _ χ₁ χ₂
    (pullback_map_eq_of_isCanonicalBaseChange _ _ _ _ h₁ h₂)

include hc in
/-- **Fullness and faithfulness together.**  An isomorphism between the pullbacks to the limit of
two finitely presented modules on a stage is, over some later stage, the canonical base change of
a morphism which is itself an isomorphism.

Both the morphism and its inverse are descended by the canonically pinned form of
[Stacks Project, Tag 01ZR] (2); because the identification is the *same* canonical one on both
sides, the two composites have the identity as their canonical base change, and
[Stacks Project, Tag 01ZR] (3) makes them the identity over a further stage. -/
theorem isIso_pullback_map_of_hasCanonicalDescent (hmap : HasCanonicalDescent D c) (i : I)
    (A B : (D.obj i).Modules) (hA : A.IsFinitePresentation) (hB : B.IsFinitePresentation)
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B) :
    ∃ (j : I) (e : j ⟶ i) (ψ : (Scheme.Modules.pullback (D.map e)).obj A ⟶
      (Scheme.Modules.pullback (D.map e)).obj B), IsIso ψ := by
  classical
  obtain ⟨j₁, e₁, χ₁, h₁⟩ := hmap i A B hA hB φ.hom
  obtain ⟨j₂, e₂, χ₂, h₂⟩ := hmap i B A hB hA φ.inv
  -- bring the two stages under one object and equalise the two morphisms down to `i`
  obtain ⟨k₀, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j₁ j₂
  obtain ⟨k, u, hu⟩ := IsCofilteredOrEmpty.cone_maps (a ≫ e₁) (b ≫ e₂)
  obtain ⟨e, he⟩ : ∃ e : k ⟶ i, e = u ≫ a ≫ e₁ := ⟨_, rfl⟩
  have hA' : ((Scheme.Modules.pullback (D.map e)).obj A).IsFinitePresentation :=
    @isFinitePresentation_pullback _ _ (D.map e) A hA
  have hB' : ((Scheme.Modules.pullback (D.map e)).obj B).IsFinitePresentation :=
    @isFinitePresentation_pullback _ _ (D.map e) B hB
  have hfac₁ : D.map (u ≫ a) ≫ D.map e₁ = D.map e := by
    rw [← D.map_comp, he, Category.assoc]
  have hfac₂ : D.map (u ≫ b) ≫ D.map e₂ = D.map e := by
    rw [← D.map_comp, he, Category.assoc, hu]
  -- the two descended morphisms, over one and the same transition morphism `D.map e`
  set ψ₁ := canConj (D.map (u ≫ a)) (D.map e₁) (D.map e) hfac₁
    ((Scheme.Modules.pullback (D.map (u ≫ a))).map χ₁) with hψ₁
  set ψ₂ := canConj (D.map (u ≫ b)) (D.map e₂) (D.map e) hfac₂
    ((Scheme.Modules.pullback (D.map (u ≫ b))).map χ₂) with hψ₂
  have hcan₁ : IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) ψ₁ φ.hom :=
    (isCanonicalBaseChange_stage_iff (c.π.app k) (D.map (u ≫ a)) (D.map e₁) (c.π.app j₁)
      (c.w (u ≫ a)) (D.map e) hfac₁ (c.π.app i) (c.w e₁) (c.w e) χ₁ φ.hom).mpr h₁
  have hcan₂ : IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) ψ₂ φ.inv :=
    (isCanonicalBaseChange_stage_iff (c.π.app k) (D.map (u ≫ b)) (D.map e₂) (c.π.app j₂)
      (c.w (u ≫ b)) (D.map e) hfac₂ (c.π.app i) (c.w e₂) (c.w e) χ₂ φ.inv).mpr h₂
  -- the two composites have the identity as their canonical base change
  have hid : ∀ (M N : (D.obj i).Modules)
      {α : (Scheme.Modules.pullback (D.map e)).obj M ⟶ (Scheme.Modules.pullback (D.map e)).obj N}
      {β : (Scheme.Modules.pullback (D.map e)).obj N ⟶ (Scheme.Modules.pullback (D.map e)).obj M}
      {s : (Scheme.Modules.pullback (c.π.app i)).obj M ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj N}
      {t : (Scheme.Modules.pullback (c.π.app i)).obj N ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj M},
      IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) α s →
      IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) β t → s ≫ t = 𝟙 _ →
      IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) (α ≫ β) (𝟙 _) := by
    intro M N α β s t ha hb hst
    refine (isCanonicalBaseChange_iff _ _ _ _ _ _).mpr ?_
    rw [CategoryTheory.Functor.map_comp, canConj_comp,
      (isCanonicalBaseChange_iff _ _ _ _ _ _).mp ha,
      (isCanonicalBaseChange_iff _ _ _ _ _ _).mp hb, hst]
  have hcomp₁ : IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) (ψ₁ ≫ ψ₂)
      (𝟙 _) := hid A B hcan₁ hcan₂ φ.hom_inv_id
  have hcomp₂ : IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e) (ψ₂ ≫ ψ₁)
      (𝟙 _) := hid B A hcan₂ hcan₁ φ.inv_hom_id
  have hone : ∀ M : (D.obj i).Modules,
      IsCanonicalBaseChange (c.π.app k) (D.map e) (c.π.app i) (c.w e)
        (𝟙 ((Scheme.Modules.pullback (D.map e)).obj M)) (𝟙 _) := by
    intro M
    refine (isCanonicalBaseChange_iff _ _ _ _ _ _).mpr ?_
    rw [CategoryTheory.Functor.map_id, canConj_id]
  -- Tag 01ZR (3) twice, and one final equalisation
  obtain ⟨k₁, f₁, hf₁⟩ := exists_pullback_map_eq_of_isCanonicalBaseChange D c hc e A A
    (ψ₁ ≫ ψ₂) (𝟙 _) hcomp₁ (hone A)
  obtain ⟨k₂, f₂, hf₂⟩ := exists_pullback_map_eq_of_isCanonicalBaseChange D c hc e B B
    (ψ₂ ≫ ψ₁) (𝟙 _) hcomp₂ (hone B)
  obtain ⟨k₃, g₁, g₂, -⟩ := IsCofilteredOrEmpty.cone_objs k₁ k₂
  obtain ⟨k₄, w, hw⟩ := IsCofilteredOrEmpty.cone_maps (g₁ ≫ f₁) (g₂ ≫ f₂)
  obtain ⟨f, hfdef⟩ : ∃ f : k₄ ⟶ k, f = w ≫ g₁ ≫ f₁ := ⟨_, rfl⟩
  have hstep : ∀ {M N : (D.obj k).Modules} {l l' : I} (m : l ⟶ l') (n : l' ⟶ k)
      {α β : M ⟶ N},
      (Scheme.Modules.pullback (D.map n)).map α = (Scheme.Modules.pullback (D.map n)).map β →
      (Scheme.Modules.pullback (D.map (m ≫ n))).map α =
        (Scheme.Modules.pullback (D.map (m ≫ n))).map β := by
    intro M N l l' m n α β h
    rw [D.map_comp]
    exact pullback_map_eq_of_precomp _ _ h
  have e₁' : (Scheme.Modules.pullback (D.map f)).map (ψ₁ ≫ ψ₂) =
      (Scheme.Modules.pullback (D.map f)).map (𝟙 _) := by
    rw [hfdef]
    exact hstep w (g₁ ≫ f₁) (hstep g₁ f₁ hf₁)
  have e₂' : (Scheme.Modules.pullback (D.map f)).map (ψ₂ ≫ ψ₁) =
      (Scheme.Modules.pullback (D.map f)).map (𝟙 _) := by
    rw [hfdef, hw]
    exact hstep w (g₂ ≫ f₂) (hstep g₂ f₂ hf₂)
  refine ⟨k₄, f ≫ e, canConj (D.map f) (D.map e) (D.map (f ≫ e)) (D.map_comp f e).symm
    ((Scheme.Modules.pullback (D.map f)).map ψ₁), ?_⟩
  refine ⟨canConj (D.map f) (D.map e) (D.map (f ≫ e)) (D.map_comp f e).symm
    ((Scheme.Modules.pullback (D.map f)).map ψ₂), ?_, ?_⟩
  · rw [← canConj_comp, show (Scheme.Modules.pullback (D.map f)).map ψ₁ ≫
      (Scheme.Modules.pullback (D.map f)).map ψ₂ =
        (Scheme.Modules.pullback (D.map f)).map (ψ₁ ≫ ψ₂) from
      (CategoryTheory.Functor.map_comp _ _ _).symm, e₁', CategoryTheory.Functor.map_id,
      canConj_id]
  · rw [← canConj_comp, show (Scheme.Modules.pullback (D.map f)).map ψ₂ ≫
      (Scheme.Modules.pullback (D.map f)).map ψ₁ =
        (Scheme.Modules.pullback (D.map f)).map (ψ₂ ≫ ψ₁) from
      (CategoryTheory.Functor.map_comp _ _ _).symm, e₂', CategoryTheory.Functor.map_id,
      canConj_id]

include hc in
/-- **The `hFullyFaithful` input of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit_of_descent`,
from the canonically pinned form of [Stacks Project, Tag 01ZR] (2) alone.**  Two finitely
presented modules on a stage whose pullbacks to the limit are isomorphic are already isomorphic
over some later stage. -/
theorem exists_pullback_iso_of_hasCanonicalDescent (hmap : HasCanonicalDescent D c) (i : I)
    (A B : (D.obj i).Modules) (hA : A.IsFinitePresentation) (hB : B.IsFinitePresentation)
    (h : Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)) :
    ∃ (j : I) (e : j ⟶ i), Nonempty ((Scheme.Modules.pullback (D.map e)).obj A ≅
      (Scheme.Modules.pullback (D.map e)).obj B) := by
  obtain ⟨φ⟩ := h
  obtain ⟨j, e, ψ, hψ⟩ := isIso_pullback_map_of_hasCanonicalDescent D c hc hmap i A B hA hB φ
  exact ⟨j, e, ⟨@asIso _ _ _ _ ψ hψ⟩⟩

end

end Stacks.AlgebraicGeometry.ModuleLimits

end
