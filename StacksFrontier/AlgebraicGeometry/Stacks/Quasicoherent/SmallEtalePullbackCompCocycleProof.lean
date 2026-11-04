module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackCompCocycle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMate
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The cocycle for the pullbacks along the morphisms of ringed sites of Stacks 070R (2)

`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso` is the composition law
`ε_b^* ⋙ ε_a^* ≅ ε_{a ∘ b}^*` for the pullbacks of sheaves of modules along the morphisms of
ringed sites of **Stacks 070R (2)**, at a chosen factorization of the composite.  This file
proves that it satisfies the **associativity cocycle condition** over a triple of composable
morphisms, which
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtalePullbackCompCocycle.lean` set up
and left open.

Neither side of that cocycle has a formula — both are comparisons of composites of *left*
adjoints — so it is proved by transporting the corresponding cocycle on the *pushforward* side,
where every comparison is restriction of sections.  The transport is
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_assoc`: a comparison of left
adjoints *defined* by uniqueness inherits the associativity coherence from the coherence of the
comparisons of the right adjoints.  So the work is in two steps.

First, `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso` is exhibited as such a
comparison.  Its right-adjoint compositor is
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso`, the composite of Mathlib's
contraction of an iterated pushforward with the reindexing
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso`; the identification is
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso`, proved by
comparing mates, since
`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackFactoredCompIso_inv` already pins
the mate of the one and `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv` pins the
mate of the other.

Second, that compositor satisfies the cocycle condition.  On sections every factor of it is a
restriction map — the contraction of an iterated pushforward is the identity on sections by
`SheafOfModules.pushforwardComp_hom_app_val_app`, and the reindexing is restriction along a
component of `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` by
`Stacks.SectionsComponents.pushforwardCongr₂_inv_app_val_app` — so both routes round the cocycle
restrict along the two routes of the indexing cocycle of **Stacks 021J**, which agree.  The
indexing cocycle is used in its `inv` form, read off
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_factoredCompIso_assoc_iso` by inverting an
equality of isomorphisms.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso`: the compositor
  `(ε_a)_* ⋙ (ε_b)_* ≅ (ε_{a ∘ b})_*` of the right adjoints, at a chosen factorization.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_factoredCompIso_assoc_inv`: the indexing
  cocycle of Stacks 021J in its `inv` form, at a component.
* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso_assoc`: **the cocycle condition
  for the compositor of the pushforwards.**
* `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso`: the
  composition law for the pullbacks is the comparison of left adjoints induced by that compositor.
* `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_assoc`: **the cocycle condition
  for `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso`.**
* `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso_assoc`: the same for
  `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`, at the literal composites.

## Implementation notes

The two evaluations on sections, `smallEtalePushforwardRightCompIso_assoc_lhs_app` and
`smallEtalePushforwardRightCompIso_assoc_rhs_app`, hold by `rfl`: each factor's component lemma
is itself a `rfl`, so the whole composite of four factors reduces without any rewriting.  Stating
them separately is what makes that available — a `simp only` with those component lemmas does
*not* fire on the `ext`-reduced goal, because the element whose type the lemma constrains is
typed by a composite of three pushforward functors rather than by the single pushforward the
lemma speaks of, and the rewrite is rejected before the `ModuleCat.Hom.hom` layer is reached.

For the same reason `Stacks.SectionsComponents.val_map_map` is applied with its two arrows
written out rather than left to unification, and the last step of
`smallEtalePushforwardRightCompIso_assoc` is a `rw` with the indexing cocycle: a `congrArg` along
the motive `fun t => M.val.map (Opposite.op t) x` makes the elaborator reconcile the composite
type of `x` with `M.val.obj (Opposite.op _)` while the motive is still open, and that exceeds
the heartbeat budget.

`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso_assoc` needs one associativity
reassociation in the base, `(a ≫ b) ≫ c = a ≫ b ≫ c`, which the factored form absorbs into its
hypotheses; this is why the factored form is the one proved first.

No `stacks` attribute is claimed here.  **Stacks 070S part (3)** is what this unblocks — the
functoriality in `f` of the rule `(f : T → S) ↦ Γ(T, f_small^*𝓖)`, whose `map_comp` needs this
cocycle — but part (3) itself also needs that presheaf, its comparison with the presheaf-level
pullback along `id_{τ,étale}` and that comparison's local bijectivity, none of which is proved
here.  Stacks 021J is tagged where it is proved, on
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_assoc`, and Stacks 075D (1) where its
transposes are.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

/-! ### The compositor of the pushforwards -/

section Compositor

variable {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z) (hab : a ≫ b = ab)

/-- **The compositor of the pushforwards along the morphisms of ringed sites of Stacks 070R (2)**,
at a morphism which is only provably the composite of the two given ones: pushing forward along
`ε_a` and then along `ε_b` is pushing forward along `ε_{a ∘ b}`.

This is Mathlib's contraction of an iterated pushforward followed by the reindexing
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso`, which replaces the structure
map of the composite by the one of the chosen factorization.  Unlike the pullbacks, both sides
are restriction of sections, so this is where the cocycle condition is proved. -/
public def smallEtalePushforwardRightCompIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b) ≅
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B ab) :=
  SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B b)
      (smallEtaleStructureMapRing B a) ≪≫
    (smallEtalePushforwardFactoredCompIso B a b ab hab).symm

/-- **The composition law for the pullbacks of Stacks 070R (2) is the comparison of left adjoints
induced by `AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso`.**

Both are isomorphisms of left adjoints, so it suffices to compare their mates, and
`CategoryTheory.conjugateEquiv` is a bijection.  The mate of the left-hand side is
`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackFactoredCompIso_inv` and the mate
of the right-hand side is `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv`; both
are the compositor itself. -/
public theorem smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso :
    smallEtalePullbackFactoredCompIso B a b ab hab =
      Adjunction.leftAdjointCompIso
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B b))
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a))
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B ab))
        (smallEtalePushforwardRightCompIso B a b ab hab) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  refine (conjugateEquiv
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B b)).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a)))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B ab))).injective ?_
  rw [conjugateEquiv_smallEtalePullbackFactoredCompIso_inv,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rfl

end Compositor

/-! ### The cocycle on the pushforward side -/

section Cocycle

variable {W X Y Z : B.Scheme} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
  (bc : X ⟶ Z) (hbc : b ≫ c = bc) (ab : W ⟶ Y) (hab : a ≫ b = ab)
  (abc : W ⟶ Z) (habc : a ≫ bc = abc) (habc' : ab ≫ c = abc)

/-- **The indexing cocycle of Stacks 021J in its `inv` form**, at a component: the two routes
round the cocycle, read with the inverses of the comparisons of
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`, agree.

This is `AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_factoredCompIso_assoc_iso` with
`CategoryTheory.Iso.inv` applied to both sides; the order of the two factors reverses, which is
why this form is the one the sections of the pushforward compositor consume. -/
public theorem smallEtaleBaseChange_factoredCompIso_assoc_inv
    (U : SmallEtale B Z.obj Z.property) :
    (smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc).inv.app U ≫
        (smallEtaleBaseChange B a).map
          ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).inv.app U) =
      (smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc').inv.app U ≫
        (smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).inv.app
          ((smallEtaleBaseChange B c).obj U) := by
  have h := congrArg (fun t : (_ : _ ⥤ _) ≅ _ => t.inv.app U)
    (smallEtaleBaseChange_factoredCompIso_assoc_iso B a b c bc hbc ab hab abc habc habc')
  simpa only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using h

/-- The left-hand route of the cocycle for
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso`, on sections: two successive
restrictions along the inverse comparisons of Stacks 021J.

Each of the four factors is the identity on sections or a restriction map, by lemmas which are
themselves `rfl`, so the composite reduces without rewriting. -/
public theorem smallEtalePushforwardRightCompIso_assoc_lhs_app
    (M : SheafOfModules.{u} (structureSheaf B W.obj W.property))
    (U : (SmallEtale B Z.obj Z.property)ᵒᵖ)
    (x : (((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B c)).obj M).val.obj U)) :
    (((isoWhiskerLeft (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
            (smallEtalePushforwardRightCompIso B b c bc hbc) ≪≫
          smallEtalePushforwardRightCompIso B a bc abc habc).hom.app M).val.app U) x =
      M.val.map ((smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc).inv.app U.unop).op
        (M.val.map ((smallEtaleBaseChange B a).map
          ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).inv.app U.unop)).op x) :=
  rfl

/-- The right-hand route of the cocycle for
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso`, on sections.  The companion of
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso_assoc_lhs_app`; the associator of
three pushforwards is the identity on sections, so it contributes nothing. -/
public theorem smallEtalePushforwardRightCompIso_assoc_rhs_app
    (M : SheafOfModules.{u} (structureSheaf B W.obj W.property))
    (U : (SmallEtale B Z.obj Z.property)ᵒᵖ)
    (x : (((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b) ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B c)).obj M).val.obj U)) :
    ((((Functor.associator (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
              (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b))
              (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B c))).symm ≪≫
          isoWhiskerRight (smallEtalePushforwardRightCompIso B a b ab hab)
            (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B c)) ≪≫
          smallEtalePushforwardRightCompIso B ab c abc habc').hom.app M).val.app U) x =
      M.val.map ((smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc').inv.app U.unop).op
        (M.val.map ((smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).inv.app
          ((smallEtaleBaseChange B c).obj U.unop)).op x) :=
  rfl

/-- **The cocycle condition for the compositor of the pushforwards of Stacks 070R (2).**
Contracting the last two pushforwards and then the result agrees with contracting the first two
and then the result.

On sections both routes are restriction along one of the two routes of the indexing cocycle of
Stacks 021J, and those agree by
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_factoredCompIso_assoc_inv`. -/
public theorem smallEtalePushforwardRightCompIso_assoc :
    isoWhiskerLeft (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
          (smallEtalePushforwardRightCompIso B b c bc hbc) ≪≫
        smallEtalePushforwardRightCompIso B a bc abc habc =
      (Functor.associator (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
          (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b))
          (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B c))).symm ≪≫
        isoWhiskerRight (smallEtalePushforwardRightCompIso B a b ab hab)
            (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B c)) ≪≫
          smallEtalePushforwardRightCompIso B ab c abc habc' := by
  ext M U x
  refine Eq.trans
    (smallEtalePushforwardRightCompIso_assoc_lhs_app B a b c bc hbc abc habc M U x) ?_
  refine Eq.trans ?_
    (smallEtalePushforwardRightCompIso_assoc_rhs_app B a b c ab hab abc habc' M U x).symm
  refine Eq.trans (Stacks.SectionsComponents.val_map_map M
    ((smallEtaleBaseChange_factoredCompIso B W X Z a bc abc habc).inv.app U.unop)
    ((smallEtaleBaseChange B a).map
      ((smallEtaleBaseChange_factoredCompIso B X Y Z b c bc hbc).inv.app U.unop)) x) ?_
  refine Eq.trans ?_ (Stacks.SectionsComponents.val_map_map M
    ((smallEtaleBaseChange_factoredCompIso B W Y Z ab c abc habc').inv.app U.unop)
    ((smallEtaleBaseChange_factoredCompIso B W X Y a b ab hab).inv.app
      ((smallEtaleBaseChange B c).obj U.unop)) x).symm
  rw [smallEtaleBaseChange_factoredCompIso_assoc_inv B a b c bc hbc ab hab abc habc habc' U.unop]

/-- **The cocycle condition for the composition law of the pullbacks of Stacks 070R (2)**, at
chosen factorizations: pulling back along `ε_c`, contracting the first two pullbacks and then the
result agrees with contracting the last two and then the result.

Neither side has a formula, both being comparisons of composites of left adjoints.  The proof is
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_assoc`, which carries the coherence
from the comparisons of the right adjoints — where it is
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso_assoc`, proved on sections — to
the comparisons of the left adjoints, together with
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso`, which
says that the composition law for the pullbacks *is* such a comparison. -/
public theorem smallEtalePullbackFactoredCompIso_assoc :
    isoWhiskerLeft (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B c))
          (smallEtalePullbackFactoredCompIso B a b ab hab) ≪≫
        smallEtalePullbackFactoredCompIso B ab c abc habc' =
      (Functor.associator (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B c))
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b))
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))).symm ≪≫
        isoWhiskerRight (smallEtalePullbackFactoredCompIso B b c bc hbc)
            (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) ≪≫
          smallEtalePullbackFactoredCompIso B a bc abc habc := by
  have key := Adjunction.leftAdjointUniq_ofNatIsoRight_comp_assoc
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B c))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B b))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B bc))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B ab))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B abc))
    (smallEtalePushforwardRightCompIso B b c bc hbc)
    (smallEtalePushforwardRightCompIso B a b ab hab)
    (smallEtalePushforwardRightCompIso B ab c abc habc')
    (smallEtalePushforwardRightCompIso B a bc abc habc)
    (smallEtalePushforwardRightCompIso_assoc B a b c bc hbc ab hab abc habc habc')
  simp only [Adjunction.leftAdjointUniq_ofNatIsoRight_comp,
    ← smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso] at key
  exact key

/-- **The cocycle condition for `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`**, the
composition law at the literal composites.

This is the factored form at `ab = a ≫ b`, `bc = b ≫ c` and `abc = a ≫ b ≫ c`; the two
factorizations of the triple composite differ by `CategoryTheory.Category.assoc` in the big étale
site, which is what the explicit factorization hypotheses of
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_assoc` absorb. -/
public theorem smallEtalePullbackCompIso_assoc :
    isoWhiskerLeft (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B c))
          (smallEtalePullbackCompIso B a b) ≪≫
        smallEtalePullbackFactoredCompIso B (a ≫ b) c (a ≫ b ≫ c) (Category.assoc a b c) =
      (Functor.associator (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B c))
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b))
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))).symm ≪≫
        isoWhiskerRight (smallEtalePullbackCompIso B b c)
            (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) ≪≫
          smallEtalePullbackFactoredCompIso B a (b ≫ c) (a ≫ b ≫ c) rfl :=
  smallEtalePullbackFactoredCompIso_assoc B a b c (b ≫ c) rfl (a ≫ b) rfl (a ≫ b ≫ c) rfl
    (Category.assoc a b c)

end Cocycle

end AlgebraicGeometry.SmallEtale

end
