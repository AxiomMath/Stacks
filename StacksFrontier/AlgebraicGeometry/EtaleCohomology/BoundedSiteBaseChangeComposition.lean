module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# The comparison of the two small étale sites is compatible with composition of base changes

Let `B` be a big étale site. For a morphism `f : T ⟶ S` of its underlying category, the square

```
SmallEtale B S ---- base change along f ----> SmallEtale B T
      |                                            |
 toEtaleSite                                   toEtaleSite
      v                                            v
   S.Etale  ------ base change along f ------->  T.Etale
```

comparing the small étale site of Stacks 021B with Mathlib's small étale site commutes up to the
canonical natural isomorphism `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`, whose
component at an object is the comparison exhibiting a fibre product formed in the size-bounded
category of schemes as a fibre product in all schemes.

This file proves the **coherence of that comparison with composition**: for `k : Z ⟶ W` and
`l : W ⟶ V`, the comparison for `k ≫ l` is the pasting of the comparisons for `k` and for `l`,
corrected by the two comparisons of a base change along a composite with the composite of the
base changes — `AlgebraicGeometry.smallEtaleBaseChange_compIso` on the bounded site and
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` on Mathlib's.

The statement is the coherence that a square of four morphisms of schemes needs. Applied to the
two factorisations `g' ≫ f` and `f' ≫ g` of the diagonal of a commutative square, it says that
the two composite comparisons agree, each being the comparison for the diagonal; that is the
site-level content of the comparison of the two presentations of the base change map of Stacks
0959, whose sheaf-level form is a hypothesis of the transport of a mate along a change of the
four categories of its square.

## Main results

* `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_comp` — the comparison of the
  two small étale sites is compatible with composition of base changes, componentwise, and
  `…_comp'` the same with the composite carried as a named morphism.
* `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_square` — **the two
  factorisations of the diagonal of a commutative square give the same comparison.**

## Implementation notes

**Why the proof is term-mode and why the pasting is done abstractly.** `Scheme.Etale` is
`CategoryTheory.MorphismProperty.Over` at the property `AlgebraicGeometry.Etale`, and
`AlgebraicGeometry.Etale` is a family of propositions rather than a term of
`CategoryTheory.MorphismProperty`; a goal about morphisms of `Scheme.Etale` is therefore not
type-correct at the transparency at which `rw` and `simp` match their patterns, and neither
tactic can so much as reassociate a composite there. The chains of reassociations and
substitutions are consequently packaged as the two private lemmas
`paste4` and `map3`, stated for an abstract category where both tactics work, and the
geometric proof applies them to explicit arguments.

**What the coherence reduces to.** Both sides are morphisms of `Z.Etale` into a chosen fibre
product, so they agree as soon as their first projections do, the second being the structure
morphism in both cases. The identity between the first projections is the four projection
formulas of the four comparisons involved: two for a base change along a composite — one on each
site — one for the action of a base change on a morphism, and one for the comparison of fibre
products under the inclusion of the size-bounded category.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})

/-! ### Reassociation, done where `rw` works -/

/-- The pasting of four projection formulas, stated for an abstract category.

Read with `e` the projection of a fibre product, this says: if the last factor `d` carries `e`
to a composite `x ≫ y` of two projections, the factor `c` before it carries `x` to `u ≫ v`, the
factor `b` carries `u` to `w` and `v` carries `y` to `t`, then the whole composite followed by
`e` is `a ≫ w ≫ t`. -/
private lemma paste4 {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ M N T : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (e : A₄ ⟶ T)
    (x : A₃ ⟶ M) (y : M ⟶ T) (u : A₂ ⟶ N) (v : N ⟶ M) (w : A₁ ⟶ N) (t : N ⟶ T)
    (h1 : d ≫ e = x ≫ y) (h2 : c ≫ x = u ≫ v) (h3 : b ≫ u = w) (h4 : v ≫ y = t) :
    (a ≫ b ≫ c ≫ d) ≫ e = a ≫ w ≫ t := by
  rw [← h3, ← h4, Category.assoc, Category.assoc, Category.assoc, h1, ← Category.assoc c x y,
    h2, Category.assoc, Category.assoc]

/-- A functor carries a threefold composite to the threefold composite of the images. -/
private lemma map3 {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A₀ A₁ A₂ A₃ : C}
    (p : A₀ ⟶ A₁) (q : A₁ ⟶ A₂) (r : A₂ ⟶ A₃) :
    F.map p ≫ F.map q ≫ F.map r = F.map (p ≫ q ≫ r) := by
  rw [← F.map_comp, ← F.map_comp]

/-! ### The inverse projection formulas -/

/-- If `i` is a left inverse of `j` and `j ≫ s = t`, then `i ≫ t = s`. -/
private lemma comp_eq_of_inv_comp_eq {C : Type*} [Category* C] {A B T : C} (i : B ⟶ A)
    (j : A ⟶ B) (s : B ⟶ T) (t : A ⟶ T) (hij : i ≫ j = 𝟙 _) (h : j ≫ s = t) : i ≫ t = s := by
  rw [← h, ← Category.assoc, hij, Category.id_comp]

/-- The inverse form of `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst`. -/
private lemma baseChangeComp_inv_app_left_fst {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' f g fg hfg).inv.app U).left ≫
        pullback.fst U.hom fg =
      pullback.fst ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj U).hom f ≫
        pullback.fst U.hom g :=
  comp_eq_of_inv_comp_eq _ _ _ _
    (congrArg (·.left) ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' f g fg hfg).inv_hom_id_app
      U)) (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst f g fg hfg U)

/-- The inverse form of
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst`: the comparison of a base
change along a composite with the composite of the base changes, on the bounded small étale
site, carries the projection of the composite to the iterated projections. -/
private lemma boundedComp_inv_app_left_fst {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V)
    (U : SmallEtale B V.obj V.property) :
    ((smallEtaleBaseChange_factoredCompIso B Z W V k l (k ≫ l) rfl).inv.app U).hom.left ≫
        pullback.fst ((smallEtaleBaseChange B l).obj U).obj.hom k ≫
          pullback.fst U.obj.hom l =
      pullback.fst U.obj.hom (k ≫ l) :=
  comp_eq_of_inv_comp_eq _ _ _ _
    (congrArg (·.hom.left) ((smallEtaleBaseChange_factoredCompIso B Z W V k l (k ≫ l) rfl
      ).inv_hom_id_app U))
    (smallEtaleBaseChange_factoredCompIso_hom_app_fst B Z W V k l (k ≫ l) rfl U)

/-! ### The coherence -/

/-- **The comparison of the two presentations of the small étale site is compatible with
composition of base changes.** For `k : Z ⟶ W` and `l : W ⟶ V` in the underlying category of a
big étale site, the component at an object `U` of the bounded small étale site of `V` of the
comparison `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso` for `k ≫ l` is the pasting of
the comparisons for `k` and for `l`, corrected at the two ends by the comparisons of a base
change along a composite with the composite of the base changes:
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` on the bounded site and
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` on Mathlib's.

Both sides are morphisms of `Z.Etale` into the chosen fibre product `U ×_V Z` formed in all
schemes, so they agree as soon as their first projections do; the second projections are the
structure morphism of the source in both cases. The identity between the first projections
pastes the four projection formulas of the four comparisons involved. -/
public theorem toEtaleSiteBaseChangeIso_hom_app_comp {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V)
    (U : SmallEtale B V.obj V.property) :
    (toEtaleSiteBaseChangeIso B (k ≫ l)).hom.app U =
      (toEtaleSite B Z.obj Z.property).map
          ((smallEtaleBaseChange_factoredCompIso B Z W V k l (k ≫ l) rfl).inv.app U) ≫
        (toEtaleSiteBaseChangeIso B k).hom.app ((smallEtaleBaseChange B l).obj U) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map k)).map
            ((toEtaleSiteBaseChangeIso B l).hom.app U) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map k)
              (B.inclusion.map l) (B.inclusion.map (k ≫ l)) (B.inclusion.map_comp k l)).inv.app
              ((toEtaleSite B V.obj V.property).obj U) := by
  have hL := PreservesPullback.iso_hom_fst B.inclusion U.obj.hom (k ≫ l)
  have hR := (paste4
      (B.inclusion.map ((smallEtaleBaseChange_factoredCompIso B Z W V k l (k ≫ l) rfl).inv.app
        U).hom.left)
      (PreservesPullback.iso B.inclusion ((smallEtaleBaseChange B l).obj U).obj.hom k).hom
      ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map k)).map
        ((toEtaleSiteBaseChangeIso B l).hom.app U)).left
      ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map k) (B.inclusion.map l)
        (B.inclusion.map (k ≫ l)) (B.inclusion.map_comp k l)).inv.app
        ((toEtaleSite B V.obj V.property).obj U)).left
      (pullback.fst ((toEtaleSite B V.obj V.property).obj U).hom (B.inclusion.map (k ≫ l)))
      (pullback.fst ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map l)).obj
        ((toEtaleSite B V.obj V.property).obj U)).hom (B.inclusion.map k))
      (pullback.fst ((toEtaleSite B V.obj V.property).obj U).hom (B.inclusion.map l))
      (pullback.fst ((toEtaleSite B W.obj W.property).obj ((smallEtaleBaseChange B l).obj U)).hom
        (B.inclusion.map k))
      (PreservesPullback.iso B.inclusion U.obj.hom l).hom
      (B.inclusion.map (pullback.fst ((smallEtaleBaseChange B l).obj U).obj.hom k))
      (B.inclusion.map (pullback.fst U.obj.hom l))
      (baseChangeComp_inv_app_left_fst (B.inclusion.map k) (B.inclusion.map l)
        (B.inclusion.map (k ≫ l)) (B.inclusion.map_comp k l)
        ((toEtaleSite B V.obj V.property).obj U))
      (Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst (B.inclusion.map k)
        ((toEtaleSiteBaseChangeIso B l).hom.app U))
      (PreservesPullback.iso_hom_fst B.inclusion ((smallEtaleBaseChange B l).obj U).obj.hom k)
      (PreservesPullback.iso_hom_fst B.inclusion U.obj.hom l)).trans
    ((map3 B.inclusion
      ((smallEtaleBaseChange_factoredCompIso B Z W V k l (k ≫ l) rfl).inv.app U).hom.left
      (pullback.fst ((smallEtaleBaseChange B l).obj U).obj.hom k)
      (pullback.fst U.obj.hom l)).trans
      (congrArg B.inclusion.map (boundedComp_inv_app_left_fst B k l U)))
  exact MorphismProperty.Over.Hom.ext (pullback.hom_ext (hL.trans hR.symm)
    ((Stacks.EtaleCohomology.smallEtaleBaseChange_w _ _).trans
      (Stacks.EtaleCohomology.smallEtaleBaseChange_w _ _).symm))

/-- `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_comp` with the composite
carried as a named morphism together with an equation naming it, rather than written out.

This is the form a square of morphisms consumes: a commutative square presents its diagonal as
two different composites, and a statement about the diagonal written out as one of them would
have to be transported to the other. -/
public theorem toEtaleSiteBaseChangeIso_hom_app_comp' {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V)
    (kl : Z ⟶ V) (hkl : kl = k ≫ l) (U : SmallEtale B V.obj V.property) :
    (toEtaleSiteBaseChangeIso B kl).hom.app U =
      (toEtaleSite B Z.obj Z.property).map
          ((smallEtaleBaseChange_factoredCompIso B Z W V k l kl hkl.symm).inv.app U) ≫
        (toEtaleSiteBaseChangeIso B k).hom.app ((smallEtaleBaseChange B l).obj U) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map k)).map
            ((toEtaleSiteBaseChangeIso B l).hom.app U) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map k)
              (B.inclusion.map l) (B.inclusion.map kl)
              (congrArg B.inclusion.map hkl)).inv.app
              ((toEtaleSite B V.obj V.property).obj U) := by
  subst hkl
  exact toEtaleSiteBaseChangeIso_hom_app_comp B k l U

/-- **The two factorisations of the diagonal of a commutative square give the same comparison of
the two presentations of the small étale site.** For a commutative square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of the underlying category of a big étale site, with the diagonal `X' ⟶ Y` carried as a named
morphism `P`, the comparison of the two small étale sites pasted along `g'` and `f` agrees with
the one pasted along `f'` and `g`: both compute the component of
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso` for `P`.

This is the identity on *sites* underlying the comparison of the two presentations of the base
change map of Stacks 0959. Each side is a comparison of the two composite direct images around
the square, read before passing to sheaves; the direct image of sheaves along a morphism of
small étale sites is restriction along the base change functor, and
`CategoryTheory.Functor.sheafPushforwardContinuousComp` identifies a composite of restrictions
with the restriction along the composite on the nose, so no sheafification and no left adjoint
intervene between this identity and its sheaf-level form. -/
public theorem toEtaleSiteBaseChangeIso_hom_app_square {X X' Y Y' : B.Scheme} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (P : X' ⟶ Y) (hP₁ : P = g' ≫ f)
    (hP₂ : P = f' ≫ g) (U : SmallEtale B Y.obj Y.property) :
    (toEtaleSite B X'.obj X'.property).map
          ((smallEtaleBaseChange_factoredCompIso B X' X Y g' f P hP₁.symm).inv.app U) ≫
        (toEtaleSiteBaseChangeIso B g').hom.app ((smallEtaleBaseChange B f).obj U) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map g')).map
            ((toEtaleSiteBaseChangeIso B f).hom.app U) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map g')
              (B.inclusion.map f) (B.inclusion.map P)
              (congrArg B.inclusion.map hP₁)).inv.app
              ((toEtaleSite B Y.obj Y.property).obj U) =
      (toEtaleSite B X'.obj X'.property).map
          ((smallEtaleBaseChange_factoredCompIso B X' Y' Y f' g P hP₂.symm).inv.app U) ≫
        (toEtaleSiteBaseChangeIso B f').hom.app ((smallEtaleBaseChange B g).obj U) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f')).map
            ((toEtaleSiteBaseChangeIso B g).hom.app U) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map f')
              (B.inclusion.map g) (B.inclusion.map P)
              (congrArg B.inclusion.map hP₂)).inv.app
              ((toEtaleSite B Y.obj Y.property).obj U) :=
  (toEtaleSiteBaseChangeIso_hom_app_comp' B g' f P hP₁ U).symm.trans
    (toEtaleSiteBaseChangeIso_hom_app_comp' B f' g P hP₂ U)

end AlgebraicGeometry.SmallEtale

end
