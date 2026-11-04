module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CochainEvaluationLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections

/-!
# Composition of internal Hom complexes is the transpose of the double contraction

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules.  Write
`H = SheafHom(L, M)` and `G = SheafHom(K, L)`.  There are two constructions of a composition
law for internal Hom complexes:

* the **composition morphism of Stacks 0A91**,
  `cmp : Tot(H ⊗_O G) ⟶ SheafHom(K, M)`
  (`AlgebraicGeometry.RingedSite.compositionMap`), built from the composition of homogeneous
  local Hom sections;
* the **transpose of the double contraction**: contract `G` against `K` by the cochain-level
  evaluation morphism of Stacks 0A90
  (`AlgebraicGeometry.RingedSite.cochainEvaluation`), use it to precompose into `H`, and uncurry
  the result by the currying isomorphism of Stacks 0A90
  (`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`) — giving a morphism
  `H ⟶ SheafHom(G, SheafHom(K, M))`, which the currying bijection on morphism groups
  (`AlgebraicGeometry.RingedSite.curryHomEquiv`) turns into a morphism
  `Tot(H ⊗_O G) ⟶ SheafHom(K, M)`.

The two agree, for arbitrary `K`, `L`, `M`, with no hypothesis and no sign.  This is the
chain-level form of the statement that the composition morphism of Stacks 0A8V is the transpose,
under the bijection of Stacks 08DI, of the double contraction against the application morphism of
Stacks 08J8.

## Main results

* `AlgebraicGeometry.RingedSite.doubleContraction`: the morphism
  `SheafHom(L, M) ⟶ SheafHom(SheafHom(K, L), SheafHom(K, M))` obtained by precomposing with the
  cochain-level evaluation of `SheafHom(K, L)` against `K` and uncurrying.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_curryHomEquiv_doubleContraction` and
  `AlgebraicGeometry.RingedSite.applyHomSectionOver_compositionMap`: the two sides on a
  homogeneous local pure tensor `β ⊗ γ`, evaluated at a local section `x` of `K`.  Both are
  `β(γ(x))`, with no sign.
* `AlgebraicGeometry.RingedSite.curryHomEquiv_doubleContraction`: **the composition morphism of
  Stacks 0A91 is the transpose of the double contraction.**

## Implementation notes

The statement transposes once more than the derived-category statement above, so that both sides
are morphisms out of `Tot(H ⊗_O G)` into `SheafHom(K, M)` and no associator is needed: the total
tensor complex of this development carries none.

`compositionMap` is a morphism out of `AlgebraicGeometry.RingedSite.tensorTotal` and
`curryHomEquiv` a bijection onto morphisms out of `Stacks.SheafOfModules.Tensor.tensorComplex`;
the statement identifies the two by `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`.

The intermediate degrees are carried as variables (`u` with `e + (b + g) = u`, and `g + e`), so
that the two sides meet without `Int` arithmetic inside a section type.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The double contraction** `SheafHom(L, M) ⟶ SheafHom(SheafHom(K, L), SheafHom(K, M))`:
precompose into `SheafHom(L, M)` with the cochain-level evaluation morphism of Stacks 0A90
`Tot(SheafHom(K, L) ⊗_O K) ⟶ L`, then uncurry by the currying isomorphism of Stacks 0A90.

On a degree-`b` local Hom section `β` of `SheafHom(L, M)` it is the section carrying a degree-`g`
local Hom section `γ` of `SheafHom(K, L)` to the section `x ↦ β(γ(x))` of `SheafHom(K, M)`. -/
def doubleContraction :
    (sheafHomComplex X L M).obj ⟶
      (sheafHomComplex X (sheafHomComplex X K L).obj (sheafHomComplex X K M).obj).obj :=
  homMap X (cochainEvaluation X K L) (𝟙 M) ≫
    (sheafHomTensorCurryIso X (sheafHomComplex X K L).obj K M).inv

/-- **The transpose of the double contraction on a homogeneous local pure tensor, evaluated.**
The transpose `Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)` of the double
contraction takes the local pure tensor of a degree-`b` section `β` of `SheafHom(L, M)` and a
degree-`g` section `γ` of `SheafHom(K, L)` to the Hom section whose value on a degree-`e` local
section `x` of `K` is `β(γ(x))`, with no sign. -/
lemma applyHomSectionOver_curryHomEquiv_doubleContraction
    (b g e u : ℤ) (heu : e + (b + g) = u) (W V : X.C) (i : V ⟶ W)
    (β : ((sheafHomComplex X L M).obj.X b).val.obj (op W))
    (γ : ((sheafHomComplex X K L).obj.X g).val.obj (op W))
    (x : (K.X e).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K M) W V i (b + g) e u heu
        ((((curryHomEquiv X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj
            (sheafHomComplex X K M).obj) (doubleContraction X K L M)).f (b + g)).val.app (op W)
          (tensorComplexSection X b g (b + g) rfl β γ)) x =
      applyHomSectionOver X (sheafHomComplex X L M) W V i b (g + e) u (by omega) β
        (applyHomSectionOver X (sheafHomComplex X K L) W V i g e (g + e) (by omega) γ x) := by
  have h1 := applyHomSectionOver_applyHomSectionOver_uncurryFun X W
    (((homMap X (cochainEvaluation X K L) (𝟙 M)).f b).val.app (op W) β)
    g (b + g) (by omega) e u heu (𝟙 W) i γ x
  have h2 := applyHomSectionOver_homMap X (cochainEvaluation X K L) (𝟙 M) W V i b (g + e) u
    (by omega) β (tensorComplexSection X g e (g + e) rfl (restrictSection X i γ) x)
  have h3 := cochainEvaluation_val_app_tensorComplexSection X K L (g + e) g e rfl (by omega) V
    (restrictSection X i γ) x
  have h4 := applyHomSectionOver_restrict X (sheafHomComplex X K L) W V i g e (g + e) (by omega)
    γ x
  rw [Category.comp_id, h2, h3, ← h4, id_f_val_app_apply] at h1
  rwa [curryHomEquiv_val_app_tensorComplexSection X _ _ _ _ (b + g) b g rfl (by omega) W β γ]

/-- **The composition morphism of Stacks 0A91 on a homogeneous local pure tensor, evaluated.**
It takes the local pure tensor of `β` and `γ` to their composite, whose value on `x` is
`β(γ(x))`. -/
lemma applyHomSectionOver_compositionMap
    (b g e u : ℤ) (heu : e + (b + g) = u) (W V : X.C) (i : V ⟶ W)
    (β : ((sheafHomComplex X L M).obj.X b).val.obj (op W))
    (γ : ((sheafHomComplex X K L).obj.X g).val.obj (op W))
    (x : (K.X e).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X K M) W V i (b + g) e u heu
        ((((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
            (sheafHomComplex X K L).obj).inv ≫ compositionMap X K L M).f (b + g)).val.app (op W)
          (tensorComplexSection X b g (b + g) rfl β γ)) x =
      applyHomSectionOver X (sheafHomComplex X L M) W V i b (g + e) u (by omega) β
        (applyHomSectionOver X (sheafHomComplex X K L) W V i g e (g + e) (by omega) γ x) := by
  rw [HomologicalComplex.comp_f, comp_val_app_apply,
    tensorTotalIsoTensorComplex_inv_tensorComplexSection, tensorTotalSectionAt_self,
    compositionMap_tensorTotalSection]
  exact compositionSection_applyOver X W V i b g (b + g) e (g + e) u rfl (by omega) (by omega)
    β γ x

/-- **The composition morphism of Stacks 0A91 is the transpose of the double contraction.**

For complexes `K`, `L`, `M` of `O`-modules, the currying bijection of Stacks 0A90 carries

`SheafHom(L, M) ⟶ SheafHom(SheafHom(K, L), SheafHom(K, M))`,

the double contraction, to the composition morphism of internal Hom complexes

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`. -/
theorem curryHomEquiv_doubleContraction :
    (curryHomEquiv X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj
        (sheafHomComplex X K M).obj) (doubleContraction X K L M) =
      (tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj).inv ≫ compositionMap X K L M := by
  refine tensorComplexSection_hom_ext X _ _ _ fun c b g hbg W β γ ↦ ?_
  subst hbg
  refine homSection_ext X (sheafHomComplex X K M) W (b + g) fun e u heu V i x ↦ ?_
  exact (applyHomSectionOver_curryHomEquiv_doubleContraction X K L M b g e u heu W V i β γ x).trans
    (applyHomSectionOver_compositionMap X K L M b g e u heu W V i β γ x).symm

end AlgebraicGeometry.RingedSite

end
