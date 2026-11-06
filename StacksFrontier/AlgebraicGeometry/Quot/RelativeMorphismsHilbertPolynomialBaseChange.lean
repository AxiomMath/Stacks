/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyTwistedEuler
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomialProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismBaseChange

/-!
# Base change of `Mor^{P, ℳ}_Q(Z, X)` and its sheaf property

Let `z : Z ⟶ Q` be flat, proper and of finite presentation and `x : X ⟶ Q` separated and of
finite presentation, let `ℳ` be an invertible module on `Z ×_Q X` and `P : ℤ → ℤ`.  For a scheme
`W` of the site and `ξ : W ⟶ Q` put `Z' = W ×_Q Z`, `X' = W ×_Q X`.  Then `Z' ×_W X'` is the base
change of `Z ×_Q X` along `ξ`, and with `ℳ'` the inverse image of `ℳ` on it

```text
Mor^{P, ℳ'}_W(Z', X') ⟶ Mor^{P, ℳ}_Q(Z, X)
        |                        |
        v                        v
        W            ⟶           Q
```

is cartesian.  This is the base change of the cartesian square of Stacks 05Y4 for `Mor` to the
subfunctors: a relative morphism over `W` lies in `Mor^{P, ℳ'}_W(Z', X')` exactly when the
relative morphism over `Q` underlying it lies in `Mor^{P, ℳ}_Q(Z, X)`, because their graphs are
isomorphic over the test scheme compatibly with `ℳ'` and `ℳ`, so have the same twisted Euler
characteristics.

Moreover `Mor^{P, ℳ}_Q(Z, X)` is an fppf sheaf: it is cut out of the sheaf `Mor_Q(Z, X)` by sets
of points of the test schemes, and covering sieves of the big fppf site are jointly surjective.

## Main definitions

* `AlgebraicGeometry.Space.graphAmbientBaseChangeHom`: the map `Z' ×_W X' ⟶ Z ×_Q X`.

## Main results

* `AlgebraicGeometry.Space.isPullback_graphAmbientBaseChangeHom`: `Z' ×_W X'` is the base change
  of `Z ×_Q X` along `ξ`.
* `AlgebraicGeometry.Space.relativeHomHilbertPolynomial_baseChange_eq_preimage`:
  `Mor^{P, ℳ'}_W(Z', X')` is the inverse image of `Mor^{P, ℳ}_Q(Z, X)`.
* `AlgebraicGeometry.Space.exists_isPullback_relativeHomHilbertPolynomial_baseChange`: the
  cartesian square above.
* `AlgebraicGeometry.Space.isSheaf_relativeHomHilbertPolynomial`: `Mor^{P, ℳ}_Q(Z, X)` is an fppf
  sheaf.

## References

* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

/-! ### Restricting a cartesian square to a subfunctor and its inverse image -/

section Restrict

/-- A cartesian square of presheaves restricts to a cartesian square on any subfunctor of its
top right corner and the inverse image of that subfunctor. -/
private theorem exists_isPullback_of_eq_preimage {C : Type*} [Category C]
    {P X Y Zc : C ⥤ Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Zc} {g : Y ⟶ Zc}
    (sq : IsPullback fst snd f g) (G : Subfunctor X) (G' : Subfunctor P)
    (h : G' = G.preimage fst) :
    ∃ t : G'.toFunctor ⟶ G.toFunctor, IsPullback t (G'.ι ≫ snd) (G.ι ≫ f) g := by
  subst h
  exact ⟨G.fromPreimage fst, (Subfunctor.isPullback_preimage fst G).paste_vert sq⟩

end Restrict

/-! ### Subfunctors cut out by sets of points are sheaves -/

section Sheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A subfunctor of an fppf sheaf which is cut out by sets of points of the test schemes is an
fppf sheaf: covering sieves of the big fppf site are jointly surjective on points. -/
private theorem isSheaf_subfunctor_of_isCutOutByPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {G : Subfunctor F}
    {p : ∀ U : BigFppfOver B S hS, Set ((BigFppfOver.toScheme B S hS).obj U) → Prop}
    (hG : IsCutOutByPoints.{0} G p) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hF)]
  intro U s hs
  obtain ⟨Zs, -, hZs⟩ := hG U.unop s
  have hall : Set.range ((BigFppfOver.toScheme B S hS).map (𝟙 U.unop)) ⊆ Zs := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨A', h, hh, hmem⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hs
      ((BigFppfOver.toScheme B S hS).map (𝟙 U.unop) v)
    exact (hZs h).1 hh hmem
  have hmem := (hZs (𝟙 U.unop)).2 hall
  rwa [op_id, Functor.map_id_apply] at hmem

end Sheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-! ### The base change of the ambient space of the graphs -/

section Ambient

variable (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) {W : BigFppfOver B S hS} (ξ : yoneda.obj W ⟶ Q)
    (hZ' : IsAlgebraicSpace B S hS (pullback ξ z)) (hX' : IsAlgebraicSpace B S hS (pullback ξ x))
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))

/-- **The canonical map `Z' ×_W X' ⟶ Z ×_Q X`** for `Z' = W ×_Q Z` and `X' = W ×_Q X`. -/
def graphAmbientBaseChangeHom :
    graphAmbient B S hS (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW ⟶
      graphAmbient B S hS z x hZ hX hQ :=
  ObjectProperty.homMk (pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
    (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition)

/-- The underlying morphism of presheaves of `graphAmbientBaseChangeHom` is the map of fibre
products `Z' ×_W X' ⟶ Z ×_Q X` induced by the projections `Z' ⟶ Z` and `X' ⟶ X`. -/
theorem graphAmbientBaseChangeHom_hom :
    (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW).hom =
      pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
        (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition :=
  rfl

private theorem graphAmbientBaseChange_fst :
    pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
        (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition ≫
        pullback.fst z x =
      pullback.fst (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.snd ξ z :=
  pullback.lift_fst _ _ _

private theorem graphAmbientBaseChange_snd :
    pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
        (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition ≫
        pullback.snd z x =
      pullback.snd (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.snd ξ x :=
  pullback.lift_snd _ _ _

/-- The square `Z' ×_W X' ⟶ Z ×_Q X` over `W ⟶ Q` is cartesian, as a square of presheaves. -/
private theorem isPullback_graphAmbientBaseChange_presheaf :
    IsPullback
      (pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
        (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition)
      (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.fst ξ z)
      (pullback.fst z x ≫ z) ξ := by
  have e₃ : pullback.snd ξ z ≫ z = pullback.fst ξ z ≫ ξ := pullback.condition.symm
  have sq₁ : IsPullback
      (pullback.snd (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.snd ξ x)
      (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x)) x (pullback.fst ξ z ≫ ξ) :=
    (IsPullback.of_hasPullback (pullback.fst ξ z) (pullback.fst ξ x)).flip.paste_horiz
      (IsPullback.of_hasPullback ξ x).flip
  have sq₂ : IsPullback
      (pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
        (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition ≫
        pullback.snd z x)
      (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x)) x (pullback.snd ξ z ≫ z) := by
    rw [graphAmbientBaseChange_snd, e₃]
    exact sq₁
  exact (sq₂.of_right (graphAmbientBaseChange_fst ξ)
    (IsPullback.of_hasPullback z x).flip).paste_vert (IsPullback.of_hasPullback ξ z).flip

/-- **`Z' ×_W X'` is the base change of `Z ×_Q X` along `ξ : W ⟶ Q`**, as a cartesian square of
algebraic spaces. -/
theorem isPullback_graphAmbientBaseChangeHom :
    IsPullback (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)
      (graphAmbientMap B S hS (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW)
      (graphAmbientMap B S hS z x hZ hX hQ)
      (ObjectProperty.homMk ξ : graphBase B S hS hW ⟶ graphBase B S hS hQ) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    (isPullback_graphAmbientBaseChange_presheaf ξ)

end Ambient

/-! ### Graphs of a relative morphism and of its image under base change -/

section Graph

variable {hZ : IsAlgebraicSpace B S hS Z} {hX : IsAlgebraicSpace B S hS X}
    {hQ : IsAlgebraicSpace B S hS Q} {W : BigFppfOver B S hS} {ξ : yoneda.obj W ⟶ Q}
    {hZ' : IsAlgebraicSpace B S hS (pullback ξ z)} {hX' : IsAlgebraicSpace B S hS (pullback ξ x)}
    {hW : IsAlgebraicSpace B S hS (yoneda.obj W)}

/-- `T ×_W Z' = T ×_Q Z`, with target the source of the graph map of the relative morphism over
`Q` underlying a relative morphism over `W`. -/
private def graphSourceBaseChangeIso {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    pullback p'.base (pullback.fst ξ z) ≅
      pullback (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').base z :=
  pullbackBaseChangeIso ξ z p'.base

private theorem graphSourceBaseChangeIso_hom_fst {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    (graphSourceBaseChangeIso p').hom ≫
        pullback.fst (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').base z =
      pullback.fst p'.base (pullback.fst ξ z) :=
  pullbackBaseChangeIso_hom_fst ξ z p'.base

private theorem graphSourceBaseChangeIso_hom_snd {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    (graphSourceBaseChangeIso p').hom ≫
        pullback.snd (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').base z =
      pullback.snd p'.base (pullback.fst ξ z) ≫ pullback.snd ξ z :=
  pullbackBaseChangeIso_hom_snd ξ z p'.base

private theorem graphSourceBaseChangeIso_hom_morphism {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    (graphSourceBaseChangeIso p').hom ≫
        (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').morphism =
      p'.morphism ≫ pullback.snd ξ x :=
  Iso.hom_inv_id_assoc _ _

/-- The isomorphism of the graph of a relative morphism over `W` with the graph of the relative
morphism over `Q` underlying it: both are isomorphic to `T ×_W Z' = T ×_Q Z`. -/
private def graphRangeBaseChangeIso {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    (Subfunctor.range (graphMap p')).toFunctor ≅
      (Subfunctor.range
        (graphMap (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p'))).toFunctor :=
  (asIso (Subfunctor.toRange (graphMap p'))).symm ≪≫ graphSourceBaseChangeIso p' ≪≫
    asIso (Subfunctor.toRange (graphMap (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p')))

/-- Compatibility of `graphRangeBaseChangeIso` with the graph maps, after any further map. -/
private theorem toRange_graphRangeBaseChangeIso_hom_ι_comp {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : pullback (pullback.fst z x ≫ z)
      (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').base ⟶ Y) :
    Subfunctor.toRange (graphMap p') ≫ (graphRangeBaseChangeIso p').hom ≫
        (Subfunctor.range (graphMap (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p'))).ι ≫
          g =
      (graphSourceBaseChangeIso p').hom ≫
        graphMap (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p') ≫ g := by
  simp only [graphRangeBaseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc, Category.assoc, Subfunctor.toRange_ι_assoc]

private theorem graphRangeBaseChangeIso_hom_ι_snd {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    (graphRangeBaseChangeIso p').hom ≫
        (Subfunctor.range (graphMap (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p'))).ι ≫
        pullback.snd (pullback.fst z x ≫ z)
          (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').base =
      (Subfunctor.range (graphMap p')).ι ≫
        pullback.snd (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.fst ξ z)
          p'.base := by
  refine (cancel_epi (Subfunctor.toRange (graphMap p'))).1 ?_
  rw [toRange_graphRangeBaseChangeIso_hom_ι_comp, Subfunctor.toRange_ι_assoc, graphMap_snd,
    graphMap_snd]
  exact graphSourceBaseChangeIso_hom_fst p'

private theorem graphRangeBaseChangeIso_hom_ι_fst {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T)) :
    ((Subfunctor.range (graphMap p')).ι ≫
        pullback.fst (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.fst ξ z)
          p'.base) ≫
        pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
          (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition =
      (graphRangeBaseChangeIso p').hom ≫
        (Subfunctor.range (graphMap (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p'))).ι ≫
        pullback.fst (pullback.fst z x ≫ z)
          (RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p').base := by
  refine (cancel_epi (Subfunctor.toRange (graphMap p'))).1 ?_
  rw [toRange_graphRangeBaseChangeIso_hom_ι_comp, Category.assoc, Subfunctor.toRange_ι_assoc]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [graphAmbientBaseChange_fst, graphMap_fst_fst_assoc, graphMap_fst_fst]
    exact (graphSourceBaseChangeIso_hom_snd p').symm
  · simp only [Category.assoc]
    rw [graphAmbientBaseChange_snd, graphMap_fst_snd_assoc, graphMap_fst_snd]
    exact (graphSourceBaseChangeIso_hom_morphism p').symm

variable (hZ hX hQ hZ' hX' hW) in
include hZ hX hQ hZ' hX' hW in
/-- **The graph of a relative morphism over `W` and the graph of the relative morphism over `Q`
underlying it have the same twisted Euler characteristics**, with respect to the inverse image
`ℳ'` of `ℳ` on `Z' ×_W X'` and to `ℳ`. -/
private theorem mem_hilbertPolynomialSubfunctor_graph_baseChange_iff
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z)
    (hsep' : IsSeparated B S hS (pullback.fst ξ x))
    (hxfp' : IsFinitePresentation B S hS (pullback.fst ξ x))
    (hfp' : IsFinitePresentation B S hS (pullback.fst ξ z))
    (hflat' : IsFlat B S hS (pullback.fst ξ z)) (hproper' : IsProper B S hS (pullback.fst ξ z))
    (M : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property M]
    (P : ℤ → ℤ) {T : BigFppfOver B S hS}
    (p' : RelativeMorphism B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
      (pullback.fst ξ z) (pullback.fst ξ x) (yoneda.obj T))
    (q : RelativeMorphism B S hS Z X Q z x (yoneda.obj T))
    (hq : q = RelativeMorphism.ofBaseChange ξ p') :
    (⟨p'.base, graphHilbertFamily hZ' hX' hW p' hsep' hfp' hflat' hproper'⟩ :
        HilbertFamilyOver
          (graphAmbientMap B S hS (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW) T) ∈
      (hilbertPolynomialSubfunctor
        (graphAmbientMap B S hS (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW)
        (isFinitePresentation_graphAmbientMap (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW
          hfp' hxfp')
        ((modulePullback B S hS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)).obj M)
        (hL := stacksIsInvertible_modulePullback_obj B S hS _ M) P).obj (op T) ↔
    (⟨q.base, graphHilbertFamily hZ hX hQ q hsep hfp hflat hproper⟩ :
        HilbertFamilyOver (graphAmbientMap B S hS z x hZ hX hQ) T) ∈
      (hilbertPolynomialSubfunctor (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp) M P).obj (op T) := by
  subst hq
  have := stacksIsInvertible_modulePullback_obj B S hS
    (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW) M
  set q := RelativeMorphism.ofBaseChange (z := z) (x := x) ξ p'
  let f' := graphAmbientMap B S hS (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW
  let f := graphAmbientMap B S hS z x hZ hX hQ
  let hf' := isFinitePresentation_graphAmbientMap (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX'
    hW hfp' hxfp'
  let hf := isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp
  let xf : HilbertFamilyOver f' T :=
    ⟨p'.base, graphHilbertFamily hZ' hX' hW p' hsep' hfp' hflat' hproper'⟩
  let yf : HilbertFamilyOver f T := ⟨q.base, graphHilbertFamily hZ hX hQ q hsep hfp hflat hproper⟩
  let e0 := graphRangeBaseChangeIso p'
  let φ : xf.subspace ≅ yf.subspace := ObjectProperty.isoMk _ e0
  have hφ : φ.hom ≫ yf.subspaceInclusion ≫ schemeBaseChangeProjectionHom B S hS f
        (CostructuredArrow.mk yf.toBase) =
      xf.subspaceInclusion ≫ schemeBaseChangeProjectionHom B S hS f'
        (CostructuredArrow.mk xf.toBase) := by
    apply ObjectProperty.hom_ext
    show e0.hom ≫ (Subfunctor.range (graphMap q)).ι ≫
        pullback.snd (pullback.fst z x ≫ z) q.base =
      (Subfunctor.range (graphMap p')).ι ≫
        pullback.snd (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.fst ξ z)
          p'.base
    exact graphRangeBaseChangeIso_hom_ι_snd p'
  let p := xf.subspaceInclusion ≫ (ObjectProperty.homMk (pullback.fst f'.hom xf.toBase) :
    schemeBaseChangeSpace f' (CostructuredArrow.mk xf.toBase) ⟶ _)
  let pp := φ.hom ≫ yf.subspaceInclusion ≫ (ObjectProperty.homMk (pullback.fst f.hom yf.toBase) :
    schemeBaseChangeSpace f (CostructuredArrow.mk yf.toBase) ⟶ _)
  have hp : p ≫ graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW = pp := by
    apply ObjectProperty.hom_ext
    show ((Subfunctor.range (graphMap p')).ι ≫
        pullback.fst (pullback.fst (pullback.fst ξ z) (pullback.fst ξ x) ≫ pullback.fst ξ z)
          p'.base) ≫
        pullback.map (pullback.fst ξ z) (pullback.fst ξ x) z x
          (pullback.snd ξ z) (pullback.snd ξ x) ξ pullback.condition pullback.condition =
      e0.hom ≫ (Subfunctor.range (graphMap q)).ι ≫ pullback.fst (pullback.fst z x ≫ z) q.base
    exact graphRangeBaseChangeIso_hom_ι_fst p'
  let e : (modulePullback B S hS p).obj
        ((modulePullback B S hS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)).obj M) ≅
      (modulePullback B S hS pp).obj M :=
    ((modulePullbackTriangle B S hS hp).app M).symm
  have key := fun t n => twistedEuler_hilbertCohObject_eq_of_iso f' hf' f hf xf yf φ hφ
    ((modulePullback B S hS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)).obj M) M
    (modulePullbackInvertibleTensorPowerCongr p pp _ M e) t n
  exact ⟨fun h t n => (h t n).trans (key t n), fun h t n => (h t n).trans (key t n).symm⟩

end Graph

/-! ### The cartesian square -/

section Main

variable (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z)
    {W : BigFppfOver B S hS} (ξ : yoneda.obj W ⟶ Q)
    (hZ' : IsAlgebraicSpace B S hS (pullback ξ z)) (hX' : IsAlgebraicSpace B S hS (pullback ξ x))
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hsep' : IsSeparated B S hS (pullback.fst ξ x))
    (hxfp' : IsFinitePresentation B S hS (pullback.fst ξ x))
    (hfp' : IsFinitePresentation B S hS (pullback.fst ξ z))
    (hflat' : IsFlat B S hS (pullback.fst ξ z)) (hproper' : IsProper B S hS (pullback.fst ξ z))
    (M : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property M]
    (P : ℤ → ℤ)

/-- **`Mor^{P, ℳ'}_W(Z', X')` is the inverse image of `Mor^{P, ℳ}_Q(Z, X)`** under the map
`Mor_W(Z', X') ⟶ Mor_Q(Z, X)` of Stacks 05Y4, where `ℳ'` is the inverse image of `ℳ` on
`Z' ×_W X'`: a relative morphism over `W` has a graph with Hilbert polynomial `P` with respect to
`ℳ'` exactly when the relative morphism over `Q` underlying it has a graph with Hilbert polynomial
`P` with respect to `ℳ`. -/
theorem relativeHomHilbertPolynomial_baseChange_eq_preimage :
    relativeHomHilbertPolynomial hZ' hX' hW hsep' hxfp' hfp' hflat' hproper'
        ((modulePullback B S hS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)).obj M)
        (hM := stacksIsInvertible_modulePullback_obj B S hS _ M) P =
      (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).preimage
        (relativeHomOfBaseChange ξ (relativeHomData B S hS Z X Q z x hZ hX hQ)
          (relativeHomData B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
            (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW)) := by
  ext T s
  exact mem_hilbertPolynomialSubfunctor_graph_baseChange_iff hZ hX hQ hZ' hX' hW hsep hxfp hfp
    hflat hproper hsep' hxfp' hfp' hflat' hproper' M P _ _
    (sections_relativeHomOfBaseChange ξ _ _ T s)

/-- **Base change of `Mor^{P, ℳ}_Q(Z, X)`.**  For a scheme `W` and `ξ : W ⟶ Q`, with
`Z' = W ×_Q Z`, `X' = W ×_Q X` and `ℳ'` the inverse image of `ℳ` on `Z' ×_W X'`, the square

```text
Mor^{P, ℳ'}_W(Z', X') ⟶ Mor^{P, ℳ}_Q(Z, X)
        |                        |
        v                        v
        W            ⟶           Q
```

is cartesian: the cartesian square of Stacks 05Y4 for `Mor` restricts to the subfunctors, since
`Mor^{P, ℳ'}_W(Z', X')` is the inverse image of `Mor^{P, ℳ}_Q(Z, X)`
(`AlgebraicGeometry.Space.relativeHomHilbertPolynomial_baseChange_eq_preimage`). -/
theorem exists_isPullback_relativeHomHilbertPolynomial_baseChange :
    ∃ t : (relativeHomHilbertPolynomial hZ' hX' hW hsep' hxfp' hfp' hflat' hproper'
          ((modulePullback B S hS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)).obj M)
          (hM := stacksIsInvertible_modulePullback_obj B S hS _ M) P).toFunctor ⟶
        (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).toFunctor,
      IsPullback t
        ((relativeHomHilbertPolynomial hZ' hX' hW hsep' hxfp' hfp' hflat' hproper'
            ((modulePullback B S hS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW)).obj M)
            (hM := stacksIsInvertible_modulePullback_obj B S hS _ M) P).ι ≫
          relativeHomProjection B S hS _ _ _ (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW)
        ((relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).ι ≫
          relativeHomProjection B S hS Z X Q z x hZ hX hQ) ξ :=
  exists_isPullback_of_eq_preimage
    (isPullback_relativeHomOfBaseChange ξ (relativeHomData B S hS Z X Q z x hZ hX hQ)
      (relativeHomData B S hS (pullback ξ z) (pullback ξ x) (yoneda.obj W)
        (pullback.fst ξ z) (pullback.fst ξ x) hZ' hX' hW)).flip _ _
    (relativeHomHilbertPolynomial_baseChange_eq_preimage hZ hX hQ hsep hxfp hfp hflat hproper ξ
      hZ' hX' hW hsep' hxfp' hfp' hflat' hproper' M P)

end Main

/-! ### The sheaf property -/

section IsSheaf

variable (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z)
    (M : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property M]
    (P : ℤ → ℤ)

/-- **`Mor^{P, ℳ}_Q(Z, X)` is an fppf sheaf.**  It is cut out of the fppf sheaf `Mor_Q(Z, X)`
(Stacks 05Y3) by open and closed sets of points of the test schemes (Stacks 0DPQ), and covering
sieves of the big fppf site are jointly surjective on points. -/
theorem isSheaf_relativeHomHilbertPolynomial :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).toFunctor :=
  isSheaf_subfunctor_of_isCutOutByPoints (isSheaf_relativeHom B S hS Z X Q z x hZ hX hQ)
    (IsCutOutByPoints.relativeHomGraphPreimage B S hS Z X Q z x hZ hX hQ hsep hfp hflat hproper
      ((QuotSituation.isCutOutByPoints_quotCondition _ (p := fun _ W => IsClopen W)
        (fun m h => @CoherentObject.hasHilbertPolynomial_of_coherentHom B S hS _ M hM P _ _ m h)
        (CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial
          (D := (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
            (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation) M
            (hL := hM) P).isCutOutOnTestSchemes).preimage _))

end IsSheaf

end AlgebraicGeometry.Space

end
