module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingNonempty
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionCorrespondence

/-!
# The locus of the classifying morphism maps into the incidence correspondence of Tag 0B1S

The incidence correspondence of Tag 0B1S is the closed subset

`T = {(x, y, [g]) : r_g(x) = y}` of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`,

which is `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionLocus`. This file assembles the
morphism from the locus of the classifying morphism into the ambient product,

`Ψ = (x, y, Φ) : U ⟶ 𝐏(V) ×_k 𝐏(V) ×_k 𝐏`,

and checks that it lands in `T` at a `k`-point: the parametrisation satisfies
`f ∘ G = (c · f u · f u') · f'`, which is the defining condition of `T` read through
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`.

This is the step that makes the incidence correspondence *parametrised* rather than merely cut
out: `U` is irreducible, so the closure of the image of `Ψ` is an irreducible closed subset of
`T`, and the dimension count of Tag 0B1S is a count on the source.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifyingToProdTwo`: the pair of points,
  `U ⟶ 𝐏(V) ×_k 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifyingToProd`: the morphism `Ψ`.

## Main results

* the three projections of `Ψ` are the two projections of the source and the classifying
  morphism: `…transitionClassifyingToProd_comp_tpSource`, `…_comp_tpTarget`, `…_comp_tpPar`.
* `…ProjectiveSpaceOfModule.transitionClassifyingToProd_comp_toSpec`: `Ψ` is a morphism over
  `Spec k`.
* `…ProjectiveSpaceOfModule.tpSource_base_transitionClassifyingToProd`, `…_tpTarget_…`,
  `…_tpPar_…`: the three projections of `Ψ` at a `k`-point of the source, the last of them the
  class of the endomorphism the parametrisation produces there.
* `…ProjectiveSpaceOfModule.mem_transitionLocus_transitionClassifyingToProd`: **a `k`-point of
  the source at which the parametrisation is nonzero is carried by `Ψ` into the incidence
  correspondence.**

## Implementation notes

**Why the containment is checked at a `k`-point and not on the whole of `U`.**
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint` is
the only reading of membership in `T` the library has, and it asks the three projections of the
point to be *closed* points of the three factors, cut out by functionals. That is exactly the
data a `k`-point of the source carries. The containment of the whole image then follows from the
density of the closed points, which is a separate step and is where `T` being closed is used.

**`Ψ` is built by two lifts, not one.** The ambient product is
`(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏`, so the pair of points is a lift into `prodTwo` and `Ψ` is a lift of
that against `Φ`. The second lift's compatibility is where
`…ProjectiveSpaceCoordinateSquare.morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec`
— the clause of [Stacks, Tag 0FCY] that `φ_{ℒ,ψ}` is a morphism of `k`-schemes — is used, against
the structure morphism `U.ι ≫ transitionSourceToSpec` that `U.toScheme` was given.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare
  (morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec)

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)
  (b : Module.Basis (Fin (Module.finrank k V)) k V)

/-! ### The pair of points -/

/-- **The pair of points of a point of the locus**, as a morphism to `𝐏(V) ×_k 𝐏(V)`: the two
projections of the source, which agree over `Spec k`. -/
public def transitionClassifyingToProdTwo :
    (transitionClassifyingOpen k V X Y hXc hYc b).toScheme ⟶ prodTwo k V :=
  pullback.lift ((transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsSource k V X Y hXc hYc)
    ((transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsTarget k V X Y hXc hYc)
    (by
      rw [Category.assoc, Category.assoc, tsSource_comp_toSpec, tsTarget_comp_toSpec])

/-- The first projection of the pair is the first projection of the source. -/
public theorem transitionClassifyingToProdTwo_comp_fst :
    transitionClassifyingToProdTwo k V X Y hXc hYc b ≫
        pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsSource k V X Y hXc hYc :=
  pullback.lift_fst _ _ _

/-- The second projection of the pair is the second projection of the source. -/
public theorem transitionClassifyingToProdTwo_comp_snd :
    transitionClassifyingToProdTwo k V X Y hXc hYc b ≫
        pullback.snd (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsTarget k V X Y hXc hYc :=
  pullback.lift_snd _ _ _

/-- The pair of points lies over `Spec k` through the structure morphism of the source. -/
public theorem transitionClassifyingToProdTwo_comp_toSpec :
    transitionClassifyingToProdTwo k V X Y hXc hYc b ≫ prodTwoToSpec k V =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫
        transitionSourceToSpec k V X Y hXc hYc := by
  have hsplit : transitionClassifyingToProdTwo k V X Y hXc hYc b ≫ prodTwoToSpec k V =
      (transitionClassifyingToProdTwo k V X Y hXc hYc b ≫
        pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)) ≫ projectiveSpaceOfModuleToSpec k V := by
    rw [prodTwoToSpec, Category.assoc]
  rw [hsplit, transitionClassifyingToProdTwo_comp_fst, Category.assoc, tsSource_comp_toSpec]

/-! ### The morphism into the ambient product -/

/-- **The morphism `Ψ = (x, y, Φ)` from the locus of the classifying morphism into
`𝐏(V) ×_k 𝐏(V) ×_k 𝐏`.** The compatibility of the two legs is the clause of [Stacks, Tag 0FCY] that
`Φ` is a morphism of `k`-schemes, against the structure morphism `U.ι ≫ transitionSourceToSpec` the
locus was given. -/
public def transitionClassifyingToProd :
    (transitionClassifyingOpen k V X Y hXc hYc b).toScheme ⟶ transitionProd k V :=
  pullback.lift (transitionClassifyingToProdTwo k V X Y hXc hYc b)
    (transitionClassifying k V X Y hXc hYc b)
    (by
      rw [transitionClassifyingToProdTwo_comp_toSpec, transitionClassifying,
        morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec]
      rfl)

/-- The projection of `Ψ` to the product of the first two factors is the pair of points. -/
public theorem transitionClassifyingToProd_comp_tpFst :
    transitionClassifyingToProd k V X Y hXc hYc b ≫ tpFst k V =
      transitionClassifyingToProdTwo k V X Y hXc hYc b :=
  pullback.lift_fst _ _ _

/-- The projection of `Ψ` to the parameter space is the classifying morphism. -/
public theorem transitionClassifyingToProd_comp_tpPar :
    transitionClassifyingToProd k V X Y hXc hYc b ≫ tpPar k V =
      transitionClassifying k V X Y hXc hYc b :=
  pullback.lift_snd _ _ _

/-- The projection of `Ψ` to the source copy of `𝐏(V)` is the first projection of the source. -/
public theorem transitionClassifyingToProd_comp_tpSource :
    transitionClassifyingToProd k V X Y hXc hYc b ≫ tpSource k V =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsSource k V X Y hXc hYc := by
  rw [tpSource, ← Category.assoc, transitionClassifyingToProd_comp_tpFst,
    transitionClassifyingToProdTwo_comp_fst]

/-- The projection of `Ψ` to the target copy of `𝐏(V)` is the second projection of the source. -/
public theorem transitionClassifyingToProd_comp_tpTarget :
    transitionClassifyingToProd k V X Y hXc hYc b ≫ tpTarget k V =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ tsTarget k V X Y hXc hYc := by
  rw [tpTarget, ← Category.assoc, transitionClassifyingToProd_comp_tpFst,
    transitionClassifyingToProdTwo_comp_snd]

/-- **`Ψ` is a morphism over `Spec k`**, through the structure morphism of the source. -/
public theorem transitionClassifyingToProd_comp_toSpec :
    transitionClassifyingToProd k V X Y hXc hYc b ≫ transitionProdToSpec k V =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫
        transitionSourceToSpec k V X Y hXc hYc := by
  rw [transitionProdToSpec, ← Category.assoc, transitionClassifyingToProd_comp_tpPar,
    transitionClassifying, morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec]
  rfl

/-! ### The image of a `k`-point lies in the incidence correspondence -/

section Point

variable {k V X Y} {hXc hYc} {b} [FiniteDimensional k V]

/-- If `ψ ≫ p = ι ≫ s`, then `p ∘ ψ` at a point `x` with `ι x = q a` is `(q ≫ s)` at `a`. -/
private theorem base_comp_eq_of_comp_eq {A B C D Q : Scheme} (ψ : A ⟶ B) (p : B ⟶ C) (ι : A ⟶ D)
    (s : D ⟶ C) (h : ψ ≫ p = ι ≫ s) (q : Q ⟶ D) (a : Q) (x : A) (hx : ι.base x = q.base a) :
    p.base (ψ.base x) = (q ≫ s).base a := by
  have : p.base (ψ.base x) = (ψ ≫ p).base x := rfl
  rw [this, h, show (ι ≫ s).base x = s.base (ι.base x) from rfl, hx]
  rfl

/-- **The source projection of `Ψ` at a `k`-point of the source** is the closed point cut out by
the functional of the first component. -/
public theorem tpSource_base_transitionClassifyingToProd
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf)
    (x : (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)
    (hx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) :
    (tpSource k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base x) =
      linearFunctionalPoint k V f hf := by
  rw [base_comp_eq_of_comp_eq _ _ _ _ (transitionClassifyingToProd_comp_tpSource k V X Y hXc hYc b)
    _ a x hx, transitionSourcePoint_comp_tsSource]
  exact e₁

/-- **The target projection of `Ψ` at a `k`-point of the source** is the closed point cut out by
the functional of the second component. -/
public theorem tpTarget_base_transitionClassifyingToProd
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf')
    (x : (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)
    (hx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a) :
    (tpTarget k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base x) =
      linearFunctionalPoint k V f' hf' := by
  rw [base_comp_eq_of_comp_eq _ _ _ _ (transitionClassifyingToProd_comp_tpTarget k V X Y hXc hYc b)
    _ a x hx, transitionSourcePoint_comp_tsTarget]
  exact e₂

/-- **The parameter projection of `Ψ` at a `k`-point of the source** is the class of the
endomorphism the parametrisation produces there, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifying_base_eq`. -/
public theorem tpPar_base_transitionClassifyingToProd
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf')
    (x : (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)
    (hx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a)
    (f₃ : Module.Dual k (ParameterModule k V)) (hf₃ : f₃ ≠ 0)
    (hf₃G : ∀ φ : ParameterModule k V, f₃ φ = φ (transitionEnd k V f f' c u u' w h)) :
    (tpPar k V).base ((transitionClassifyingToProd k V X Y hXc hYc b).base x) =
      linearFunctionalPoint k (ParameterModule k V) f₃ hf₃ := by
  have hcomp : (tpPar k V).base
      ((transitionClassifyingToProd k V X Y hXc hYc b).base x) =
      (transitionClassifying k V X Y hXc hYc b).base x := by
    rw [← transitionClassifyingToProd_comp_tpPar k V X Y hXc hYc b]
    rfl
  rw [hcomp]
  exact transitionClassifying_base_eq pt hpt c u u' w h a f hf e₁ f' hf' e₂ x hx f₃ hf₃ hf₃G

/-- **`Ψ` carries a `k`-point of the source into the incidence correspondence.** At the point
carrying the pair of `k`-points `(f, f')` and the parameters `(c, u, u', w, h)` the three
projections of `Ψ` are the closed points `[f]`, `[f']` and `[G]`, and the defining condition of
the correspondence at such a triple is `f ∘ G ∈ k · f'` — which the parametrisation satisfies by
construction, `f ∘ G = (c · f u · f u') · f'`. -/
public theorem mem_transitionLocus_transitionClassifyingToProd
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf')
    (x : (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)
    (hx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a)
    (f₃ : Module.Dual k (ParameterModule k V)) (hf₃ : f₃ ≠ 0)
    (hf₃G : ∀ φ : ParameterModule k V, f₃ φ = φ (transitionEnd k V f f' c u u' w h)) :
    (transitionClassifyingToProd k V X Y hXc hYc b).base x ∈ transitionLocus k V := by
  refine (mem_transitionLocus_iff_of_linearFunctionalPoint k V _ f hf
    (tpSource_base_transitionClassifyingToProd pt c u u' w h a f hf e₁ x hx) f' hf'
    (tpTarget_base_transitionClassifyingToProd pt c u u' w h a f' hf' e₂ x hx) f₃ hf₃
    (tpPar_base_transitionClassifyingToProd pt hpt c u u' w h a f hf e₁ f' hf' e₂ x hx f₃ hf₃
      hf₃G) (transitionEnd k V f f' c u u' w h) hf₃G).mpr ?_
  rw [comp_transitionEnd]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f')

end Point

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
