module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Cosimplicial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.HomotopyCategory
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence

/-!
# Čech cohomology of a hypercovering depends only on the homotopy class

Let `C` be a site with fibre products and let `X` be an object of `C`.  The opening paragraph of
[Stacks, Tag 01GZ] asserts: if `a, b : K ⟶ L` are homotopic maps of hypercoverings of `X` then
`F(a)` and `F(b)` are homotopic maps of cosimplicial abelian groups ([Stacks, Tag 019Y]), hence
have the same effect on the cohomology of the associated cochain complexes
([Stacks, Tag 01A0]).  That is what makes `Ȟ^i(-, F)` a diagram on `HC(C, X)ᵒᵖ`, the
hypercoverings of `X` with maps up to homotopy, and so what makes the colimit of
[Stacks, Tag 01H0] meaningful.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.cechCohomologyHypercoveringsFunctorOp`: `Ȟ^p(-, -)` on the
  hypercoverings of `X`, contravariantly, before passing to homotopy classes.
* `Stacks.CategoryTheory.Hypercovering.cechCohomologyHypercoveringsHomotopyFunctor`:
  **Tag 01GZ** — `Ȟ^p(-, -) : HC(C, X)ᵒᵖ ⥤ (Ab(C) ⥤ Ab)`, the diagram
  [Stacks, Tag 01H0] takes the colimit of.

## Main results

* `CategoryTheory.SimplicialObject.IsHomotopy.exists_cosimplicialHomotopy_rightOp`:
  [Stacks, Tag 019Y] (third part) for a homotopy in the sense of [Stacks, Tag 019K]: a
  contravariant functor carries a simplicial homotopy to a cosimplicial one, with the transported
  homotopy pinned to the family of images of its components.
* `Stacks.CategoryTheory.Hypercovering.homotopic_cochainComplexFunctorMap_app_of_isHomotopy`:
  homotopic maps of simplicial formal coproducts induce chain homotopic maps of Čech complexes.
* `Stacks.CategoryTheory.Hypercovering`'s
  `homologyMap_hypercoverCochainNatFunctorMap_app_eq_of_isHomotopy` and
  `whiskerRight_hypercoverCochainNatFunctorMap_eq_of_isHomotopy`: **Tag 01GZ** — homotopic
  maps have the same effect on Čech cohomology, at a sheaf and as natural transformations.

## Implementation notes

The library carries two notions of simplicial homotopy: [Stacks, Tag 019K]'s
`CategoryTheory.SimplicialObject.IsHomotopy`, a morphism out of the copower `K × Δ[1]`, which is
the one `Stacks.CategoryTheory.Hypercovering.homotopyRel` and so `HC(C, X)` is built on; and
Mathlib's `CategoryTheory.SimplicialObject.Homotopy`, which [Stacks, Tag 019Y] is stated for.  No
declaration relates them, so [Stacks, Tag 019Y] cannot be applied to a `homotopyRel` witness as it
stands.  Rather than build that bridge, the third part of [Stacks, Tag 019Y] is reproved here
directly from the copower form, which is short: the components `h_{m, α} : K_m ⟶ L_m` of a
copower homotopy are already indexed by the simplices of `Δ[1]`, exactly as the cosimplicial
homotopies of [Stacks, Tag 0FKJ] that [Stacks, Tag 01A0] consumes are, and the naturality of `h`
transported along a contravariant functor *is* the required relation, by `Sigma.ι_comp_map'`.
The two index sets differ only in the universe of `Δ[1]`, and `SSet.stdSimplex.objEquiv`
identifies them.

The Čech complex of `K` is `FormalCoproduct.cochainComplexFunctor K`, which at a presheaf `P` is
`alternatingCofaceMapComplex` of `K.rightOp ⋙ (FormalCoproduct.evalOp _ _).obj P` — the shape the
third part of [Stacks, Tag 019Y] produces — so no transport intervenes between the two inputs.

The descent to `HC(C, X)` is `CategoryTheory.Quotient.lift`, whose hypothesis is the *generating*
relation `homotopyRel` rather than the congruence it generates, so a single homotopy suffices.
Čech cohomology is contravariant in the hypercovering, so the functor lifted is the one valued in
the opposite category and `Functor.leftOp` turns it round afterwards; `CategoryTheory.Quotient` is
defined for covariant functors only.

## References

* [Stacks Project, Tag 01GZ](https://stacks.math.columbia.edu/tag/01GZ)
* [Stacks Project, Tag 019Y](https://stacks.math.columbia.edu/tag/019Y)
* [Stacks Project, Tag 01A0](https://stacks.math.columbia.edu/tag/01A0)
* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
-/

@[expose] public section

universe t w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet

namespace CategoryTheory.SimplicialObject

/-- **[Stacks, Tag 019Y], third part, for a homotopy in the sense of [Stacks, Tag 019K].**  A
contravariant functor `G` carries a homotopy `h : E × Δ[1] ⟶ E'` from `a` to `b` to a homotopy of
cosimplicial objects from `G(a)` to `G(b)`, in the component form of [Stacks, Tag 0FKJ]; the
transported homotopy is pinned to the family of images of the components of `h`. -/
theorem IsHomotopy.exists_cosimplicialHomotopy_rightOp {D : Type u} [Category.{v} D]
    {A : Type*} [Category* A] {E E' : SimplicialObject D}
    [∀ m, HasCoproduct fun _ : (Δ[1] : SSet.{t}).obj m => E.obj m]
    {a b : E ⟶ E'} {h : E.copower (Δ[1] : SSet.{t}) ⟶ E'} (hh : IsHomotopy h a b)
    (G : Dᵒᵖ ⥤ A) :
    ∃ k : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
        ((E'.rightOp ⋙ G).obj n ⟶ (E.rightOp ⋙ G).obj n),
      (∀ ⦃n m : SimplexCategory⦄ (g : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
          (E'.rightOp ⋙ G).map g ≫ k m α =
            k n ((Δ[1] : SSet.{0}).map g.op α) ≫ (E.rightOp ⋙ G).map g) ∧
        (∀ n : SimplexCategory, k n (stdSimplex.const 1 0 (op n)) =
            (Functor.whiskerRight (NatTrans.rightOp a) G).app n) ∧
        (∀ n : SimplexCategory, k n (stdSimplex.const 1 1 (op n)) =
            (Functor.whiskerRight (NatTrans.rightOp b) G).app n) := by
  refine ⟨fun n α ↦ G.map (Sigma.ι (fun _ : (Δ[1] : SSet.{t}).obj (op n) ↦ E.obj (op n))
      (stdSimplex.objEquiv.symm (stdSimplex.objEquiv α)) ≫ h.app (op n)).op, ?_, ?_, ?_⟩
  · intro n m g α
    have key : (Sigma.ι (fun _ : (Δ[1] : SSet.{t}).obj (op m) ↦ E.obj (op m))
            (stdSimplex.objEquiv.symm (stdSimplex.objEquiv α)) ≫ h.app (op m)) ≫
          E'.map g.op =
        E.map g.op ≫ Sigma.ι (fun _ : (Δ[1] : SSet.{t}).obj (op n) ↦ E.obj (op n))
            (stdSimplex.objEquiv.symm
              (stdSimplex.objEquiv ((Δ[1] : SSet.{0}).map g.op α))) ≫ h.app (op n) := by
      have hι : (stdSimplex.objEquiv.symm
            (stdSimplex.objEquiv ((Δ[1] : SSet.{0}).map g.op α)) :
              (Δ[1] : SSet.{t}).obj (op n)) =
          (Δ[1] : SSet.{t}).map g.op
            (stdSimplex.objEquiv.symm (stdSimplex.objEquiv α)) := by
        rfl
      rw [hι, Category.assoc, ← h.naturality g.op, ← Category.assoc,
        Functor.copower_map, Sigma.ι_comp_map']
      simp
    exact (G.map_comp _ _).symm.trans
      ((congrArg G.map (congrArg Quiver.Hom.op key)).trans (G.map_comp _ _))
  · intro n
    exact congrArg (fun z ↦ G.map (Quiver.Hom.op z)) (hh.1 (op n))
  · intro n
    exact congrArg (fun z ↦ G.map (Quiver.Hom.op z)) (hh.2 (op n))

end CategoryTheory.SimplicialObject

namespace Stacks.CategoryTheory.Hypercovering

section General

variable {D : Type u} [Category.{v} D] {A : Type*} [Category* A] [HasProducts.{w} A]
  [Preadditive A]

/-- **Homotopic maps of simplicial formal coproducts induce chain homotopic maps of Čech
complexes**, which is [Stacks, Tag 019Y] followed by [Stacks, Tag 01A0]: the Čech complex is the
alternating coface complex of the cosimplicial object of sections, and the pullback of sections
along a morphism of simplicial formal coproducts is the image of that morphism under the
contravariant functor `FormalCoproduct.evalOp` of the coefficient presheaf. -/
@[sga "4 Vbis 3.0.2.3" "special case"]
theorem homotopic_cochainComplexFunctorMap_app_of_isHomotopy
    {E E' : SimplicialObject (FormalCoproduct.{w} D)}
    [∀ m, HasCoproduct fun _ : (Δ[1] : SSet.{t}).obj m ↦ E.obj m]
    {ψ ψ' : E ⟶ E'} {h : E.copower (Δ[1] : SSet.{t}) ⟶ E'}
    (hh : SimplicialObject.IsHomotopy h ψ ψ') (P : Dᵒᵖ ⥤ A) :
    homotopic A (ComplexShape.up ℕ)
      ((cochainComplexFunctorMap.{w} (A := A) ψ).app P)
      ((cochainComplexFunctorMap.{w} (A := A) ψ').app P) :=
  AlgebraicTopology.homotopic_alternatingCofaceMapComplex_map
    (Relation.EqvGen.rel _ _
      (hh.exists_cosimplicialHomotopy_rightOp ((FormalCoproduct.evalOp.{w} D A).obj P)))

/-- **Homotopic maps of simplicial formal coproducts have the same effect on the cohomology of
the Čech complex**, their images being chain homotopic. -/
theorem homologyMap_cochainComplexFunctorMap_app_eq_of_isHomotopy [CategoryWithHomology A]
    {E E' : SimplicialObject (FormalCoproduct.{w} D)}
    [∀ m, HasCoproduct fun _ : (Δ[1] : SSet.{t}).obj m ↦ E.obj m]
    {ψ ψ' : E ⟶ E'} {h : E.copower (Δ[1] : SSet.{t}) ⟶ E'}
    (hh : SimplicialObject.IsHomotopy h ψ ψ') (P : Dᵒᵖ ⥤ A) (p : ℕ) :
    HomologicalComplex.homologyMap ((cochainComplexFunctorMap.{w} (A := A) ψ).app P) p =
      HomologicalComplex.homologyMap ((cochainComplexFunctorMap.{w} (A := A) ψ').app P) p :=
  (homotopic_cochainComplexFunctorMap_app_of_isHomotopy.{t} hh P).some.homologyMap_eq p

end General

section Sheaf

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (J : Pretopology C) (X : C)

/-- **Stacks Project, Tag 01GZ.**  Homotopic maps of simplicial semi-representable objects over
`X` have the same effect on the Čech cohomology of an abelian sheaf: by [Stacks, Tag 019Y] their
images on the cosimplicial object of sections are homotopic, and by [Stacks, Tag 01A0] homotopic
maps of cosimplicial objects induce the same map on the cohomology of the associated cochain
complexes. -/
@[stacks 01GZ "homotopic maps of hypercoverings have the same effect on Čech cohomology"]
theorem homologyMap_hypercoverCochainNatFunctorMap_app_eq_of_isHomotopy
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))}
    [∀ m, HasCoproduct fun _ : (Δ[1] : SSet.{t}).obj m ↦ K.obj m]
    {ψ ψ' : K ⟶ K'} {h : K.copower (Δ[1] : SSet.{t}) ⟶ K'}
    (hh : SimplicialObject.IsHomotopy h ψ ψ')
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p : ℕ) :
    HomologicalComplex.homologyMap
        ((hypercoverCochainNatFunctorMap.{w} J X ψ).app F) p =
      HomologicalComplex.homologyMap
        ((hypercoverCochainNatFunctorMap.{w} J X ψ').app F) p :=
  homologyMap_cochainComplexFunctorMap_app_eq_of_isHomotopy.{t} hh
    ((sectionsOnOverFunctor.{w} J X).obj F) p

/-- **Stacks Project, Tag 01GZ**, as natural transformations.  The map `Ȟ^p(K', -) ⟶ Ȟ^p(K, -)`
of Čech cohomology functors induced by a map `K ⟶ K'` depends only on its homotopy class. -/
@[stacks 01GZ "the induced natural transformation on Ȟ^p depends only on the homotopy class"]
theorem whiskerRight_hypercoverCochainNatFunctorMap_eq_of_isHomotopy
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))}
    [∀ m, HasCoproduct fun _ : (Δ[1] : SSet.{t}).obj m ↦ K.obj m]
    {ψ ψ' : K ⟶ K'} {h : K.copower (Δ[1] : SSet.{t}) ⟶ K'}
    (hh : SimplicialObject.IsHomotopy h ψ ψ') (p : ℕ) :
    Functor.whiskerRight (hypercoverCochainNatFunctorMap.{w} J X ψ)
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
          (ComplexShape.up ℕ) p) =
      Functor.whiskerRight (hypercoverCochainNatFunctorMap.{w} J X ψ')
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
          (ComplexShape.up ℕ) p) :=
  NatTrans.ext (funext fun F ↦
    homologyMap_hypercoverCochainNatFunctorMap_app_eq_of_isHomotopy.{t} J X hh F p)

/-- `Ȟ^p(-, -)` on the hypercoverings of `X`, as a functor into the *opposite* of the category of
functors on abelian sheaves: Čech cohomology is contravariant in the hypercovering, and
`CategoryTheory.Quotient.lift` lifts covariant functors only. -/
noncomputable def cechCohomologyHypercoveringsFunctorOp (p : ℕ) :
    Hypercoverings.{w} J X ⥤
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max u v w})ᵒᵖ where
  obj K := op (hypercoverCochainNatFunctor.{w} J X K.obj ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) p)
  map {_ _} ψ := (Functor.whiskerRight (hypercoverCochainNatFunctorMap.{w} J X ψ.hom)
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
      (ComplexShape.up ℕ) p)).op
  map_id K := by
    refine Quiver.Hom.unop_inj ?_
    change Functor.whiskerRight (hypercoverCochainNatFunctorMap.{w} J X (𝟙 K.obj)) _ = _
    rw [hypercoverCochainNatFunctorMap_id]
    exact Functor.whiskerRight_id' _
  map_comp {_ _ _} ψ φ := by
    refine Quiver.Hom.unop_inj ?_
    change Functor.whiskerRight
        (hypercoverCochainNatFunctorMap.{w} J X (ψ.hom ≫ φ.hom)) _ = _
    rw [hypercoverCochainNatFunctorMap_comp, Functor.whiskerRight_comp]
    rfl

/-- **Stacks Project, Tag 01GZ.**  `Ȟ^p(-, -) : HC(C, X)ᵒᵖ ⥤ (Ab(C) ⥤ Ab)`: the Čech cohomology
of a hypercovering of `X`, as a diagram on the hypercoverings of `X` with maps up to homotopy.

This is the diagram whose colimit [Stacks, Tag 01H0] compares with sheaf cohomology; it exists
because homotopic maps have the same effect on Čech cohomology, which is
`whiskerRight_hypercoverCochainNatFunctorMap_eq_of_isHomotopy`. -/
@[stacks 01GZ "Ȟ^p(-, 𝓕) as a diagram on HC(C, X)ᵒᵖ"]
noncomputable def cechCohomologyHypercoveringsHomotopyFunctor (p : ℕ) :
    (HypercoveringsHomotopy.{w} J X)ᵒᵖ ⥤
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max u v w}) :=
  (CategoryTheory.Quotient.lift (homotopyRel.{w} J X)
    (cechCohomologyHypercoveringsFunctorOp.{w} J X p)
    (fun _ _ _ _ ⟨_, hh⟩ ↦ Quiver.Hom.unop_inj
      (whiskerRight_hypercoverCochainNatFunctorMap_eq_of_isHomotopy J X hh p))).leftOp

end Sheaf

end Stacks.CategoryTheory.Hypercovering

end
