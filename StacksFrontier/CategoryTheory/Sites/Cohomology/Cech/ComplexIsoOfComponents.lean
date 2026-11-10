module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor

/-!
# Čech complexes which agree on the iterated fibre products

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target and
`G = {V_i → V}` a family of morphisms of a category `D` with fixed target, indexed by the same
type, and let `P` and `Q` be additive presheaves on `C` and on `D`. The Čech complex of `E` with
coefficients in `P` only evaluates `P` at the iterated fibre products
`U_{i_0} ×_U … ×_U U_{i_n}` and along the reindexing maps between them, and similarly for `G`
and `Q`. So isomorphisms

`P(U_{i_0} ×_U … ×_U U_{i_n}) ≅ Q(V_{i_0} ×_V … ×_V V_{i_n})`,

one for each tuple of indices, which commute with the restriction maps along the reindexing
maps, identify the two Čech complexes. Nothing is asked of `P` and `Q` at any other object, and
no functor between `C` and `D` is involved.

## Main definitions

* `Stacks.CechSite.cechComplexIsoOfComponents`: the isomorphism of Čech complexes.
* `Stacks.CechSite.cechCohomologyIsoOfComponents`: the resulting isomorphism of Čech
  cohomology objects.

## Main results

* `Stacks.CechSite.cechCohomology_isZero_of_components`: vanishing of Čech cohomology
  transfers along such a family of isomorphisms.

## Implementation notes

The two families are given by their members over a common index type `I`, so that the tuples
indexing the two Čech complexes are literally the same and the comparison is degreewise a
`CategoryTheory.Limits.Pi.map`. The compatibility is asked for every map of tuples
`Fin (n + 1) → Fin (n + 2)`, which is more than the coface maps the differential uses and is
what a natural family of isomorphisms supplies.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03OL](https://stacks.math.columbia.edu/tag/03OL)
-/

@[expose] public section

universe w v v₂ v' u u₂ u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap

section Complex

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  {I : Type w} {X : C} (Z : I → C) (g : ∀ i, Z i ⟶ X)
  {Y : D} (Z' : I → D) (g' : ∀ i, Z' i ⟶ Y)
  [hE : ∀ (n : ℕ) (i : Fin (n + 1) → I), HasProduct (fun a ↦ Over.mk (g (i a)))]
  [hG : ∀ (n : ℕ) (i : Fin (n + 1) → I), HasProduct (fun a ↦ Over.mk (g' (i a)))]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A)
  (e : ∀ (n : ℕ) (i : Fin (n + 1) → I),
    P.obj (op (∏ᶜ (fun a ↦ Over.mk (g (i a)))).left) ≅
      Q.obj (op (∏ᶜ (fun a ↦ Over.mk (g' (i a)))).left))

/-- The degree-`n` component of the comparison of Čech complexes: on the factor indexed by a
tuple `i`, the given isomorphism at the iterated fibre product of `i`. -/
noncomputable def cechComplexIsoOfComponentsDegree (n : ℕ) :
    (∏ᶜ fun l : Fin (n + 1) → I ↦ P.obj (op (∏ᶜ (fun a ↦ Over.mk (g (l a)))).left)) ≅
      ∏ᶜ fun l : Fin (n + 1) → I ↦ Q.obj (op (∏ᶜ (fun a ↦ Over.mk (g' (l a)))).left) :=
  Pi.mapIso (e n)

omit [Preadditive A] in
/-- The degree-`n` comparison map followed by the projection onto the factor of a tuple `i` is
the projection onto that factor followed by the given isomorphism at `i`. -/
@[reassoc]
theorem cechComplexIsoOfComponentsDegree_hom_comp_π (n : ℕ) (i : Fin (n + 1) → I) :
    (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e n).hom ≫
        Pi.π (fun l : Fin (n + 1) → I ↦ Q.obj (op (∏ᶜ (fun a ↦ Over.mk (g' (l a)))).left)) i =
      Pi.π (fun l : Fin (n + 1) → I ↦ P.obj (op (∏ᶜ (fun a ↦ Over.mk (g (l a)))).left)) i ≫
        (e n i).hom := by
  simp [cechComplexIsoOfComponentsDegree]

variable (he : ∀ (n : ℕ) (d : Fin (n + 1) → Fin (n + 2)) (i : Fin (n + 2) → I),
    P.map ((cechFormalCoproductMap (PreZeroHypercover.mk I Z g) d).φ i).left.op ≫
        (e (n + 1) i).hom =
      (e n (i ∘ d)).hom ≫
        Q.map ((cechFormalCoproductMap (PreZeroHypercover.mk I Z' g') d).φ i).left.op)

include he in
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- The degreewise comparison maps commute with each signed coface map. -/
theorem cechComplexIsoOfComponentsDegree_zsmul_δ_comm (n : ℕ) (k : Fin (n + 2)) :
    (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e n).hom ≫
        ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over Y) A).obj ((Over.forget Y).op ⋙ Q)).map
            ((cechSimplicialObject (PreZeroHypercover.mk I Z' g')).map
              (SimplexCategory.δ k).op).op) =
      ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over X) A).obj ((Over.forget X).op ⋙ P)).map
            ((cechSimplicialObject (PreZeroHypercover.mk I Z g)).map
              (SimplexCategory.δ k).op).op) ≫
        (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e (n + 1)).hom := by
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine congrArg (fun z ↦ ((-1 : ℤ) ^ (k : ℕ)) • z) ?_
  refine Pi.hom_ext _ _ fun j ↦ ?_
  set gE := (cechSimplicialObject (PreZeroHypercover.mk I Z g)).map (SimplexCategory.δ k).op
  set gG := (cechSimplicialObject (PreZeroHypercover.mk I Z' g')).map (SimplexCategory.δ k).op
  have hE := evalOpMapCompPi ((Over.forget X).op ⋙ P) gE j
  have hG := evalOpMapCompPi ((Over.forget Y).op ⋙ Q) gG j
  have hLow := cechComplexIsoOfComponentsDegree_hom_comp_π Z g Z' g' P Q e n (gG.f j)
  have hHigh := cechComplexIsoOfComponentsDegree_hom_comp_π Z g Z' g' P Q e (n + 1) j
  let d : Fin (n + 1) → Fin (n + 2) :=
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ k)).toFun
  conv_lhs => rw [Category.assoc, hG, ← Category.assoc]; erw [hLow]; rw [Category.assoc]
  conv_rhs => rw [Category.assoc]; erw [hHigh, ← Category.assoc, hE]; rw [Category.assoc]
  simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op]
  exact congrArg (fun z ↦ Pi.π _ _ ≫ z) (he n d j).symm

include he in
/-- The degreewise comparison maps commute with the differentials of the two Čech complexes. -/
theorem cechComplexIsoOfComponentsDegree_comm (n : ℕ) :
    (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e n).hom ≫
        (cechComplex (PreZeroHypercover.mk I Z' g') Q).d n (n + 1) =
      (cechComplex (PreZeroHypercover.mk I Z g) P).d n (n + 1) ≫
        (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e (n + 1)).hom := by
  change (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e n).hom ≫
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w}
            (cechSimplicialObject (PreZeroHypercover.mk I Z' g'))).obj
          ((Over.forget Y).op ⋙ Q))).d n (n + 1) =
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w}
            (cechSimplicialObject (PreZeroHypercover.mk I Z g))).obj
          ((Over.forget X).op ⋙ P))).d n (n + 1) ≫
      (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e (n + 1)).hom
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  exact comp_objD_comm
    (XE := (FormalCoproduct.cosimplicialObjectFunctor.{w}
        (cechSimplicialObject (PreZeroHypercover.mk I Z' g'))).obj ((Over.forget Y).op ⋙ Q))
    (XG := (FormalCoproduct.cosimplicialObjectFunctor.{w}
        (cechSimplicialObject (PreZeroHypercover.mk I Z g))).obj ((Over.forget X).op ⋙ P))
    (fun m ↦ (cechComplexIsoOfComponentsDegree Z g Z' g' P Q e m).hom)
    (fun m l ↦ cechComplexIsoOfComponentsDegree_zsmul_δ_comm Z g Z' g' P Q e he m l) n

/-- **Čech complexes which agree on the iterated fibre products are isomorphic.** Isomorphisms
between the values of `P` and of `Q` at corresponding iterated fibre products of two families
with the same index type, compatible with the restriction maps along every reindexing, give an
isomorphism of the two Čech complexes. -/
noncomputable def cechComplexIsoOfComponents :
    cechComplex (PreZeroHypercover.mk I Z g) P ≅ cechComplex (PreZeroHypercover.mk I Z' g') Q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ cechComplexIsoOfComponentsDegree Z g Z' g' P Q e n) (by
      intro m n h
      obtain rfl : m + 1 = n := h
      exact cechComplexIsoOfComponentsDegree_comm Z g Z' g' P Q e he m)

end Complex

section Cohomology

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  {I : Type w} {X : C} (Z : I → C) (g : ∀ i, Z i ⟶ X)
  {Y : D} (Z' : I → D) (g' : ∀ i, Z' i ⟶ Y)
  [hE : ∀ (n : ℕ) (i : Fin (n + 1) → I), HasProduct (fun a ↦ Over.mk (g (i a)))]
  [hG : ∀ (n : ℕ) (i : Fin (n + 1) → I), HasProduct (fun a ↦ Over.mk (g' (i a)))]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  (P : Cᵒᵖ ⥤ A) (Q : Dᵒᵖ ⥤ A)
  (e : ∀ (n : ℕ) (i : Fin (n + 1) → I),
    P.obj (op (∏ᶜ (fun a ↦ Over.mk (g (i a)))).left) ≅
      Q.obj (op (∏ᶜ (fun a ↦ Over.mk (g' (i a)))).left))
  (he : ∀ (n : ℕ) (d : Fin (n + 1) → Fin (n + 2)) (i : Fin (n + 2) → I),
    P.map ((cechFormalCoproductMap (PreZeroHypercover.mk I Z g) d).φ i).left.op ≫
        (e (n + 1) i).hom =
      (e n (i ∘ d)).hom ≫
        Q.map ((cechFormalCoproductMap (PreZeroHypercover.mk I Z' g') d).φ i).left.op)

include e he in
/-- **Čech cohomology of families which agree on the iterated fibre products.** -/
noncomputable def cechCohomologyIsoOfComponents (p : ℕ) :
    cechCohomology (PreZeroHypercover.mk I Z g) P p ≅
      cechCohomology (PreZeroHypercover.mk I Z' g') Q p :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (cechComplexIsoOfComponents Z g Z' g' P Q e he)

include e he in
/-- Vanishing of Čech cohomology transfers between families which agree on the iterated fibre
products. -/
theorem cechCohomology_isZero_of_components (p : ℕ)
    (hp : IsZero (cechCohomology (PreZeroHypercover.mk I Z' g') Q p)) :
    IsZero (cechCohomology (PreZeroHypercover.mk I Z g) P p) :=
  hp.of_iso (cechCohomologyIsoOfComponents Z g Z' g' P Q e he p)

end Cohomology

end Stacks.CechSite

end
