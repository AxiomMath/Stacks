module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# Homomorphisms of sheaves of graded algebras from chart-local data

Let `X` be a topological space, `𝒪` a sheaf of rings on `X`, and `A`, `B` sheaves of graded
`𝒪`-algebras. A homomorphism `A ⟶ B` is a morphism of sheaves of modules in every degree
together with multiplicativity on the sections over *every* open of `X`. Comparisons of graded
algebras in algebraic geometry are, however, almost never produced in that shape: they are
produced on a basis of charts, where both algebras have an explicit presentation, and nowhere
else.

This file closes that gap. Given a basis of `X` presented as the range of a family
`U : ι → Opens X`, a degreewise family of maps on the sections over the `U a` which commutes
with the restriction maps between them, and multiplicativity *of that family only over the
`U a`*, there is a homomorphism `A ⟶ B` whose component on `U a` in degree `n` is the given map.
If moreover every member of the family is an isomorphism, the result is an isomorphism `A ≅ B`.

## Main definitions

* `Stacks.BasisRestriction.IsMultiplicativeOnBasis`: multiplicativity of a degreewise family of
  maps on the sections over the members of a family of opens.
* `Stacks.BasisRestriction.gradedAlgebraHomOfSectionHomOnBasis`: the homomorphism of sheaves of
  graded algebras assembled from such a family, with
  `gradedAlgebraHomOfSectionHomOnBasis_app_app` its chartwise components.
* `Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis`: the same for a family of
  isomorphisms, with `gradedAlgebraIsoOfSectionIsoOnBasis_hom_app_app` and
  `gradedAlgebraIsoOfSectionIsoOnBasis_inv_app_app` its chartwise components.

## Main results

* `Stacks.BasisRestriction.map_mul_of_onBasis`: **a degreewise family of morphisms of sheaves of
  modules which is multiplicative on a basis is multiplicative on every open.** This is the one
  mathematical step of the file.

## Implementation notes

The degreewise morphisms come from `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`
and `moduleSheafIsoOfSectionIsoOnBasis`, the hom- and iso-level readings of the basis-restriction
equivalence of Tag 009U; no gluing is redone here. The multiplicativity, by contrast, cannot be
obtained from any such equivalence: it is an equation between two sections of `B.piece (i + j)`
over an arbitrary open `W`, and the hypothesis constrains it only over the members of the basis
contained in `W`. Those cover `W`, so `map_mul_of_onBasis` is exactly the *separatedness* of
`B.piece (i + j)` — `Stacks.BasisRestriction.moduleSheafSection_ext_onBasis` — applied after
pushing both sides down to a chart, where the restriction maps are pulled through the degreewise
morphisms by `PresheafOfModules.naturality_apply` and through the multiplications by
`Stacks.BilinearMap.naturality`.

Separatedness is the whole of it: nothing is assumed about `A` being generated in degree one,
and nothing would be gained from it. A rigidity hypothesis of that kind constrains a degree-`n`
section over a *general* open to be a sum of products of degree-one sections, which is false for
the conormal algebra of an immersion — such a section is only *locally* such a sum — and it is
not needed, because the two sections being compared here are already determined by their
restrictions to a basis.

The isomorphism is assembled by `SheafOfModules.GradedAlgebra.isoOfPieceIso`, which asks
multiplicativity only of the forward maps; `map_mul_of_onBasis` supplies it from the chartwise
hypothesis.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.BasisRestriction

universe u

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}

/-! ### Multiplicativity on a basis, and its descent to every open -/

section Mul

variable (A B : SheafOfModules.GradedAlgebra.{u, u} 𝒪) {ι : Type*} (U : ι → Opens X)

/-- Multiplicativity of a degreewise family of maps on the sections over the members of a family
of opens: the map in degree `i + j` carries a product of a degree-`i` and a degree-`j` section
over `U a` to the product of their images. -/
public abbrev IsMultiplicativeOnBasis
    (e : ∀ (n : ℤ) (a : ι), (A.piece n).val.obj (op (U a)) ⟶ (B.piece n).val.obj (op (U a))) :
    Prop :=
  ∀ (i j : ℤ) (a : ι) (x : (A.piece i).val.obj (op (U a)))
      (y : (A.piece j).val.obj (op (U a))),
    e (i + j) a ((A.mul i j).app (op (U a)) x y) =
      (B.mul i j).app (op (U a)) (e i a x) (e j a y)

/-- **A degreewise family of morphisms of sheaves of modules which is multiplicative on a basis
is multiplicative over every open.** The two sides are sections of `B.piece (i + j)` over the
given open, and the members of the basis contained in it cover it, so it suffices to compare
their restrictions to a chart; there the restriction maps pass through the degreewise morphisms
by naturality and through the two multiplications by bilinearity, and the hypothesis applies. -/
public theorem map_mul_of_onBasis (hU : Opens.IsBasis (Set.range U))
    (φ : ∀ n : ℤ, A.piece n ⟶ B.piece n)
    (hmul : ∀ (i j : ℤ) (a : ι) (x : (A.piece i).val.obj (op (U a)))
        (y : (A.piece j).val.obj (op (U a))),
      (φ (i + j)).val.app (op (U a)) ((A.mul i j).app (op (U a)) x y) =
        (B.mul i j).app (op (U a)) ((φ i).val.app (op (U a)) x) ((φ j).val.app (op (U a)) y))
    (i j : ℤ) {W : Opens X} (x : (A.piece i).val.obj (op W))
    (y : (A.piece j).val.obj (op W)) :
    (φ (i + j)).val.app (op W) ((A.mul i j).app (op W) x y) =
      (B.mul i j).app (op W) ((φ i).val.app (op W) x) ((φ j).val.app (op W) y) := by
  refine moduleSheafSection_ext_onBasis (B.piece (i + j)) U hU _ _ fun a hle => ?_
  have hleft := PresheafOfModules.naturality_apply (φ (i + j)).val (homOfLE hle).op
    ((A.mul i j).app (op W) x y)
  have hmulA := (A.mul i j).naturality (homOfLE hle).op x y
  have hmulB := (B.mul i j).naturality (homOfLE hle).op
    ((φ i).val.app (op W) x) ((φ j).val.app (op W) y)
  have hi := PresheafOfModules.naturality_apply (φ i).val (homOfLE hle).op x
  have hj := PresheafOfModules.naturality_apply (φ j).val (homOfLE hle).op y
  refine Eq.trans hleft.symm ?_
  refine Eq.trans (congrArg (fun z => (φ (i + j)).val.app (op (U a)) z) hmulA) ?_
  refine Eq.trans (hmul i j a _ _) ?_
  refine Eq.trans ?_ hmulB.symm
  exact congrArg₂ (fun z w => (B.mul i j).app (op (U a)) z w) hi hj

end Mul

/-! ### The assembly -/

section Assembly

variable (A B : SheafOfModules.GradedAlgebra.{u, u} 𝒪) {ι : Type*} (U : ι → Opens X)

section Hom

variable (e : ∀ (n : ℤ) (a : ι),
    (A.piece n).val.obj (op (U a)) ⟶ (B.piece n).val.obj (op (U a)))
  (hU : Opens.IsBasis (Set.range U))
  (hcomp : ∀ n : ℤ, IsCompatibleOnBasis (A.piece n) (B.piece n) U (e n))

/-- The morphism of the degree-`n` pieces glued from the degree-`n` part of the family. -/
public noncomputable def pieceHomOfSectionHomOnBasis (n : ℤ) : A.piece n ⟶ B.piece n :=
  moduleSheafHomOfSectionHomOnBasis (A.piece n) (B.piece n) U (e n) hU (hcomp n)

/-- The glued morphism of the degree-`n` pieces has `e n a` as its component on `U a`. -/
public theorem pieceHomOfSectionHomOnBasis_app (n : ℤ) (a : ι) :
    (pieceHomOfSectionHomOnBasis A B U e hU hcomp n).val.app (op (U a)) = e n a :=
  moduleSheafHomOfSectionHomOnBasis_app (A.piece n) (B.piece n) U (e n) hU (hcomp n) a

/-- **The homomorphism of sheaves of graded algebras assembled from a degreewise family of maps
on a basis.** The degreewise morphisms are `moduleSheafHomOfSectionHomOnBasis` and the
multiplicativity is `map_mul_of_onBasis`. -/
public noncomputable def gradedAlgebraHomOfSectionHomOnBasis
    (hmul : IsMultiplicativeOnBasis A B U e) : A ⟶ B where
  app n := pieceHomOfSectionHomOnBasis A B U e hU hcomp n
  map_mul i j V x y := by
    obtain ⟨W⟩ := V
    refine map_mul_of_onBasis A B U hU (pieceHomOfSectionHomOnBasis A B U e hU hcomp)
      (fun i j a x y => ?_) i j x y
    rw [pieceHomOfSectionHomOnBasis_app, pieceHomOfSectionHomOnBasis_app,
      pieceHomOfSectionHomOnBasis_app]
    exact hmul i j a x y

/-- The assembled homomorphism has `e n a` as its degree-`n` component on `U a`. -/
public theorem gradedAlgebraHomOfSectionHomOnBasis_app_app
    (hmul : IsMultiplicativeOnBasis A B U e) (n : ℤ) (a : ι) :
    ((gradedAlgebraHomOfSectionHomOnBasis A B U e hU hcomp hmul).app n).val.app (op (U a)) =
      e n a :=
  pieceHomOfSectionHomOnBasis_app A B U e hU hcomp n a

end Hom

variable (e : ∀ (n : ℤ) (a : ι),
  (A.piece n).val.obj (op (U a)) ≅ (B.piece n).val.obj (op (U a)))

variable (hU : Opens.IsBasis (Set.range U))
  (hcomp : ∀ n : ℤ, IsCompatibleOnBasis (A.piece n) (B.piece n) U fun a => (e n a).hom)

/-- The isomorphism of the degree-`n` pieces glued from the degree-`n` part of the family. -/
public noncomputable def pieceIsoOfSectionIsoOnBasis (n : ℤ) : A.piece n ≅ B.piece n :=
  moduleSheafIsoOfSectionIsoOnBasis (A.piece n) (B.piece n) U (e n) hU (hcomp n)

/-- The glued isomorphism of the degree-`n` pieces has `(e n a).hom` as its component on
`U a`. -/
public theorem pieceIsoOfSectionIsoOnBasis_hom_app (n : ℤ) (a : ι) :
    (pieceIsoOfSectionIsoOnBasis A B U e hU hcomp n).hom.val.app (op (U a)) = (e n a).hom :=
  moduleSheafIsoOfSectionIsoOnBasis_hom_app (A.piece n) (B.piece n) U (e n) hU (hcomp n) a

/-- The inverse of the glued isomorphism of the degree-`n` pieces has `(e n a).inv` as its
component on `U a`. -/
public theorem pieceIsoOfSectionIsoOnBasis_inv_app (n : ℤ) (a : ι) :
    (pieceIsoOfSectionIsoOnBasis A B U e hU hcomp n).inv.val.app (op (U a)) = (e n a).inv :=
  moduleSheafIsoOfSectionIsoOnBasis_inv_app (A.piece n) (B.piece n) U (e n) hU (hcomp n) a

/-- **The isomorphism of sheaves of graded algebras assembled from a degreewise family of
isomorphisms on a basis.** The degreewise isomorphisms are `moduleSheafIsoOfSectionIsoOnBasis`
and the multiplicativity of their forward maps — all that
`SheafOfModules.GradedAlgebra.isoOfPieceIso` requires — is `map_mul_of_onBasis`. -/
public noncomputable def gradedAlgebraIsoOfSectionIsoOnBasis
    (hmul : IsMultiplicativeOnBasis A B U fun n a => (e n a).hom) : A ≅ B :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (pieceIsoOfSectionIsoOnBasis A B U e hU hcomp)
    (by
      intro i j V x y
      obtain ⟨W⟩ := V
      refine map_mul_of_onBasis A B U hU
        (fun n => (pieceIsoOfSectionIsoOnBasis A B U e hU hcomp n).hom)
        (fun i j a x y => ?_) i j x y
      rw [pieceIsoOfSectionIsoOnBasis_hom_app, pieceIsoOfSectionIsoOnBasis_hom_app,
        pieceIsoOfSectionIsoOnBasis_hom_app]
      exact hmul i j a x y)

/-- The degree-`n` component of the assembled isomorphism is the glued isomorphism of the
degree-`n` pieces. -/
public theorem gradedAlgebraIsoOfSectionIsoOnBasis_hom_app
    (hmul : IsMultiplicativeOnBasis A B U fun n a => (e n a).hom) (n : ℤ) :
    (gradedAlgebraIsoOfSectionIsoOnBasis A B U e hU hcomp hmul).hom.app n =
      (pieceIsoOfSectionIsoOnBasis A B U e hU hcomp n).hom :=
  rfl

/-- The assembled isomorphism has `(e n a).hom` as its degree-`n` component on `U a`. -/
public theorem gradedAlgebraIsoOfSectionIsoOnBasis_hom_app_app
    (hmul : IsMultiplicativeOnBasis A B U fun n a => (e n a).hom) (n : ℤ) (a : ι) :
    ((gradedAlgebraIsoOfSectionIsoOnBasis A B U e hU hcomp hmul).hom.app n).val.app (op (U a)) =
      (e n a).hom :=
  pieceIsoOfSectionIsoOnBasis_hom_app A B U e hU hcomp n a

/-- The inverse of the assembled isomorphism has `(e n a).inv` as its degree-`n` component on
`U a`. -/
public theorem gradedAlgebraIsoOfSectionIsoOnBasis_inv_app_app
    (hmul : IsMultiplicativeOnBasis A B U fun n a => (e n a).hom) (n : ℤ) (a : ι) :
    ((gradedAlgebraIsoOfSectionIsoOnBasis A B U e hU hcomp hmul).inv.app n).val.app (op (U a)) =
      (e n a).inv :=
  pieceIsoOfSectionIsoOnBasis_inv_app A B U e hU hcomp n a

end Assembly

end Stacks.BasisRestriction

end
