module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceSquares
public import StacksFrontier.Algebra.NegOnePowSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.NegOnePowNegNatCastSmul

/-!
# The differential of the target of Section 0FMK, read through the degreewise comparison

[Stacks, Section 0FMK] identifies the `k`-th graded piece of the filtration of `Ω^•_{X/S}` by the
forms pulled back from `Y` with

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

for `f : X ⟶ Y` smooth over a base `S`, and
`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares` reduces that identification to
two squares against the differentials — the one in the degree of the cut and the ones above it.
Each of those squares has the differential of the target complex in it, between two instances of
`Stacks.DeRhamSmooth.gradedTargetXIso`. **This file computes that part of the squares once**, so
that neither of them has to:

`(gradedTargetXIso k j n)⁻¹ ≫ d ≫ (gradedTargetXIso k (j+1) n') = (-1)^k(1 ⊗ d_{X/Y})`,

with `d_{X/Y} : Ω^j_{X/Y} ⟶ Ω^{j+1}_{X/Y}` in the degrees Section 50.12 names and the sign the
one the shift `[-k]` carries. Nothing is assumed of `f`: this is the target of the identification,
not the identification.

Both sides of the two squares are then free of the degree `n = k + j` and of every transport of
it, and what is left in them is the Leibniz rule on the graded piece — the mathematics the squares
are for.

## Main results

* `Stacks.DeRhamSmooth.gradedTargetXIso_inv` and `Stacks.DeRhamSmooth.gradedTargetXIso_hom`: the
  degreewise comparison of the target complex and its inverse, **with the transport of the degree
  cleared** — each is a single morphism `1 ⊗ u` of the tensored side, not a composite.
* `Stacks.DeRhamSmooth.gradedTargetXIso_inv_d`: **the differential of the target complex read
  through the degreewise comparison is `(-1)^k(1 ⊗ d_{X/Y})`**, and
  `Stacks.DeRhamSmooth.gradedTargetXIso_inv_comp_d`, the same with the comparison one degree up
  moved to the other side — the form the squares of Section 0FMK meet.

## Implementation notes

`Stacks.DeRhamSmooth.gradedTargetXIso` is built from three things: the `eqToIso` of
`Stacks.DeRhamSmooth.gradedTargetComplex_X`, the transport `HomologicalComplex.XIsoOfEq` from the
degree `n + -k` the shift names to the degree `j` Section 50.12 names, and
`Stacks.DeRhamSmooth.deRhamCochainXIso`. In the square the first of those meets the one in the
other direction and the middle one meets the differential, so the square is a composite of five
factors in which only the two copies of `deRhamCochainXIso` survive. Each of the three
cancellations is isolated in a statement of its own, and none of them is performed inside the
square:

* the `eqToIso` is an identity morphism — `Stacks.DeRhamSmooth.eqToHom_gradedTargetComplex_X` and
  its `_symm` — and it is cleared in `Stacks.DeRhamSmooth.gradedTargetXIso_inv` and
  `Stacks.DeRhamSmooth.gradedTargetXIso_hom`, whose goals carry nothing but one isomorphism. The
  same identity inside the square is **not** cleared by `CategoryTheory.Category.id_comp`;
* the two factors of a composite are merged under the two functors by
  `Stacks.DeRhamSmooth.gradedTargetMapComp` and its three-factor form, applied as terms.
  `← CategoryTheory.Functor.map_comp` cannot do this by rewriting: `F.map ?f ≫ F.map ?g` never
  matches the right-associated `F.map u ≫ (v ≫ w)` that `CategoryTheory.Category.assoc` leaves,
  and dropping associativity to let it fire does not elaborate at these binders;
* the conjugation of the differential by the two transports of the degree is
  `Stacks.GradedTargetDifferential.comp_XIsoOfEq_inv_comp_d_comp_XIsoOfEq_hom_comp`, stated over
  an abstract complex, where it is free.

The sign is `Int.negOnePow (-k)` as the shift convention of `CochainComplex.shiftFunctor` writes
it (`Stacks.DeRhamSmooth.gradedTargetComplex_d`) and `(-1 : ℤ) ^ k` as a graded Leibniz rule
writes it; `units_negOnePow_neg_natCast_smul` crosses between the two actions, and crossing first
is what makes `CategoryTheory.Preadditive.zsmul_comp` and `comp_zsmul` applicable to pull the
scalar out of the composite.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.GradedTargetDifferential

/-- **A differential conjugated by two transports of a degree is the differential between the
transported degrees**, inside a composite: for `e : p = p'` and `e' : q = q'`,

`(α ≫ (XIsoOfEq e)⁻¹) ≫ d p q ≫ ((XIsoOfEq e') ≫ β) = α ≫ d p' q' ≫ β`.

`HomologicalComplex.XIsoOfEq_inv_comp_d` and `HomologicalComplex.d_comp_XIsoOfEq_hom` are the two
halves; what this adds is the bracketing, the one a composite of morphisms `1 ⊗ u` meets once its
factors have been merged under the functors. Stated over an abstract complex because that is where
it is free: inside the square of
`Stacks.DeRhamSmooth.gradedTargetXIso_inv_d` the same cancellation is not.

Costs 160 heartbeats against the default budget of 200,000. -/
theorem comp_XIsoOfEq_inv_comp_d_comp_XIsoOfEq_hom_comp {V : Type*} [Category* V]
    [HasZeroMorphisms V] {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex V c)
    {p q p' q' : ι} (e : p = p') (e' : q = q') {Z Z' : V} (α : Z ⟶ K.X p') (β : K.X q' ⟶ Z') :
    (α ≫ (K.XIsoOfEq e).inv) ≫ K.d p q ≫ ((K.XIsoOfEq e').hom ≫ β) =
      α ≫ K.d p' q' ≫ β := by
  subst e; subst e'; simp

end Stacks.GradedTargetDifferential

namespace Stacks.DeRhamSmooth

/-! The derived-category and abelian structures, pinned rather than restated exactly as in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered`: resolving them at the
concrete inverse-image ringed space exceeds the default instance-synthesis budget. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **Tensoring with `f^{-1}Ω^k_{Y/S}` and restricting scalars carry a composite to a
composite**: `(1 ⊗ a) ≫ (1 ⊗ b) = 1 ⊗ (a ≫ b)`, read over `(f ∘ g)^{-1}𝒪_S`.

Nothing but `CategoryTheory.Functor.map_comp` of the two functors. It is stated, rather than
rewritten with where it is needed, because the right-associated composites of the squares of
Section 0FMK do not match the shape `← CategoryTheory.Functor.map_comp` rewrites.

Costs 357 heartbeats against the default budget of 200,000. -/
theorem gradedTargetMapComp (k : ℕ) {A B C : Modules (inverseImageBase f)}
    (a : A ⟶ B) (b : B ⟶ C) :
    (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map a) ≫
        (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map b) =
      (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map (a ≫ b)) :=
  Eq.trans ((coefficientRestriction f g).map_comp _ _).symm
    (congrArg (coefficientRestriction f g).map
      ((pulledBackTargetFormsTensor f g k).map_comp a b).symm)

/-- `Stacks.DeRhamSmooth.gradedTargetMapComp` for three factors, right-associated — the shape the
square of `Stacks.DeRhamSmooth.gradedTargetXIso_inv_d` has once its scalar has been pulled out.

Costs 491 heartbeats against the default budget of 200,000. -/
theorem gradedTargetMapComp₃ (k : ℕ) {A B C D : Modules (inverseImageBase f)}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map a) ≫
        (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map b) ≫
          (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map c) =
      (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map (a ≫ b ≫ c)) :=
  Eq.trans
    (congrArg
      (fun u => (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map a) ≫ u)
      (gradedTargetMapComp f g k b c))
    (gradedTargetMapComp f g k a (b ≫ c))

/-- **The inverse of the degreewise comparison of the target complex, with the transport of the
degree cleared**: it is the single morphism

`1 ⊗ ((deRhamCochainXIso j)⁻¹ ≫ (XIsoOfEq)⁻¹)`

of `f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} (−)`, read over `(f ∘ g)^{-1}𝒪_S`, and not a composite: the
`eqToIso` of `Stacks.DeRhamSmooth.gradedTargetComplex_X` that
`Stacks.DeRhamSmooth.gradedTargetXIso` carries is an identity morphism
(`Stacks.DeRhamSmooth.eqToHom_gradedTargetComplex_X_symm`).

Isolated in a statement of its own: the goal here carries one isomorphism and the identity is
free, while the same identity inside a square that also carries the two differentials is not
cleared by `CategoryTheory.Category.id_comp` at all.

Costs 19,052 heartbeats against the default budget of 200,000. -/
theorem gradedTargetXIso_inv (k j n : ℕ) (h : k + j = n) :
    (gradedTargetXIso f g k j n h).inv =
      (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map
        ((deRhamCochainXIso f j).inv ≫
          ((deRhamCochainComplex f).XIsoOfEq
            (show ((n : ℕ) : ℤ) + -(k : ℤ) = ((j : ℕ) : ℤ) by
              subst h; push_cast; ring)).inv)) := by
  refine (show _ = _ ≫ eqToHom (gradedTargetComplex_X f g k ((n : ℕ) : ℤ)).symm from rfl).trans ?_
  rw [eqToHom_gradedTargetComplex_X_symm, Category.comp_id]
  rfl

/-- `Stacks.DeRhamSmooth.gradedTargetXIso_inv` for the comparison itself. Stated separately rather
than obtained from it: the two transports are matched syntactically, not up to `Eq.symm`, and the
identity is cleared on the other side of the composite.

Costs 29,762 heartbeats against the default budget of 200,000. -/
theorem gradedTargetXIso_hom (k j n : ℕ) (h : k + j = n) :
    (gradedTargetXIso f g k j n h).hom =
      (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map
        (((deRhamCochainComplex f).XIsoOfEq
            (show ((n : ℕ) : ℤ) + -(k : ℤ) = ((j : ℕ) : ℤ) by
              subst h; push_cast; ring)).hom ≫ (deRhamCochainXIso f j).hom)) := by
  refine (show _ = eqToHom (gradedTargetComplex_X f g k ((n : ℕ) : ℤ)) ≫ _ from rfl).trans ?_
  rw [eqToHom_gradedTargetComplex_X]
  exact Category.id_comp _

/-- **The differential of the target complex of Section 0FMK, read through the degreewise
comparison, is `(-1)^k(1 ⊗ d_{X/Y})`.** For a cut `k`, degrees `n = k + j` and `n' = k + (j + 1)`,

`(gradedTargetXIso k j n)⁻¹ ≫ d n n' ≫ (gradedTargetXIso k (j+1) n')
    = (-1)^k ⋅ (1 ⊗ (deRhamCochainXIso j)⁻¹ ≫ d_{X/Y} ≫ (deRhamCochainXIso (j+1)))`,

with the de Rham differential of `f` between the degrees `j` and `j + 1` that Section 50.12 names
and no transport of a degree left on either side. Nothing is assumed of `f`.

This is the part of the two squares of
`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares` that is about the target complex
alone, computed once for both: the sign is the one the shift `[-k]` carries
(`Stacks.DeRhamSmooth.gradedTargetComplex_d`) and the factor `1 ⊗ d_{X/Y}` is the differential of
the tensored complex, the tensor product being formed degreewise.

Costs 10,810 heartbeats against the default budget of 200,000. -/
theorem gradedTargetXIso_inv_d (k j n n' : ℕ) (h : k + j = n) (h' : k + (j + 1) = n') :
    (gradedTargetXIso f g k j n h).inv ≫
        (gradedTargetComplex f g k).d ((n : ℕ) : ℤ) ((n' : ℕ) : ℤ) ≫
          (gradedTargetXIso f g k (j + 1) n' h').hom =
      (-1 : ℤ) ^ k • (coefficientRestriction f g).map
        ((pulledBackTargetFormsTensor f g k).map
          ((deRhamCochainXIso f j).inv ≫
            (deRhamCochainComplex f).d ((j : ℕ) : ℤ) ((j + 1 : ℕ) : ℤ) ≫
              (deRhamCochainXIso f (j + 1)).hom)) := by
  rw [gradedTargetXIso_inv, gradedTargetXIso_hom, gradedTargetComplex_d,
    units_negOnePow_neg_natCast_smul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  refine congrArg (fun u => (-1 : ℤ) ^ k • u) ?_
  refine Eq.trans (gradedTargetMapComp₃ f g k _ _ _) ?_
  exact congrArg
    (fun u => (coefficientRestriction f g).map ((pulledBackTargetFormsTensor f g k).map u))
    (Stacks.GradedTargetDifferential.comp_XIsoOfEq_inv_comp_d_comp_XIsoOfEq_hom_comp
      (deRhamCochainComplex f) _ _ _ _)

/-- **`Stacks.DeRhamSmooth.gradedTargetXIso_inv_d` with the comparison one degree up moved to the
other side**: the differential of the target complex pushed past the inverse of the degreewise
comparison is `(-1)^k(1 ⊗ d_{X/Y})` followed by the inverse of the comparison one degree up.

This is the form the two squares of
`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares` meet, both of their degreewise
comparisons ending in the inverse of a `Stacks.DeRhamSmooth.gradedTargetXIso`; the `@[reassoc]`
form is the one that applies when something precedes the differential.

Costs 1,041 heartbeats against the default budget of 200,000. -/
@[reassoc]
theorem gradedTargetXIso_inv_comp_d (k j n n' : ℕ) (h : k + j = n) (h' : k + (j + 1) = n') :
    (gradedTargetXIso f g k j n h).inv ≫
        (gradedTargetComplex f g k).d ((n : ℕ) : ℤ) ((n' : ℕ) : ℤ) =
      ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
        ((pulledBackTargetFormsTensor f g k).map
          ((deRhamCochainXIso f j).inv ≫
            (deRhamCochainComplex f).d ((j : ℕ) : ℤ) ((j + 1 : ℕ) : ℤ) ≫
              (deRhamCochainXIso f (j + 1)).hom))) ≫
        (gradedTargetXIso f g k (j + 1) n' h').inv :=
  (Iso.eq_comp_inv _).2
    (Eq.trans (Category.assoc _ _ _) (gradedTargetXIso_inv_d f g k j n n' h h'))

end Stacks.DeRhamSmooth

end
