module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOneRepresents
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartDegreeOpenEquiv
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic

/-!
# Relative `Proj` is the relative `U_1` when the algebra is generated in degree one

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra as in Situation 01NN which is
generated in degree one over every affine open of the base
(`Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne`). This file proves that for
an arbitrary relative homogeneous spectrum `X` of `𝒜` the relative degree-one open `U_1` is all
of `X`, and deduces from residue (i) of [Stacks, Tag 01NY] over a general base the **relative
universal property at degree one**: for every test scheme `W` and every morphism `f : W ⟶ S` the
strict-equivalence classes of quadruples `(1, f, L, ψ)` of Section 01NS are in bijection with the
morphisms `W ⟶ X` over `S`.

That bijection is the relativisation of the absolute universal property
`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.existsUnique_classifies` of [Stacks, Tag 01NA]:
the absolute statement is for the `Proj` of a single graded ring generated in degree one, and the
descent along the charts of the base is carried by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.degreeOpenEquiv`, which is unconditional.
Generation in degree one enters only through `U_1 = X`, which turns "morphisms into `U_1`" into
"morphisms into `X`".

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.degreeOpen_one_eq_top`: **`X = U_1`** over an
  arbitrary base, for `𝒜` generated in degree one.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.degreeOpenOneIso`: hence the inclusion of `U_1` is
  an isomorphism onto relative `Proj`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.classifyingHom`: the morphism `W ⟶ X` a class of
  quadruples at degree one defines, and
  `classifyingHom_comp_toBase`: it lies over the morphism to `S` the class records.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClassEquiv`: **the relative universal
  property at degree one** — the bijection between the strict-equivalence classes of quadruples
  over `f : W ⟶ S` and the morphisms `W ⟶ X` over `S`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClassEquiv_naturality`: it is natural in
  the test scheme.

## Implementation notes

**The degree appears as a natural number.**
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.degreeOpenEquiv` is stated at a degree
`(k : ℤ)` coming from `k : ℕ`, while `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple`
is indexed by an integer; at `k = 1` the two spellings `((1 : ℕ) : ℤ)` and `(1 : ℤ)` are
definitionally equal, so the statements below are given at `(1 : ℤ)`, which is the spelling
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.quadruple` produces.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (P : RelativeProjData A)

/-! ### `X = U_1` over an arbitrary base -/

/-- **`X = U_1` over an arbitrary base.** For a quasi-coherent graded `𝒪_S`-algebra generated in
degree one over every affine open of the base, the relative degree-one open of an arbitrary
relative homogeneous spectrum is the whole of it.

Over an affine open `U` of the base the absolute statement
`Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.degreeOpen_one_eq_top` says that the degree-one
open of `Proj Γ(U, 𝒜)` is everything, so the chart's image of it is the chart's whole image,
which is the inverse image of `U`
(`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top`); those inverse images cover. -/
public theorem degreeOpen_one_eq_top (hgen : IsGeneratedInDegreeOne A) :
    P.degreeOpen 1 = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← RelativeProjTwistGlue.iSup_toBase_preimage_eq_top P]
  refine iSup_le fun U => ?_
  have h1 : AlgebraicGeometry.Proj.degreeOpen (A.grading (U.1 : S.Opens)) 1 = ⊤ :=
    ProjDegreeOneRepresents.degreeOpen_one_eq_top _ (hgen U.1 U.2)
  have h2 := P.chart_image_degreeOpen_le (U.1 : S.Opens) U.2 1
  rwa [h1, RelativeProjTwistGlue.chart_image_top P (U.1 : S.Opens) U.2] at h2

/-- The inclusion of the relative degree-one open into relative `Proj` is an isomorphism, for an
algebra generated in degree one. -/
public def degreeOpenOneIso (hgen : IsGeneratedInDegreeOne A) :
    (P.degreeOpen 1).toScheme ≅ P.scheme :=
  P.scheme.isoOfEq (degreeOpen_one_eq_top A P hgen) ≪≫ P.scheme.topIso

/-- The isomorphism of `degreeOpenOneIso` is the inclusion of the relative degree-one open. -/
@[simp]
public theorem degreeOpenOneIso_hom (hgen : IsGeneratedInDegreeOne A) :
    (degreeOpenOneIso A P hgen).hom = (P.degreeOpen 1).ι :=
  Scheme.isoOfEq_hom_ι P.scheme (degreeOpen_one_eq_top A P hgen)

/-- For an algebra generated in degree one the inclusion of the relative degree-one open is an
isomorphism. -/
public theorem isIso_degreeOpen_one_ι (hgen : IsGeneratedInDegreeOne A) :
    IsIso (P.degreeOpen 1).ι :=
  degreeOpenOneIso_hom A P hgen ▸ (degreeOpenOneIso A P hgen).isIso_hom

/-! ### The morphism to relative `Proj` a class of quadruples defines -/

/-- **The morphism `W ⟶ X` a strict-equivalence class of quadruples at degree one defines**: the
glued morphism into the relative degree-one open of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.homDegreeOpen`, followed by the inclusion of
that open. No hypothesis on the algebra is used. -/
public def classifyingHom {W : Scheme.{u}} (ξ : Fd (situationAlgebra A) (1 : ℤ) W) :
    W ⟶ P.scheme :=
  Fd.homDegreeOpen A P (k := 1) Nat.one_pos ξ ≫ (P.degreeOpen 1).ι

/-- **The classifying morphism lies over the morphism to the base the class records.** -/
public theorem classifyingHom_comp_toBase {W : Scheme.{u}}
    (ξ : Fd (situationAlgebra A) (1 : ℤ) W) :
    classifyingHom A P ξ ≫ P.toBase = ξ.1 := by
  rw [classifyingHom, Category.assoc]
  exact Fd.homDegreeOpen_comp_toBase A P Nat.one_pos ξ

/-- The classifying morphism is natural in the test scheme. -/
public theorem classifyingHom_pullback {W W' : Scheme.{u}} (h : W' ⟶ W)
    (ξ : Fd (situationAlgebra A) (1 : ℤ) W) :
    classifyingHom A P (Fd.pullback h ξ) = h ≫ classifyingHom A P ξ := by
  rw [classifyingHom, classifyingHom, Fd.homDegreeOpen_pullback' A P Nat.one_pos h ξ,
    Category.assoc]

/-- **The classifying morphism is a bijection onto all of the morphisms `W ⟶ X`**, for an algebra
generated in degree one: the glued morphism into `U_1` is a bijection onto the morphisms into
`U_1` by residue (i) of [Stacks, Tag 01NY] over a general base, and `U_1 = X`. -/
public theorem bijective_classifyingHom (hgen : IsGeneratedInDegreeOne A) (W : Scheme.{u}) :
    Function.Bijective (classifyingHom A P (W := W)) := by
  have := isIso_degreeOpen_one_ι A P hgen
  constructor
  · intro ξ η hξη
    exact (Fd.degreeOpenEquiv A P (k := 1) Nat.one_pos W).injective
      ((cancel_mono (P.degreeOpen 1).ι).mp hξη)
  · intro g
    obtain ⟨ξ, hξ⟩ := (Fd.degreeOpenEquiv A P (k := 1) Nat.one_pos W).surjective
      (g ≫ inv (P.degreeOpen 1).ι)
    refine ⟨ξ, ?_⟩
    change Fd.homDegreeOpen A P (k := 1) Nat.one_pos ξ ≫ (P.degreeOpen 1).ι = g
    rw [show Fd.homDegreeOpen A P (k := 1) Nat.one_pos ξ = g ≫ inv (P.degreeOpen 1).ι from hξ,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-! ### The relative universal property at degree one -/

/-- **The relative universal property at degree one**, the relativisation of [Stacks, Tag 01NA]
to an arbitrary base: for a quasi-coherent graded `𝒪_S`-algebra generated in degree one, an
arbitrary relative homogeneous spectrum `X` of it, a test scheme `W` and a morphism `f : W ⟶ S`,
the strict-equivalence classes of quadruples `(1, f, L, ψ)` of Section 01NS are in bijection with
the morphisms `W ⟶ X` over `S`.

The forward map is `Stacks.AlgebraicGeometry.ProjRepresentsF1.classifyingHom`; the bijectivity is
`bijective_classifyingHom`, read fibre by fibre over the morphism to the base, which is legitimate
because the classifying morphism lies over the class's own morphism to the base. -/
public def quadrupleClassEquiv (hgen : IsGeneratedInDegreeOne A) {W : Scheme.{u}} (f : W ⟶ S) :
    Quotient (Quadruple.setoid f (situationAlgebra A) (1 : ℤ)) ≃
      {g : W ⟶ P.scheme // g ≫ P.toBase = f} :=
  Equiv.ofBijective
    (fun q => ⟨classifyingHom A P ⟨f, q⟩, classifyingHom_comp_toBase A P ⟨f, q⟩⟩)
    ⟨fun q q' hq => by
      have h : (⟨f, q⟩ : Fd (situationAlgebra A) (1 : ℤ) W) = ⟨f, q'⟩ :=
        (bijective_classifyingHom A P hgen W).1 (congrArg Subtype.val hq)
      exact eq_of_heq (Sigma.mk.injEq .. ▸ h).2,
     fun g => by
      obtain ⟨ξ, hξ⟩ := (bijective_classifyingHom A P hgen W).2 g.1
      obtain ⟨f', q'⟩ := ξ
      have hf : f' = f :=
        (classifyingHom_comp_toBase A P (⟨f', q'⟩ : Fd (situationAlgebra A) (1 : ℤ) W)).symm.trans
          (by rw [hξ]; exact g.2)
      subst hf
      exact ⟨q', Subtype.ext hξ⟩⟩

/-- The morphism underlying the value of the bijection is the classifying morphism of the
quadruple class. -/
@[simp]
public theorem quadrupleClassEquiv_apply (hgen : IsGeneratedInDegreeOne A) {W : Scheme.{u}}
    (f : W ⟶ S) (q : Quotient (Quadruple.setoid f (situationAlgebra A) (1 : ℤ))) :
    (quadrupleClassEquiv A P hgen f q).1 = classifyingHom A P ⟨f, q⟩ :=
  rfl

/-- **The relative universal property at degree one is natural in the test scheme.** -/
public theorem quadrupleClassEquiv_naturality (hgen : IsGeneratedInDegreeOne A)
    {W W' : Scheme.{u}} (h : W' ⟶ W) (f : W ⟶ S)
    (q : Quotient (Quadruple.setoid f (situationAlgebra A) (1 : ℤ))) :
    classifyingHom A P (Fd.pullback h (⟨f, q⟩ : Fd (situationAlgebra A) (1 : ℤ) W)) =
      h ≫ (quadrupleClassEquiv A P hgen f q).1 :=
  classifyingHom_pullback A P h ⟨f, q⟩

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
