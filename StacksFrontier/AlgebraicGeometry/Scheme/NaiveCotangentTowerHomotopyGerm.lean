module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermVariable
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegsSquare
public import StacksFrontier.RingTheory.NaiveCotangent.CompositionNullHomotopy

/-!
# The stalk of the null homotopy of a tower of sheaves of rings

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a topological
space `T` and let `x` be a point of `T`.  The square with horizontal morphisms `a`, `b` and
vertical morphisms `a`, `b` carries a `B`-linear chain map `NL_{B/A} ⟶ NL_{C/B}`, and that chain
map is null homotopic: the homotopy
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy` sits in the single bidegree `(0, -1)` and
sends the local section `1 ⊗ d [t]` of `B ⊗[A[B]] Ω[A[B]/A]` attached to a section `t` of `B` to
the conormal class of the relation `[b t] - t` of the canonical presentation `B[C] ⟶ C`
(`Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`).

Over a ring the same homotopy is `NaiveCotangent.towerNullHomotopy`, and Stacks 07VC computes it
on the basis `Algebra.Generators.cotangentSpaceBasis` of `Ω_{A[B]/A} ⊗_{A[B]} B`: the basis
element `d[t]` goes to the class of `[φ(t)] - t`
(`NaiveCotangent.towerNullHomotopy_cotangentSpaceBasis`).  This file proves that the stalk at `x`
of the sheaf homotopy is that ring-level homotopy for the stalk maps `Aₓ → Bₓ → Cₓ`, on every one
of those basis elements, the two sides being compared through the identifications of Stacks 0D09
of the two terms of the stalk of a naive cotangent complex
(`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv` on the source and
`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv` on the target).

Together with the germ of the *source* section, which is
`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_X`,
this is the stalkwise description of the homotopy that the proof of **Stacks 0E1Y** needs: it is
the half of that proof which meets the ring-level computation of the cokernel of the homotopy,
`NaiveCotangent.bijective_towerCokernelMap`.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentTowerHomotopyStalk`: the stalk at `x` of the homotopy,
  as a map of abelian groups.  Restriction of scalars along `b` leaves the underlying sheaf of
  abelian groups of the target untouched, so this is the stalk of the morphism of sheaves of
  `B`-modules read additively; the two identifications of Stacks 0D09 being linear over different
  rings, an additive map is what can be compared.

## Main results

* `Stacks.SheafOfModules.canonicalStalkRingEquiv_germ_towerHomotopyRelation`: under the
  identification `(B[C])ₓ ≅ Bₓ[Cₓ]` the germ of the relation `[b t] - t` is the polynomial
  `X_{b(tₓ)} - C tₓ`.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_germ_towerHomotopyRelation`:
  **the germ of the target section.**  The germ of the conormal class of `[b t] - t` is the class
  of `X_{b(tₓ)} - C tₓ` in the conormal module of the canonical presentation of `Cₓ` over `Bₓ`.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_germ_towerHomotopy_X`
  and `..._towerHomotopyStalk_moduleGerm_X`: the value of the homotopy, and of its
  stalk, on the germ of the local section `1 ⊗ d [t]` is
  `NaiveCotangent.towerNullHomotopy` of the basis element indexed by the germ of `t`.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_cotangentSpaceBasis`:
  **the stalk of the homotopy is the ring-level null homotopy on every basis element** of
  `Ω_{Aₓ[Bₓ]/Aₓ} ⊗_{Aₓ[Bₓ]} Bₓ`.  Every element of `Bₓ` is a germ
  (`TopCat.Presheaf.exists_germ_eq`), so the basis is exhausted by the germs of local sections
  and the preceding statement covers it.

## Implementation notes

The target of the homotopy is spelled with
`Stacks.Sites.FreeAlgebra.canonicalPresentation`, which is the spelling
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy` and the local formula for it use, while the
identification of its stalk is spelled with
`Stacks.SheafOfModules.presentation … (𝟙 _)`, which is the spelling the stalk lemmas use.  The
two are definitionally equal (`Stacks.SheafOfModules.presentation_id`) and the statements below
cross between them at the one place where the two halves meet, in the proof of
`naiveCotangentStalkCotangentEquiv_germ_towerHomotopyRelation`; the abbreviations
`Stacks.NaiveCotangentAffineStalkLegs.AA`, `pres`, `cSheaf` and `tSheaf` keep the statements
short enough to read.

As in the companion files on germs, the identity for the source is stated through the comparison
on sections rather than directly on the local section `1 ⊗ d [t]`, because
`Stacks.Sites.Conormal.tensorDifferential` is typed through `(conormalSequence …).X₂` and
unfolding that under a stalk exceeds the elaborator's budget.  Nothing of the kind is needed for
the target: `Stacks.Sites.Conormal.conormalClass` is typed through `.X₁`, whose stalk the
identification of Stacks 0D09 is literally about.

The `A_x`-algebra structure on `C_x` that `NaiveCotangent.towerNullHomotopy` consumes is the one
read off the composite `a ≫ b`, and the tower `Aₓ → Bₓ → Cₓ` is
`Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase` at that factorisation.

## References

* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the null homotopy of a
  tower over a ring.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), where the description is
  consumed.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical polynomial
  presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.RelativeDifferentialStalk (algebraStalk)
open Stacks.NaiveCotangentAffineStalkLegs (AA pres cSheaf tSheaf)

variable {T : TopCat.{u}} (B C : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (b : B ⟶ C) (x : T) (U : Opens T) (hx : x ∈ U)

/-- **The germ of the relation `[b t] - t`.**  Under the identification `(B[C])ₓ ≅ Bₓ[Cₓ]` of the
stalk of the free algebra with a polynomial algebra, the germ at `x` of the section
`[b t] - t` of `B[C]` over `U` is the polynomial `X_{b(tₓ)} - C tₓ`, whose class in `J/J²` is the
value of the ring-level homotopy of Stacks 07VC on the basis element indexed by `tₓ`.

The two summands are the variable half and the coefficient half of that identification,
`Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkRingEquiv_variable` and
`Stacks.SheafOfModules.canonicalStalkRingEquiv_coefficientMap`, and in both the germ is moved
across the morphism of sheaves by `TopCat.Presheaf.stalkFunctor_map_germ_apply`. -/
theorem canonicalStalkRingEquiv_germ_towerHomotopyRelation (t : ToType (B.obj.obj (op U))) :
    letI := algebraStalk b.hom x
    canonicalStalkRingEquiv B C x
        ((TopCat.Presheaf.germ
            (freeAlgebraSheaf (Opens.grothendieckTopology T) B
              (underlyingPresheaf (Opens.grothendieckTopology T) C)).obj U x hx).hom
          ((towerHomotopyRelation (Opens.grothendieckTopology T) B C b b (𝟙 B)
            (Category.id_comp b) (op U) t :
              ToType ((freeAlgebraSheaf (Opens.grothendieckTopology T) B
                (underlyingPresheaf (Opens.grothendieckTopology T) C)).obj.obj (op U))))) =
      MvPolynomial.X (algebraMap (ToType (TopCat.Presheaf.stalk B.obj x))
          (ToType (TopCat.Presheaf.stalk C.obj x))
          ((TopCat.Presheaf.germ B.obj U x hx).hom t)) -
        MvPolynomial.C ((TopCat.Presheaf.germ B.obj U x hx).hom t) := by
  let := algebraStalk b.hom x
  have hid : ((𝟙 B : B ⟶ B)).hom.app (op U) t = t := rfl
  rw [towerHomotopyRelation_coe, hid, map_sub, map_sub]
  refine congrArg₂ (· - ·) ?_ ?_
  · refine (Stacks.NaiveCotangentAffineStalkLegs.canonicalStalkRingEquiv_variable B C x U hx
      (b.hom.app (op U) t)).trans ?_
    exact congrArg MvPolynomial.X
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx b.hom t).symm
  · exact (congrArg (canonicalStalkRingEquiv B C x)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) B
          (underlyingPresheaf (Opens.grothendieckTopology T) C)).hom t).symm).trans
      (canonicalStalkRingEquiv_coefficientMap B C x _)

/-- **The germ of the target section of the homotopy.**  Under the identification of Stacks 0D09
of the stalk at `x` of the degree `-1` term of `NL_{C/B}` with the conormal module of the
canonical presentation of `Cₓ` over `Bₓ`, the germ of the conormal class of the relation
`[b t] - t` is the class of `X_{b(tₓ)} - C tₓ`.

This is the half of the stalkwise description of the homotopy that the germ lemmas for the
*source* do not supply.  The identification is the identification of the stalk of a conormal
sheaf with the conormal module of the stalks
(`Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv`, which carries the germ of a conormal
class to the conormal class of a germ), followed by the conormal map of the isomorphism of
presentations `(B[C])ₓ ≅ Bₓ[Cₓ]`; so the computation reduces to the germ of the relation itself,
which is `Stacks.SheafOfModules.canonicalStalkRingEquiv_germ_towerHomotopyRelation`. -/
theorem naiveCotangentStalkCotangentEquiv_germ_towerHomotopyRelation
    (t : ToType (B.obj.obj (op U))) :
    letI := algebraStalk b.hom x
    naiveCotangentStalkCotangentEquiv B C b x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (cSheaf B C b).val.presheaf U x hx
          (conormalClass.{u, u, u, u} (Opens.grothendieckTopology T) B (AA B C) C
            (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) B
              (underlyingPresheaf (Opens.grothendieckTopology T) C))
            (canonicalPresentation (Opens.grothendieckTopology T) B C b) (op U)
            (towerHomotopyRelation (Opens.grothendieckTopology T) B C b b (𝟙 B)
              (Category.id_comp b) (op U) t))) =
      Algebra.Extension.Cotangent.mk
        ⟨MvPolynomial.X (algebraMap (ToType (TopCat.Presheaf.stalk B.obj x))
                (ToType (TopCat.Presheaf.stalk C.obj x))
                ((TopCat.Presheaf.germ B.obj U x hx).hom t)) -
            MvPolynomial.C ((TopCat.Presheaf.germ B.obj U x hx).hom t),
          NaiveCotangent.X_sub_C_mem_ker (ToType (TopCat.Presheaf.stalk B.obj x))
            (ToType (TopCat.Presheaf.stalk C.obj x))
            ((TopCat.Presheaf.germ B.obj U x hx).hom t)⟩ := by
  let := algebraStalk b.hom x
  refine Eq.trans (naiveCotangentStalkCotangentEquiv_apply B C b x _) ?_
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map (canonicalStalkExtensionHom B C b x))
    (conormalSheafStalkLinearEquiv_germ_conormalClass (AA B C) C (pres B C b) x B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) B
        (underlyingPresheaf (Opens.grothendieckTopology T) C)) U hx
      (towerHomotopyRelation (Opens.grothendieckTopology T) B C b b (𝟙 B)
        (Category.id_comp b) (op U) t))) ?_
  refine Eq.trans (Algebra.Extension.Cotangent.map_mk (canonicalStalkExtensionHom B C b x) _) ?_
  exact congrArg Algebra.Extension.Cotangent.mk (Subtype.ext
    (canonicalStalkRingEquiv_germ_towerHomotopyRelation B C b x U hx t))

variable (A : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (a : A ⟶ B)

/-- **The stalk at `x` of the null homotopy of the tower `A ⟶ B ⟶ C`**, as a map of abelian
groups from the stalk of the degree `0` term of `NL_{B/A}` to the stalk of the degree `-1` term of
`NL_{C/B}`.  Restriction of scalars along `b` leaves the underlying sheaf of abelian groups of the
target untouched, so this is the stalk of the morphism of sheaves of `B`-modules; it is recorded
additively because the two identifications of Stacks 0D09 that it is compared through are linear
over different rings. -/
def naiveCotangentTowerHomotopyStalk :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (tSheaf A B a).val.presheaf x) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (cSheaf B C b).val.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (naiveCotangentTowerHomotopy.{u, u, u, u} (Opens.grothendieckTopology T) A B C a b a b
        (𝟙 B) (Category.id_comp b) (Category.comp_id a)).val)).hom

/-- The stalk of the homotopy carries the germ of a local section to the germ of its image. -/
theorem naiveCotangentTowerHomotopyStalk_moduleGerm (s : (tSheaf A B a).val.obj (op U)) :
    naiveCotangentTowerHomotopyStalk B C b x A a (moduleGerm (tSheaf A B a).val x U hx s) =
      moduleGerm (cSheaf B C b).val x U hx
        ((naiveCotangentTowerHomotopy.{u, u, u, u} (Opens.grothendieckTopology T) A B C a b a b
          (𝟙 B) (Category.id_comp b) (Category.comp_id a)).val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf B).obj).map
      (naiveCotangentTowerHomotopy.{u, u, u, u} (Opens.grothendieckTopology T) A B C a b a b
        (𝟙 B) (Category.id_comp b) (Category.comp_id a)).val) s

/-- **The germ of the value of the homotopy on the local section `1 ⊗ d [t]`.**  Under the
identification of Stacks 0D09 it is `NaiveCotangent.towerNullHomotopy` of the basis element of
`Ω_{Aₓ[Bₓ]/Aₓ} ⊗_{Aₓ[Bₓ]} Bₓ` indexed by the germ of `t`.

The local section is written as the image of `1 ⊗ d X_t` under the comparison on sections, which
is the spelling in which both halves of the computation are available: the homotopy's value on it
is `Stacks.SheafOfModules.naiveCotangentTowerHomotopy_sectionsTensorComparison_one_tmul_D_X`, and
the germ of that value is the preceding statement. -/
theorem naiveCotangentStalkCotangentEquiv_germ_towerHomotopy_X
    (t : ToType (B.obj.obj (op U))) :
    letI := algebraSections (Opens.grothendieckTopology T) A B a (op U)
    letI := algebraStalk a.hom x
    letI := algebraStalk b.hom x
    letI := algebraStalk (a ≫ b).hom x
    haveI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a x rfl
    naiveCotangentStalkCotangentEquiv B C b x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (cSheaf B C b).val.presheaf U x hx
          ((naiveCotangentTowerHomotopy.{u, u, u, u} (Opens.grothendieckTopology T) A B C a b a b
              (𝟙 B) (Category.id_comp b) (Category.comp_id a)).val.app (op U)
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology T) A B a (op U)
              ((1 : ToType (B.obj.obj (op U)))
                ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                    (ToType (B.obj.obj (op U)))).toExtension.Ring]
                  KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                    ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                      (ToType (B.obj.obj (op U)))).toExtension.Ring) (MvPolynomial.X t))))) =
      NaiveCotangent.towerNullHomotopy (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x)) (ToType (TopCat.Presheaf.stalk C.obj x))
        ((Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).cotangentSpaceBasis
            ((TopCat.Presheaf.germ B.obj U x hx).hom t)) := by
  let := algebraSections (Opens.grothendieckTopology T) A B a (op U)
  let := algebraStalk a.hom x
  let := algebraStalk b.hom x
  let := algebraStalk (a ≫ b).hom x
  have _ := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a x rfl
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv B C b x)
    (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (cSheaf B C b).val.presheaf U x hx)
      (naiveCotangentTowerHomotopy_sectionsTensorComparison_one_tmul_D_X.{u, u, u, u}
        (Opens.grothendieckTopology T) A B a (op U) C b a b (𝟙 B) (Category.id_comp b)
        (Category.comp_id a) t))) ?_
  refine Eq.trans (naiveCotangentStalkCotangentEquiv_germ_towerHomotopyRelation
    B C b x U hx t) ?_
  exact (NaiveCotangent.towerNullHomotopy_cotangentSpaceBasis
    (ToType (TopCat.Presheaf.stalk A.obj x)) (ToType (TopCat.Presheaf.stalk B.obj x))
    (ToType (TopCat.Presheaf.stalk C.obj x)) ((TopCat.Presheaf.germ B.obj U x hx).hom t)).symm

/-- **The stalk of the homotopy on the germ of the local section `1 ⊗ d [t]`**: it is
`NaiveCotangent.towerNullHomotopy` of the basis element indexed by the germ of `t`.  This is the
preceding statement read through
`Stacks.SheafOfModules.naiveCotangentTowerHomotopyStalk_moduleGerm`. -/
theorem naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_moduleGerm_X
    (t : ToType (B.obj.obj (op U))) :
    letI := algebraSections (Opens.grothendieckTopology T) A B a (op U)
    letI := algebraStalk a.hom x
    letI := algebraStalk b.hom x
    letI := algebraStalk (a ≫ b).hom x
    haveI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a x rfl
    naiveCotangentStalkCotangentEquiv B C b x
        (naiveCotangentTowerHomotopyStalk B C b x A a
          (moduleGerm (tSheaf A B a).val x U hx
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology T) A B a (op U)
              ((1 : ToType (B.obj.obj (op U)))
                ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                    (ToType (B.obj.obj (op U)))).toExtension.Ring]
                  KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                    ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                      (ToType (B.obj.obj (op U)))).toExtension.Ring) (MvPolynomial.X t))))) =
      NaiveCotangent.towerNullHomotopy (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x)) (ToType (TopCat.Presheaf.stalk C.obj x))
        ((Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).cotangentSpaceBasis
            ((TopCat.Presheaf.germ B.obj U x hx).hom t)) := by
  let := algebraSections (Opens.grothendieckTopology T) A B a (op U)
  let := algebraStalk a.hom x
  let := algebraStalk b.hom x
  let := algebraStalk (a ≫ b).hom x
  have _ := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a x rfl
  refine Eq.trans (congrArg (naiveCotangentStalkCotangentEquiv B C b x)
    (naiveCotangentTowerHomotopyStalk_moduleGerm B C b x U hx A a _)) ?_
  exact naiveCotangentStalkCotangentEquiv_germ_towerHomotopy_X
    B C b x U hx A a t

/-- **The stalk of the null homotopy of the tower is the ring-level null homotopy of Stacks 07VC,
on every basis element.**  Transporting a basis element `d[s]` of `Ω_{Aₓ[Bₓ]/Aₓ} ⊗_{Aₓ[Bₓ]} Bₓ`
into the stalk of the degree `0` term of `NL_{B/A}` along the identification of Stacks 0D09,
applying the stalk of the sheaf homotopy and transporting the result back along the identification
of the degree `-1` term of `NL_{C/B}` gives `NaiveCotangent.towerNullHomotopy` of `d[s]`.

The basis is indexed by `Bₓ` and every element of `Bₓ` is the germ of a section of `B`
(`TopCat.Presheaf.exists_germ_eq`), so this is the preceding statement at a section `t` with
`tₓ = s`, after the germ of the source section has been identified with the basis element by
`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_X`
and `Algebra.Generators.cotangentSpaceBasis_apply`. -/
theorem naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_cotangentSpaceBasis
    (s : ToType (TopCat.Presheaf.stalk B.obj x)) :
    letI := algebraStalk a.hom x
    letI := algebraStalk b.hom x
    letI := algebraStalk (a ≫ b).hom x
    haveI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a x rfl
    naiveCotangentStalkCotangentEquiv B C b x
        (naiveCotangentTowerHomotopyStalk B C b x A a
          ((naiveCotangentStalkCotangentSpaceEquiv A B a x).symm
            ((Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
              (ToType (TopCat.Presheaf.stalk B.obj x))).cotangentSpaceBasis s))) =
      NaiveCotangent.towerNullHomotopy (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x)) (ToType (TopCat.Presheaf.stalk C.obj x))
        ((Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).cotangentSpaceBasis s) := by
  let := algebraStalk a.hom x
  let := algebraStalk b.hom x
  let := algebraStalk (a ≫ b).hom x
  have _ := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A B C b (a ≫ b) a x rfl
  obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.obj s
  let := algebraSections (Opens.grothendieckTopology T) A B a (op U)
  have hsrc :=
    (naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_X A B a x U hx t).trans
      (Algebra.Generators.cotangentSpaceBasis_apply _ _).symm
  rw [← hsrc, AddEquiv.symm_apply_apply, hsrc]
  exact naiveCotangentStalkCotangentEquiv_towerHomotopyStalk_moduleGerm_X
    B C b x U hx A a t

end Stacks.SheafOfModules

end

end
