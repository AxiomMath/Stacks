module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGerm

/-!
# The germ of the degree `0` comparison on sections, on every element

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X`, let `U`
be an open of `X` and let `x` be a point of `U`.  Taking sections over `U` gives the canonical map

`NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)`

of `Stacks.SheafOfModules.sectionsNaiveCotangentComparison`, and taking stalks at `x` gives the
identification `NL_{B/A, x} = NL_{Bₓ/Aₓ}` of Stacks 0D09.  The companion file
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGerm` identifies the germ at `x` of the
degree `-1` component of the first with the conormal map of the morphism of extensions attached to
the square of germ maps, and identifies the degree `0` component on the elements `1 ⊗ d p` only.
This file removes that restriction: the degree `0` formula is proved here on a general element of
the cotangent space of the canonical presentation of `B(U)` over `A(U)`.

## Main results

* `Stacks.SheafOfModules.cotangentSpaceStalkLinearEquiv_germ_smul_tensorDifferential`: the
  identification of the stalk of `B ⊗[A] Ω[A/R]` with the cotangent space of the stalk extension
  carries the germ of `φ(s) • (1 ⊗ d f)` to the tensor of the image of the germ of `s` in `Bₓ`
  with `d (fₓ)`.  This is the one statement in the chain that mentions the identification
  `Aₓ/Iₓ ≅ Bₓ`, and it is stated over abstract sheaves of rings for that reason.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison`:
  the germ at `x` of the degree `0` component of the comparison on sections over `U` is the
  cotangent-space map of the morphism of extensions given by the germ maps, on every element.
  Together with
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_germ_sectionsConormalComparison`
  this identifies both components of the comparison on sections, which is what the proof of
  Stacks 0D0I needs in order to compare its sheaf-level comparison map with the stalkwise
  quasi-isomorphism of
  `Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom`.

## Implementation notes

**Everything is stated over abstract sheaves of rings and instantiated once.**  The concrete
presentation `A[B] ⟶ B` is a sheafification, and a term built at it by hand is expensive for the
elaborator: writing out the intermediate section-level identity as the type of a `have` and
rewriting the goal with it costs about `4.3` million heartbeats, which no budget allows.  The
whole of that intermediate step is therefore packaged into
`Stacks.SheafOfModules.cotangentSpaceStalkLinearEquiv_germ_smul_tensorDifferential`, whose
statement mentions only abstract sheaves and so is cheap; the concrete proof then instantiates it
and proceeds exactly as the degree `0` formula on `1 ⊗ d p` does.  The same identity assembled
from its three pieces at the concrete presentation costs about `0.6` million heartbeats, so the
packaging is what makes the step affordable rather than any change of mathematics.

**Why the scalar is carried by an element of the source.**  The degree `0` component of the
comparison on sections sends `b ⊗ d p` to `b • (1 ⊗ d (λ p))` with `b` a section of `B`, whereas
the identification of stalks is semilinear over the stalk of `A[B]`.  The formula is therefore
first proved with the scalar written as the image `φ(s)` of a section `s` of `A[B]`, where no
identification of the two actions is needed, and only then transported to a general `b` by
exhibiting `b` as the image of the variable `X_b` of the canonical presentation.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical polynomial
  presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

/-! ### Abstract ingredients -/

/-- **The identification `Aₓ/Iₓ ≅ Bₓ` undoes the germ map on classes.**  The class of a section
`s` of `A` over `U` goes, under the germ map `A(U)/I(U) → Aₓ/Iₓ` followed by `Aₓ/Iₓ ≅ Bₓ`, to the
image of the germ of `s` under the map on stalks.  Both steps are `Ideal.quotientMap` and the
quotient of a ring map, so the identity is definitional; what makes it worth naming is that the
concrete canonical presentation is a sheafification, where establishing the same identity in place
exhausts the elaborator's budget. -/
theorem stalkQuotientLinearEquiv_germQuotientₛₗ_mk {X : TopCat.{u}}
    {A B : X.Presheaf CommRingCat.{u}} (φ : A ⟶ B) (x : X)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ]
    (U : Opens X) (hx : x ∈ U) (s : A.obj (op U)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk φ x
    stalkQuotientLinearEquiv φ x
        (germQuotientₛₗ φ x U hx (Ideal.Quotient.mk (kernelIdeal φ (op U)) s)) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ).hom
        ((TopCat.Presheaf.germ A U x hx).hom s) := rfl

/-- **A scalar multiple of `1 ⊗ d f` is the class of the scalar tensored with `d f`.**  For
sections `s` and `f` of `A` over `U`, the local section `φ(s) • (1 ⊗ d f)` of `B ⊗[A] Ω[A/R]` is
the image under the unit of sheafification of `[s] ⊗ d f`.  This is
`Stacks.SheafOfModules.toAssociatedModule_quotient_mk_tmul` read at a universal differential. -/
theorem toAssociatedModule_smul_tensorDifferential {X : TopCat.{u}}
    (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (a : R ⟶ A) (φ : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (Y : (Opens X)ᵒᵖ)
    (s f : A.obj.obj Y) :
    (φ.hom.app Y).hom s •
        tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X) R A B a φ Y f =
      toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A B φ
        (tensorPresheaf φ.hom a.hom) Y
        ((Ideal.Quotient.mk (kernelIdeal φ.hom Y) s) ⊗ₜ[A.obj.obj Y]
          CommRingCat.KaehlerDifferential.d (f := a.hom.app Y) f) :=
  (toAssociatedModule_quotient_mk_tmul R A B a φ Y s
    (CommRingCat.KaehlerDifferential.d (f := a.hom.app Y) f)).symm

/-- **The germ of a scalar multiple of a universal differential.**  The identification of the
stalk at `x` of `B ⊗[A] Ω[A/R]` with the cotangent space `Bₓ ⊗[Aₓ] Ω[Aₓ/Rₓ]` of the stalk
extension carries the germ of the local section `φ(s) • (1 ⊗ d f)` to the tensor of the image of
the germ of `s` in `Bₓ` with `d (fₓ)`.

This is the whole of the degree `0` comparison on a scalar multiple, assembled where the terms are
small: with the concrete canonical presentation substituted, assembling the same identity from
`Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv_germ_tmul_d` and the two statements above
costs some three million heartbeats, whereas instantiating this one costs almost nothing. -/
theorem cotangentSpaceStalkLinearEquiv_germ_smul_tensorDifferential {X : TopCat.{u}}
    (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (a : R ⟶ A) (φ : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))] (U : Opens X) (hx : x ∈ U)
    (s f : A.obj.obj (op U)) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := Stacks.RelativeDifferentialStalk.algebraStalk φ.hom x
    cotangentSpaceStalkLinearEquiv R A B a φ x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (tensorDifferentialsSheaf (Opens.grothendieckTopology X) R A B a φ).val.presheaf U x hx
          ((φ.hom.app (op U)).hom s •
            tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X) R A B a φ (op U) f)) =
      (show ToType (TopCat.Presheaf.stalk B.obj x) from
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom
            ((TopCat.Presheaf.germ A.obj U x hx).hom s))
        ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x))
          ((TopCat.Presheaf.germ A.obj U x hx).hom f) := by
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := Stacks.RelativeDifferentialStalk.algebraStalk φ.hom x
  rw [toAssociatedModule_smul_tensorDifferential R A B a φ (op U) s f]
  refine Eq.trans (cotangentSpaceStalkLinearEquiv_germ_tmul_d R A B a φ x U hx
    (Ideal.Quotient.mk (kernelIdeal φ.hom (op U)) s) f) ?_
  exact congrArg (fun c : ToType (TopCat.Presheaf.stalk B.obj x) =>
      c ⊗ₜ[ToType (TopCat.Presheaf.stalk A.obj x)]
        KaehlerDifferential.D (ToType (TopCat.Presheaf.stalk R.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x)) ((TopCat.Presheaf.germ A.obj U x hx).hom f))
    (stalkQuotientLinearEquiv_germQuotientₛₗ_mk φ.hom x U hx s)

/-- The germ at `x` of a sum of sections of a presheaf of modules is the sum of the germs. -/
theorem moduleGerm_add {X : TopCat.{u}} {O : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} O)
    (x : X) (U : Opens X) (hx : x ∈ U) (s t : M.obj (op U)) :
    moduleGerm M x U hx (s + t) = moduleGerm M x U hx s + moduleGerm M x U hx t :=
  map_add _ s t

/-! ### The germ of the comparison on sections in degree `0` -/

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (x : X) (U : Opens X) (hx : x ∈ U)

/-- **Every section of `B` over `U` is the image of a variable of the canonical presentation.**
The structural map of the canonical presentation of `B(U)` over `A(U)` carries the variable `X_b`
to `b`. -/
theorem algebraMap_sections_mvPolynomialX :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    ∀ b : ToType (B.obj.obj (op U)),
      algebraMap ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
        (ToType (B.obj.obj (op U)))).toExtension.Ring) (ToType (B.obj.obj (op U)))
          (MvPolynomial.X b) = b := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  intro b
  refine Eq.trans (Algebra.Generators.algebraMap_apply (Algebra.Generators.self
    (ToType (A.obj.obj (op U))) (ToType (B.obj.obj (op U)))) (MvPolynomial.X b)) ?_
  exact MvPolynomial.aeval_X _ b

/-- **The germ of the degree `0` comparison, on `φ(s) ⊗ d p`.**  Under the identification of the
stalk at `x` of the degree `0` term of `NL_{B/A}` with the cotangent space of the canonical
presentation of `Bₓ` over `Aₓ` (Stacks 0D09), the germ at `x` of the degree `0` component of the
comparison on sections over `U` agrees with the cotangent-space map of the morphism of extensions
given by the germ maps, on the elements whose scalar is the image of a section of `A[B]`.

Writing the scalar this way is what makes the formula provable: the comparison on sections is
`B(U)`-linear while the identification of stalks is semilinear over the stalk of `A[B]`, and a
scalar of this shape is carried by both. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_presentation :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    letI := algebraGermComp A B a x U hx
    haveI := isScalarTower_germ A B a x U hx
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    ∀ (s : ToType ((freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj.obj (op U)))
      (p : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
        (ToType (B.obj.obj (op U)))).toExtension.Ring),
      naiveCotangentStalkCotangentSpaceEquiv A B a x
          (moduleGerm _ x U hx
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U)
              (((presentation (Opens.grothendieckTopology X) A B a
                    (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom.app
                  (op U)).hom s
                ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                    (ToType (B.obj.obj (op U)))).toExtension.Ring]
                  KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                    ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                      (ToType (B.obj.obj (op U)))).toExtension.Ring) p))) =
        Algebra.Extension.CotangentSpace.map (germSelfHom A B a x U hx)
          (((presentation (Opens.grothendieckTopology X) A B a
                (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom.app (op U)).hom s
            ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                (ToType (B.obj.obj (op U)))).toExtension.Ring]
              KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                  (ToType (B.obj.obj (op U)))).toExtension.Ring) p) := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGerm A x U hx
  let := algebraGerm B x U hx
  let := algebraGermComp A B a x U hx
  have _ := isScalarTower_germ A B a x U hx
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  intro s p
  have h := cotangentSpaceStalkLinearEquiv_germ_smul_tensorDifferential A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x U hx s
    (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) p)
  rw [sectionsTensorComparison_tmul.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U),
    naiveCotangentStalkCotangentSpaceEquiv_apply]
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (canonicalStalkExtensionHom A B a x)) h) ?_
  refine Eq.trans (Algebra.Extension.CotangentSpace.map_tmul
    (canonicalStalkExtensionHom A B a x) _ _) ?_
  refine Eq.trans ?_ (Algebra.Extension.CotangentSpace.map_tmul
    (germSelfHom A B a x U hx) _ p).symm
  refine congrArg₂ (fun (bb : ToType (stalk B.obj x))
      (qq : (Algebra.Generators.self (ToType (stalk A.obj x))
        (ToType (stalk B.obj x))).toExtension.Ring) =>
      bb ⊗ₜ[(Algebra.Generators.self (ToType (stalk A.obj x))
          (ToType (stalk B.obj x))).toExtension.Ring]
        KaehlerDifferential.D (ToType (stalk A.obj x))
          ((Algebra.Generators.self (ToType (stalk A.obj x))
            (ToType (stalk B.obj x))).toExtension.Ring) qq) ?_ ?_
  · exact (Algebra.algebraMap_self_apply _).trans
      (stalkFunctor_map_germ_apply U x hx
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom s)
  · exact canonicalStalkRingEquiv_germ_freeAlgebraSectionsMap A B x U hx p

/-- **The germ of the degree `0` comparison, on `b ⊗ d p`.**  The same formula for an arbitrary
section `b` of `B` over `U`, obtained from the previous one by writing `b` as the image of the
variable `X_b` of the canonical presentation. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_tmul :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    letI := algebraGermComp A B a x U hx
    haveI := isScalarTower_germ A B a x U hx
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    ∀ (b : ToType (B.obj.obj (op U)))
      (p : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
        (ToType (B.obj.obj (op U)))).toExtension.Ring),
      naiveCotangentStalkCotangentSpaceEquiv A B a x
          (moduleGerm _ x U hx
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U)
              (b ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                  (ToType (B.obj.obj (op U)))).toExtension.Ring]
                KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                  ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                    (ToType (B.obj.obj (op U)))).toExtension.Ring) p))) =
        Algebra.Extension.CotangentSpace.map (germSelfHom A B a x U hx)
          (b ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
              (ToType (B.obj.obj (op U)))).toExtension.Ring]
            KaehlerDifferential.D (ToType (A.obj.obj (op U)))
              ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                (ToType (B.obj.obj (op U)))).toExtension.Ring) p) := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGerm A x U hx
  let := algebraGerm B x U hx
  let := algebraGermComp A B a x U hx
  have _ := isScalarTower_germ A B a x U hx
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  intro b p
  have h := naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_presentation
    A B a x U hx
    (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) (MvPolynomial.X b)) p
  rwa [presentation_freeAlgebraSectionsMap A B a U (MvPolynomial.X b),
    algebraMap_sections_mvPolynomialX A B a U b] at h

/-- **The germ of the degree `0` comparison is the degree `0` comparison of stalks.**  Under the
identification of the stalk at `x` of the degree `0` term of `NL_{B/A}` with the cotangent space
of the canonical presentation of `Bₓ` over `Aₓ` (Stacks 0D09), the germ at `x` of the degree `0`
component of the comparison on sections over `U` is the cotangent-space map of the morphism of
extensions given by the germ maps.

This is the degree `0` counterpart of
`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_germ_sectionsConormalComparison`, and
with it both components of the comparison on sections are identified.  The elements `b ⊗ d p`
generate the cotangent space as an abelian group
(`Stacks.NaiveCotangent.cotangentSpace_hom_ext`), so the formula on them determines it. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    letI := algebraGermComp A B a x U hx
    haveI := isScalarTower_germ A B a x U hx
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    ∀ z : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension.CotangentSpace,
      naiveCotangentStalkCotangentSpaceEquiv A B a x
          (moduleGerm _ x U hx
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U)
              z)) =
        Algebra.Extension.CotangentSpace.map (germSelfHom A B a x U hx) z := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGerm A x U hx
  let := algebraGerm B x U hx
  let := algebraGermComp A B a x U hx
  have _ := isScalarTower_germ A B a x U hx
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  refine fun z => DFunLike.congr_fun (Stacks.NaiveCotangent.cotangentSpace_hom_ext
    (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension
    (AddMonoidHom.mk' (fun w => naiveCotangentStalkCotangentSpaceEquiv A B a x
      (moduleGerm _ x U hx
        (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U) w)))
      (fun w w' => ?_))
    (Algebra.Extension.CotangentSpace.map (germSelfHom A B a x U hx)).toAddMonoidHom
    (naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_tmul A B a x U hx)) z
  rw [map_add (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U)),
    moduleGerm_add]
  exact map_add (naiveCotangentStalkCotangentSpaceEquiv A B a x) _ _

end Stacks.SheafOfModules

end

end
