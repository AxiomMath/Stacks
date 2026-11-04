module

public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Homology.TwoTermComplex.Ext
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import StacksFrontier.RingTheory.NaiveCotangent.ExtCokernelLinear

/-!
# Ext of a naive cotangent complex

For a polynomial presentation of an algebra, the first Ext group of its naive cotangent
complex is the cokernel of the map on dual modules induced by the conormal differential.

## Main definitions

* `conormalHomExtClass` is the Ext class corresponding to a conormal functional.

## Main results

* `extOne_naiveCotangentComplex_addEquiv_cokernel` computes its first Ext group.
* `extOne_naiveCotangentComplex_linearEquiv_cokernel` is the same comparison as an
  equivalence of `B`-modules; the additive version above is its underlying additive
  equivalence, and `conormalHomExtClass_eq` identifies the Ext class of a conormal functional
  with the explicit cocycle built from that functional.
* `Algebra.Extension.cotangentComplex` is Mathlib's differential of the naive cotangent
  complex of a presentation, which is the complex of **Stacks 0GPU**.

## Implementation notes

The source's `NL(α)` is `NaiveCotangent.NL P`. For the derived-category Ext API, we realize
this existing two-term complex as the mapping cone of its differential between complexes
concentrated in degree zero; thus its conormal module lies in degree `-1` and its cotangent
space lies in degree `0`. The categorical cokernel in the source is represented by the quotient
of the target linear-Hom module by the range of precomposition with this differential.

## References

* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
-/

public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe uA uB uι uN

add_to_stacks 0GPU "presentation_complex" Algebra.Extension.cotangentComplex

namespace NaiveCotangent
-- Keep the biproduct instance used in the statements. The homotopy-cofiber imports needed by
-- the proofs otherwise select ModuleCat's direct instance instead.
attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

section ExtOneProofInstances

private theorem extOneComparisonAux
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N] :
    Nonempty (DerivedCategory.Ext
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat.{max uA uB uι uN} B) ℤ ⥤ _).obj
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).map
              (ModuleCat.ofHom
                (ULift.moduleEquiv.{uB, max (max uA uB) uι,
                  max uA uB uι uN}.symm.toLinearMap.comp
                  ((NaiveCotangent.NL P).d.comp
                    ULift.moduleEquiv.{uB, max uA uι,
                      max uA uB uι uN}.toLinearMap))))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
          (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 ≃+
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range
        ((LinearMap.lcomp B N (NaiveCotangent.NL P).d) :
          (P.toExtension.CotangentSpace →ₗ[B] N) →ₗ[B]
            (P.toExtension.Cotangent →ₗ[B] N)))) :=
  ⟨(extOne_naiveCotangentComplex_linearEquiv_cokernel P).toAddEquiv⟩
/-- The private comparison construction is exposed as an existence result so the public
equivalence can be defined after the proof-only instance scope has ended. -/
public theorem extOneComparisonAux_exists
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N] : Nonempty (
    DerivedCategory.Ext
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat.{max uA uB uι uN} B) ℤ ⥤ _).obj
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).map
              (ModuleCat.ofHom
                (ULift.moduleEquiv.{uB, max (max uA uB) uι,
                  max uA uB uι uN}.symm.toLinearMap.comp
                  ((NaiveCotangent.NL P).d.comp
                    ULift.moduleEquiv.{uB, max uA uι,
                      max uA uB uι uN}.toLinearMap))))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
          (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 ≃+
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range
        ((LinearMap.lcomp B N (NaiveCotangent.NL P).d) :
          (P.toExtension.CotangentSpace →ₗ[B] N) →ₗ[B]
            (P.toExtension.Cotangent →ₗ[B] N)))) := extOneComparisonAux P
end ExtOneProofInstances

@[expose] public noncomputable section

/-- The comparison which computes the first Ext group of the naive cotangent complex of a
polynomial presentation. On the right, the cokernel is represented as the quotient by the
range of precomposition with the conormal differential.

It is the underlying additive equivalence of
`extOne_naiveCotangentComplex_linearEquiv_cokernel`, so the two cannot drift apart; use that
one for anything involving scalars. -/
@[stacks 0GPU "ext_cokernel"]
public noncomputable def extOne_naiveCotangentComplex_addEquiv_cokernel
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N] :
    DerivedCategory.Ext
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat.{max uA uB uι uN} B) ℤ ⥤ _).obj
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).map
              (ModuleCat.ofHom
                (ULift.moduleEquiv.{uB, max (max uA uB) uι,
                  max uA uB uι uN}.symm.toLinearMap.comp
                  ((NaiveCotangent.NL P).d.comp
                    ULift.moduleEquiv.{uB, max uA uι,
                      max uA uB uι uN}.toLinearMap))))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
          (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 ≃+
      ((P.toExtension.Cotangent →ₗ[B] N) ⧸ LinearMap.range
        ((LinearMap.lcomp B N (NaiveCotangent.NL P).d) :
          (P.toExtension.CotangentSpace →ₗ[B] N) →ₗ[B]
            (P.toExtension.Cotangent →ₗ[B] N))) :=
  (extOne_naiveCotangentComplex_linearEquiv_cokernel P).toAddEquiv

/-- The first Ext class represented by a homomorphism out of the conormal module. -/
public noncomputable def conormalHomExtClass
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (f : P.toExtension.Cotangent →ₗ[B] N) :
    DerivedCategory.Ext
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat.{max uA uB uι uN} B) ℤ ⥤ _).obj
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).map
              (ModuleCat.ofHom
                (ULift.moduleEquiv.{uB, max (max uA uB) uι,
                  max uA uB uι uN}.symm.toLinearMap.comp
                  ((NaiveCotangent.NL P).d.comp
                    ULift.moduleEquiv.{uB, max uA uι,
                      max uA uB uι uN}.toLinearMap))))))
        ((DerivedCategory.singleFunctor (ModuleCat.{max uA uB uι uN} B) 0).obj
          (ModuleCat.of B (ULift.{max uA uB uι uN} N))) 1 :=
  (extOne_naiveCotangentComplex_addEquiv_cokernel P).symm
    (Submodule.Quotient.mk f)

/-- `conormalHomExtClass P f` is the image of the residue class of `f` under the inverse of the
linear comparison. -/
private theorem conormalHomExtClass_eq_symm_mk
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (f : P.toExtension.Cotangent →ₗ[B] N) :
    conormalHomExtClass P f =
      (extOne_naiveCotangentComplex_linearEquiv_cokernel P).symm (Submodule.Quotient.mk f) :=
  rfl

/-- Under the Ext--cokernel comparison, the class represented by `f` maps to the residue
class of `f`. -/
public lemma extOne_naiveCotangentComplex_addEquiv_cokernel_apply_conormalHomExtClass
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (f : P.toExtension.Cotangent →ₗ[B] N) :
    extOne_naiveCotangentComplex_addEquiv_cokernel P (conormalHomExtClass P f) =
      Submodule.Quotient.mk f := by
  simp [conormalHomExtClass]

/-- The additive comparison is the underlying additive equivalence of the linear one. -/
public lemma extOne_naiveCotangentComplex_addEquiv_cokernel_eq
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N] :
    extOne_naiveCotangentComplex_addEquiv_cokernel (N := N) P =
      (extOne_naiveCotangentComplex_linearEquiv_cokernel (N := N) P).toAddEquiv :=
  rfl

/-- **The Ext class of a conormal functional is an explicit cocycle.** It is the class of the
cochain map which is the functional on the conormal summand of the mapping cone and zero on
the cotangent-space summand, `NaiveCotangent.presentationExtOneClass`.

This is the statement that the additive comparison could not support. Unlike
`extOne_naiveCotangentComplex_addEquiv_cokernel_apply_conormalHomExtClass`, whose proof is
`simp [conormalHomExtClass]` because `conormalHomExtClass` is defined as the inverse image of
a residue class, the right-hand side here is built from `f` without reference to the
comparison. -/
public lemma conormalHomExtClass_eq
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (f : P.toExtension.Cotangent →ₗ[B] N) :
    conormalHomExtClass P f = presentationExtOneClass P f :=
  presentationCokernelExtOneEquiv_symm_mk P f

/-- The Ext class of a conormal functional is additive in the functional. -/
public lemma conormalHomExtClass_add
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (f g : P.toExtension.Cotangent →ₗ[B] N) :
    conormalHomExtClass P (f + g) = conormalHomExtClass P f + conormalHomExtClass P g := by
  rw [conormalHomExtClass_eq_symm_mk, conormalHomExtClass_eq_symm_mk,
    conormalHomExtClass_eq_symm_mk, ← map_add]
  rfl

/-- **The Ext class of a conormal functional is `B`-linear in the functional.** This is what
the additive comparison could not give, and what the tangent-space clauses of Stacks 0DY3,
0DY4 and 0ET4 need. -/
public lemma conormalHomExtClass_smul
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (b : B) (f : P.toExtension.Cotangent →ₗ[B] N) :
    conormalHomExtClass P (b • f) = b • conormalHomExtClass P f := by
  rw [conormalHomExtClass_eq_symm_mk, conormalHomExtClass_eq_symm_mk, ← map_smul]
  rfl

/-- **The kernel of the class map.** The Ext class of a conormal functional vanishes exactly
when the functional factors through the conormal differential. -/
public lemma conormalHomExtClass_eq_zero_iff
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N]
    (f : P.toExtension.Cotangent →ₗ[B] N) :
    conormalHomExtClass P f = 0 ↔
      ∃ g : P.toExtension.CotangentSpace →ₗ[B] N, f = g.comp (NaiveCotangent.NL P).d := by
  rw [conormalHomExtClass_eq_symm_mk, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, hg.symm⟩⟩

/-- Every first extension class of the naive cotangent complex is the class of a conormal
functional. -/
public lemma surjective_conormalHomExtClass
    {A : Type uA} {B : Type uB} {ι : Type uι} {N : Type uN}
    [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Generators A B ι) [AddCommGroup N] [Module B N] :
    Function.Surjective (conormalHomExtClass (N := N) P) :=
  (extOne_naiveCotangentComplex_addEquiv_cokernel P).symm.surjective.comp
    (Submodule.Quotient.mk_surjective _)

end

end NaiveCotangent
end
