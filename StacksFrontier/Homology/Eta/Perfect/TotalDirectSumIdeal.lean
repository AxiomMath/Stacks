module

public import StacksFrontier.Homology.Eta.Perfect.DirectSum

/-!
# The canonical total obstruction ideal of the décalage of a complex

Let `A` be a commutative ring, let `f ∈ A` be a nonzerodivisor and let `M^•` be a bounded
complex of finite free `A`-modules, written in chosen bases as a `BoundedComplex A`, whose
determinantal ideals `I_i(M^•, f)` are all principal.

Two descriptions of the degreewise obstruction ideals of `M^•` in `A ⧸ fA` are available.  More
on Algebra, Tag 0GSW works with the ideal `J_i(M^•, f)` defined canonically as the infimum of
the ideals having the universal property of Tag 0F80 for the reduction modulo `f` of the graph
map `(1, dⁱ)` on the degree-`i` décalage term; this is `etaDirectSumIdeal`.  More on Algebra,
Tag 0F81 asserts the *existence* of a family of ideals with that universal property and proves
all the finiteness and vanishing statements one wants of them.

This file reconciles the two.  An ideal with the universal property is unique, so the family
produced by Tag 0F81 is the canonical one and every conclusion of that tag holds for
`J_i(M^•, f)`.  In particular the *total* obstruction ideal
`J(M^•, f) = ∑ᵢ J_i(M^•, f) ⊆ A ⧸ fA`
is finitely generated, the quotient map `A ⧸ fA → (A ⧸ fA) ⧸ J(M^•, f)` is of finite
presentation, the cohomology of the décalage of `M^•` becomes finite projective over
`(A ⧸ fA) ⧸ J(M^•, f)`, and `J(M^•, f)` dies after localizing at a prime containing `f` at
which the cohomology of `M^•` is free.

## Main definitions

* `Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal`: the total obstruction ideal
  `J(M^•, f) = ⨆ᵢ J_i(M^•, f)` of `A ⧸ fA`.

## Main results

* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_le_ker_iff`: an ideal with the
  universal property of Tag 0F80 for the reduced graph map in degree `i` is `J_i(M^•, f)`.
* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_le_ker_iff`: under principality of the
  determinantal ideals, `J_i(M^•, f)` itself has that universal property.
* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_fg`,
  `Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal_fg`: both ideals are finitely
  generated.
* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_bot_of_rank_eq_zero`: the degrees in
  which `M^•` vanishes contribute nothing to the sum.
* `Stacks.Decalage.DirectSumIdeal.finitePresentation_quotient_mk_etaTotalDirectSumIdeal`: the
  closed immersion cut out by `J(M^•, f)` in `Spec(A ⧸ fA)` is of finite presentation.
* `Stacks.Decalage.DirectSumIdeal.subsingleton_localizedModule_etaTotal_of_free_homology`:
  `J(M^•, f)` localizes to zero at a prime containing `f` at which every cohomology module of
  `M^•` is free.
* `Stacks.Decalage.DirectSumIdeal.finite_projective_etaHomology_quotient_etaTotalDirectSumIdeal`:
  over `(A ⧸ fA) ⧸ J(M^•, f)` every cohomology module of the décalage `η_f M^•` is finite
  projective.
* `Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_eq_baseChange`: the degreewise
  obstruction ideal extends along a flat ring map, `J_i(M^•, f) · (B ⧸ φ(f)B)
  = J_i(M^• ⊗_A B, φ(f))`.
* `Stacks.Decalage.DirectSumIdeal.map_etaDirectSumIdeal_unit_mul_eq`: the degreewise obstruction
  ideal is unchanged by replacing the equation `f` with a unit multiple `u·f`,
  `J_i(M^•, u·f) = J_i(M^•, f)`, read across the identification `A ⧸ u·fA ≃+* A ⧸ fA` of the
  two quotients by one and the same ideal.

## The rôle of this file in Tag 0GTZ

More on Flatness, Tag 0GTZ asserts, for a good triple `(X, D, M)`, the existence of a closed
immersion `i : T → D` of finite presentation whose source scheme-theoretically contains
`D ∩ W`, where `W ⊂ X` is the maximal open over which the cohomology sheaves of `M` are locally
free, together with two statements about `Li^*Lη_I M`.  The ideal `J(M^•, f)` of this file is
the ideal cutting `T` out on a good affine chart `(U, A, f, M^•)`, which is where the proof of
that tag begins.  The finite presentation of `i` and part (1) of the tag are read off that
chart-local description in
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme`, which is where the
`@[stacks 0GTZ]` attribute sits; nothing here carries it, this file being purely about the
ideal of one chart.

Two of the three compatibilities the gluing of those chart-local closed subschemes needs are
the last two results listed above: the obstruction ideal extends along the flat ring map
`A → A_g` of a restriction of charts, and it does not change when the equation of the divisor
is replaced by the unit multiple that a second chart's equation is.  The third, the agreement
of the obstruction ideals of two charts whose complexes merely become isomorphic in the derived
category, is Tag 0GSW,
`Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_derived_iso`.

## Implementation notes

Uniqueness of an ideal with the universal property of Tag 0F80 is the one-line argument that
each of two such ideals is contained in the kernel of the quotient map by the other.  It is
proved for an arbitrary predicate on algebras, since no property of the predicate is used.

Only the universal property over algebras in the *same* universe as `A` is used, which is the
universe in which `etaDirectSumIdeal` takes its infimum; the two-universe form of Tag 0F81 is
instantiated accordingly.

## References

* [Stacks Project, Tag 0GSW](https://stacks.math.columbia.edu/tag/0GSW)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0F80](https://stacks.math.columbia.edu/tag/0F80)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Decalage.DirectSumIdeal

variable {A : Type u} [CommRing A]

/-- Two ideals with one and the same universal property among algebras over a ring are equal:
each is contained in the kernel of the quotient map by the other, that kernel being the other
ideal.  No property of the predicate `P` is used. -/
public theorem eq_of_le_ker_iff {R : Type u} [CommRing R]
    (P : (D : Type u) → [CommRing D] → [Algebra R D] → Prop) {J K : Ideal R}
    (hJ : ∀ (D : Type u) [CommRing D] [Algebra R D],
      J ≤ RingHom.ker (algebraMap R D) ↔ P D)
    (hK : ∀ (D : Type u) [CommRing D] [Algebra R D],
      K ≤ RingHom.ker (algebraMap R D) ↔ P D) :
    J = K := by
  have key : ∀ {J K : Ideal R},
      (∀ (D : Type u) [CommRing D] [Algebra R D], J ≤ RingHom.ker (algebraMap R D) ↔ P D) →
      (∀ (D : Type u) [CommRing D] [Algebra R D], K ≤ RingHom.ker (algebraMap R D) ↔ P D) →
      J ≤ K := by
    intro J K hJ hK
    have hker : RingHom.ker (algebraMap R (R ⧸ K)) = K := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact ((hJ (R ⧸ K)).mpr ((hK (R ⧸ K)).mp hker.ge)).trans hker.le
  exact le_antisymm (key hJ hK) (key hK hJ)

/-- The definition of `J_i(M^•, f)` as the infimum of the ideals of `A ⧸ fA` with the universal
property of Tag 0F80 for the reduction modulo `f` of the graph map `(1, dⁱ)` on the degree-`i`
décalage term of `M^•`. -/
public theorem etaDirectSumIdeal_eq_sInf (C : BoundedComplex A) (f : A) (i : ℤ) :
    etaDirectSumIdeal C f i =
      sInf {J : Ideal (A ⧸ Ideal.span {f}) |
        ∀ (D : Type u) [CommRing D] [Algebra (A ⧸ Ideal.span {f}) D],
          J ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) D) ↔
            Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
              (ObstructionIdeal.etaReductionMap C f i) D} :=
  rfl

/-- **An ideal with the universal property of Tag 0F80 for the reduced graph map is
`J_i(M^•, f)`.**  Such an ideal is unique, hence equal to the infimum of all of them, which is
how `J_i(M^•, f)` is defined. -/
public theorem etaDirectSumIdeal_eq_of_le_ker_iff (C : BoundedComplex A) (f : A) (i : ℤ)
    {J : Ideal (A ⧸ Ideal.span {f})}
    (hJ : ∀ (D : Type u) [CommRing D] [Algebra (A ⧸ Ideal.span {f}) D],
      J ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) D) ↔
        Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
          (ObstructionIdeal.etaReductionMap C f i) D) :
    etaDirectSumIdeal C f i = J := by
  rw [etaDirectSumIdeal_eq_sInf]
  refine le_antisymm (sInf_le hJ) (le_sInf fun K hK => ?_)
  exact (eq_of_le_ker_iff
    (fun D _ _ => Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
      (ObstructionIdeal.etaReductionMap C f i) D) hJ hK).le

/-- **The total obstruction ideal `J(M^•, f) = ∑ᵢ J_i(M^•, f) ⊆ A ⧸ fA`** of a bounded complex
of finite free `A`-modules and a nonzerodivisor `f ∈ A`.  When the determinantal ideals
`I_i(M^•, f)` are principal this is the ideal of More on Algebra, Tag 0F81: the closed subscheme
it cuts out in `Spec(A ⧸ fA)` is the universal one over which the décalage `η_f M^•` has
locally free cohomology. -/
public def etaTotalDirectSumIdeal (C : BoundedComplex A) (f : A) :
    Ideal (A ⧸ Ideal.span {f}) :=
  ⨆ i : ℤ, etaDirectSumIdeal C f i

/-- Tag 0F81 restated for the canonical obstruction ideals of Tag 0GSW.  The family of ideals
the tag produces has the universal property that defines `J_i(M^•, f)`, hence is that family,
and its sum is `J(M^•, f)`. -/
private theorem etaDirectSumIdeal_spec (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) :
    (∀ i : ℤ, (etaDirectSumIdeal C f i).FG) ∧
    (∀ i : ℤ, ∀ (D : Type u) [CommRing D] [Algebra (A ⧸ Ideal.span {f}) D],
      etaDirectSumIdeal C f i ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) D) ↔
        Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
          (ObstructionIdeal.etaReductionMap C f i) D) ∧
    (∀ i : ℤ, C.rank i = 0 → C.rank (i + 1) = 0 → etaDirectSumIdeal C f i = ⊥) ∧
    (etaTotalDirectSumIdeal C f).FG ∧
    RingHom.FinitePresentation (Ideal.Quotient.mk (etaTotalDirectSumIdeal C f)) ∧
    (∀ (p : Ideal A) [p.IsPrime], f ∈ p →
      (∀ i : ℤ, Module.Free (Localization.AtPrime p)
        ((ObstructionIdeal.associatedComplex (C.baseChange
          (algebraMap A (Localization.AtPrime p)))).homology i)) →
      Subsingleton (LocalizedModule p.primeCompl (etaTotalDirectSumIdeal C f))) ∧
    (∀ i : ℤ,
      ∃ hfin : Module.Finite ((A ⧸ Ideal.span {f}) ⧸ etaTotalDirectSumIdeal C f)
        ((((ModuleCat.extendScalars
            ((Ideal.Quotient.mk (etaTotalDirectSumIdeal C f)).comp
              (Ideal.Quotient.mk (Ideal.span {f})))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (EtaComplex.etaObject f (ObstructionIdeal.associatedComplex C))).homology i),
        letI := hfin
        Module.Projective ((A ⧸ Ideal.span {f}) ⧸ etaTotalDirectSumIdeal C f)
          ((((ModuleCat.extendScalars
              ((Ideal.Quotient.mk (etaTotalDirectSumIdeal C f)).comp
                (Ideal.Quotient.mk (Ideal.span {f})))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (EtaComplex.etaObject f (ObstructionIdeal.associatedComplex C))).homology i)) := by
  obtain ⟨Jᵢ, J, hfg, hJ, hzero, hsup, hfgJ, -, hfp, -, hvanish, hlift, hproj⟩ :=
    ObstructionIdeal.exists_fg_obstructionIdeal_with_finiteProjective_etaHomology.{u, u}
      C f hf hI
  have hJi : Jᵢ = fun i => etaDirectSumIdeal C f i :=
    funext fun i => (etaDirectSumIdeal_eq_of_le_ker_iff C f i (hJ i)).symm
  subst hJi
  have hsup' : J = etaTotalDirectSumIdeal C f := hsup
  subst hsup'
  exact ⟨hfg, hJ, hzero, hfgJ, hfp,
    fun p hp hfmem hfree => hvanish p (hlift p hfmem hfree), hproj⟩

variable (C : BoundedComplex A) (f : A) (hf : IsRegular f)
  (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal)

include hf hI

/-- **The universal property of `J_i(M^•, f)`.**  When the determinantal ideals `I_i(M^•, f)`
are principal, an `A ⧸ fA`-algebra `D` kills `J_i(M^•, f)` exactly when the reduction modulo `f`
of the graph map `(1, dⁱ)` identifies, over `D`, the degree-`i` décalage term with the direct
sum of the two submodules it maps into.  This is the universal property of More on Algebra, Tag
0F80 as it is used in Tag 0F81. -/
public theorem etaDirectSumIdeal_le_ker_iff (i : ℤ) (D : Type u) [CommRing D]
    [Algebra (A ⧸ Ideal.span {f}) D] :
    etaDirectSumIdeal C f i ≤ RingHom.ker (algebraMap (A ⧸ Ideal.span {f}) D) ↔
      Stacks.SplitInjectionDirectSum.IdentifiesDirectSum
        (ObstructionIdeal.etaReductionMap C f i) D :=
  (etaDirectSumIdeal_spec C f hf hI).2.1 i D

/-- The degreewise obstruction ideal `J_i(M^•, f)` is finitely generated. -/
public theorem etaDirectSumIdeal_fg (i : ℤ) : (etaDirectSumIdeal C f i).FG :=
  (etaDirectSumIdeal_spec C f hf hI).1 i

/-- A degree in which `M^•` and its successor both vanish contributes nothing to the total
obstruction ideal. -/
public theorem etaDirectSumIdeal_eq_bot_of_rank_eq_zero {i : ℤ} (h : C.rank i = 0)
    (h' : C.rank (i + 1) = 0) : etaDirectSumIdeal C f i = ⊥ :=
  (etaDirectSumIdeal_spec C f hf hI).2.2.1 i h h'

/-- The total obstruction ideal `J(M^•, f)` is finitely generated: only the finitely many
degrees in which `M^•` is nonzero contribute to the sum, and each contribution is finitely
generated. -/
public theorem etaTotalDirectSumIdeal_fg : (etaTotalDirectSumIdeal C f).FG :=
  (etaDirectSumIdeal_spec C f hf hI).2.2.2.1

/-- **The closed immersion cut out by the total obstruction ideal is of finite presentation.**
The quotient map `A ⧸ fA → (A ⧸ fA) ⧸ J(M^•, f)` is surjective with finitely generated kernel,
so it is a ring map of finite presentation; this is the ring map `A ⧸ fA → C` of More on
Algebra, Tag 0F81. -/
public theorem finitePresentation_quotient_mk_etaTotalDirectSumIdeal :
    RingHom.FinitePresentation (Ideal.Quotient.mk (etaTotalDirectSumIdeal C f)) :=
  (etaDirectSumIdeal_spec C f hf hI).2.2.2.2.1

/-- **The total obstruction ideal vanishes where the cohomology of `M^•` is free.**  At a prime
`p` containing `f` at which every cohomology module of `M^•` becomes a free module over the
local ring, the localization of `J(M^•, f)` is zero: the cycles of `M^•` lift modulo `f` at such
a prime, by More on Algebra, Tag 0F81, and the obstruction ideal dies exactly there. -/
public theorem subsingleton_localizedModule_etaTotal_of_free_homology
    (p : Ideal A) [p.IsPrime] (hfmem : f ∈ p)
    (hfree : ∀ i : ℤ, Module.Free (Localization.AtPrime p)
      ((ObstructionIdeal.associatedComplex (C.baseChange
        (algebraMap A (Localization.AtPrime p)))).homology i)) :
    Subsingleton (LocalizedModule p.primeCompl (etaTotalDirectSumIdeal C f)) :=
  (etaDirectSumIdeal_spec C f hf hI).2.2.2.2.2.1 p hfmem hfree

/-- **The cohomology of the décalage is finite projective over the total obstruction
quotient.**  Every cohomology module of `η_f M^•` becomes a finite projective module after
extension of scalars along `A → (A ⧸ fA) ⧸ J(M^•, f)`.  This is the conclusion of More on
Algebra, Tag 0F81 for the canonical ideal. -/
public theorem finite_projective_etaHomology_quotient_etaTotalDirectSumIdeal (i : ℤ) :
    ∃ hfin : Module.Finite ((A ⧸ Ideal.span {f}) ⧸ etaTotalDirectSumIdeal C f)
      ((((ModuleCat.extendScalars
          ((Ideal.Quotient.mk (etaTotalDirectSumIdeal C f)).comp
            (Ideal.Quotient.mk (Ideal.span {f})))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (EtaComplex.etaObject f (ObstructionIdeal.associatedComplex C))).homology i),
      letI := hfin
      Module.Projective ((A ⧸ Ideal.span {f}) ⧸ etaTotalDirectSumIdeal C f)
        ((((ModuleCat.extendScalars
            ((Ideal.Quotient.mk (etaTotalDirectSumIdeal C f)).comp
              (Ideal.Quotient.mk (Ideal.span {f})))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (EtaComplex.etaObject f (ObstructionIdeal.associatedComplex C))).homology i) :=
  (etaDirectSumIdeal_spec C f hf hI).2.2.2.2.2.2 i

end Stacks.Decalage.DirectSumIdeal

end

/-! ## Flat base change of the degreewise obstruction ideal -/

section FlatBaseChange

@[expose] public noncomputable section

namespace Stacks.Decalage.DirectSumIdeal

universe u

/-- The reduction of a ring map modulo `f`: the map `A ⧸ fA → B ⧸ φ(f)B` induced by
`φ : A →+* B`, which carries the class of `a` to the class of `φ a`. -/
public def quotientSpanMap {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (f : A) :
    A ⧸ Ideal.span {f} →+* B ⧸ Ideal.span {φ f} :=
  Ideal.quotientMap (Ideal.span {φ f}) φ (by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self (φ f)))

/-- `quotientSpanMap φ f` sends the class of `x` modulo `f` to the class of `φ x` modulo `φ f`. -/
@[simp]
public theorem quotientSpanMap_mk {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (f : A) (x : A) :
    quotientSpanMap φ f (Ideal.Quotient.mk (Ideal.span {f}) x)
      = Ideal.Quotient.mk (Ideal.span {φ f}) (φ x) :=
  Ideal.quotientMap_mk

/-- If the algebra structures on `D` over `R` and `S` are compatible with `ψ : R →+* S`, then
`J.map ψ` is killed in `D` exactly when `J` is. -/
private theorem map_le_ker_algebraMap_iff {R S D : Type*} [CommRing R] [CommRing S] [CommRing D]
    [Algebra R D] [Algebra S D] (ψ : R →+* S)
    (h : ∀ x, algebraMap R D x = algebraMap S D (ψ x)) (J : Ideal R) :
    J.map ψ ≤ RingHom.ker (algebraMap S D) ↔ J ≤ RingHom.ker (algebraMap R D) := by
  rw [Ideal.map_le_iff_le_comap]
  simp only [SetLike.le_def, Ideal.mem_comap, RingHom.mem_ker, h]

/-- **Flat base change of the canonical obstruction ideal.**  Let `A → B` be a flat ring map,
let `f ∈ A` be a nonzerodivisor, and let `M^•` be a bounded complex of finite free `A`-modules
whose determinantal ideals `I_i(M^•, f)` are principal.  Then the degreewise obstruction ideal
of Tag 0GSW extends along the reduction `A ⧸ fA → B ⧸ φ(f)B` to the degreewise obstruction
ideal of the base-changed complex:
`J_i(M^•, f) · (B ⧸ φ(f)B) = J_i(M^• ⊗_A B, φ(f))`.

This is the compatibility of `etaDirectSumIdeal` with flat base change, and hence of the total
obstruction ideal `J(M^•, f)` of `etaTotalDirectSumIdeal` with the restriction of a good affine
chart to a smaller affine chart.  It is the second of the three inputs listed in the module
header as missing for More on Flatness, Tag 0GTZ: the obstruction ideals computed on two
charts agree on the overlap, so the closed subschemes they cut out glue.  (It is stated for an
arbitrary flat ring map, not only for a localization `A → A_g`.)

Both sides are characterised by the same universal property, so neither has to be computed.
On the left, `Ideal.map ψ J ≤ ker (A ⧸ fA → B ⧸ φ(f)B → D)` says exactly
`J ≤ ker (A ⧸ fA → D)`, which by `etaDirectSumIdeal_le_ker_iff` is the universal property of
Tag 0F80 for the reduced décalage inclusion of `M^•`; by
`identifiesDirectSum_etaReductionMap_baseChange_iff` that is the same condition on `D` as the
universal property for `M^• ⊗_A B`, which by `etaDirectSumIdeal_eq_of_le_ker_iff` pins the
right-hand side.  Flatness is what identifies the two décalage inclusions after base change;
principality of the `I_i(M^•, f)` is what gives `J_i(M^•, f)` the universal property in the
first place. -/
public theorem map_etaDirectSumIdeal_eq_baseChange {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (i : ℤ) :
    Ideal.map (quotientSpanMap (algebraMap A B) f) (etaDirectSumIdeal C f i)
      = etaDirectSumIdeal (C.baseChange (algebraMap A B)) (algebraMap A B f) i := by
  symm
  apply etaDirectSumIdeal_eq_of_le_ker_iff
  intro D _ _
  let : Algebra B D :=
    ((algebraMap (B ⧸ Ideal.span {algebraMap A B f}) D).comp
      (algebraMap B (B ⧸ Ideal.span {algebraMap A B f}))).toAlgebra
  have : IsScalarTower B (B ⧸ Ideal.span {algebraMap A B f}) D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (A ⧸ Ideal.span {f}) D :=
    ((algebraMap (B ⧸ Ideal.span {algebraMap A B f}) D).comp
      (quotientSpanMap (algebraMap A B) f)).toAlgebra
  have hmap : ∀ x : A ⧸ Ideal.span {f},
      algebraMap (A ⧸ Ideal.span {f}) D x
        = algebraMap (B ⧸ Ideal.span {algebraMap A B f}) D
            (quotientSpanMap (algebraMap A B) f x) := fun _ => rfl
  have : IsScalarTower A (A ⧸ Ideal.span {f}) D :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hmap, Ideal.Quotient.algebraMap_eq, quotientSpanMap_mk]
      rfl
  rw [map_le_ker_algebraMap_iff _ hmap, etaDirectSumIdeal_le_ker_iff C f hf hI i D]
  exact identifiesDirectSum_etaReductionMap_baseChange_iff C f hf i D

/-- The identification `A ⧸ u·fA ≃+* A ⧸ fA` for a unit `u`: the two ideals are the same, by
`Ideal.span_singleton_mul_left_unit`. -/
public def quotEquivUnitMul {A : Type u} [CommRing A] (f : A) (u : Aˣ) :
    A ⧸ Ideal.span {(u : A) * f} ≃+* A ⧸ Ideal.span {f} :=
  Ideal.quotEquivOfEq (Ideal.span_singleton_mul_left_unit u.isUnit f)

/-- `quotEquivUnitMul f u` sends the class of `x` modulo `u·f` to the class of `x` modulo `f`. -/
@[simp]
public theorem quotEquivUnitMul_mk {A : Type u} [CommRing A] (f : A) (u : Aˣ) (x : A) :
    quotEquivUnitMul f u (Ideal.Quotient.mk (Ideal.span {(u : A) * f}) x)
      = Ideal.Quotient.mk (Ideal.span {f}) x :=
  rfl

/-- **Unit-invariance of the degreewise obstruction ideal.**  Let `f ∈ A` be a nonzerodivisor,
let `u ∈ A` be a unit, and let `M^•` be a bounded complex of finite free `A`-modules whose
determinantal ideals `I_i(M^•, f)` are principal.  Then the degreewise obstruction ideal of Tag
0GSW at `u·f` is the one at `f`, read across the identification `A ⧸ u·fA ≃+* A ⧸ fA` of the
two quotients by one and the same ideal:
`J_i(M^•, u·f) = J_i(M^•, f)`.

This is the counterpart for `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal` of
`idealI_unit_mul_eq`, Tag 0GST, for the determinantal ideals, and it is what makes the
obstruction ideals of two affine charts of a good triple comparable on a common open: the
equations of two charts agree only up to a unit there.

Both sides are characterised by the same universal property, so neither has to be computed.  By
`Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_le_ker_iff` an `A ⧸ u·fA`-algebra `D` kills
`J_i(M^•, u·f)` exactly when the reduced décalage inclusion of `M^•` at `u·f` identifies a
direct sum over `D`, and by
`Stacks.Decalage.DirectSumIdeal.identifiesDirectSum_etaReductionMap_unit_mul_iff` that is the
same condition on `D` as the one at `f`, which by
`Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_le_ker_iff` pins the right-hand side.
Principality of the `I_i(M^•, f)` is what gives the ideals their universal property in the
first place; it transfers to `u·f` by Tag 0GST. -/
public theorem map_etaDirectSumIdeal_unit_mul_eq {A : Type u} [CommRing A]
    (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (u : Aˣ) (i : ℤ) :
    Ideal.map (quotEquivUnitMul f u : A ⧸ Ideal.span {(u : A) * f} →+* A ⧸ Ideal.span {f})
        (etaDirectSumIdeal C ((u : A) * f) i)
      = etaDirectSumIdeal C f i := by
  have hfu : IsRegular ((u : A) * f) := u.isUnit.isRegular.mul hf
  have hIu : ∀ i : ℤ, (idealI C ((u : A) * f) i).IsPrincipal := fun i =>
    (idealI_unit_mul_eq C f u i) ▸ hI i
  symm
  apply etaDirectSumIdeal_eq_of_le_ker_iff C f i
  intro D _ _
  let : Algebra A D :=
    ((algebraMap (A ⧸ Ideal.span {f}) D).comp (Ideal.Quotient.mk (Ideal.span {f}))).toAlgebra
  have hA : ∀ x : A, algebraMap A D x
      = algebraMap (A ⧸ Ideal.span {f}) D (Ideal.Quotient.mk (Ideal.span {f}) x) := fun _ => rfl
  have : IsScalarTower A (A ⧸ Ideal.span {f}) D :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hA, Ideal.Quotient.algebraMap_eq]
  let : Algebra (A ⧸ Ideal.span {(u : A) * f}) D :=
    ((algebraMap (A ⧸ Ideal.span {f}) D).comp
      (quotEquivUnitMul f u : A ⧸ Ideal.span {(u : A) * f} →+* _)).toAlgebra
  have hmap : ∀ x : A ⧸ Ideal.span {(u : A) * f},
      algebraMap (A ⧸ Ideal.span {(u : A) * f}) D x
        = algebraMap (A ⧸ Ideal.span {f}) D (quotEquivUnitMul f u x) := fun _ => rfl
  have : IsScalarTower A (A ⧸ Ideal.span {(u : A) * f}) D :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hA, hmap, Ideal.Quotient.algebraMap_eq, quotEquivUnitMul_mk]
  rw [map_le_ker_algebraMap_iff _ hmap, etaDirectSumIdeal_le_ker_iff C ((u : A) * f) hfu hIu i D]
  exact identifiesDirectSum_etaReductionMap_unit_mul_iff C f hf u i D

end Stacks.Decalage.DirectSumIdeal

end

end FlatBaseChange
