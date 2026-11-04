module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import StacksFrontier.RingTheory.Henselian.Pair.NilpotentFactorization
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale lifting along locally nilpotent ideals, and weak ideals of definition

Two independent inputs, and their combination.

The first is the unique-lifting property of an étale algebra along a *locally nilpotent* ideal of
the target, for an arbitrary such ideal: for `R → S` étale, `T` an `R`-algebra and `J ⊆ T` an
ideal every element of which is nilpotent, every `R`-algebra map `S → T ⧸ J` lifts to `S → T`,
uniquely. Existence is smooth lifting (Stacks 07K4, `main_theorem07K4`); uniqueness is formal
unramifiedness after replacing `J` by the finitely generated — hence nilpotent — ideal generated
by the differences of the two candidate lifts on a finite set of algebra generators.

Mathlib has both halves only for a *nilpotent* ideal, as
`Algebra.FormallySmooth.exists_lift` and `Algebra.FormallyUnramified.lift_unique`, and packages
them as a bijection only for a square-zero ideal, `Algebra.FormallyEtale.comp_bijective`. This
library has the locally nilpotent statement for the special shape `J = I · T` with
`I ≤ nilradical R`, as `bijective_mkₐ_comp_of_etale_of_le_nilradical`; what is proved here is the
version for an arbitrary locally nilpotent ideal of `T`, which contains that one.

The second input is topological. Every element of a weak ideal of definition `J₀` is
topologically nilpotent, so a power of it lies in any given *open* ideal `J`;
hence the image of `J₀` in `R ⧸ J` consists of nilpotent elements:
`J₀ ⧸ J ≤ nilradical (R ⧸ J)`. No completeness, separatedness or weak admissibility is needed,
and `J` need not be contained in `J₀` nor contain it.

Combining the two, Stacks 0ALI applies to the pair `(R ⧸ J, J₀ ⧸ J)`: reduction is an
equivalence on étale algebras and the pair is henselian.

## Main results

* `AlgHom.ext_of_isLocallyNilpotent`: two algebra maps out of a finite-type formally unramified
  algebra which agree modulo a locally nilpotent ideal are equal.
* `Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent` and
  `Algebra.Etale.bijective_mkₐ_comp_of_isLocallyNilpotent`: unique lifting of étale algebra maps
  along an arbitrary locally nilpotent ideal of the target.
* `Algebra.Etale.existsUnique_algEquiv_of_isLocallyNilpotent` and
  `Algebra.Etale.existsUnique_algEquiv_of_le_nilradical`: the *object*-level form of the same
  principle — two étale lifts of one algebra are uniquely isomorphic.
* `TopologicalRing.map_quotient_le_nilradical_of_isWeakIdealOfDefinition`: the image of a weak
  ideal of definition in the quotient by an open ideal lies in the nilradical.
* `TopologicalRing.etaleBaseChange_isEquivalence_and_henselianPair_map_quotient`: Stacks 0ALI for
  the pair `(R ⧸ J, J₀ ⧸ J)`.

## References

* [Stacks: Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks: Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
* [Stacks: Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
-/

@[expose] public noncomputable section

section LocallyNilpotent

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Two `R`-algebra maps out of a finite-type formally unramified `R`-algebra `S` which agree
modulo a locally nilpotent ideal `J` of the target are equal.

The differences of the two maps on a finite set of algebra generators span a finitely generated
subideal of `J`, which is therefore nilpotent, and the two maps already agree modulo it. -/
@[ega "0 19.10.2" "special case"]
theorem AlgHom.ext_of_isLocallyNilpotent [Algebra.FiniteType R S]
    [Algebra.FormallyUnramified R S] {J : Ideal T} (hJ : J.IsLocallyNilpotent)
    {f g : S →ₐ[R] T}
    (h : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) : f = g := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have hd : ∀ x ∈ (t : Set S), Ideal.Quotient.mk J (f x) = Ideal.Quotient.mk J (g x) :=
    fun x _ => by simpa using AlgHom.congr_fun h x
  refine Algebra.FormallyUnramified.lift_unique
    (Ideal.span ((fun x : S => f x - g x) '' (t : Set S)))
    (isNilpotent_of_fg hJ ?_ (Submodule.fg_span (t.finite_toSet.image _))) f g ?_
  · rw [Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hd x hx, sub_self]
  · refine AlgHom.ext_of_adjoin_eq_top ht fun x hx => ?_
    have hmem : f x - g x ∈ Ideal.span ((fun x : S => f x - g x) '' (t : Set S)) :=
      Ideal.subset_span (Set.mem_image_of_mem _ hx)
    simpa using Ideal.Quotient.eq.mpr hmem

/-- **Unique lifting along a locally nilpotent ideal for an étale algebra.** For an étale
`R`-algebra `S`, an `R`-algebra `T` and an ideal `J ⊆ T` all of whose elements are nilpotent,
every `R`-algebra map `S → T ⧸ J` has a unique lift to an `R`-algebra map `S → T`. -/
@[sga "4 XIII 1.5" "special case"]
theorem Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent [Algebra.Etale R S]
    {J : Ideal T} (hJ : J.IsLocallyNilpotent) (g : S →ₐ[R] T ⧸ J) :
    ∃! f : S →ₐ[R] T, (Ideal.Quotient.mkₐ R J).comp f = g := by
  obtain ⟨f, hf⟩ := main_theorem07K4 R S T J hJ g
  exact ⟨f, hf, fun f' hf' => AlgHom.ext_of_isLocallyNilpotent hJ (hf'.trans hf.symm)⟩

/-- **Unique lifting along a locally nilpotent ideal for an étale algebra**, as a bijection.
For an étale `R`-algebra `S` and an ideal `J` of an `R`-algebra `T` all of whose elements are
nilpotent, composing with `T → T ⧸ J` is a bijection on `R`-algebra maps out of `S`. -/
theorem Algebra.Etale.bijective_mkₐ_comp_of_isLocallyNilpotent [Algebra.Etale R S]
    {J : Ideal T} (hJ : J.IsLocallyNilpotent) :
    Function.Bijective fun f : S →ₐ[R] T => (Ideal.Quotient.mkₐ R J).comp f :=
  ⟨fun _ _ h => AlgHom.ext_of_isLocallyNilpotent hJ h,
    fun g => (Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent hJ g).exists⟩

/-- If `ψ : A → C` and `ψ' : C → A` lift `φ` and `φ.symm` along locally nilpotent ideals, then
`ψ' ∘ ψ` is the identity. -/
private theorem comp_eq_id_of_isLocallyNilpotent
    {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra.Etale R A] {JA : Ideal A} {JC : Ideal C} (hA : JA.IsLocallyNilpotent)
    (φ : (A ⧸ JA) ≃ₐ[R] (C ⧸ JC)) (ψ : A →ₐ[R] C) (ψ' : C →ₐ[R] A)
    (hψ : (Ideal.Quotient.mkₐ R JC).comp ψ = φ.toAlgHom.comp (Ideal.Quotient.mkₐ R JA))
    (hψ' : (Ideal.Quotient.mkₐ R JA).comp ψ' = φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R JC)) :
    ψ'.comp ψ = AlgHom.id R A := by
  refine AlgHom.ext_of_isLocallyNilpotent hA ?_
  rw [← AlgHom.comp_assoc, hψ', AlgHom.comp_assoc, hψ, ← AlgHom.comp_assoc]
  ext a
  simp

/-- **Two étale lifts of one algebra are uniquely isomorphic.** Let `I ⊆ R` be an ideal and let
`A` and `C` be étale `R`-algebras whose extended ideals `IA` and `IC` are locally nilpotent.
Then every `R`-algebra isomorphism `A ⧸ IA ≃ C ⧸ IC` of the reductions is the reduction of a
unique `R`-algebra isomorphism `A ≃ C`.

This is the object-level counterpart of
`Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent`, and it is the form in which the
fully faithful half of Stacks 0ALI gets used: the *uniqueness* clause is what makes a family of
such comparison isomorphisms, one for each member of a directed system of ideals,
automatically compatible with the transition maps, since both composites around a transition
square lift one and the same isomorphism of reductions. In the proof of Stacks 0AN8 this is the
family `φ_J : A ⧸ JA ≃ Ā_J` identifying the quotients of a chosen étale lift `A` with the
stagewise base changes, whose compatibility for varying `J` the source obtains in exactly this
way.

Both directions are lifted separately, and the two composites are the identity because each
lifts the identity of a reduction, so uniqueness of lifts identifies them. -/
theorem Algebra.Etale.existsUnique_algEquiv_of_isLocallyNilpotent
    {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra.Etale R A] [Algebra.Etale R C] (I : Ideal R)
    (hA : (I.map (algebraMap R A)).IsLocallyNilpotent)
    (hC : (I.map (algebraMap R C)).IsLocallyNilpotent)
    (φ : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (C ⧸ I.map (algebraMap R C))) :
    ∃! ψ : A ≃ₐ[R] C,
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R C))).comp (ψ : A →ₐ[R] C) =
        (φ : (A ⧸ I.map (algebraMap R A)) →ₐ[R] (C ⧸ I.map (algebraMap R C))).comp
          (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) := by
  obtain ⟨ψ, hψ, huniq⟩ := Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent hC
    ((φ : (A ⧸ I.map (algebraMap R A)) →ₐ[R] (C ⧸ I.map (algebraMap R C))).comp
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))))
  obtain ⟨ψ', hψ', -⟩ := Algebra.Etale.existsUnique_lift_of_isLocallyNilpotent hA
    ((φ.symm : (C ⧸ I.map (algebraMap R C)) →ₐ[R] (A ⧸ I.map (algebraMap R A))).comp
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R C))))
  have h1 := comp_eq_id_of_isLocallyNilpotent hA φ ψ ψ' hψ hψ'
  have h2 := comp_eq_id_of_isLocallyNilpotent hC φ.symm ψ' ψ hψ' hψ
  refine ⟨AlgEquiv.ofAlgHom ψ ψ' h2 h1, hψ, fun χ hχ => ?_⟩
  have hχψ : (χ : A →ₐ[R] C) = ψ := huniq _ hχ
  ext a
  exact AlgHom.congr_fun hχψ a

/-- **Two étale lifts of one algebra are uniquely isomorphic**, in the hypothesis shape of
Stacks 0ALI: the ideal `I` is assumed to lie in the nilradical of the *base*, and local
nilpotence of the extended ideals follows by Stacks 0544
(`Ideal.IsLocallyNilpotent0544.map`). This is the form the proof of Stacks 0AN8 applies, with
`R ⧸ J` for the base and the image of a weak ideal of definition `J₀` for `I`, whose nilpotence
is `TopologicalRing.map_quotient_le_nilradical_of_isWeakIdealOfDefinition`. -/
theorem Algebra.Etale.existsUnique_algEquiv_of_le_nilradical
    {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra.Etale R A] [Algebra.Etale R C] (I : Ideal R) (hI : I ≤ nilradical R)
    (φ : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (C ⧸ I.map (algebraMap R C))) :
    ∃! ψ : A ≃ₐ[R] C,
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R C))).comp (ψ : A →ₐ[R] C) =
        (φ : (A ⧸ I.map (algebraMap R A)) →ₐ[R] (C ⧸ I.map (algebraMap R C))).comp
          (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) :=
  Algebra.Etale.existsUnique_algEquiv_of_isLocallyNilpotent I
    (fun x hx => Ideal.IsLocallyNilpotent0544.map (algebraMap R A) I
      (fun _ hy => mem_nilradical.mp (hI hy)) x hx)
    (fun x hx => Ideal.IsLocallyNilpotent0544.map (algebraMap R C) I
      (fun _ hy => mem_nilradical.mp (hI hy)) x hx) φ

end LocallyNilpotent

namespace TopologicalRing

section WeakIdeal

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- An ideal `J₀` consisting of topologically nilpotent elements has nilpotent image in the
quotient by any open ideal `J`: a power of each element of `J₀` already lies in `J`. -/
@[ega "0 7.1.3" "(i)"]
theorem map_quotient_le_nilradical_of_isTopologicallyNilpotent {J₀ J : Ideal R}
    (hJ₀ : ∀ x ∈ J₀, IsTopologicallyNilpotent x) (hJ : IsOpen (J : Set R)) :
    J₀.map (Ideal.Quotient.mk J) ≤ nilradical (R ⧸ J) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨n, hn⟩ := (hJ₀ x hx).exists_pow_mem_of_mem_nhds (hJ.mem_nhds J.zero_mem)
  refine Ideal.mem_comap.mpr (mem_nilradical.mpr ⟨n, ?_⟩)
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hn

/-- **`J₀ ⧸ J ≤ nilradical (R ⧸ J)`.** The image of a weak ideal of definition `J₀` in the
quotient of `R` by an open ideal `J` is contained in the nilradical. -/
theorem map_quotient_le_nilradical_of_isWeakIdealOfDefinition {J₀ J : Ideal R}
    (hJ₀ : IsWeakIdealOfDefinition J₀) (hJ : IsOpen (J : Set R)) :
    J₀.map (Ideal.Quotient.mk J) ≤ nilradical (R ⧸ J) :=
  map_quotient_le_nilradical_of_isTopologicallyNilpotent hJ₀.2 hJ

end WeakIdeal

section WeakIdealEtale

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- **Stacks 0ALI for the pair `(R ⧸ J, J₀ ⧸ J)`.** For a weak ideal of definition `J₀` and an
open ideal `J` of a topologized commutative ring `R`, reduction modulo `J₀ ⧸ J` is an equivalence
from étale `R ⧸ J`-algebras to étale `(R ⧸ J) ⧸ (J₀ ⧸ J)`-algebras, and `(R ⧸ J, J₀ ⧸ J)` is a
henselian pair. -/
theorem etaleBaseChange_isEquivalence_and_henselianPair_map_quotient {J₀ J : Ideal R}
    (hJ₀ : IsWeakIdealOfDefinition J₀) (hJ : IsOpen (J : Set R)) :
    (etaleBaseChange (J₀.map (Ideal.Quotient.mk J))).IsEquivalence ∧
      HenselianPair (R ⧸ J) (J₀.map (Ideal.Quotient.mk J)) :=
  etaleBaseChange_isEquivalence_and_henselianPair_of_le_nilradical _
    (map_quotient_le_nilradical_of_isWeakIdealOfDefinition hJ₀ hJ)

/-- Unique lifting of étale algebra maps along a weak ideal of definition. For a weak ideal of
definition `J₀`, an open ideal `J`, an étale `R ⧸ J`-algebra `S` and any `R ⧸ J`-algebra `T`,
composing with `T → T ⧸ (J₀ ⧸ J) T` is a bijection on `R ⧸ J`-algebra maps out of `S`. -/
theorem bijective_mkₐ_comp_of_etale_of_isWeakIdealOfDefinition {J₀ J : Ideal R}
    (hJ₀ : IsWeakIdealOfDefinition J₀) (hJ : IsOpen (J : Set R))
    (S T : Type*) [CommRing S] [CommRing T] [Algebra (R ⧸ J) S] [Algebra (R ⧸ J) T]
    [Algebra.Etale (R ⧸ J) S] :
    Function.Bijective fun f : S →ₐ[R ⧸ J] T =>
      (Ideal.Quotient.mkₐ (R ⧸ J)
        ((J₀.map (Ideal.Quotient.mk J)).map (algebraMap (R ⧸ J) T))).comp f :=
  bijective_mkₐ_comp_of_etale_of_le_nilradical _
    (map_quotient_le_nilradical_of_isWeakIdealOfDefinition hJ₀ hJ) S T

end WeakIdealEtale

end TopologicalRing

end
