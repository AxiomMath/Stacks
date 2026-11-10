module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleLiftWeakIdealOfDefinition

/-!
# Rigidity of étale lifts along a locally nilpotent ideal

Let `R` be a commutative ring and let `I ⊆ R` be an ideal every element of which is nilpotent.
Two étale `R`-algebras `S` and `T` whose reductions `S ⧸ IS` and `T ⧸ IT` are identified are
then *uniquely* isomorphic over `R` compatibly with that identification.

That rigidity statement is `Algebra.Etale.existsUnique_algEquiv_of_le_nilradical`, proved in
`StacksFrontier.Topology.Algebra.AdicTopology.EtaleLiftWeakIdealOfDefinition` from unique lifting
along a locally nilpotent ideal. This file adds that the comparison isomorphisms compose, and
specializes the rigidity to the pair attached to a weak ideal of definition.

The application is the step `φ_J` of the essential surjectivity half of Stacks 0AN8. There `R`
is the quotient `B ⧸ J` of a topological ring `B` by an open ideal `J`, and `I` is the image of
a weak ideal of definition `J₀` of `B`, which consists of nilpotent elements by
`TopologicalRing.map_quotient_le_nilradical_of_isWeakIdealOfDefinition`: the two étale
`B ⧸ J`-algebras are the ring of the stagewise base change of the given representable étale
morphism and the quotient `A ⧸ JA` of the étale lift `A` produced by Stacks 04D1, and both
reduce to the fixed étale `B ⧸ J₀`-algebra `A₀`.

## Main results

* `Algebra.Etale.mkₐ_comp_toAlgHom_trans`: a composite of comparison isomorphisms is a
  comparison isomorphism of the composite identification, which with the uniqueness clause is
  the compatibility of the family `φ_J`.
* `TopologicalRing.existsUnique_algEquiv_of_isWeakIdealOfDefinition`: rigidity of étale lifts
  for the pair `(R ⧸ J, J₀ ⧸ J)` attached to a weak ideal of definition `J₀` and an open ideal
  `J`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public noncomputable section

namespace Algebra.Etale

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **The comparison isomorphisms compose.** If `φ₁ : S ≅ T` reduces to `e₁` modulo `I` and
`φ₂ : T ≅ U` reduces to `e₂`, then `φ₁ ≫ φ₂` reduces to `e₁ ≫ e₂`.

No hypothesis on `I` is needed. Together with the uniqueness clause of
`Algebra.Etale.existsUnique_algEquiv_of_le_nilradical` this is the compatibility of the
comparisons that the source of Stacks 0AN8 obtains from uniqueness: the family `φ_J` it builds
stage by stage is automatically compatible with the transitions, because a composite of
comparisons is a comparison of the composite and there is only one of those. -/
theorem mkₐ_comp_toAlgHom_trans {U : Type*} [CommRing U] [Algebra R U] {I : Ideal R}
    {e₁ : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] T ⧸ I.map (algebraMap R T)}
    {e₂ : (T ⧸ I.map (algebraMap R T)) ≃ₐ[R] U ⧸ I.map (algebraMap R U)}
    {φ₁ : S ≃ₐ[R] T} {φ₂ : T ≃ₐ[R] U}
    (h₁ : (Ideal.Quotient.mkₐ R (I.map (algebraMap R T))).comp φ₁.toAlgHom =
      e₁.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))))
    (h₂ : (Ideal.Quotient.mkₐ R (I.map (algebraMap R U))).comp φ₂.toAlgHom =
      e₂.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R T)))) :
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R U))).comp (φ₁.trans φ₂).toAlgHom =
      (e₁.trans e₂).toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S))) := by
  refine AlgHom.ext fun x => ?_
  have k₁ : Ideal.Quotient.mk (I.map (algebraMap R T)) (φ₁ x) =
      e₁ (Ideal.Quotient.mk (I.map (algebraMap R S)) x) := AlgHom.congr_fun h₁ x
  have k₂ : Ideal.Quotient.mk (I.map (algebraMap R U)) (φ₂ (φ₁ x)) =
      e₂ (Ideal.Quotient.mk (I.map (algebraMap R T)) (φ₁ x)) := AlgHom.congr_fun h₂ (φ₁ x)
  change Ideal.Quotient.mk (I.map (algebraMap R U)) (φ₂ (φ₁ x)) =
    (e₁.trans e₂) (Ideal.Quotient.mk (I.map (algebraMap R S)) x)
  rw [k₂, k₁, AlgEquiv.trans_apply]

end Algebra.Etale

namespace TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- **Stacks 0AN8, the rigidity step `φ_J` of the essential surjectivity half.** Let `J₀` be a
weak ideal of definition of a topologized commutative ring `R` and let `J` be an open ideal of
`R`. Two étale `R ⧸ J`-algebras whose reductions modulo the image of `J₀` are identified are
uniquely isomorphic over `R ⧸ J` compatibly with that identification.

The image of `J₀` in `R ⧸ J` consists of nilpotent elements, a power of a topologically
nilpotent element lying in the open ideal `J`, so this is rigidity of étale lifts along a
locally nilpotent ideal. In the source's proof `J ⊆ J₀` and the two étale `R ⧸ J`-algebras both
reduce to the fixed étale `R ⧸ J₀`-algebra `A₀`. -/
@[stacks 0AN8 "the rigidity step of the essential surjectivity half: for a weak ideal of \
definition `J₀` and an open ideal `J`, two étale `R ⧸ J`-algebras with identified reductions \
modulo the image of `J₀` are uniquely isomorphic compatibly with that identification.  This is \
the uniqueness that produces the family `φ_J` of the source's proof; the construction of the \
étale lift, the identification of the stagewise base changes of a representable étale morphism \
with the spectra of étale algebras, the equivalence of categories and the McQuillan conclusion \
are not included"]
theorem existsUnique_algEquiv_of_isWeakIdealOfDefinition {J₀ J : Ideal R}
    (hJ₀ : IsWeakIdealOfDefinition J₀) (hJ : IsOpen (J : Set R))
    (S T : Type*) [CommRing S] [CommRing T] [Algebra (R ⧸ J) S] [Algebra (R ⧸ J) T]
    [Algebra.Etale (R ⧸ J) S] [Algebra.Etale (R ⧸ J) T]
    (e : (S ⧸ (J₀.map (Ideal.Quotient.mk J)).map (algebraMap (R ⧸ J) S)) ≃ₐ[R ⧸ J]
      T ⧸ (J₀.map (Ideal.Quotient.mk J)).map (algebraMap (R ⧸ J) T)) :
    ∃! φ : S ≃ₐ[R ⧸ J] T,
      (Ideal.Quotient.mkₐ (R ⧸ J)
          ((J₀.map (Ideal.Quotient.mk J)).map (algebraMap (R ⧸ J) T))).comp φ.toAlgHom =
        e.toAlgHom.comp (Ideal.Quotient.mkₐ (R ⧸ J)
          ((J₀.map (Ideal.Quotient.mk J)).map (algebraMap (R ⧸ J) S))) :=
  Algebra.Etale.existsUnique_algEquiv_of_le_nilradical _
    (map_quotient_le_nilradical_of_isWeakIdealOfDefinition hJ₀ hJ) e

end TopologicalRing

end
