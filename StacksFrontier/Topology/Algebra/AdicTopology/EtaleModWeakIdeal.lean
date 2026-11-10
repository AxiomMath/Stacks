module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver

/-!
# Étale ring maps modulo the weak ideals of definition of a linearly topologized ring

Let `B` be a linearly topologized ring, let `f : B →+* A` be an étale ring map and let `A^∧` be
the completion of `A` over `B`.  For every weak ideal of definition `J` of `B` the induced map
`B ⧸ J → A ⧸ JA` is étale, and so is the map `B ⧸ J → A^∧ ⧸ ker (A^∧ → A ⧸ JA)` that the
canonical map `B → A^∧` induces on the corresponding quotient stages.  These are the étale maps
of quotients that the proof of Tag 0AN8 runs on: the quotient stages of `Spf A^∧ ⟶ Spf B` are
their spectra.

## Main results

* `RingHom.Etale.quotientMap`: étale passes to `B ⧸ J → A ⧸ JA`, for an arbitrary ideal `J`.
* `TopologicalRing.etale_quotientMap_weakIdealOfDefinition`: the same for a weak ideal of
  definition of `B`.
* `TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap`: the map induced on the
  quotient stages attached to a weak ideal of definition of `B` by the canonical map
  `B → A^∧` is étale.
* `TopologicalRing.exists_etale_surjection_weakIdealOfDefinition`: the étale-lift step of the
  essential surjectivity half of Tag 0AN8 — an étale `B ⧸ J₀`-algebra, for `J₀` a weak ideal of
  definition of `B`, is the quotient stage of an étale `B`-algebra.

## Implementation notes

`A ⧸ JA` is the base change `(B ⧸ J) ⊗[B] A` by
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, and being étale is stable under base change
and transported along algebra isomorphisms; the quotient map of the title is
`Ideal.quotientMap (J.map f) f Ideal.le_comap_map`, which is definitionally the algebra map of
`Ideal.Quotient.algebraQuotientMapQuotient`, so no transport of algebra structures is needed.

The stage of `A^∧` attached to `J` is `A^∧ ⧸ ker (TopologicalRing.CompletionOver.projection f J)`,
and that projection is surjective with `A ⧸ JA` as target, so the stage is `A ⧸ JA` up to a ring
isomorphism; `etale_of_ringEquiv_comp` cancels it.

## References

* [Stacks Project, Tag 00U1](https://stacks.math.columbia.edu/tag/00U1)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public section

universe u v w

namespace RingHom

/-- A ring map whose composite with a ring isomorphism is étale is itself étale: the isomorphism
is one of algebras over the source, and being étale is transported along those. -/
public theorem etale_of_ringEquiv_comp {R : Type u} {S : Type v} {T : Type w} [CommRing R]
    [CommRing S] [CommRing T] (g : R →+* S) (e : S ≃+* T)
    (h : ((e : S →+* T).comp g).Etale) : g.Etale := by
  let : Algebra R S := g.toAlgebra
  let : Algebra R T := ((e : S →+* T).comp g).toAlgebra
  have : Algebra.Etale R T := h
  exact Algebra.Etale.of_equiv (R := R) (A := T) (B := S)
    (AlgEquiv.ofRingEquiv (f := e.symm) fun x => e.symm_apply_apply (g x))

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A]

/-- If `f : B →+* A` is étale, so is the induced map `B ⧸ J → A ⧸ JA`: indeed `A ⧸ JA` is
`(B ⧸ J) ⊗[B] A`, and being étale is stable under base change. -/
public theorem Etale.quotientMap (f : B →+* A) (hf : f.Etale) (J : Ideal B) :
    (Ideal.quotientMap (J.map f) f Ideal.le_comap_map).Etale := by
  let : Algebra B A := f.toAlgebra
  have : Algebra.Etale B A := hf
  exact RingHom.etale_algebraMap.mpr <|
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A J).symm

end RingHom

namespace TopologicalRing

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] [TopologicalSpace B]

/-- **Stacks 0AN8**, first step of the proof.  For an étale ring map `f : B →+* A` and a weak
ideal of definition `J` of `B`, the induced map `B ⧸ J → A ⧸ JA` is étale. -/
@[stacks 0AN8 "first step of the proof: for an étale ring map `B → A` and a weak ideal of \
definition `J` of `B`, the ring map `B ⧸ J → A ⧸ JA` of quotient stages is étale.  The \
assertions about morphisms of formal spectra — representability, étaleness, full faithfulness, \
essential surjectivity, the equivalence of categories and the McQuillan conclusion — are not \
included"]
public theorem etale_quotientMap_weakIdealOfDefinition {f : B →+* A} (hf : f.Etale)
    (J : WeakIdealOfDefinitionIndex B) :
    (Ideal.quotientMap (extendedIdeal f J) f Ideal.le_comap_map).Etale :=
  RingHom.Etale.quotientMap f hf J.1

/-- **Stacks 0AN8**, the étale-lift step of the essential surjectivity half.  Let `J₀` be a weak
ideal of definition of a linearly topologized ring `B` and let `A₀` be an étale `B ⧸ J₀`-algebra.
Then `A₀` is the quotient stage attached to `J₀` of an étale `B`-algebra: there is an étale
`B`-algebra `C` and a surjection `ψ : C → A₀` of rings whose kernel is the extended ideal `J₀ C`
and which is compatible with the two structure maps, so that `A₀ ≅ C ⧸ J₀ C` over `B ⧸ J₀`.

This is the step of the source's proof that produces the étale `B`-algebra from the étale
`B ⧸ J₀`-algebra `A₀` cut out by the fixed weak ideal of definition `J₀`; the source invokes
Algebra, Lemma 10.143.10, which this library carries as Stacks 04D1
(`etale_lift_along_surjection`).  Only the existence of the lift is asserted.  The comparison
family `φ_J` that the source obtains from uniqueness of étale lifts is
`TopologicalRing.existsUnique_algEquiv_of_isWeakIdealOfDefinition`; the identification of the
stagewise base changes of a representable étale morphism with the spectra of étale algebras, the
colimit assembly `X = Spf A^∧`, and the equivalence of categories are not part of this
statement.

The conclusion is phrased as a surjection with a named kernel rather than as an isomorphism
`A₀ ≅ C ⧸ J₀ C`, which is the shape Stacks 04D1 is stated in here; the kernel is spelled with
this module's `extendedIdeal`. -/
@[stacks 0AN8 "the étale-lift step of the essential surjectivity half: for a weak ideal of \
definition `J₀` of `B` and an étale `B ⧸ J₀`-algebra `A₀`, there is an étale `B`-algebra `C` \
together with a surjection `C → A₀` compatible with the structure maps whose kernel is the \
extended ideal `J₀ C`, so that `A₀` is the quotient stage `C ⧸ J₀ C`.  This is the existence of \
the étale lift only; the comparison family `φ_J`, the identification of the stagewise base \
changes of a representable étale morphism with the spectra of étale algebras, the colimit \
assembly of the essential surjectivity half, the assertions about morphisms of formal spectra — \
representability, étaleness, full faithfulness — the equivalence of categories and the \
McQuillan conclusion are not included"]
public theorem exists_etale_surjection_weakIdealOfDefinition
    (J₀ : WeakIdealOfDefinitionIndex B) (A₀ : Type w) [CommRing A₀]
    [Algebra (B ⧸ (J₀.1 : Ideal B)) A₀] [Algebra.Etale (B ⧸ (J₀.1 : Ideal B)) A₀] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C), Algebra.Etale B C ∧
      ∃ ψ : C →+* A₀, Function.Surjective ψ ∧
        RingHom.ker ψ = extendedIdeal (algebraMap B C) J₀ ∧
        ψ.comp (algebraMap B C) =
          (algebraMap (B ⧸ (J₀.1 : Ideal B)) A₀).comp
            (Ideal.Quotient.mk (J₀.1 : Ideal B)) := by
  let : Algebra B A₀ :=
    ((algebraMap (B ⧸ (J₀.1 : Ideal B)) A₀).comp
      (Ideal.Quotient.mk (J₀.1 : Ideal B))).toAlgebra
  have : IsScalarTower B (B ⧸ (J₀.1 : Ideal B)) A₀ := .of_algebraMap_eq fun _ => rfl
  obtain ⟨C, _, _, hC, ψ, hsurj, hker⟩ :=
    etale_lift_along_surjection B (B ⧸ (J₀.1 : Ideal B)) A₀ Ideal.Quotient.mk_surjective
  refine ⟨C, inferInstance, inferInstance, hC, (ψ : C →+* A₀), hsurj, ?_,
    RingHom.ext ψ.commutes⟩
  have hq : RingHom.ker (algebraMap B (B ⧸ (J₀.1 : Ideal B))) = (J₀.1 : Ideal B) := by
    ext x
    simp
  rw [hker, hq]

namespace CompletionOver

/-- A weak ideal of definition of `B` lands in the kernel of the projection of the completion of
`A` over `B` attached to it. -/
public theorem le_comap_ker_projection (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    (J.1 : Ideal B) ≤ Ideal.comap (canonicalMap f) (RingHom.ker (projection f J)) := by
  intro b hb
  change projection f J (canonicalMap f b) = 0
  rw [projection_canonicalMap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hb)

/-- **Stacks 0AN8**, first step of the proof, on the stages of the completion.  For an étale ring
map `f : B →+* A` and a weak ideal of definition `J` of `B`, the map
`B ⧸ J → A^∧ ⧸ ker (A^∧ → A ⧸ JA)` induced by the canonical map `B → A^∧` is étale; the quotient
stages of `Spf A^∧ ⟶ Spf B` are the spectra of these maps. -/
@[stacks 0AN8 "first step of the proof, on the stages of the completion: for an étale ring map \
`B → A` and a weak ideal of definition `J` of `B`, the map `B ⧸ J → A^∧ ⧸ ker (A^∧ → A ⧸ JA)` \
of quotient stages of the canonical map `B → A^∧` is étale.  The assertions about morphisms of \
formal spectra — representability, étaleness, full faithfulness, essential surjectivity, the \
equivalence of categories and the McQuillan conclusion — are not included"]
public theorem etale_quotientMap_canonicalMap {f : B →+* A} (hf : f.Etale)
    (J : WeakIdealOfDefinitionIndex B) :
    (Ideal.quotientMap (RingHom.ker (projection f J)) (canonicalMap f)
      (le_comap_ker_projection f J)).Etale := by
  let equivalence := (projection f J).quotientKerEquivOfSurjective (projection_surjective f J)
  refine RingHom.etale_of_ringEquiv_comp _ equivalence ?_
  convert etale_quotientMap_weakIdealOfDefinition hf J using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
  change equivalence (Ideal.Quotient.mk (RingHom.ker (projection f J)) (canonicalMap f b)) =
    Ideal.Quotient.mk (extendedIdeal f J) (f b)
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk, projection_canonicalMap]

end CompletionOver

end TopologicalRing

end
