module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct

/-!
# Transporting a quotient system along a bicontinuous ring isomorphism

Let `S` be a scheme contained in a big fppf site `B` and let `e : A ≃+* A'` be an isomorphism
of topological rings which is continuous in both directions. A quotient system over `S` for
`A` — the datum presenting `A` as a formal spectrum over `S`, Stacks 0AIF — transports to one
for `A'`.

The weak ideals of definition of `A'` pull back to weak ideals of definition of `A` along `e`:
the preimage of an open ideal is open because `e` is continuous, and an element whose image is
topologically nilpotent is itself topologically nilpotent because `e.symm` is. Each quotient
stage `A' ⧸ J` is then isomorphic as a ring to `A ⧸ e⁻¹J`, so its spectrum is isomorphic as a
scheme — hence lies in the site — and carries the structure morphism to `S` read through that
isomorphism. The isomorphism and its inverse are themselves continuous homomorphisms over `S`
between the two systems, so `Spf A ≅ Spf A'` follows from the functoriality of `Spf`.

This is what makes a ring that is only *isomorphic* to a presenting ring usable as one. It is
the missing step between the finite-product constructions of
`StacksFrontier/AlgebraicGeometry/FormalSpace/FormalSpectrumFiniteProduct.lean`, which present
`∀ i, Wᵢ`, and **Stacks 0AN9**, whose conditions are stated for a quotient system on the
completion `TopologicalRing.CompletionOver c` itself.

## Main definitions

* `AlgebraicGeometry.FormalSpace.weakIdealComapOfRingEquiv`: the preimage of a weak ideal of
  definition.
* `AlgebraicGeometry.FormalSpace.quotientEquivOfRingEquiv`: the induced isomorphism of quotient
  stages.
* `AlgebraicGeometry.FormalSpace.quotientSystemOfRingEquiv`: the transported quotient system.
* `AlgebraicGeometry.FormalSpace.continuousHomOfRingEquiv` and
  `AlgebraicGeometry.FormalSpace.continuousHomOfRingEquivSymm`: the isomorphism and its inverse
  as continuous homomorphisms over `S` between the two systems.

## Implementation notes

No `@[stacks]` registration: the construction of Stacks 0AIF is registered where it is given,
and this is bookkeeping around it rather than a numbered statement of the source.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A A' : Type u} [CommRing A] [TopologicalSpace A] [CommRing A'] [TopologicalSpace A']

section Transport

variable (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm)

/-- The preimage along a bicontinuous ring isomorphism of a weak ideal of definition. -/
def weakIdealComapOfRingEquiv
    (J : { I : Ideal A' // TopologicalRing.IsWeakIdealOfDefinition I }) :
    { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨Ideal.comap (e : A →+* A') J.1, J.2.1.preimage he, fun x hx ↦ by
    simpa using (J.2.2 (e x) hx).map he'⟩

/-- The ideal underlying `weakIdealComapOfRingEquiv e he he' J` is the preimage of `J`
under `e`. -/
theorem weakIdealComapOfRingEquiv_coe
    (J : { I : Ideal A' // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (weakIdealComapOfRingEquiv e he he' J).1 = Ideal.comap (e : A →+* A') J.1 := rfl

/-- The isomorphism of quotient stages induced by a bicontinuous ring isomorphism. -/
def quotientEquivOfRingEquiv
    (J : { I : Ideal A' // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (A ⧸ (weakIdealComapOfRingEquiv e he he' J).1) ≃+* A' ⧸ J.1 :=
  Ideal.quotientEquiv _ J.1 e
    (Ideal.map_comap_of_surjective (e : A →+* A') e.surjective J.1).symm

/-- `quotientEquivOfRingEquiv e he he' J` sends the class of `a` to the class of `e a`. -/
@[simp]
theorem quotientEquivOfRingEquiv_mk
    (J : { I : Ideal A' // TopologicalRing.IsWeakIdealOfDefinition I }) (a : A) :
    quotientEquivOfRingEquiv e he he' J
        (Ideal.Quotient.mk (weakIdealComapOfRingEquiv e he he' J).1 a) =
      Ideal.Quotient.mk J.1 (e a) := rfl

/-- **The quotient system transported along a bicontinuous ring isomorphism.** A quotient
system over `S` for a topological ring is one for any ring bicontinuously isomorphic to it: the
weak ideals of definition correspond under preimage, and the quotient stages are isomorphic
rings, so their spectra are isomorphic schemes carrying the same structure morphism to `S`. -/
def quotientSystemOfRingEquiv (D : QuotientSystem B S hS A) : QuotientSystem B S hS A' where
  inSite J := by
    have hiso : Spec (.of (A' ⧸ J.1)) ≅
        Spec (.of (A ⧸ (weakIdealComapOfRingEquiv e he he' J).1)) :=
      Scheme.Spec.mapIso (quotientEquivOfRingEquiv e he he' J).toCommRingCatIso.op
    have hsize : (Spec (.of (A ⧸ (weakIdealComapOfRingEquiv e he he' J).1))).size < B.cutoff :=
      D.inSite _
    rwa [← Scheme.size_congr hiso] at hsize
  overS J := Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom) ≫
    D.overS (weakIdealComapOfRingEquiv e he he' J)
  compatible J L h := by
    have hc : (weakIdealComapOfRingEquiv e he he' J).1 ≤
      (weakIdealComapOfRingEquiv e he he' L).1 := Ideal.comap_mono h
    have hring : (Ideal.Quotient.factor h).comp
          (quotientEquivOfRingEquiv e he he' J).toRingHom =
        (quotientEquivOfRingEquiv e he he' L).toRingHom.comp (Ideal.Quotient.factor hc) := by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have hcr : CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom ≫
          CommRingCat.ofHom (Ideal.Quotient.factor h) =
        CommRingCat.ofHom (Ideal.Quotient.factor hc) ≫
          CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' L).toRingHom :=
      CommRingCat.hom_ext hring
    have hfac : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
          Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom) =
        Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' L).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hc)) := by
      have e1 := Spec.map_comp
        (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom)
        (CommRingCat.ofHom (Ideal.Quotient.factor h))
      have e2 := Spec.map_comp (CommRingCat.ofHom (Ideal.Quotient.factor hc))
        (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' L).toRingHom)
      exact e1.symm.trans ((congrArg (fun f ↦ Spec.map f) hcr).trans e2)
    calc Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
            Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom) ≫
            D.overS (weakIdealComapOfRingEquiv e he he' J)
        = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
            Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom)) ≫
            D.overS (weakIdealComapOfRingEquiv e he he' J) := (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' L).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hc))) ≫
            D.overS (weakIdealComapOfRingEquiv e he he' J) := by rw [hfac]
      _ = Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' L).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hc)) ≫
            D.overS (weakIdealComapOfRingEquiv e he he' J) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' L).toRingHom) ≫
            D.overS (weakIdealComapOfRingEquiv e he he' L) := by
          rw [D.compatible _ _ hc]

/-- The structure morphism to `S` of the stage `Spec (A' ⧸ J)` of the transported system is
`Spec` of the quotient isomorphism followed by the structure morphism of the stage
`Spec (A ⧸ e⁻¹J)` of `D`. -/
@[simp]
theorem overS_quotientSystemOfRingEquiv (D : QuotientSystem B S hS A)
    (J : { I : Ideal A' // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (quotientSystemOfRingEquiv B S hS e he he' D).overS J =
      Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom) ≫
        D.overS (weakIdealComapOfRingEquiv e he he' J) := rfl

/-- The isomorphism itself, as a continuous homomorphism over `S` to the transported system. -/
def continuousHomOfRingEquiv (D : QuotientSystem B S hS A) :
    ContinuousHom D (quotientSystemOfRingEquiv B S hS e he he' D) where
  toRingHom := (e : A →+* A')
  continuous := he
  overS J K h := by
    have hring : Ideal.quotientMap K.1 (e : A →+* A') h =
        (quotientEquivOfRingEquiv e he he' K).toRingHom.comp (Ideal.Quotient.factor h) := by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have hcr : CommRingCat.ofHom (Ideal.quotientMap K.1 (e : A →+* A') h) =
        CommRingCat.ofHom (Ideal.Quotient.factor h) ≫
          CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' K).toRingHom :=
      CommRingCat.hom_ext hring
    have h2 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 (e : A →+* A') h)) =
        Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
      (congrArg (fun f ↦ Spec.map f) hcr).trans (Spec.map_comp _ _)
    rw [overS_quotientSystemOfRingEquiv, h2, Category.assoc, D.compatible J _ h]

/-- The ring homomorphism underlying `continuousHomOfRingEquiv` is `e`. -/
@[simp]
theorem continuousHomOfRingEquiv_toRingHom (D : QuotientSystem B S hS A) :
    (continuousHomOfRingEquiv B S hS e he he' D).toRingHom = (e : A →+* A') := rfl

/-- The inverse isomorphism, as a continuous homomorphism over `S` out of the transported
system. -/
def continuousHomOfRingEquivSymm (D : QuotientSystem B S hS A) :
    ContinuousHom (quotientSystemOfRingEquiv B S hS e he he' D) D where
  toRingHom := (e.symm : A' →+* A)
  continuous := he'
  overS J K h := by
    have hle : (weakIdealComapOfRingEquiv e he he' J).1 ≤ K.1 := by
      intro a ha
      have : e.symm (e a) ∈ K.1 := h ha
      simpa using this
    have hring : (Ideal.quotientMap K.1 (e.symm : A' →+* A) h).comp
          (quotientEquivOfRingEquiv e he he' J).toRingHom =
        Ideal.Quotient.factor hle := by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk K.1 (e.symm (e a)) = Ideal.Quotient.mk K.1 a
      rw [e.symm_apply_apply]
    have hcr : CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom ≫
          CommRingCat.ofHom (Ideal.quotientMap K.1 (e.symm : A' →+* A) h) =
        CommRingCat.ofHom (Ideal.Quotient.factor hle) :=
      CommRingCat.hom_ext hring
    have h2 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 (e.symm : A' →+* A) h)) ≫
          Spec.map (CommRingCat.ofHom (quotientEquivOfRingEquiv e he he' J).toRingHom) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)) :=
      (Spec.map_comp _ _).symm.trans (congrArg (fun f ↦ Spec.map f) hcr)
    rw [overS_quotientSystemOfRingEquiv, ← Category.assoc, h2, D.compatible _ K hle]

/-- The ring homomorphism underlying `continuousHomOfRingEquivSymm` is `e.symm`. -/
@[simp]
theorem continuousHomOfRingEquivSymm_toRingHom (D : QuotientSystem B S hS A) :
    (continuousHomOfRingEquivSymm B S hS e he he' D).toRingHom = (e.symm : A' →+* A) := rfl

end Transport

end AlgebraicGeometry.FormalSpace

end
