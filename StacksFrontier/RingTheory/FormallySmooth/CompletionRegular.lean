module

public import StacksFrontier.RingTheory.FormallySmooth.Adic
public import StacksFrontier.RingTheory.FormallySmooth.Regularity
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Smoothing.PopescuTheorem

/-!
# Completion of a formally smooth local homomorphism

Let `f : A → B` be a local homomorphism of Noetherian local rings which is formally smooth for
the `𝔪_B`-adic topology. Completing `A` and `B` at their maximal ideals gives a local
homomorphism `f^ : A^ → B^` of complete Noetherian local rings. This file shows that `f^` is
again formally smooth for the `𝔪_{B^}`-adic topology [Stacks, Tag 07ED], hence regular by
[Stacks, Tag 07PM], hence a filtered colimit of smooth algebras by Popescu's theorem
[Stacks, Tag 07GC]. It also records that the extended ideal `𝔪_A B` is prime: the special fibre
`κ(𝔪_A) ⊗_A B = B / 𝔪_A B` is geometrically regular by [Stacks, Tag 07NQ], hence a regular local
ring, hence a domain [Stacks, Tag 00NP].

## Main results

* `formallySmoothNAdic_completion_mapRingHom`: the completed map is formally smooth for the
  adic topology of the maximal ideal of the completion of `B`.
* `isRegularRingHom_completion_mapRingHom`: the completed map is regular.
* `indSmooth_completion_mapRingHom`: the completion of `B` is ind-smooth over the completion
  of `A`.
* `isPrime_map_maximalIdeal_of_formallySmoothNAdic`: the extended maximal ideal `𝔪_A B` is
  prime.

## References

* [Stacks Project, Tag 07ED](https://stacks.math.columbia.edu/tag/07ED)
* [Stacks Project, Tag 07PM](https://stacks.math.columbia.edu/tag/07PM)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 07NQ](https://stacks.math.columbia.edu/tag/07NQ)
* [Stacks Project, Tag 00NP](https://stacks.math.columbia.edu/tag/00NP)
-/

@[expose] public noncomputable section

universe u

open IsLocalRing UniformSpace Stacks.FormallySmooth.TopologicalRings
open scoped TensorProduct

section Completion

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- If a local homomorphism `f : A → B` of Noetherian local rings is formally smooth for the
`𝔪_B`-adic topology, then so is its completion `A^ → B^` for the `𝔪_{B^}`-adic topology. -/
theorem formallySmoothNAdic_completion_mapRingHom (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal B)) :
    letI : WithIdeal A := ⟨maximalIdeal A⟩
    letI : WithIdeal B := ⟨maximalIdeal B⟩
    letI := isLocalRing_uniformCompletion (IsNoetherian.noetherian (maximalIdeal B))
    RingHom.FormallySmoothNAdic.{u}
      (Completion.mapRingHom f f.continuous_adic_of_isLocalHom)
      (maximalIdeal (Completion B)) := by
  let m : Ideal A := maximalIdeal A
  let n : Ideal B := maximalIdeal B
  have hm : m.FG := IsNoetherian.noetherian m
  have hn : n.FG := IsNoetherian.noetherian n
  have hc := f.continuous_adic_of_isLocalHom
  let : WithIdeal A := ⟨m⟩
  let : WithIdeal B := ⟨n⟩
  let := isLocalRing_uniformCompletion hn
  let fhat : Completion A →+* Completion B := Completion.mapRingHom f hc
  have htop : (let : TopologicalSpace A := m.adicTopology
      let : IsTopologicalRing A := m.nonarchimedean.toIsTopologicalRing
      let : IsLinearTopology A A := m.isLinearTopology
      let : TopologicalSpace B := n.adicTopology
      let : IsTopologicalRing B := n.nonarchimedean.toIsTopologicalRing
      let : IsLinearTopology B B := n.isLinearTopology
      IsFormallySmooth.{u} f) := by
    intro _ _ _ _ _ _
    exact ⟨hc, RingHom.formallySmoothTop_of_formallySmoothNAdic f n rfl hf⟩
  have hiff := isFormallySmooth_iff_adicCompletion m n hm hn f hc
  have hhat := hiff.2.mp (hiff.1.mp htop)
  let mhat : Ideal (Completion A) := m.map Completion.coeRingHom
  let nhat : Ideal (Completion B) := n.map Completion.coeRingHom
  have hdisc := ((isFormallySmooth_of_formallySmooth_and_isAdic_and_iff_discrete fhat).2
    mhat nhat hhat.1).mp hhat
  rw [maximalIdeal_uniformCompletion_eq_map hn]
  let : TopologicalSpace (Completion A) := ⊥
  let : DiscreteTopology (Completion A) := ⟨rfl⟩
  let : TopologicalSpace (Completion B) := nhat.adicTopology
  let : IsTopologicalRing (Completion B) := nhat.ringFilterBasis.isTopologicalRing
  exact (RingHom.formallySmoothTop_iff_formallySmoothNAdic fhat nhat rfl).mp hdisc.2

/-- If a local homomorphism `f : A → B` of Noetherian local rings is formally smooth for the
`𝔪_B`-adic topology, then its completion `A^ → B^` is a regular ring homomorphism. -/
theorem isRegularRingHom_completion_mapRingHom (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal B)) :
    letI : WithIdeal A := ⟨maximalIdeal A⟩
    letI : WithIdeal B := ⟨maximalIdeal B⟩
    IsRegularRingHom (Completion.mapRingHom f f.continuous_adic_of_isLocalHom) := by
  have hm : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have hn : (maximalIdeal B).FG := IsNoetherian.noetherian _
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  let := isNoetherianRing_uniformCompletion (maximalIdeal A)
  let := isNoetherianRing_uniformCompletion (maximalIdeal B)
  let := isLocalRing_uniformCompletion hm
  let := isLocalRing_uniformCompletion hn
  let := isLocalHom_mapRingHom hm hn f f.continuous_adic_of_isLocalHom
  let := isAdicComplete_maximalIdeal_uniformCompletion hm
  let := isAdicComplete_maximalIdeal_uniformCompletion hn
  exact ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
    (Completion.mapRingHom f f.continuous_adic_of_isLocalHom)).out 4 1).mp
    (formallySmoothNAdic_completion_mapRingHom f hf)

/-- If a local homomorphism `f : A → B` of Noetherian local rings is formally smooth for the
`𝔪_B`-adic topology, then the completion of `B` is a filtered colimit of smooth algebras over
the completion of `A`. -/
theorem indSmooth_completion_mapRingHom (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal B)) :
    letI : WithIdeal A := ⟨maximalIdeal A⟩
    letI : WithIdeal B := ⟨maximalIdeal B⟩
    letI : Algebra (Completion A) (Completion B) :=
      (Completion.mapRingHom f f.continuous_adic_of_isLocalHom).toAlgebra
    Stacks.Smoothing.IndSmooth (Completion A) (Completion B) := by
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  let := isNoetherianRing_uniformCompletion (maximalIdeal A)
  let := isNoetherianRing_uniformCompletion (maximalIdeal B)
  let : Algebra (Completion A) (Completion B) :=
    (Completion.mapRingHom f f.continuous_adic_of_isLocalHom).toAlgebra
  exact Stacks.Smoothing.indSmooth_of_isRegularRingMap _ _
    (Stacks.Smoothing.isRegularRingMap_of_regularRingHom _ _
      (isRegularRingHom_completion_mapRingHom f hf))

end Completion

/-- If a local homomorphism `f : A → B` of Noetherian local rings is formally smooth for the
`𝔪_B`-adic topology, then the extended ideal `𝔪_A B` is prime: the special fibre
`B / 𝔪_A B = κ(𝔪_A) ⊗_A B` is a geometrically regular local ring, hence a domain. -/
theorem isPrime_map_maximalIdeal_of_formallySmoothNAdic {A : Type u} {B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) [IsLocalHom f]
    (hf : RingHom.FormallySmoothNAdic.{u} f (maximalIdeal B)) :
    ((maximalIdeal A).map f).IsPrime := by
  let : Algebra A B := f.toAlgebra
  let fiber := ResidueField A ⊗[A] B
  have hgeo : Module.Flat A B ∧ Algebra.IsGeometricallyRegular (ResidueField A) fiber :=
    ((flat_geometricallyRegular_specialFiber_formallySmooth_tfae f).out 3 1).mp hf
  let := hgeo.2
  let : IsRegularRing fiber := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.lid (ResidueField A) fiber).toRingEquiv
  let : IsNoetherianRing fiber := isNoetherianRing_of_surjective B fiber
    Algebra.TensorProduct.includeRight.toRingHom
    (TensorProduct.mk_surjective A B (ResidueField A) residue_surjective)
  let : IsRegularLocalRing fiber := IsRegularLocalRing.of_isRegularRing_of_isLocalRing fiber
  let : IsDomain fiber := IsRegularLocalRing.isDomain fiber
  let e : (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≃+* fiber :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).toRingEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp (e.injective.isDomain e)

end
