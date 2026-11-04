module

public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatModWeakIdeal
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatQuotientOpenIdeal
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# Noetherian adic rings descend along the completion of a faithfully flat ring map

Let `A` be a weakly admissible topological ring and let `c : A →+* R₁` be a faithfully flat ring
map, `R₁` carrying no topology. If the completion `(R₁)^∧ = lim R₁ ⧸ J R₁` of Stacks 0AN6 is an
adic Noetherian topological ring, then so is `A`.

This is the ring-theoretic content of the step of Stacks 0AKX at the property "Noetherian": an
affine formal algebraic space covered by finitely many Noetherian ones, by representable étale
morphisms, is Noetherian. By Stacks 0AN8 and Stacks 0AN9 the covering is the formal spectrum of
the completion of a faithfully flat étale ring map, and the argument is the one of Stacks 0AKW.

## Main results

* `TopologicalRing.CompletionOver.faithfullyFlat_quotientMap_closure_canonicalMap`: for a
  faithfully flat `c : A →+* R₁` over a weakly pre-admissible `A` and every open ideal `I` of
  `A`, the map `A ⧸ I → (R₁)^∧ ⧸ (I (R₁)^∧)‾` is faithfully flat.
* `TopologicalRing.CompletionOver.isNoetherianAdic_of_faithfullyFlat`: the descent.

## Implementation notes

For a weak ideal of definition `J` of `A` the closure of `J (R₁)^∧` is the kernel of the
projection `(R₁)^∧ → R₁ ⧸ J R₁` (Stacks 0AN6), which is surjective, so `A ⧸ J → (R₁)^∧ ⧸ (J
(R₁)^∧)‾` is `A ⧸ J → R₁ ⧸ J R₁` up to an isomorphism of its target, a quotient of the faithfully
flat `c`. Faithful flatness passes from `J` to every open ideal above it by
`RingHom.faithfullyFlat_quotientMap_closure_of_le`.

The canonical map `A → (R₁)^∧` is then continuous, taut, with faithfully flat quotients by open
ideals, and its target has a finitely generated ideal of definition, so Stacks 0GXQ gives `A` a
finitely generated ideal of definition `J₀` defining its topology. `A ⧸ J₀` is Noetherian by
Stacks 033E, its faithfully flat extension being a quotient of the Noetherian `(R₁)^∧`, and `A`,
complete for the `J₀`-adic topology, is Noetherian by Stacks 05GH.

## References

* [Stacks Project, Tag 033E](https://stacks.math.columbia.edu/tag/033E)
* [Stacks Project, Tag 05GH](https://stacks.math.columbia.edu/tag/05GH)
* [Stacks Project, Tag 0AKW](https://stacks.math.columbia.edu/tag/0AKW)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0GXQ](https://stacks.math.columbia.edu/tag/0GXQ)
-/

@[expose] public section

universe u

namespace TopologicalRing.CompletionOver

variable {A R₁ : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing R₁]

omit [IsTopologicalRing A] in
/-- For a faithfully flat ring map `c : A →+* R₁` over a weakly pre-admissible topological ring
`A` and an open ideal `I` of `A`, the map `A ⧸ I → (R₁)^∧ ⧸ (I (R₁)^∧)‾` induced by the canonical
map into the completion of Stacks 0AN6 is faithfully flat.

For a weak ideal of definition `J ≤ I` the target `(R₁)^∧ ⧸ (J (R₁)^∧)‾` is `R₁ ⧸ J R₁`, through
the projection of the completion, so the map is the quotient of `c` by `J` up to an isomorphism;
faithful flatness then rises from `J` to `I`. -/
theorem faithfullyFlat_quotientMap_closure_canonicalMap
    (hA : TopologicalRing.IsWeaklyPreAdmissible A) (c : A →+* R₁) (hc : c.FaithfullyFlat)
    (I : Ideal A) (hI : IsOpen (I : Set A)) :
    (Ideal.quotientMap (Ideal.closure (I.map (canonicalMap c))) (canonicalMap c)
      (Ideal.map_le_iff_le_comap.mp fun _ hx ↦ subset_closure hx)).FaithfullyFlat := by
  obtain ⟨J₀, hJ₀⟩ := hA
  let J : WeakIdealOfDefinitionIndex A := ⟨J₀ ⊓ I, ⟨hJ₀.1.inter hI, fun x hx ↦ hJ₀.2 x hx.1⟩⟩
  have hopen : IsOpen ((Ideal.closure (J.1.map (canonicalMap c)) : Ideal (CompletionOver c)) :
      Set (CompletionOver c)) := by
    rw [← ker_projection_eq_closure]
    exact isOpen_ker_projection c J
  refine RingHom.faithfullyFlat_quotientMap_closure_of_le (canonicalMap c)
    (inf_le_right : J.1 ≤ I) hopen ?_
  -- the case of the weak ideal of definition `J`: the kernel of a projection
  have key : ∀ (K : Ideal (CompletionOver c)) (_hK : K = RingHom.ker (projection c J))
      (h : J.1 ≤ K.comap (canonicalMap c)),
      (Ideal.quotientMap K (canonicalMap c) h).FaithfullyFlat := by
    rintro K rfl h
    set e := RingHom.quotientKerEquivOfSurjective (projection_surjective c J) with he
    have hcomp : e.toRingHom.comp (Ideal.quotientMap (RingHom.ker (projection c J))
        (canonicalMap c) h) = Ideal.quotientMap (J.1.map c) c Ideal.le_comap_map := by
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
      simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
      rfl
    have hq : (Ideal.quotientMap (RingHom.ker (projection c J)) (canonicalMap c) h) =
        e.symm.toRingHom.comp (Ideal.quotientMap (J.1.map c) c Ideal.le_comap_map) := by
      rw [← hcomp, ← RingHom.comp_assoc]
      ext x
      simp
    rw [hq]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.faithfullyFlat_quotientMap c hc J.1)
      (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)
  exact key _ (ker_projection_eq_closure c J).symm _

/-- **An adic Noetherian completion over a faithfully flat ring map forces the base to be adic
Noetherian.** Let `A` be a weakly admissible topological ring and `c : A →+* R₁` a faithfully
flat ring map. If the completion `(R₁)^∧` of Stacks 0AN6 is adic and Noetherian, then `A` is
adic and Noetherian.

Stacks 0GXQ along the canonical map `A → (R₁)^∧` — continuous, taut, with faithfully flat
quotients by open ideals — gives `A` a finitely generated ideal of definition `J` defining its
topology; `A ⧸ J` is Noetherian by Stacks 033E, its faithfully flat extension
`(R₁)^∧ ⧸ (J (R₁)^∧)‾` being a quotient of a Noetherian ring; and `A`, complete for the
`J`-adic topology, is Noetherian by Stacks 05GH. -/
theorem isNoetherianAdic_of_faithfullyFlat [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (c : A →+* R₁) (hc : c.FaithfullyFlat)
    (hC : TopologicalRing.IsAdic (CompletionOver c) ∧ IsNoetherianRing (CompletionOver c)) :
    TopologicalRing.IsAdic A ∧ IsNoetherianRing A := by
  have : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hA.2.1
  have : T2Space A := hA.2.2
  have hCwa := completionOver_isWeaklyAdmissible c hA
  have : @CompleteSpace (CompletionOver c)
      (IsTopologicalAddGroup.rightUniformSpace (CompletionOver c)) := hCwa.2.1
  have : T2Space (CompletionOver c) := hCwa.2.2
  have : IsNoetherianRing (CompletionOver c) := hC.2
  have hB : ∃ K : Ideal (CompletionOver c), _root_.IsAdic K ∧ K.FG := by
    obtain ⟨K, -, hK⟩ := hC.1.1
    exact ⟨K, hK, IsNoetherian.noetherian K⟩
  obtain ⟨J, hJ, hJfg⟩ := exists_fg_ideal_of_definition_of_taut (canonicalMap c)
    (continuous_canonicalMap c) (isTaut_canonicalMap c hA.1)
    (faithfullyFlat_quotientMap_closure_canonicalMap hA.1 c hc) hB
  have hJopen : IsOpen (J : Set A) := by simpa using (isAdic_iff.mp hJ).1 1
  refine ⟨⟨⟨J, isIdealOfDefinition_of_isAdic hJ, hJ⟩, hA.2.2, hA.2.1⟩, ?_⟩
  have hquot : IsNoetherianRing (A ⧸ J) :=
    descent_noetherian _ (faithfullyFlat_quotientMap_closure_canonicalMap hA.1 c hc J hJopen)
      inferInstance
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : IsAdicComplete J A := hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  exact noetherian_of_isAdicComplete_fg A J hJfg inferInstance hquot

end TopologicalRing.CompletionOver

end
