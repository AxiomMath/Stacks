module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatModWeakIdeal
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# From the weak ideals of definition to every open ideal

Let `φ : A → C` be a taut continuous homomorphism of linearly topologized rings with `A`
weakly admissible. The ring-theoretic descent lemmas of Stacks 0GXL, 0GXM, 0GXP and 0GXQ all
ask that the induced map `A ⧸ I → C ⧸ closure (I C)` be faithfully flat for every *open* ideal
`I` of `A`, whereas the geometry produces it only for the *weak ideals of definition* of `A`:
those are the ideals whose closed extension is cut out by a quotient stage of `Spf C` over a
quotient stage of `Spf A`. This file bridges the two.

The point is an instance of **Stacks 0AMZ**. Fix a weak ideal of definition `I₀ ⊆ I`. Tautness
makes `closure (I₀ C)` an open — hence closed — ideal of `C`, so

  `closure (I C) = closure (I₀ C) + I C`,

the right-hand side already being closed. Dividing,

  `C ⧸ closure (I C) = (C ⧸ closure (I₀ C)) ⊗_{A ⧸ I₀} (A ⧸ I)`,

which is faithfully flat over `A ⧸ I` because `A ⧸ I₀ → C ⧸ closure (I₀ C)` is faithfully flat
and faithful flatness is stable under base change. Both quotients are realised by the third
isomorphism theorem rather than by a tensor product: `RingHom.faithfullyFlat_quotientMap`
already carries the base change along `A ⧸ I₀ → (A ⧸ I₀) ⧸ I`, and `DoubleQuot` identifies the
two iterated quotients with `A ⧸ I` and `C ⧸ closure (I C)`.

## Main results

* `TopologicalRing.closure_map_eq_sup_closure_map_of_le`: the identity
  `closure (I C) = closure (I₀ C) + I C` for `I₀ ⊆ I` with `closure (I₀ C)` open.
* `RingHom.faithfullyFlat_closure_quotientMap_of_isOpen`: faithful flatness of
  `A ⧸ I → C ⧸ closure (I C)` for every open ideal `I`, given it for every weak ideal of
  definition.

## References

* [Stacks Project, Tag 0AMX](https://stacks.math.columbia.edu/tag/0AMX)
* [Stacks Project, Tag 0AMZ](https://stacks.math.columbia.edu/tag/0AMZ)
* [Stacks Project, Tag 0GXL](https://stacks.math.columbia.edu/tag/0GXL)
-/

@[expose] public section

universe u

namespace TopologicalRing

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- The closed extension of an open ideal `I` of `A` is reached from that of any smaller ideal
`I₀` whose own closed extension is open: `closure (I C) = closure (I₀ C) + I C`.

The right-hand side contains the open ideal `closure (I₀ C)`, so it is open and therefore
closed, and it contains `I C`; that gives one inclusion. The other is monotonicity of the
closure together with `I C ⊆ closure (I C)`. -/
public theorem closure_map_eq_sup_closure_map_of_le (φ : A →+* C) {I₀ I : Ideal A}
    (hle : I₀ ≤ I) (hopen : IsOpen (Ideal.closure (I₀.map φ) : Set C)) :
    Ideal.closure (I.map φ) = Ideal.closure (I₀.map φ) ⊔ I.map φ := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le
    (Submodule.topologicalClosure_mono (Ideal.map_mono hle)) fun _ hy ↦ subset_closure hy)
  exact closure_minimal
    (show (I.map φ : Set C) ⊆ ((Ideal.closure (I₀.map φ) ⊔ I.map φ : Ideal C) : Set C) from
      show I.map φ ≤ Ideal.closure (I₀.map φ) ⊔ I.map φ from le_sup_right)
    ((Ideal.closure (I₀.map φ) ⊔ I.map φ).toAddSubgroup.isClosed_of_isOpen
      (Ideal.isOpen_of_isOpen_subideal le_sup_left hopen))
    (show x ∈ closure ((I.map φ : Ideal C) : Set C) from hx)

end TopologicalRing

namespace RingHom

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]

/-- **The passage from the weak ideals of definition of `A` to all its open ideals.** Let
`φ : A → C` be a taut homomorphism with `A` weakly admissible. If the induced map
`A ⧸ J → C ⧸ closure (J C)` is faithfully flat for every weak ideal of definition `J` of `A`,
then it is faithfully flat for every open ideal `I` of `A`.

Choose a weak ideal of definition `I₀ ⊆ I`, which exists because the weak ideals of definition
of a weakly admissible ring are a fundamental system of neighbourhoods of zero. Writing
`K₀ = closure (I₀ C)`, the map `A ⧸ I₀ → C ⧸ K₀` is faithfully flat, hence so is its base
change along the quotient by the image of `I` in `A ⧸ I₀`. By
`TopologicalRing.closure_map_eq_sup_closure_map_of_le` — an instance of Stacks 0AMZ — that base
change is `A ⧸ I → C ⧸ closure (I C)` once the two iterated quotients are identified by the
third isomorphism theorem. -/
public theorem faithfullyFlat_closure_quotientMap_of_isOpen
    (hA : TopologicalRing.IsWeaklyAdmissible A) (φ : A →+* C) (htaut : RingHom.IsTaut φ)
    (hff : ∀ J : Ideal A, TopologicalRing.IsWeakIdealOfDefinition J →
      (Ideal.quotientMap (Ideal.closure (J.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure)).FaithfullyFlat)
    (I : Ideal A) (hI : IsOpen (I : Set A)) :
    (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FaithfullyFlat := by
  obtain ⟨I₀, hI₀, hsub⟩ :=
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).mem_iff.mp
      (hI.mem_nhds I.zero_mem)
  have hle : I₀ ≤ I := hsub
  have hsup : Ideal.closure (I.map φ) = Ideal.closure (I₀.map φ) ⊔ I.map φ :=
    TopologicalRing.closure_map_eq_sup_closure_map_of_le φ hle (htaut.1 I₀ hI₀.1)
  set K₀ : Ideal C := Ideal.closure (I₀.map φ)
  set ψ : A ⧸ I₀ →+* C ⧸ K₀ :=
    Ideal.quotientMap K₀ φ (Ideal.map_le_iff_le_comap.mp subset_closure) with hψ
  set Ibar : Ideal (A ⧸ I₀) := I.map (Ideal.Quotient.mk I₀) with hIbar
  have hθ := RingHom.faithfullyFlat_quotientMap ψ (hff I₀ hI₀) Ibar
  have hmap : Ibar.map ψ = (I.map φ).map (Ideal.Quotient.mk K₀) := by
    rw [hIbar, Ideal.map_map, Ideal.map_map, hψ, Ideal.quotientMap_comp_mk]
  -- the source: the third isomorphism theorem for `I₀ ≤ I`
  set e : (A ⧸ I₀) ⧸ Ibar ≃+* A ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hle
  -- the target: the same for `K₀ ≤ closure (I C)`, after Stacks 0AMZ
  set d : (C ⧸ K₀) ⧸ Ibar.map ψ ≃+* C ⧸ Ideal.closure (I.map φ) :=
    (Ideal.quotEquivOfEq hmap).trans
      ((DoubleQuot.quotQuotEquivQuotSup K₀ (I.map φ)).trans
        (Ideal.quotEquivOfEq hsup.symm))
  have key : ((d : (C ⧸ K₀) ⧸ Ibar.map ψ →+* C ⧸ Ideal.closure (I.map φ)).comp
        (Ideal.quotientMap (Ibar.map ψ) ψ Ideal.le_comap_map)).comp
      (e.symm : A ⧸ I →+* (A ⧸ I₀) ⧸ Ibar) =
      Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  rw [← key]
  exact RingHom.FaithfullyFlat.respectsIso.2 _ e.symm
    (RingHom.FaithfullyFlat.respectsIso.1 _ d hθ)

end RingHom

end
