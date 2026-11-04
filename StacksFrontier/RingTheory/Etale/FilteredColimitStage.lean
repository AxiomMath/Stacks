module

import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

universe t w u

/-!
# An étale algebra over a filtered colimit of rings comes from a stage

Let `A = colim_{i ∈ J} A_i` be a filtered colimit of commutative rings and let `A → B` be étale.
This file proves item (9) of Stacks 00U2: there are an index `i` and an étale `A_i`-algebra `B_i`
with `B ≅ A ⊗_{A_i} B_i` as `A`-algebras.

The colimit is an arbitrary filtered diagram `F : J ⥤ CommRingCat` together with a colimiting
cocone `c`, whose vertex is `A` and whose legs `A_i → A` are the comparison maps; the algebra
structure of `A` over the stage `A_i` in the conclusion is pinned to be the leg `c.ι.app i`.

## The proof

This is the source's proof. By item (8), which is Mathlib's `Algebra.Etale.exists_subalgebra_fg`,
the étale algebra `B` over `A` is already the base change of an étale algebra `B₀` over a
`ℤ`-subalgebra `A₀ ⊆ A` of finite type, so `B ≅ A ⊗_{A₀} B₀`. Since `ℤ` is Noetherian, `A₀` is of
finite presentation over `ℤ`, hence the inclusion `A₀ → A` factors through a stage: there is a
ring map `ψ : A₀ → A_i` with `A₀ → A_i → A` the inclusion
(`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`, read at the initial object
`ULift ℤ` of `CommRingCat`, where every map is a map over the base and the compatibility
conditions are automatic). Now `B_i = A_i ⊗_{A₀} B₀` is étale over `A_i`, being a base change of
an étale algebra, and
`A ⊗_{A_i} B_i = A ⊗_{A_i} (A_i ⊗_{A₀} B₀) ≅ A ⊗_{A₀} B₀ ≅ B`
by `Algebra.TensorProduct.cancelBaseChange`, the last step using that `A₀ → A_i → A` is the
inclusion.

## Main results

* `Algebra.Etale.exists_etale_stage_of_isColimit`: item (9) of Stacks 00U2.

## Implementation notes

The index category is an arbitrary filtered category rather than a directed preorder, since the
source says "filtered colimit"; what is assumed of it is only `CategoryTheory.IsFiltered`. As in
`StacksFrontier.RingTheory.Etale.ColimitBaseChange` (Stacks 07RI) the instance
`PreservesColimit F (forget CommRingCat)` is carried along: it says that the colimit of rings is
computed on underlying sets, which is what makes `A` the colimit of the `A_i` rather than merely
the vertex of some colimiting cocone of a diagram of rings. It is automatic for a small index
category, by `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`.

The stage `B_i` is returned together with its `CommRing` and `Algebra A_i` structures, as the
`A_i` are the values of a diagram in `CommRingCat` and carry no algebra structure of their own.
For the same reason the `A_i`-algebra structure of `A` is introduced by a `letI` inside the
statement: the tensor product `A ⊗_{A_i} B_i` cannot be spelled without it, and pinning it to the
cocone leg is what makes the conclusion say that `B` is the base change along the comparison map
`A_i → A` of the source rather than along some other map.

A pushout-square form of this statement, for a small index category, is `exists_isPushout_etale` in
`StacksFrontier.RingTheory.Etale.FilteredColimit.Basic`, where it is used (untagged) as the spreading
out property of the morphism property of étale ring maps; the statement here is the source's own,
in the language of algebras and with the tensor product as the model of the base change.

## Faithfulness

Every hypothesis is used. Étaleness of `A → B` cannot be weakened to finite presentation: with
`A = ℚ = colim_n ℤ[1/n!]` and `B = ℚ[x] ⧸ (x ^ 2)` the conclusion would exhibit `B` as a base
change of an étale algebra, hence as étale over `A`, which it is not. Filteredness supplies the
index, as `0 ∈ I` does in the source: over an empty index category the conclusion asserts an `i`
that does not exist. Nothing is assumed Noetherian: the Noetherian ring of the proof is `ℤ`,
while the stages `A_i`, the colimit `A` and the algebras `B₀`, `B_i`, `B` are arbitrary. The
instantiation is not degenerate: for `A = ℚ = colim_n ℤ[1/n!]` and
`B = ℚ[x] ⧸ (x * (x - 2))` the conclusion holds exactly for those stages in which `2` is
invertible, so the index produced is genuinely constrained.

The conclusion is the source's, not a weakening: the isomorphism is an isomorphism of
`A`-algebras, so it is compatible with the structure maps of `B` and of `A ⊗_{A_i} B_i`, and
`A_i → B_i` is asserted étale, not merely smooth or of finite presentation.

## References

* [StacksProject 00U2](https://stacks.math.columbia.edu/tag/00U2)

## Tags

étale, filtered colimit, base change, spreading out, descent
-/

open CategoryTheory Limits TensorProduct

/-- **Item (9) of Stacks 00U2.** Let `A = colim_{i ∈ J} A_i` be a filtered colimit of rings,
computed on underlying sets, and let `B` be an étale `A`-algebra. Then there are an index `i` and
an étale `A_i`-algebra `B_i` with `B ≅ A ⊗_{A_i} B_i` as `A`-algebras, the `A_i`-algebra structure
of `A` being the comparison map `A_i → A`. -/
@[stacks 00U2 "(9) The filtered colimit `A = colim A_i` is an arbitrary filtered diagram
`F : J ⥤ CommRingCat` together with a colimiting cocone `c` with vertex `A`, plus the instance
saying the colimit is computed on underlying sets; the stages `A_i` are `F.obj i` and the
comparison maps are the legs `c.ι.app i`, which are also the `A_i`-algebra structure of `A` in the
conclusion. The isomorphism `B ≅ A ⊗_{A_i} B_i` is one of `A`-algebras, with the tensor product as
the model of the base change. The existing registration of item (5) is
`Algebra.etaleLocus_eq_of_isPushout`; item (8), which this is deduced from, is Mathlib's
`Algebra.Etale.exists_subalgebra_fg`. See the module docstring."]
theorem Algebra.Etale.exists_etale_stage_of_isColimit {J : Type w} [Category.{t} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) {c : Cocone F} (hc : IsColimit c)
    [PreservesColimit F (forget CommRingCat)]
    (B : Type*) [CommRing B] [Algebra (c.pt : Type u) B] [Algebra.Etale (c.pt : Type u) B] :
    ∃ (i : J) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i : Type u) Bᵢ),
      Algebra.Etale (F.obj i : Type u) Bᵢ ∧
        (letI : Algebra (F.obj i : Type u) (c.pt : Type u) := (c.ι.app i).hom.toAlgebra;
          Nonempty (B ≃ₐ[(c.pt : Type u)] (c.pt : Type u) ⊗[(F.obj i : Type u)] Bᵢ)) := by
  obtain ⟨A₀, B₀, _, _, hfg, hB₀, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg ℤ (c.pt : Type u) B
  have hA₀ : Algebra.FinitePresentation ℤ ↥A₀ :=
    Algebra.FinitePresentation.of_finiteType.mp ⟨A₀.fg_top.mpr hfg⟩
  have hfp : (CommRingCat.isInitial.to (CommRingCat.of ↥A₀)).hom.FinitePresentation := by
    rw [CommRingCat.isInitial.hom_ext (CommRingCat.isInitial.to (CommRingCat.of ↥A₀))
      (CommRingCat.ofHom ((algebraMap ℤ ↥A₀).comp ULift.ringEquiv.toRingHom)),
      CommRingCat.hom_ofHom]
    exact (RingHom.finitePresentation_algebraMap.mpr hA₀).comp
      (.of_bijective ULift.ringEquiv.bijective)
  obtain ⟨i, ψ, -, hψ⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of (ULift.{u} ℤ)) F
    { app := fun _ ↦ CommRingCat.isInitial.to _
      naturality := fun _ _ _ ↦ CommRingCat.isInitial.hom_ext _ _ }
    (CommRingCat.isInitial.to (CommRingCat.of ↥A₀)) c hc hfp
    (CommRingCat.ofHom (algebraMap ↥A₀ (c.pt : Type u)))
    (fun _ ↦ CommRingCat.isInitial.hom_ext _ _)
  let : Algebra ↥A₀ (F.obj i : Type u) := ψ.hom.toAlgebra
  let : Algebra (F.obj i : Type u) (c.pt : Type u) := (c.ι.app i).hom.toAlgebra
  have : IsScalarTower ↥A₀ (F.obj i : Type u) (c.pt : Type u) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      have h := congrArg (fun φ : CommRingCat.of ↥A₀ ⟶ c.pt ↦ φ.hom x) hψ
      simpa [RingHom.algebraMap_toAlgebra] using h
  exact ⟨i, (F.obj i : Type u) ⊗[↥A₀] B₀, inferInstance, inferInstance, inferInstance,
    ⟨e.trans (Algebra.TensorProduct.cancelBaseChange ↥A₀ (F.obj i : Type u) (c.pt : Type u)
      (c.pt : Type u) B₀).symm⟩⟩

/-- **Item (9) of Stacks 00U2** over a small filtered index category, which is the source's own
hypothesis: there the colimit of rings is computed on underlying sets automatically, by
`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`, so no instance is carried.

This is `Algebra.Etale.exists_etale_stage_of_isColimit`, which is tagged, read at a small index
category. -/
theorem Algebra.Etale.exists_etale_stage_of_isColimit_of_smallCategory {J : Type u}
    [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) {c : Cocone F} (hc : IsColimit c)
    (B : Type*) [CommRing B] [Algebra (c.pt : Type u) B] [Algebra.Etale (c.pt : Type u) B] :
    ∃ (i : J) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i : Type u) Bᵢ),
      Algebra.Etale (F.obj i : Type u) Bᵢ ∧
        (letI : Algebra (F.obj i : Type u) (c.pt : Type u) := (c.ι.app i).hom.toAlgebra;
          Nonempty (B ≃ₐ[(c.pt : Type u)] (c.pt : Type u) ⊗[(F.obj i : Type u)] Bᵢ)) :=
  Algebra.Etale.exists_etale_stage_of_isColimit F hc B

end
