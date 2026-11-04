module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence

/-!
# Quasi-isomorphisms of complexes of abelian sheaves, tested on sections over a basis

Let `X` be a topological space and let `𝔅` be a basis of its topology. This file proves that
a morphism `φ : K ⟶ L` of cochain complexes of abelian sheaves on `X` is a quasi-isomorphism as
soon as, for every `U ∈ 𝔅`, the morphism `Γ(U, K) ⟶ Γ(U, L)` of complexes of sections is a
quasi-isomorphism of complexes of abelian groups.

The proof passes through the mapping cone. Exactness of a complex of abelian sheaves in a degree
is a local condition (`Stacks.AbelianSheaves.exact_of_locallyLiftable`), and a basis provides,
around every point of every open, a member over which the sections are exact; so a complex of
abelian sheaves whose complexes of sections over the members of `𝔅` are exact is itself exact.
Taking sections is additive, hence commutes with mapping cones, and a morphism of complexes in an
abelian category is a quasi-isomorphism exactly when its mapping cone is acyclic.

## Main results

* `Stacks.AbelianSheaves.exactAt_of_forall_sections_exactAt`: **a complex of abelian sheaves is
  exact in a degree as soon as its complexes of sections over the members of a basis are.**
* `Stacks.AbelianSheaves.quasiIso_of_forall_sections_quasiIso`: **a morphism of `ℤ`-indexed
  cochain complexes of abelian sheaves is a quasi-isomorphism as soon as its morphisms of
  complexes of sections over the members of a basis are.**
* `Stacks.AbelianSheaves.quasiIso_of_forall_sections_quasiIso_nat`: the same for `ℕ`-indexed
  cochain complexes, such as de Rham complexes, by extension by zero to `ℤ`.

## References

* [Stacks Project, Tag 03CN](https://stacks.math.columbia.edu/tag/03CN)
* [Stacks Project, Tag 0A8E](https://stacks.math.columbia.edu/tag/0A8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.LerayLowDegree

universe u

namespace Stacks.AbelianSheaves

variable {X : TopCat.{u}} {𝔅 : Set (Opens X)}

/-- **A complex of abelian sheaves is exact in a degree as soon as its complexes of sections
over the members of a basis of the topology are.** Around every point of an open set `V` a
member `U ⊆ V` of the basis may be chosen; a cycle over `V` restricts to a cycle over `U`, which
is a boundary there. So every cycle is locally a boundary, which is exactness of a complex of
abelian sheaves. -/
theorem exactAt_of_forall_sections_exactAt {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) c) (i : ι)
    (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ U ∈ 𝔅, (((abelianSections.{u, u} X U).mapHomologicalComplex c).obj K).ExactAt i) :
    K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_locallyLiftable (J := Opens.grothendieckTopology X) _ fun V z hz => ?_
  refine ⟨Sieve.generate fun W (_ : W ⟶ V) => W ∈ 𝔅, ?_, ?_⟩
  · rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.1 h𝔅 hx
    exact ⟨U, homOfLE hUV, ⟨U, 𝟙 U, homOfLE hUV, hU, Category.id_comp _⟩, hxU⟩
  · rintro W p ⟨U, q, r, hU, rfl⟩
    have hex : ((K.sc i).map (abelianSections.{u, u} X U)).Exact :=
      (HomologicalComplex.exactAt_iff _ i).1 (h U hU)
    have hv : (K.sc i).g.hom.app (op U) ((K.sc i).X₂.obj.map r.op z) = 0 := by
      rw [NatTrans.naturality_apply, hz, map_zero]
    obtain ⟨t, ht⟩ := (ShortComplex.ab_exact_iff _).1 hex ((K.sc i).X₂.obj.map r.op z) hv
    refine ⟨(K.sc i).X₁.obj.map q.op t, ?_⟩
    have ht' : (K.sc i).f.hom.app (op U) t = (K.sc i).X₂.obj.map r.op z := ht
    rw [NatTrans.naturality_apply, ht', op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- **A morphism of `ℤ`-indexed cochain complexes of abelian sheaves is a quasi-isomorphism as
soon as its morphisms of complexes of sections over the members of a basis are.** Taking
sections over `U` carries the mapping cone of `φ` to the mapping cone of the morphism of
sections, which is acyclic for `U ∈ 𝔅`; so the mapping cone of `φ` is acyclic. -/
theorem quasiIso_of_forall_sections_quasiIso
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ}
    (φ : K ⟶ L) (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ U ∈ 𝔅,
      QuasiIso (((abelianSections.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  intro i
  refine exactAt_of_forall_sections_exactAt _ i h𝔅 fun U hU => ?_
  have hU := (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).1 (h U hU) i
  exact hU.of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ (abelianSections.{u, u} X U)).symm

/-- **A morphism of `ℕ`-indexed cochain complexes of abelian sheaves is a quasi-isomorphism as
soon as its morphisms of complexes of sections over the members of a basis are.** This is
`Stacks.AbelianSheaves.quasiIso_of_forall_sections_quasiIso` after extension by zero to `ℤ`,
which preserves and reflects quasi-isomorphisms and commutes with taking sections. -/
theorem quasiIso_of_forall_sections_quasiIso_nat
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ}
    (φ : K ⟶ L) (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ U ∈ 𝔅,
      QuasiIso (((abelianSections.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) :
    QuasiIso φ := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff φ ComplexShape.embeddingUpNat]
  refine quasiIso_of_forall_sections_quasiIso _ h𝔅 fun U hU => ?_
  have := h U hU
  have hext : QuasiIso (HomologicalComplex.extendMap
      (((abelianSections.{u, u} X U).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 this
  rw [← quasiIso_iff_comp_right _ (HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianSections.{u, u} X U) L ComplexShape.embeddingUpNat).inv,
    HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality]
  infer_instance

end Stacks.AbelianSheaves

end
