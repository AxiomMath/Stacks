module

public import Mathlib.Order.ULift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionExists
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat resolutions with flat terms and a termwise surjective quasi-isomorphism

Let `(C, 𝒪)` be a ringed site and `G` a cochain complex of `𝒪`-modules. The resolution of
[Stacks, Tag 077J] produces a K-flat complex together with a quasi-isomorphism onto `G`
(`Stacks.SheafOfModules.exists_isKFlat_quasiIso`). This file supplies the two further
properties that [Stacks, Tag 06YS] asserts of the same resolution, so that the tag sits on the
full statement: the terms of the K-flat complex are flat `𝒪`-modules, and the
quasi-isomorphism is an epimorphism in every degree.

## Main results

* `CochainComplex.isIso_ιTruncLE_f`: below the truncation bound the canonical map
  `K.truncLE n ⟶ K` is an isomorphism in that degree.
* `Stacks.SheafOfModules.isFlat_colimit_system_X`: every term of the colimit of the ladder of
  [Stacks, Tag 077J] is a flat `𝒪`-module.
* `Stacks.SheafOfModules.epi_colimitComparison_f`: the colimit comparison of that ladder is an
  epimorphism in every degree.
* `Stacks.SheafOfModules.exists_isKFlat_isFlat_quasiIso_epi`: [Stacks, Tag 06YS].

## Implementation notes

Termwise flatness. Degreewise evaluation of complexes preserves colimits, so the degree `i`
term of `colimit L.system` is the colimit of the degree `i` terms of the rungs, each of which
is a direct sum of extensions by zero of structure sheaves of slice sites and hence flat by
`isFlat_of_isSumOfExtensionByZeroStructureSheaves`. A filtered colimit of flat sheaves of
modules is flat by [Stacks, Tag 05NG], i.e. `FlatColimits.isFlat_colimit`.

That last statement is indexed by a filtered category `I : Type z` with `Category.{z} I`,
where `z` is the universe of the module sections; for a `RingedSite.{u, u, u}` that is `u`,
while the ladder is indexed by `ℕ`, whose preorder category is `Category.{0} ℕ`. The two meet
at `ULift.{u} ℕ`: it is a preorder in `Type u`, hence filtered with homs in `Type u`, and it is
equivalent to `ℕ` as a category by `uliftNatEquiv`, so `HasColimit.isoOfEquivalence` identifies
the two colimits. Nothing about the ladder is re-proved along the way — the diagram that
`isFlat_colimit` is applied to is literally the ladder precomposed with that equivalence.

Termwise surjectivity. `ResolutionByDirectSumsExtensionsByZero.epi_f` makes each rung
termwise epimorphic onto a truncation of `G`, and `colimitComparison_fac` factors the colimit
comparison through it after the canonical map out of that truncation. In a fixed degree `i`
choose a rung resolving `τ_{≤ n+1} G` with `i < n + 1`; there the canonical map
`G.truncLE (n+1) ⟶ G` is an isomorphism, so the composite into `G.X i` is an epimorphism and
the comparison, which it factors through, is one too.

Mathlib records that `K.ιTruncLE n` is a degreewise monomorphism and that it is an isomorphism
once `K` is strictly supported below `n`, but not that it is an isomorphism in each individual
degree below `n`; `CochainComplex.isIso_ιTruncLE_f` fills that in, by transporting the
dual statement `HomologicalComplex.isIso_restrictionToTruncGE'` across the opposite category,
which is how `ιTruncLE` is defined in the first place.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CochainComplex

/-- Below the truncation bound the canonical monomorphism `K.truncLE n ⟶ K` is an isomorphism
in that degree. The canonical truncation only modifies the complex in degree `n`, where it
takes the cycles, and above it, where it vanishes. -/
public theorem isIso_ιTruncLE_f {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (n i : ℤ) (hi : i < n) :
    IsIso ((K.ιTruncLE n).f i) := by
  have hfi : (ComplexShape.embeddingUpIntLE n).f (n - i).natAbs = i := by
    rw [ComplexShape.embeddingUpIntLE_f, Int.natAbs_of_nonneg (by lia)]
    lia
  have hb : ¬ (ComplexShape.embeddingUpIntLE n).BoundaryLE (n - i).natAbs := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    lia
  show IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f i).unop
  have h3 : IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f i) := by
    dsimp only [HomologicalComplex.πTruncGE, HomologicalComplex.truncGE]
    rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _
      (hi := (show (ComplexShape.embeddingUpIntLE n).op.f (n - i).natAbs = i from hfi))]
    exact K.op.isIso_restrictionToTruncGE' _ _ (by simpa using hb)
  infer_instance

end CochainComplex

namespace Stacks.SheafOfModules

/-- The monotone map `ULift.down`, as a functor between the preorder categories. -/
private def uliftNatFunctor : ULift.{u} ℕ ⥤ ℕ :=
  Monotone.functor (f := ULift.down) fun _ _ h => h

/-- The monotone map `ULift.up`, as a functor between the preorder categories. -/
private def natUliftFunctor : ℕ ⥤ ULift.{u} ℕ :=
  Monotone.functor (f := ULift.up) fun _ _ h => h

/-- `ULift.{u} ℕ` and `ℕ` are equivalent as categories. This moves a sequential diagram into a
category whose objects and morphisms both live in `Type u`, which is the shape that
`Stacks.SheafOfModules.FlatColimits.isFlat_colimit` is stated for. -/
private def uliftNatEquiv : ULift.{u} ℕ ≌ ℕ where
  functor := uliftNatFunctor
  inverse := natUliftFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

/-- Every term of the colimit of the ladder of [Stacks, Tag 077J] is a flat `𝒪`-module: it is a
filtered colimit of the corresponding terms of the rungs, which are direct sums of extensions
by zero of the structure sheaves of slice sites and hence flat. -/
public theorem isFlat_colimit_system_X
    {G : CochainComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ}
    (L : ResolutionByDirectSumsExtensionsByZero X G) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((colimit L.system).X i) := by
  let A := _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  let F : ULift.{u} ℕ ⥤ A := uliftNatEquiv.functor ⋙ L.system ⋙ ev
  refine isFlat_of_iso X (?_ : colimit F ≅ (colimit L.system).X i)
    (FlatColimits.isFlat_colimit (O := X.O) F fun _ =>
      isFlat_of_isSumOfExtensionByZeroStructureSheaves X (L.term_isSum _ i))
  exact HasColimit.isoOfEquivalence uliftNatEquiv (Iso.refl _) ≪≫
    (preservesColimitIso ev L.system).symm

/-- The colimit comparison of the ladder of [Stacks, Tag 077J] is an epimorphism in every
degree: in degree `i` it is factored through by the map out of a rung resolving `τ_{≤ n+1} G`
with `i < n + 1`, which is an epimorphism onto the truncation followed by an isomorphism. -/
public theorem epi_colimitComparison_f
    {G : CochainComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ}
    (L : ResolutionByDirectSumsExtensionsByZero X G) (i : ℤ) :
    Epi (L.colimitComparison.f i) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i < (n : ℤ) + 1 :=
    ⟨i.toNat, by have := Int.self_le_toNat i; lia⟩
  have h : (colimit.ι L.system n).f i ≫ L.colimitComparison.f i =
      (L.toTruncation n).f i ≫ (G.ιTruncLE ((n : ℤ) + 1)).f i := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, L.colimitComparison_fac n]
  have : IsIso ((G.ιTruncLE ((n : ℤ) + 1)).f i) :=
    CochainComplex.isIso_ιTruncLE_f G _ i hn
  have : Epi ((L.toTruncation n).f i) := L.epi_f n i
  exact epi_of_epi_fac h

section Resolution

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 06YS.** Every cochain complex `G` of modules on a ringed site receives a termwise
surjective quasi-isomorphism from a K-flat complex whose terms are flat.

The complex is the colimit of the ladder of [Stacks, Tag 077J]. It is K-flat because each rung
is bounded above with flat terms, hence K-flat by [Stacks, Tag 06YQ], and a sequential colimit
of K-flat complexes is K-flat by [Stacks, Tag 06YE]. Its terms are flat because they are
filtered colimits of the flat terms of the rungs ([Stacks, Tag 05NG]), and the comparison is
termwise surjective because each rung is termwise surjective onto a truncation of `G`. -/
@[stacks 06YS]
public theorem exists_isKFlat_isFlat_quasiIso_epi
    (G : CochainComplex
      (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) :
    ∃ (K : CochainComplex
        (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ) (s : K ⟶ G),
      IsKFlat X.O K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
      QuasiIso s ∧ ∀ i : ℤ, Epi (s.f i) := by
  obtain ⟨L⟩ := exists_resolutionByDirectSumsExtensionsByZero X G
  exact ⟨colimit L.system, L.colimitComparison,
    kFlat_colimit X.O L.system (isKFlat_resolutionByDirectSumsExtensionsByZero_system X L),
    isFlat_colimit_system_X X L, L.colimit_quasiIso, epi_colimitComparison_f X L⟩

end Resolution

end Stacks.SheafOfModules

end
