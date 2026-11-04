module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleKaroubiColimit

/-!
# Restricting a presented system of étale sheaves to the indices above a fixed one

Let `I` be a directed set and `i₀ ∈ I`. The indices `i ≥ i₀` form a directed set `GeIndex i₀`,
cofinal in `I`. Restricting an inverse system of schemes `D : Iᵒᵖ ⥤ Scheme`, a cone over it and a
system of abelian sheaves on it in the sense of [Stacks, Tag 0EZL] to these indices changes
neither the limit nor the colimit of the inverse images: a limit cone restricts to a limit cone
and a colimit presentation to a colimit presentation.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.GeIndex` — the indices above `i₀`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.geIndexOpFunctor` — their inclusion, on
  opposite categories.
* `Stacks.EtaleCohomology.EtaleSheafSystem.restrictIndex` — the restriction of a system.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isLimit_whisker_geIndexOpFunctor` — a limit
  cone restricts to a limit cone.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_restrictIndex` — a
  colimit presentation restricts to a colimit presentation.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

section Index

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I)

/-- The indices above `i₀`. -/
abbrev GeIndex : Type v := {i : I // i₀ ≤ i}

/-- The indices above `i₀` form a nonempty set. -/
instance : Nonempty (GeIndex i₀) := ⟨⟨i₀, le_rfl⟩⟩

/-- The indices above `i₀` form a directed set. -/
instance : IsDirected (GeIndex i₀) (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩

/-- The inclusion of the indices above `i₀` into `I` is monotone. -/
theorem geIndex_val_monotone : Monotone (Subtype.val : GeIndex i₀ → I) := fun _ _ h => h

/-- The inclusion of the indices above `i₀`. -/
abbrev geIndexFunctor : GeIndex i₀ ⥤ I := (geIndex_val_monotone i₀).functor

/-- The inclusion of the indices above `i₀` is a final functor. -/
instance : (geIndexFunctor i₀).Final :=
  (Monotone.final_functor_iff (geIndex_val_monotone i₀)).mpr fun i => by
    obtain ⟨c, h₁, h₂⟩ := directed_of (· ≤ ·) i i₀
    exact ⟨⟨c, h₂⟩, h₁⟩

/-- The inclusion of the indices above `i₀`, on opposite categories. -/
abbrev geIndexOpFunctor : (GeIndex i₀)ᵒᵖ ⥤ Iᵒᵖ := (geIndexFunctor i₀).op

/-- The inclusion of the indices above `i₀`, on opposite categories, is an initial functor. -/
instance : (geIndexOpFunctor i₀).Initial := inferInstanceAs (geIndexFunctor i₀).op.Initial

/-- **A limit cone restricts to a limit cone** over the indices above `i₀`. -/
def isLimit_whisker_geIndexOpFunctor {C : Type*} [Category* C] {D : Iᵒᵖ ⥤ C} {c : Cone D}
    (hc : IsLimit c) : IsLimit (c.whisker (geIndexOpFunctor i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv (geIndexOpFunctor i₀) c).symm hc

end Index

section System

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) {D : Iᵒᵖ ⥤ Scheme.{u}}
  {A : Type w} [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]
  [∀ (i j : (GeIndex i₀)ᵒᵖ) (a : i ⟶ j),
    (systemPushforward (geIndexOpFunctor i₀ ⋙ D) A a).IsRightAdjoint]

/-- **The restriction of a system of sheaves to the indices above `i₀`.** -/
def _root_.Stacks.EtaleCohomology.EtaleSheafSystem.restrictIndex (F : EtaleSheafSystem D A) :
    EtaleSheafSystem (geIndexOpFunctor i₀ ⋙ D) A where
  obj j := F.obj ((geIndexOpFunctor i₀).obj j)
  map a := F.map ((geIndexOpFunctor i₀).map a)
  map_comp a b := F.map_comp ((geIndexOpFunctor i₀).map a) ((geIndexOpFunctor i₀).map b)

end System

section Presentation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]

/-- **A colimit presentation restricts to a colimit presentation** over the indices above `i₀`. -/
theorem isColimitPresentation_restrictIndex {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢}
    (h : IsColimitPresentation F 𝒢 ι) :
    IsColimitPresentation (c := c.whisker (geIndexOpFunctor i₀)) (F.restrictIndex i₀) 𝒢
      (fun j => ι ((geIndexOpFunctor i₀).obj j)) :=
  isColimitPresentation_of_isColimit (fun a => h.compatible ((geIndexOpFunctor i₀).map a))
    ((Functor.Final.isColimitWhiskerEquiv (geIndexFunctor i₀) _).symm
      (isColimit_systemKaroubiCocone h))

end Presentation

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
