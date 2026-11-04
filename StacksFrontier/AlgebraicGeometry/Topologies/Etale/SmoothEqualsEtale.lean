module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmoothRefinement
public import StacksFrontier.CategoryTheory.Sites.Pretopology.PrecoverageUpToRefinement
public import StacksCore.Tactic.StacksAttribute

/-!
# The smooth and étale topologies on schemes coincide

The étale coverings are cofinal among the smooth ones — Tag 055V,
`AlgebraicGeometry.exists_etale_cover_refining_smooth_cover` — and conversely an étale covering
*is* a smooth covering. Mutual refinement of the two precoverages therefore identifies the two
generated Grothendieck topologies on the category of schemes:

`AlgebraicGeometry.Scheme.grothendieckTopology @Smooth = AlgebraicGeometry.Scheme.etaleTopology`.

This is an equality of topologies, not merely an equivalence of their sheaf categories, so every
statement about the big étale topology on schemes becomes a statement about the big smooth
topology by rewriting. Note that the two *precoverages* are emphatically not equal: a smooth
covering is not an étale covering. Only the generated topologies agree, which is the content of
Stacks 00VX (2) and the reason the source may say that the smooth and the étale topology "have
the same sheaves".

## Main results

* `AlgebraicGeometry.exists_etale_refinement_of_mem_smoothPrecoverage`: the presieve-level form
  of Tag 055V — a smooth covering presieve is refined by an étale covering presieve.
* `AlgebraicGeometry.Scheme.etalePrecoverage_le_smoothPrecoverage`: the easy direction, an étale
  morphism being smooth.
* `AlgebraicGeometry.Scheme.grothendieckTopology_smooth_eq_etaleTopology`: **the smooth and
  étale topologies on schemes are equal.**
* `AlgebraicGeometry.Scheme.isSheaf_smooth_iff_isSheaf_etale`: consequently a presheaf is a
  smooth sheaf exactly when it is an étale sheaf.

## Implementation notes

Tag 055V is stated for `AlgebraicGeometry.Scheme.Cover`, that is for an *indexed* family, while
a `CategoryTheory.Precoverage` is a collection of presieves, which have forgotten their
indexing. The passage between the two is Mathlib's canonical section
`CategoryTheory.Presieve.preZeroHypercover`, which indexes a presieve by its own arrows; the
refinement morphism of pre-`0`-hypercovers that Tag 055V produces is then turned into the
presieve-level notion of refinement of Stacks 00VT (2) by
`CategoryTheory.PreZeroHypercover.Hom.factorsThru_presieve₀`.

No size bound is involved anywhere: the refining étale family of Tag 055V is indexed by the
points of the base, so the statements below are about arbitrary schemes and arbitrary covering
families.

## References

* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
* [Stacks Project, Tag 00VX](https://stacks.math.columbia.edu/tag/00VX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The presieve-level form of **Stacks Project, Tag 055V**: a jointly surjective family of
smooth morphisms to `X`, presented as a covering presieve, is refined by a jointly surjective
family of étale morphisms to `X`.

This is `AlgebraicGeometry.exists_etale_cover_refining_smooth_cover` with the indexing of the
families forgotten, which is the form the comparison of generated topologies needs. -/
theorem exists_etale_refinement_of_mem_smoothPrecoverage {X : Scheme.{u}} (R : Presieve X)
    (hR : R ∈ Scheme.precoverage (@Smooth.{u}) X) :
    ∃ R' ∈ Scheme.etalePrecoverage.{u} X, Presieve.FactorsThru R' R := by
  let 𝒰 : X.Cover.{u + 1} (Scheme.precoverage (@Smooth.{u})) :=
    { toPreZeroHypercover := R.preZeroHypercover
      mem₀ := by rwa [Presieve.presieve₀_preZeroHypercover] }
  obtain ⟨𝒱, ⟨φ⟩⟩ := exists_etale_cover_refining_smooth_cover 𝒰
  refine ⟨𝒱.toPreZeroHypercover.presieve₀, 𝒱.mem₀, ?_⟩
  have h := φ.factorsThru_presieve₀
  rwa [show 𝒰.toPreZeroHypercover.presieve₀ = R from
    Presieve.presieve₀_preZeroHypercover R] at h

namespace Scheme

/-- An étale morphism of schemes is smooth, so an étale covering family is a smooth covering
family. -/
theorem etalePrecoverage_le_smoothPrecoverage :
    etalePrecoverage.{u} ≤ precoverage (@Smooth.{u}) :=
  precoverage_mono fun _ _ f hf => by let : Etale f := hf; infer_instance

/-- **The smooth and étale topologies on the category of schemes are equal.**

The inclusion `étale ≤ smooth` holds because an étale morphism is smooth; the inclusion
`smooth ≤ étale` is Stacks 055V, every smooth covering being refined by an étale one. Since
mutual refinement of precoverages gives equality of the generated topologies
(`CategoryTheory.Precoverage.toGrothendieck_eq_of_refines`), no descent argument is needed. -/
theorem grothendieckTopology_smooth_eq_etaleTopology :
    grothendieckTopology (@Smooth.{u}) = etaleTopology.{u} :=
  Precoverage.toGrothendieck_eq_of_refines _ _
    (fun _ R hR => exists_etale_refinement_of_mem_smoothPrecoverage R hR)
    fun _ R hR => ⟨R, etalePrecoverage_le_smoothPrecoverage _ hR,
      Presieve.factorsThru_of_le _ _ le_rfl⟩

/-- The étale topology on schemes is the smooth one, stated in the direction in which the
rewrite is usually wanted. -/
theorem etaleTopology_eq_grothendieckTopology_smooth :
    etaleTopology.{u} = grothendieckTopology (@Smooth.{u}) :=
  grothendieckTopology_smooth_eq_etaleTopology.symm

/-- A presheaf on schemes is a sheaf for the smooth topology exactly when it is a sheaf for the
étale topology. Unlike the corresponding statement obtained from Stacks 00VX alone, this is a
consequence of an equality of topologies, so it holds for sheaves valued in any category. -/
theorem isSheaf_smooth_iff_isSheaf_etale {A : Type*} [Category A]
    (P : Scheme.{u}ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (grothendieckTopology (@Smooth.{u})) P ↔
      Presheaf.IsSheaf etaleTopology.{u} P := by
  rw [grothendieckTopology_smooth_eq_etaleTopology]

end Scheme

end AlgebraicGeometry

end
