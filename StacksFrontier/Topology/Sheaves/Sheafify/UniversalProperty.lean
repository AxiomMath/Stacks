module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal property of sheafification (Stacks tag 0080)

Let `F` be a presheaf of sets on a topological space `X` and let `G` be a sheaf of sets. Stacks
tag 0080 says that any morphism `η : F ⟶ G` factors uniquely as `F → F^# → G`, where `F^#` is the
sheafification of tag 007Y: the sections of `F^#` over `U` are the functions `U → ∐ₓ F_x` that
are locally germs of sections of `F`, and `F → F^#` sends a section to its germs. In Mathlib this
is `TopCat.Presheaf.sheafify` with the map `TopCat.Presheaf.toSheafify`, and the tag is
`TopCat.Presheaf.existsUnique_toSheafify_comp_eq`.

The proof shows that `F.toSheafify` is locally injective and locally surjective for the
Grothendieck topology of open covers (two sections with the same germs agree near each point, and
a locally-germ section is near each point the germ of a section of `F`). A locally bijective
morphism of presheaves of sets becomes invertible after sheafification
(`GrothendieckTopology.WEqualsLocallyBijective`), so precomposition with it is a bijection on
morphisms into any sheaf.

The same factorization for the abstract sheafification `CategoryTheory.sheafify` on an arbitrary
site is `sheafify_universal_property`.
-/

@[expose] public section

open CategoryTheory


universe v₁ v₂ u₁ u₂

/-- Any morphism `η : F ⟶ G` from a presheaf to a sheaf on a site `(C, J)` factors uniquely as
`F → sheafify J F → G` through the abstract sheafification `CategoryTheory.sheafify J F`. For the
locally-germ sheafification of a presheaf of sets on a topological space (Stacks tag 0080) see
`TopCat.Presheaf.existsUnique_toSheafify_comp_eq`. -/
@[ega "0 3.5.3" "partial, special case", ega "0 3.5.6" "more general"]
theorem sheafify_universal_property
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] [HasWeakSheafify J D]
    {F G : Cᵒᵖ ⥤ D} (η : F ⟶ G) (hG : Presheaf.IsSheaf J G) :
    ∃! γ : sheafify J F ⟶ G, toSheafify J F ≫ γ = η :=
  ⟨sheafifyLift J η hG, toSheafify_sheafifyLift J η hG,
    fun γ h => sheafifyLift_unique J η hG γ h⟩

namespace TopCat.Presheaf

open Opposite TopologicalSpace

universe v

variable {X : TopCat.{v}} (F : Presheaf (Type v) X)

/-- Two sections of `F` with the same image in the sheafification `F^#` have the same germ at
every point, hence agree on a neighbourhood of every point: `F.toSheafify` is locally injective
for the topology of open covers. -/
instance isLocallyInjective_toSheafify :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) F.toSheafify where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    have hgerm : F.germ U.unop x hx s = F.germ U.unop x hx t :=
      congrFun (congrArg Subtype.val h) ⟨x, hx⟩
    obtain ⟨W, hxW, iU, iV, e⟩ := F.germ_eq x hx hx s t hgerm
    refine ⟨W, iU, ?_, hxW⟩
    have : iV = iU := Subsingleton.elim _ _
    subst this
    exact e

/-- A section of the sheafification `F^#` is, near each point, the family of germs of a section
of `F`: `F.toSheafify` is locally surjective for the topology of open covers. -/
instance isLocallySurjective_toSheafify :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) F.toSheafify where
  imageSieve_mem {U} t := by
    intro x hx
    obtain ⟨V, hxV, i, g, hg⟩ := t.2 ⟨x, hx⟩
    refine ⟨V, i, ⟨g, ?_⟩, hxV⟩
    apply Subtype.ext
    funext y
    exact (hg y).symm

/-- **Stacks tag 0080.** Let `F` be a presheaf of sets on a topological space `X`. Any morphism
`η : F ⟶ G` into a sheaf of sets `G` factors uniquely as `F → F^# → G`, where `F^#` is the
sheafification `TopCat.Presheaf.sheafify` of tag 007Y (sections that are locally germs) and
`F → F^#` is `TopCat.Presheaf.toSheafify`. -/
@[stacks 0080 "The sheafification `F^#` is Mathlib's `TopCat.Presheaf.sheafify`, built from \
locally-germ sections as in 007Y, with `toSheafify` the map to it. The factorization is \
obtained from local injectivity and local surjectivity of `toSheafify` for open covers."]
theorem existsUnique_toSheafify_comp_eq (G : Sheaf (Type v) X) (η : F ⟶ G.presheaf) :
    ∃! γ : F.sheafify.presheaf ⟶ G.presheaf, F.toSheafify ≫ γ = η := by
  have hW : (Opens.grothendieckTopology X).W F.toSheafify :=
    (Opens.grothendieckTopology X).W_of_isLocallyBijective F.toSheafify
  have hb := hW G.presheaf G.2
  obtain ⟨γ, hγ⟩ := hb.2 η
  exact ⟨γ, hγ, fun γ' h => hb.1 (h.trans hγ.symm)⟩

end TopCat.Presheaf
