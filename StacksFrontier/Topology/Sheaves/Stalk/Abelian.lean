module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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

/-!
# Stacks 007F — the abelian group structure on the stalk of an abelian presheaf

Stacks 007F (Lemma 6.12.1) says that for a presheaf `F` of abelian groups on a topological space
`X` and a point `x`, there is a *unique* structure of an abelian group on the stalk `F_x` such that
for every `U ⊂ X` open with `x ∈ U` the map `F(U) → F_x` is a group homomorphism, and that
moreover `F_x = colim_{x ∈ U} F(U)` holds in the category of abelian groups.

Both assertions are formalized, and neither is vacuous:

* `existsUnique_addCommGroup_stalk`: there is exactly one `AddCommGroup` structure on the
  underlying type of `F.stalk x` for which every germ map `F(U) → F_x` is additive. Existence is
  the structure that Mathlib's `AddCommGrpCat`-valued stalk already carries, additivity of its
  germ maps being `stalk_germ_add`. Uniqueness, `stalk_addCommGroup_unique`, is the content of the
  source's proof: any two elements of `F_x` are germs of sections `s` over `U` and `t` over `V`,
  which restrict to the common open neighbourhood `U ⊓ V` of `x`, so additivity of the germ maps
  forces `a + b` to be the germ of `s|_{U ⊓ V} + t|_{U ⊓ V}`; an abelian group structure is
  determined by its addition (`AddCommGroup.ext`). Only additivity of the germ maps is assumed,
  which for group structures is equivalent to being a group homomorphism and makes the uniqueness
  statement the stronger one.
* `stalk_eq_colimit_openNhds`: the colimit formula, as the literal equality of objects of
  `AddCommGrpCat` that the source writes. Mathlib defines the stalk to *be* the colimit of `F`
  along `(OpenNhds.inclusion x).op`, so the equality holds by `rfl`; stating it as an equality
  pins that definition down, whereas asserting a mere isomorphism between the two sides would
  unfold to `A ≅ A` and assert nothing.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite

namespace Stacks.AbelianStalk

universe u

variable {X : TopCat.{u}} (F : Presheaf AddCommGrpCat.{u} X) (x : X)

/--
The germ maps of a presheaf of abelian groups are additive for the abelian group structure that
Mathlib's `AddCommGrpCat`-valued stalk carries, i.e. `germ_x (s + t) = germ_x s + germ_x t` for
sections `s`, `t` over an open neighbourhood of `x`. This is the existence half of Stacks 007F.
-/
theorem stalk_germ_add (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))) :
    F.germ U x hx (s + t) = F.germ U x hx s + F.germ U x hx t :=
  map_add _ _ _

/--
The uniqueness half of Stacks 007F: an abelian group structure on the stalk `F_x` all of whose
germ maps `F(U) → F_x` are additive is unique. Given two such structures `G₁` and `G₂`, write
`a b : F_x` as germs of sections `s` over `U` and `t` over `V`; restricting both to `U ⊓ V` and
using additivity of the germ map of `U ⊓ V` computes `a + b` as the germ of
`s|_{U ⊓ V} + t|_{U ⊓ V}` in either structure, so the two additions agree, and an abelian group
structure is determined by its addition.
-/
theorem stalk_addCommGroup_unique (G₁ G₂ : AddCommGroup (ToType (F.stalk x)))
    (h₁ : letI := G₁
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        F.germ U x hx (s + t) = F.germ U x hx s + F.germ U x hx t)
    (h₂ : letI := G₂
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        F.germ U x hx (s + t) = F.germ U x hx s + F.germ U x hx t) :
    G₁ = G₂ := by
  apply AddCommGroup.ext
  funext a b
  obtain ⟨U, hU, s, rfl⟩ := F.exists_germ_eq a
  obtain ⟨V, hV, t, rfl⟩ := F.exists_germ_eq b
  have hW : x ∈ U ⊓ V := ⟨hU, hV⟩
  rw [← F.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hW s,
    ← F.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hW t, ← h₁ _ hW, ← h₂ _ hW]

/--
**Stacks 007F**, first assertion. There exists a unique structure of an abelian group on the stalk
`F_x` of a presheaf of abelian groups `F` at a point `x` such that for every open `U` with `x ∈ U`
the map `F(U) → F_x` is a homomorphism of groups. The witness is the structure carried by
Mathlib's stalk in `AddCommGrpCat`.
-/
@[stacks 007F]
theorem existsUnique_addCommGroup_stalk :
    ∃! G : AddCommGroup (ToType (F.stalk x)), letI := G
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        F.germ U x hx (s + t) = F.germ U x hx s + F.germ U x hx t :=
  ⟨(F.stalk x).str, stalk_germ_add F x, fun G hG =>
    stalk_addCommGroup_unique F x G (F.stalk x).str hG (stalk_germ_add F x)⟩

/--
**Stacks 007F**, second assertion: `F_x = colim_{x ∈ U} F(U)` in the category of abelian groups,
the colimit being taken over the diagram of sections indexed by the open neighbourhoods of `x`.
This is an equality of objects of `AddCommGrpCat`, as in the source, and it holds by `rfl` because
Mathlib defines the stalk to be exactly that colimit; the statement therefore pins Mathlib's
definition of `TopCat.Presheaf.stalk` down.
-/
@[stacks 007F]
theorem stalk_eq_colimit_openNhds :
    F.stalk x = Limits.colimit ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ F) :=
  rfl

end Stacks.AbelianStalk
