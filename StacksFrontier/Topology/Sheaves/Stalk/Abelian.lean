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

Here `F_x` is the stalk of the underlying presheaf of *sets* (Stacks Section 6.11), i.e. the
`Type`-valued stalk `Presheaf.stalk (F ⋙ forget AddCommGrpCat) x`, which a priori carries no group
structure. Both assertions are formalized for it:

* `existsUnique_addCommGroup_forget_stalk`: there is exactly one `AddCommGroup` structure on
  `Presheaf.stalk (F ⋙ forget AddCommGrpCat) x` for which every germ map `F(U) → F_x` is
  additive. Existence transports the structure of Mathlib's `AddCommGrpCat`-valued stalk along the
  comparison bijection `stalkForgetEquiv` (the forgetful functor preserves filtered colimits),
  which sends germs to germs. Uniqueness, `forget_stalk_addCommGroup_unique`, is the source's
  proof: two elements of `F_x` are germs of sections `s` over `U` and `t` over `V`, which restrict
  to `U ⊓ V`, so additivity of the germ maps forces their sum to be the germ of
  `s|_{U ⊓ V} + t|_{U ⊓ V}`.
* `isColimitGermCocone`: with this group structure, `F_x` together with the germ maps
  (`germCocone`, whose legs are the germs by `germCocone_ι_app_apply`) is a colimit cocone in
  `AddCommGrpCat` of the sections of `F` over the open neighbourhoods of `x`.

The earlier declarations `existsUnique_addCommGroup_stalk` and `stalk_eq_colimit_openNhds` state
the analogous facts for the carrier of Mathlib's `AddCommGrpCat`-valued stalk `F.stalk x`, which
is by definition already the colimit in `AddCommGrpCat`; they are auxiliary (the first is used for
the uniqueness argument above) and do not by themselves state Stacks 007F.
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
The analogue of Stacks 007F's first assertion for the carrier of Mathlib's `AddCommGrpCat`-valued
stalk `F.stalk x`: it carries exactly one abelian group structure making every germ map additive,
namely its own. This is not Stacks 007F itself, whose `F_x` is the set-valued stalk; that is
`existsUnique_addCommGroup_forget_stalk`.
-/
theorem existsUnique_addCommGroup_stalk :
    ∃! G : AddCommGroup (ToType (F.stalk x)), letI := G
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        F.germ U x hx (s + t) = F.germ U x hx s + F.germ U x hx t :=
  ⟨(F.stalk x).str, stalk_germ_add F x, fun G hG =>
    stalk_addCommGroup_unique F x G (F.stalk x).str hG (stalk_germ_add F x)⟩

/--
Mathlib's `AddCommGrpCat`-valued stalk is by definition the colimit, in `AddCommGrpCat`, of the
sections of `F` over the open neighbourhoods of `x`; this holds by `rfl`. It is a definitional
remark, not Stacks 007F's second assertion, which is about the set-valued stalk with its induced
group structure: `isColimitGermCocone`.
-/
theorem stalk_eq_colimit_openNhds :
    F.stalk x = Limits.colimit ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ F) :=
  rfl

/-! ### The set-valued stalk

Stacks' `F_x` is the stalk of the underlying presheaf of *sets*, i.e. the `Type`-valued stalk
`Presheaf.stalk (F ⋙ forget AddCommGrpCat) x`. Since the forgetful functor preserves filtered
colimits, it is in bijection with the carrier of the `AddCommGrpCat`-valued stalk, compatibly with
germs; this transports the group structure and the colimit property to it. -/

/-- The comparison bijection between the carrier of the `AddCommGrpCat`-valued stalk `F.stalk x`
and the set-valued stalk `Presheaf.stalk (F ⋙ forget AddCommGrpCat) x`, coming from the fact
that the forgetful functor preserves the (filtered) colimit defining the stalk. -/
noncomputable def stalkForgetEquiv :
    ToType (F.stalk x) ≃ Presheaf.stalk (F ⋙ forget AddCommGrpCat) x :=
  (preservesColimitIso (forget AddCommGrpCat) ((OpenNhds.inclusion x).op ⋙ F)).toEquiv

/-- The comparison bijection `stalkForgetEquiv` sends germs to germs. -/
theorem stalkForgetEquiv_germ (U : Opens X) (hx : x ∈ U) (s : ToType (F.obj (op U))) :
    stalkForgetEquiv F x (F.germ U x hx s) =
      Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx s :=
  ConcreteCategory.congr_hom (ι_preservesColimitIso_hom (forget AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)) s

/-- The abelian group structure on the set-valued stalk
`Presheaf.stalk (F ⋙ forget AddCommGrpCat) x`, transported from Mathlib's `AddCommGrpCat`-valued
stalk along `stalkForgetEquiv`. -/
noncomputable abbrev stalkAddCommGroup :
    AddCommGroup (Presheaf.stalk (F ⋙ forget AddCommGrpCat) x) :=
  (stalkForgetEquiv F x).symm.addCommGroup

attribute [local instance] stalkAddCommGroup

/-- For `stalkAddCommGroup`, every germ map `F(U) → F_x` into the set-valued stalk is additive. -/
theorem forget_germ_add (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))) :
    Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx (s + t) =
      Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx s +
        Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx t := by
  rw [← stalkForgetEquiv_germ, ← stalkForgetEquiv_germ, ← stalkForgetEquiv_germ,
    stalk_germ_add]
  change _ = stalkForgetEquiv F x ((stalkForgetEquiv F x).symm _ + (stalkForgetEquiv F x).symm _)
  simp only [Equiv.symm_apply_apply]

/-- Uniqueness on the set-valued stalk: an abelian group structure on
`Presheaf.stalk (F ⋙ forget AddCommGrpCat) x` all of whose germ maps are additive is unique. -/
theorem forget_stalk_addCommGroup_unique
    (G₁ G₂ : AddCommGroup (Presheaf.stalk (F ⋙ forget AddCommGrpCat) x))
    (h₁ : letI := G₁
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx (s + t) =
          Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx s +
            Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx t)
    (h₂ : letI := G₂
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx (s + t) =
          Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx s +
            Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx t) :
    G₁ = G₂ := by
  apply AddCommGroup.ext
  funext a b
  obtain ⟨U, hU, s, hs⟩ := F.exists_germ_eq ((stalkForgetEquiv F x).symm a)
  obtain ⟨V, hV, t, ht⟩ := F.exists_germ_eq ((stalkForgetEquiv F x).symm b)
  rw [Equiv.eq_symm_apply, stalkForgetEquiv_germ] at hs ht
  subst hs ht
  have hW : x ∈ U ⊓ V := ⟨hU, hV⟩
  rw [← Presheaf.germ_res_apply (F ⋙ forget AddCommGrpCat)
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hW s,
    ← Presheaf.germ_res_apply (F ⋙ forget AddCommGrpCat)
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hW t]
  exact (h₁ _ hW _ _).symm.trans (h₂ _ hW _ _)

/--
**Stacks 007F**, first assertion. Let `F` be a presheaf of abelian groups on `X` and `x : X`.
There exists a unique structure of an abelian group on the stalk `F_x` — the stalk of the
underlying presheaf of sets, `Presheaf.stalk (F ⋙ forget AddCommGrpCat) x` — such that for every
open `U` with `x ∈ U` the germ map `F(U) → F_x` is a homomorphism of groups (equivalently,
additive). The witness is `stalkAddCommGroup`.
-/
@[stacks 007F]
theorem existsUnique_addCommGroup_forget_stalk :
    ∃! G : AddCommGroup (Presheaf.stalk (F ⋙ forget AddCommGrpCat) x), letI := G
      ∀ (U : Opens X) (hx : x ∈ U) (s t : ToType (F.obj (op U))),
        Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx (s + t) =
          Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx s +
            Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx t :=
  ⟨stalkAddCommGroup F x, forget_germ_add F x, fun G hG =>
    forget_stalk_addCommGroup_unique F x G (stalkAddCommGroup F x) hG (forget_germ_add F x)⟩

/-- The germ cocone: the set-valued stalk `Presheaf.stalk (F ⋙ forget AddCommGrpCat) x` with the
group structure `stalkAddCommGroup`, viewed as an object of `AddCommGrpCat`, together with the germ
maps `F(U) → F_x` (now group homomorphisms) as a cocone over the diagram of sections of `F` on the
open neighbourhoods of `x`. -/
noncomputable def germCocone : Limits.Cocone ((OpenNhds.inclusion x).op ⋙ F) where
  pt := AddCommGrpCat.of (Presheaf.stalk (F ⋙ forget AddCommGrpCat) x)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (Presheaf.germ (F ⋙ forget AddCommGrpCat) U.unop.1 x U.unop.2)
          (forget_germ_add F x U.unop.1 U.unop.2))
      naturality := fun U V i => by
        ext s
        exact (Presheaf.germ_res_apply' (F ⋙ forget AddCommGrpCat) i.unop.op x V.unop.2 s).trans
          rfl }

/-- The legs of `germCocone` are the germ maps into the set-valued stalk. -/
theorem germCocone_ι_app_apply (U : Opens X) (hx : x ∈ U) (s : ToType (F.obj (op U))) :
    (germCocone F x).ι.app (op ⟨U, hx⟩) s =
      Presheaf.germ (F ⋙ forget AddCommGrpCat) U x hx s :=
  rfl

/--
**Stacks 007F**, second assertion: `F_x = colim_{x ∈ U} F(U)` in the category of abelian groups.
The set-valued stalk `F_x = Presheaf.stalk (F ⋙ forget AddCommGrpCat) x`, with the group
structure of `existsUnique_addCommGroup_forget_stalk` and the germ maps `F(U) → F_x` as legs
(`germCocone`, `germCocone_ι_app_apply`), is a colimit cocone in `AddCommGrpCat` of the diagram of
sections of `F` over the open neighbourhoods of `x`.
-/
@[stacks 007F]
noncomputable def isColimitGermCocone : Limits.IsColimit (germCocone F x) :=
  Limits.IsColimit.ofIsoColimit (Limits.colimit.isColimit _)
    (Limits.Cocone.ext
      (AddEquiv.toAddCommGrpIso (X := F.stalk x)
        (Y := AddCommGrpCat.of (Presheaf.stalk (F ⋙ forget AddCommGrpCat) x))
        (stalkForgetEquiv F x).symm.addEquiv.symm)
      (fun U => by
        ext s
        exact stalkForgetEquiv_germ F x U.unop.1 U.unop.2 s))

end Stacks.AbelianStalk
