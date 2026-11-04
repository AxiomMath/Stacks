module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# A sheaf on an irreducible space whose generization maps are bijective is constant

Let `X` be a topological space with a point `η` contained in every nonempty open set — the
generic point of an irreducible sober space, for instance. For a sheaf `G` of abelian groups on
`X` and a point `x`, the specialization map `G_x → G_η` is the generization map. If every
generization map of `G` is bijective then `G` is the constant sheaf on `G_η`: over every open
set containing `η` the germ map at `η` is bijective, and consequently every restriction map
between opens containing `η` is an isomorphism.

Injectivity of the germ map comes from injectivity of the generization maps together with the
sheaf axiom: a section whose germ at `η` vanishes has vanishing germ at every point.
Surjectivity then uses injectivity: a prescribed element of `G_η` has, near every point, a
representing section with that germ at `η`, and two such sections agree on the intersection of
their domains, which contains `η`, by the injectivity just proved.

## Main results

* `Stacks.ConstantSheaf.injective_germ_of_injective_stalkSpecializes`
* `Stacks.ConstantSheaf.bijective_germ_of_bijective_stalkSpecializes`
* `Stacks.ConstantSheaf.isIso_map_of_bijective_stalkSpecializes` — the restriction maps between
  opens containing `η` are isomorphisms.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.ConstantSheaf

variable {X : TopCat.{u}} (G : TopCat.Presheaf AddCommGrpCat.{u} X) {η : X}

/-- If every generization map of a sheaf is injective, then so is the germ map at `η` over every
open set containing `η`: a section whose germ at `η` vanishes has vanishing germ everywhere. -/
theorem injective_germ_of_injective_stalkSpecializes (hG : G.IsSheaf) (hspec : ∀ x : X, η ⤳ x)
    (hinj : ∀ x : X, Function.Injective (G.stalkSpecializes (hspec x)))
    (V : Opens X) (hηV : η ∈ V) : Function.Injective (G.germ V η hηV) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext ⟨G, hG⟩ V s t fun x hx => hinj x ?_
  simpa only [TopCat.Presheaf.germ_stalkSpecializes_apply] using hst

/-- **A sheaf with bijective generization maps is constant.** If `η` lies in every nonempty open
set of `X` and every generization map `G_x → G_η` of a sheaf `G` is bijective, then the germ map
at `η` is bijective over every open set containing `η`. -/
theorem bijective_germ_of_bijective_stalkSpecializes (hG : G.IsSheaf)
    (hdense : ∀ V : Opens X, (V : Set X).Nonempty → η ∈ V) (hspec : ∀ x : X, η ⤳ x)
    (hbij : ∀ x : X, Function.Bijective (G.stalkSpecializes (hspec x)))
    (U : Opens X) (hηU : η ∈ U) : Function.Bijective (G.germ U η hηU) := by
  have hinj := injective_germ_of_injective_stalkSpecializes G hG hspec
    (fun x => (hbij x).injective)
  refine ⟨hinj U hηU, fun a => ?_⟩
  -- near every point of `U` choose a section whose germ at `η` is `a`
  have hloc : ∀ x : U, ∃ W : Opens X, W ≤ U ∧ (x : X) ∈ W ∧
      ∃ t : G.obj (op W), ∀ hηW : η ∈ W, G.germ W η hηW t = a := by
    intro x
    obtain ⟨b, hb⟩ := (hbij x).surjective a
    obtain ⟨W, hWU, hxW, t, ht⟩ := G.exists_le_germ_eq b x.2
    refine ⟨W, hWU, hxW, t, fun hηW => ?_⟩
    rw [← hb, ← ht]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply (F := G) (U := W) hxW
      (hspec (x : X)) t).symm
  choose W hWU hxW s hs using hloc
  have hη : ∀ i : U, η ∈ W i := fun i => hdense (W i) ⟨(i : X), hxW i⟩
  -- the sections agree on overlaps, because every overlap contains `η`
  have hcompat : TopCat.Presheaf.IsCompatible (C := AddCommGrpCat.{u}) G W s := by
    intro i j
    refine hinj (W i ⊓ W j) ⟨hη i, hη j⟩ ?_
    rw [G.germ_res_apply (Opens.infLELeft (W i) (W j)) η ⟨hη i, hη j⟩ (s i),
      G.germ_res_apply (Opens.infLERight (W i) (W j)) η ⟨hη i, hη j⟩ (s j), hs i, hs j]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := (⟨G, hG⟩ : TopCat.Sheaf _ X))
    W U (fun i => homOfLE (hWU i)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
    s hcompat
  refine ⟨t, ?_⟩
  rw [← hs ⟨η, hηU⟩ (hη ⟨η, hηU⟩), ← ht ⟨η, hηU⟩,
    G.germ_res_apply (homOfLE (hWU ⟨η, hηU⟩)) η (hη ⟨η, hηU⟩) t]

/-- If every generization map of a sheaf `G` is bijective, then every restriction map of `G`
between open sets containing `η` is an isomorphism. -/
theorem isIso_map_of_bijective_stalkSpecializes (hG : G.IsSheaf)
    (hdense : ∀ V : Opens X, (V : Set X).Nonempty → η ∈ V) (hspec : ∀ x : X, η ⤳ x)
    (hbij : ∀ x : X, Function.Bijective (G.stalkSpecializes (hspec x)))
    {U V : Opens X} (i : V ⟶ U) (hηV : η ∈ V) : IsIso (G.map i.op) := by
  have hU := bijective_germ_of_bijective_stalkSpecializes G hG hdense hspec hbij U (i.le hηV)
  have hV := bijective_germ_of_bijective_stalkSpecializes G hG hdense hspec hbij V hηV
  rw [ConcreteCategory.isIso_iff_bijective]
  have hcomp : ∀ s, G.germ V η hηV (G.map i.op s) = G.germ U η (i.le hηV) s := fun s =>
    G.germ_res_apply i η hηV s
  refine ⟨fun a b hab => hU.injective ?_, fun b => ?_⟩
  · rw [← hcomp a, ← hcomp b, hab]
  · obtain ⟨c, hc⟩ := hU.surjective (G.germ V η hηV b)
    exact ⟨c, hV.injective ((hcomp c).trans hc)⟩

end Stacks.ConstantSheaf
