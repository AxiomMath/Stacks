module

public import Mathlib.Topology.Sheaves.Stalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of a presheaf whose coefficients are larger than its space

For a presheaf of `Type (max u t)`-valued sections on a space `X : TopCat.{u}`, the stalk at a
point `x` is the colimit of the sections over the open neighbourhoods of `x`, a colimit over the
`u`-small category `(OpenNhds x)ᵒᵖ`. This file defines that stalk and the germs of sections in
it, with the coefficient universe independent of the universe of the space, unlike
`TopCat.Presheaf.stalk`, whose coefficient category has its morphisms in the universe of the
space.

## Main definitions

* `TopCat.Presheaf.stalkOfSize`: the stalk of a presheaf of `Type (max u t)`-valued sections on a
  space of `TopCat.{u}`.
* `TopCat.Presheaf.germOfSize`: the germ at `x` of a section over an open neighbourhood of `x`.

## Main results

* `TopCat.Presheaf.germOfSize_res_apply`: the germ of a restricted section is the germ of the
  section.
* `TopCat.Presheaf.exists_germOfSize_eq`: every element of the stalk is the germ of a section.
* `TopCat.Presheaf.germOfSize_eq`: two sections with the same germ at `x` agree on an open
  neighbourhood of `x`.
* `TopCat.Presheaf.sectionOfSize_ext`: two sections of a sheaf with the same germ at every point
  are equal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u t

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- The stalk at `x` of a presheaf of `Type (max u t)`-valued sections on a space of `TopCat.{u}`:
the colimit of the sections over the open neighbourhoods of `x`. -/
def stalkOfSize (𝒢 : X.Presheaf (Type (max u t))) (x : X) : Type (max u t) :=
  colimit ((OpenNhds.inclusion x).op ⋙ 𝒢)

/-- The germ at `x` of a section of `𝒢` over an open neighbourhood `V` of `x`: its image in the
stalk at `x`. -/
@[ega "0 3.1.6" "special case"]
def germOfSize (𝒢 : X.Presheaf (Type (max u t))) (V : Opens X) (x : X) (hx : x ∈ V) :
    𝒢.obj (op V) ⟶ stalkOfSize.{u, t} 𝒢 x :=
  colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒢) (op ⟨V, hx⟩)

/-- The germ at `x` of the restriction of a section to a smaller open neighbourhood of `x` is the
germ of the section. -/
lemma germOfSize_res_apply (𝒢 : X.Presheaf (Type (max u t))) {V W : Opens X} (i : V ⟶ W) (x : X)
    (hx : x ∈ V) (s : 𝒢.obj (op W)) :
    germOfSize.{u, t} 𝒢 V x hx (𝒢.map i.op s) = germOfSize.{u, t} 𝒢 W x (i.le hx) s :=
  congrFun (congrArg (fun f ↦ (ConcreteCategory.hom f : _ → _))
    (colimit.w ((OpenNhds.inclusion x).op ⋙ 𝒢)
      (op (show (⟨V, hx⟩ : OpenNhds x) ⟶ ⟨W, i.le hx⟩ from i)))) s

/-- Every element of the stalk at `x` is the germ at `x` of a section over an open neighbourhood
of `x`. -/
lemma exists_germOfSize_eq (𝒢 : X.Presheaf (Type (max u t))) {x : X}
    (a : stalkOfSize.{u, t} 𝒢 x) :
    ∃ (V : Opens X) (hx : x ∈ V) (s : 𝒢.obj (op V)), germOfSize.{u, t} 𝒢 V x hx s = a := by
  obtain ⟨V, s, e⟩ := Types.jointly_surjective' (F := (OpenNhds.inclusion x).op ⋙ 𝒢) a
  exact ⟨(unop V).1, (unop V).2, s, e⟩

/-- Two sections with the same germ at `x` have equal restrictions to some open neighbourhood of
`x`. -/
lemma germOfSize_eq (𝒢 : X.Presheaf (Type (max u t))) {V W : Opens X} (x : X) (hV : x ∈ V)
    (hW : x ∈ W) (s : 𝒢.obj (op V)) (s' : 𝒢.obj (op W))
    (h : germOfSize.{u, t} 𝒢 V x hV s = germOfSize.{u, t} 𝒢 W x hW s') :
    ∃ (U : Opens X) (_ : x ∈ U) (iV : U ⟶ V) (iW : U ⟶ W), 𝒢.map iV.op s = 𝒢.map iW.op s' := by
  obtain ⟨U, iV, iW, e⟩ := (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ 𝒢)).eq_iff.mp h
  exact ⟨(unop U).1, (unop U).2, iV.unop, iW.unop, e⟩

/-- **Sections of a sheaf are determined by their germs.** Two sections of a sheaf of
`Type (max u t)`-valued sections over an open `V` whose germs agree at every point of `V` are
equal. -/
lemma sectionOfSize_ext (F : TopCat.Sheaf (Type (max u t)) X) (V : Opens X)
    (s s' : F.1.obj (op V))
    (h : ∀ (x : X) (hx : x ∈ V), germOfSize.{u, t} F.1 V x hx s =
      germOfSize.{u, t} F.1 V x hx s') :
    s = s' := by
  choose U m i₁ i₂ heq using fun x : V ↦ germOfSize_eq.{u, t} F.1 x.1 x.2 x.2 s s' (h x.1 x.2)
  refine F.eq_of_locally_eq' U V i₁ (fun x hxV => ?_) s s' fun x => ?_
  · simpa only [Opens.mem_iSup] using ⟨⟨x, hxV⟩, m ⟨x, hxV⟩⟩
  · rw [heq, Subsingleton.elim (i₁ x) (i₂ x)]

end TopCat.Presheaf

end

end
