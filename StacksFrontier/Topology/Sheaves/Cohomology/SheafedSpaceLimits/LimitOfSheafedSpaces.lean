module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Geometry.RingedSpace.SheafedSpace

/-!
# Limits of sheafed spaces: the underlying space and the sheaf on it

Tag 0A37 is stated over an abstract limiting cone `c` in `SheafedSpace C`.  Neither
`PresheafedSpace C` nor `SheafedSpace C` has limits at the Mathlib revision this project is
pinned at — only colimits — so the hypothesis `IsLimit c` is the *only* handle on what the
vertex of `c` is.  This file turns that hypothesis into the two concrete descriptions the tag
reaches for:

* the underlying topological space of `c.pt` is the limit of the underlying spaces; and
* the sheaf on `c.pt` is the colimit of the inverse images of the sheaves at the stages.

## Main definitions

* `constTerminalFunctor` sends a space to itself carrying the constant sheaf at a terminal
  object of `C`.
* `reseat` replaces the sheaf on the vertex of `c` by an arbitrary sheaf on the same space,
  and `leg`, `over`, `pull` are the morphisms of sheafed spaces that this makes available.

## Main results

* `constTerminalForgetAdjunction`: `SheafedSpace.forget C` is a **right adjoint**, with left
  adjoint `constTerminalFunctor`.  Hence `isLimit_mapCone_forget`: the forgetful functor to
  `TopCat` carries a limiting cone of sheafed spaces to a limiting cone of spaces.  This holds
  with no hypothesis beyond a terminal object in `C`, and in particular needs no limits in
  `SheafedSpace C`.
* `existsUnique_pull_eq`: **the sheaf on the vertex of a limiting cone is the colimit of the
  inverse images of the sheaves at the stages**, in corepresented form.  For every sheaf `H` on
  the space underlying `c.pt` and every family of maps `Fₖ ⟶ (pₖ)_* H` compatible with the
  transition maps, there is a unique `g : c.pt.presheaf ⟶ H` with `(pₖ)-adjoint` equal to the
  given family.

## Implementation notes

The left adjoint of the forgetful functor is `Z ↦ (Z, constant sheaf at ⊤_ C)`: a morphism of
presheafed spaces `(Z, ⊤) ⟶ (X, F)` is a continuous map `Z ⟶ X` together with a map
`F ⟶ f_* ⊤`, and the latter is unique because every value of `f_* ⊤` is a terminal object.  The
constant presheaf at a terminal object is a sheaf by
`CategoryTheory.Presheaf.isSheaf_of_isTerminal`.

The sheaf statement is proved by restricting the universal property of `c` to the morphisms of
sheafed spaces whose base map is the identity.  The identification of the base map of the lift
with the identity is exactly `isLimit_mapCone_forget`, which is why the two halves are in one
file.  No transport is needed anywhere: `𝟙 ≫ f = f` holds by `rfl` in `TopCat` and
`TopCat.Presheaf.Pushforward.comp_eq` holds by `rfl`, so `over g ≫ c.π.app k` and
`leg k (pull g k)` are *definitionally* the same morphism of sheafed spaces.

The ambient sheaf is carried as a presheaf together with a separate sheaf condition rather than
as a `TopCat.Sheaf`: the latter is a semireducible `def` over an `ObjectProperty.FullSubcategory`
and unfolds under `simp`, which makes goals mentioning it fail to be type-correct at the
`implicit` transparency level.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe v u w

namespace Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

variable {C : Type u} [Category.{v} C] [HasTerminal C]

/-! ### The forgetful functor to spaces is a right adjoint -/

variable (C) in
/-- **The constant presheaf at a terminal object of `C` is a sheaf.**  Every value of the
presheaf is terminal, so every gluing problem has a unique solution. -/
theorem isSheaf_constTerminal (Z : TopCat.{w}) :
    TopCat.Presheaf.IsSheaf ((Functor.const (Opens Z)ᵒᵖ).obj (⊤_ C)) :=
  CategoryTheory.Presheaf.isSheaf_of_isTerminal _ terminalIsTerminal

variable (C) in
/-- The space `Z` carrying the constant sheaf at a terminal object of `C`. -/
def constTerminal (Z : TopCat.{w}) : SheafedSpace.{u, v, w} C where
  carrier := Z
  presheaf := (Functor.const (Opens Z)ᵒᵖ).obj (⊤_ C)
  IsSheaf := isSheaf_constTerminal C Z

variable (C) in
/-- The map from any presheaf to the pushforward of the constant terminal sheaf: each component
is the unique map to a terminal object. -/
def toConstTerminal {Z W : TopCat.{w}} (f : Z ⟶ W) (P : W.Presheaf C) :
    P ⟶ f _* (constTerminal C Z).presheaf where
  app _ := terminal.from _
  naturality _ _ _ := terminal.hom_ext _ _

variable (C) in
/-- `toConstTerminal` is the only such map, because its codomain is pointwise terminal.  This is
what makes `constTerminalFunctor` a left adjoint of the forgetful functor: a morphism out of a
constant terminal sheafed space is exactly its base map. -/
theorem toConstTerminal_unique {Z W : TopCat.{w}} (f : Z ⟶ W) (P : W.Presheaf C)
    (α β : P ⟶ f _* (constTerminal C Z).presheaf) : α = β :=
  NatTrans.ext (funext fun _ => terminal.hom_ext _ _)

variable (C) in
/-- The morphism of sheafed spaces out of a constant terminal sheafed space with a given base
map. -/
def constTerminalHomMk {Z : TopCat.{w}} {Y : SheafedSpace.{u, v, w} C} (f : Z ⟶ (Y : TopCat)) :
    constTerminal C Z ⟶ Y :=
  InducedCategory.homMk { base := f, c := toConstTerminal C f Y.presheaf }

variable (C) in
/-- Carrying a space to itself equipped with the constant sheaf at a terminal object of `C`.
This is the left adjoint of `SheafedSpace.forget C`. -/
def constTerminalFunctor : TopCat.{w} ⥤ SheafedSpace.{u, v, w} C where
  obj Z := constTerminal C Z
  map f := constTerminalHomMk C f
  map_id _ := InducedCategory.hom_ext
    (PresheafedSpace.hext _ _ rfl (heq_of_eq (toConstTerminal_unique C _ _ _ _)))
  map_comp _ _ := InducedCategory.hom_ext
    (PresheafedSpace.hext _ _ rfl (heq_of_eq (toConstTerminal_unique C _ _ _ _)))

variable (C) in
/-- **The forgetful functor `SheafedSpace C ⥤ TopCat` is a right adjoint**, with left adjoint
`constTerminalFunctor C`: a morphism `(Z, ⊤) ⟶ (X, F)` of sheafed spaces is its base map and
nothing else, because the sheaf component is forced by `toConstTerminal_unique`. -/
def constTerminalForgetAdjunction :
    constTerminalFunctor.{v, u, w} C ⊣ SheafedSpace.forget.{u, v, w} C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun g => g.hom.base
          invFun := fun f => constTerminalHomMk C f
          left_inv := fun _ => InducedCategory.hom_ext
            (PresheafedSpace.hext _ _ rfl (heq_of_eq (toConstTerminal_unique C _ _ _ _)))
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := fun _ _ => InducedCategory.hom_ext
        (PresheafedSpace.hext _ _ rfl (heq_of_eq (toConstTerminal_unique C _ _ _ _)))
      homEquiv_naturality_right := fun _ _ => rfl }

variable (C) in
/-- `SheafedSpace.forget C` is a right adjoint, recorded as an instance so that the limit
preservation instances apply. -/
instance isRightAdjoint_forget : (SheafedSpace.forget.{u, v, w} C).IsRightAdjoint :=
  (constTerminalForgetAdjunction C).isRightAdjoint

/-- **The underlying space of a limit of sheafed spaces is the limit of the underlying spaces.**
The forgetful functor to `TopCat` is a right adjoint, so it preserves all limits; no limits in
`SheafedSpace C` are needed, only the limiting cone that is given. -/
def isLimit_mapCone_forget {K : Type*} [Category K]
    {E : K ⥤ SheafedSpace.{u, v, w} C} {c : Cone E} (hc : IsLimit c) :
    IsLimit ((SheafedSpace.forget C).mapCone c) :=
  isLimitOfPreserves _ hc

/-! ### The sheaf on the vertex is the colimit of the inverse images -/

variable {K : Type*} [Category K] {E : K ⥤ SheafedSpace.{u, v, w} C} (c : Cone E)
  (H : (c.pt : TopCat).Presheaf C) (hH : H.IsSheaf)

/-- The space underlying the vertex of `c`, carrying the sheaf `H` instead of its own. -/
def reseat : SheafedSpace.{u, v, w} C where
  carrier := (c.pt : TopCat)
  presheaf := H
  IsSheaf := hH

/-- A morphism `reseat c H hH ⟶ E.obj k` whose base map is the `k`-th projection of `c`.  By
the pushforward–inverse image adjunction its sheaf component `ψ` is the same thing as a map
`pₖ⁻¹ Fₖ ⟶ H`, so these are the arrows of the colimit cocone of Tag 0A37. -/
def leg (k : K) (ψ : (E.obj k).presheaf ⟶ (c.π.app k).hom.base _* H) :
    reseat c H hH ⟶ E.obj k :=
  InducedCategory.homMk { base := (c.π.app k).hom.base, c := ψ }

/-- A morphism `reseat c H hH ⟶ c.pt` whose base map is the identity: these are exactly the maps
of sheaves `c.pt.presheaf ⟶ H` on the vertex. -/
def over (g : c.pt.presheaf ⟶ H) : reseat c H hH ⟶ c.pt :=
  InducedCategory.homMk { base := 𝟙 _, c := g }

/-- The `k`-th component of the cocone comparison attached to a map of sheaves `g` on the
vertex: the `k`-th projection's sheaf map followed by `g` pushed forward. -/
def pull (g : c.pt.presheaf ⟶ H) (k : K) :
    (E.obj k).presheaf ⟶ (c.π.app k).hom.base _* H :=
  (c.π.app k).hom.c ≫ (TopCat.Presheaf.pushforward C (c.π.app k).hom.base).map g

omit [HasTerminal C] in
/-- Composing `over g` with the `k`-th projection of `c` is the leg determined by `pull g k`.
This holds by `rfl`: in `TopCat` the identity is a definitional left unit, and
`TopCat.Presheaf.Pushforward.comp_eq` holds by `rfl`. -/
theorem over_comp_π (g : c.pt.presheaf ⟶ H) (k : K) :
    over c H hH g ≫ c.π.app k = leg c H hH k (pull c H g k) :=
  rfl

omit [HasTerminal C] in
/-- `leg` is injective in its sheaf component: the base maps of the two sides agree on the
nose, so the sheaf components live in the same type and the structure is injective. -/
theorem leg_inj {k : K} {ψ ψ' : (E.obj k).presheaf ⟶ (c.π.app k).hom.base _* H}
    (h : leg c H hH k ψ = leg c H hH k ψ') : ψ = ψ' := by
  injection h with h
  injection h with _ h

omit [HasTerminal C] in
/-- `over` is injective: the base maps of the two sides are both the identity, so the sheaf
components live in the same type and the structure is injective. -/
theorem over_inj {g g' : c.pt.presheaf ⟶ H} (h : over c H hH g = over c H hH g') : g = g' := by
  injection h with h
  injection h with _ h

/-- **The sheaf on the vertex of a limiting cone of sheafed spaces is the colimit of the inverse
images of the sheaves at the stages**, in the form corepresented by an arbitrary sheaf `H` on
the space underlying the vertex.

Given a family `φ k : Fₖ ⟶ (pₖ)_* H` — equivalently, by the pushforward–inverse image
adjunction, a family `pₖ⁻¹ Fₖ ⟶ H` — compatible with the transition maps of `E`, there is a
unique map of sheaves `g : c.pt.presheaf ⟶ H` on the vertex with `pull g = φ`.

The proof restricts the universal property of `c` to the morphisms of sheafed spaces with
identity base map.  The lift `hc.lift d` of the cone `d` with vertex `reseat c H hH` and legs
`leg k (φ k)` has base map a morphism into the limit of the underlying spaces commuting with all
the projections, hence the identity by `isLimit_mapCone_forget`; and then `over_comp_π` and
`leg_inj` translate `hc.fac` and `hc.uniq` into the two halves of the assertion. -/
theorem existsUnique_pull_eq (hc : IsLimit c)
    (φ : ∀ k, (E.obj k).presheaf ⟶ (c.π.app k).hom.base _* H)
    (hφ : ∀ {i j : K} (a : i ⟶ j),
      leg c H hH i (φ i) ≫ E.map a = leg c H hH j (φ j)) :
    ∃! g : c.pt.presheaf ⟶ H, ∀ k, pull c H g k = φ k := by
  let d : Cone E :=
    { pt := reseat c H hH
      π := { app := fun k => leg c H hH k (φ k), naturality := fun i j a => by simp [hφ a] } }
  have hfac : ∀ k, hc.lift d ≫ c.π.app k = leg c H hH k (φ k) := hc.fac d
  have hbase : (hc.lift d).hom.base = 𝟙 _ := by
    refine (isLimit_mapCone_forget hc).hom_ext fun k => ?_
    show (hc.lift d).hom.base ≫ (c.π.app k).hom.base = 𝟙 _ ≫ (c.π.app k).hom.base
    rw [Category.id_comp]
    exact congrArg (fun m => m.hom.base) (hfac k)
  set f := hc.lift d
  clear_value f
  obtain ⟨⟨b, γ⟩⟩ := f
  subst hbase
  obtain ⟨g₀, hfac'⟩ : ∃ g₀ : c.pt.presheaf ⟶ H,
      ∀ k, over c H hH g₀ ≫ c.π.app k = leg c H hH k (φ k) := ⟨γ, hfac⟩
  have hγ : ∀ k, pull c H g₀ k = φ k :=
    fun k => leg_inj c H hH ((over_comp_π c H hH g₀ k).symm.trans (hfac' k))
  refine ⟨g₀, hγ, fun g hg => over_inj c H hH (hc.hom_ext fun k => ?_)⟩
  rw [over_comp_π, over_comp_π, hg k, hγ k]

end Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

end
