module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FibrewiseSoftPullback
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.UnitOnSections

/-!
# Sections of an inverse image across a square, and across an isomorphism of spaces

Let

```
Z₁ --ι₁--> X₁
|          |
φ          g
v          v
Z₂ --ι₂--> X₂
```

be a commuting square of topological spaces whose left vertical arrow `φ` is an isomorphism.
`Stacks.Topology.inverseImageSquareIso` identifies the two composite inverse images
`ι₁^{-1} g^{-1}` and `φ^{-1} ι₂^{-1}`, and `Stacks.Topology.inverseImageIsoDirectImageUnivLE`
identifies `φ^{-1}` with the direct image along `φ^{-1}`, whose sections over an open are the
sections of the original over the preimage. Both are
`CategoryTheory.Adjunction.leftAdjointUniq`, so neither comes with any description of what it
does on sections.

This file supplies those descriptions. The content is that `Stacks.Topology.ambientSection` —
the canonical map taking a section of a sheaf on the target to a section of its inverse image —
is *pseudofunctorial* across the square:

* `Stacks.Topology.ambientSection_comp_inverseImageSquareIso`: taking a section along `g` and
  then along `ι₁`, and transporting across `inverseImageSquareIso`, is the same as taking it
  along `ι₂` and then along `φ`;
* `Stacks.Topology.ambientSection_comp_ambientTopIso`: along an isomorphism of spaces,
  `ambientSection` read on *global* sections is a section of `Stacks.Topology.ambientTopIso`,
  hence (`Stacks.Topology.isIso_ambientSection_top_of_iso`) its inverse, and in particular an
  isomorphism;
* `Stacks.Topology.ambientSection_comp_squareSectionsIso`: the two combined. The canonical
  isomorphism `Γ(Z₁, ι₁^{-1} g^{-1} F) ≅ Γ(Z₂, ι₂^{-1} F)` of global sections on the two
  "fibres" carries the section induced along `ι₁ ∘ g` to the section induced along `ι₂`.

The last statement is the compatibility that the stalkwise route to underived proper base change
for abelian sheaves ([Stacks, Tag 09V6], `Stacks.Cohomology.AbelianProperBaseChange`) needs: there
`Z₁` is a fibre of the base-changed map, `Z₂` the corresponding fibre of the original map, and `φ`
the homeomorphism between them of
`Stacks.Topology.fiberIsoOfPullbackPresentation`. The stalk of a direct image along a closed map
is the sections on the fibre (`Stacks.Topology.isIso_fiberStalkSectionsMap`) *via*
`ambientSection` (`Stacks.Topology.fiberStalkSectionsMap_germ`), so a comparison of the two
fibre-section groups is usable only once it is known to agree with `ambientSection`.

## Main results

All in the namespace `Stacks.Topology`.

* `ambientSection_comp_restrict`: `ambientSection` followed by restriction to a smaller open of
  the source is `ambientSection` for the smaller open. A general-purpose lemma about
  `ambientSection`, at arbitrary coefficients, that the library did not have.
* `le_map_comp_of_comm`: the inclusion of opens that a commuting square supplies.
* `ambientSection_comp_inverseImageSquareIso`, and `…_top`, its reading on global sections of
  `Z₁`.
* `ambientTopIso`, `ambientSection_comp_ambientTopIso`,
  `ambientSection_top_eq_ambientTopIso_inv`, `isIso_ambientSection_top_of_iso`.
* `squareSectionsIso`, `ambientSection_comp_squareSectionsIso`.

## Implementation notes

Every proof here is one application of
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read at one open, plus the recognition
of the unit of the abstract adjunction on sections as `ambientSection`
(`Stacks.Topology.ambientSection_eq_unit`). Three things make that cheap:

* at a coefficient universe equal to the universe of the space, the universe-free functors
  `Stacks.Topology.inverseImageUnivLE`, `directImageUnivLE` and
  `inverseImageAdjunctionUnivLE` are Mathlib's `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pushforward` and `TopCat.Sheaf.pullbackPushforwardAdjunction` *on the nose*;
* reading the unit of a composite adjunction at an open, and reading the direct image of a
  morphism at an open, are both `rfl`, so no unit of a composite ever has to be expanded by
  rewriting;
* the residual comparison that `CategoryTheory.Functor.sheafPushforwardContinuousIso` leaves is a
  restriction map of the sheaf along a morphism of opens, and morphisms of opens are unique, so
  it is identified by `Subsingleton.elim` rather than by computing an `eqToHom`.

No step rewrites inside a term mentioning
`(TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F`: `TopCat.Sheaf` is a plain `def`,
so such a goal is not type-correct at the `implicit` transparency `rw` and `simp` re-check at.
The equalities are therefore introduced by `congrArg` on a function whose type is written out,
and composed with `Eq.trans`.

## References

* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe v u

noncomputable section

/-! ### Restricting a section induced on an inverse image -/

section Restrict

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- **Restricting the section of `f⁻¹ F` induced by a section of `F` gives the induced section on
the smaller open.** This is the counterpart, on the source, of
`Stacks.Topology.ambientSection_map`, which shrinks the open of the *target*. -/
theorem ambientSection_comp_restrict (F : Y.Sheaf C) {U : Opens Y} {V V' : Opens X}
    (h' : V' ≤ (Opens.map f).obj U) (hVV' : V ≤ V') :
    ambientSection f F h' ≫
        ((TopCat.Sheaf.pullback C f).obj F).presheaf.map (homOfLE hVV').op =
      ambientSection f F (hVV'.trans h') := by
  have hA : ∀ {W : Opens X} (hW : W ≤ (Opens.map f).obj U),
      ambientSection f F hW =
        ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
          (inverseImagePresheaf f F).map (homOfLE hW).op ≫
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (inverseImagePresheaf f F) ≫
            (sheafPullbackPresheafIso f F).inv).app (op W) := by
    intro W hW
    simp only [ambientSection, NatTrans.comp_app]
  rw [hA h', hA (hVV'.trans h'), Category.assoc, Category.assoc,
    ← (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (inverseImagePresheaf f F) ≫
      (sheafPullbackPresheafIso f F).inv).naturality (homOfLE hVV').op,
    ← Category.assoc ((inverseImagePresheaf f F).map (homOfLE h').op), ← Functor.map_comp]
  congr 2

end Restrict

/-! ### Across a commuting square -/

section Square

variable {X₁ X₂ Z₁ Z₂ : TopCat.{u}} (ι₁ : Z₁ ⟶ X₁) (g : X₁ ⟶ X₂) (φ : Z₁ ≅ Z₂) (ι₂ : Z₂ ⟶ X₂)

/-- The two ways of pulling an open of `X₂` back to `Z₁` along a commuting square agree; stated as
an inclusion, which is the form `Stacks.Topology.ambientSection` consumes. -/
theorem le_map_comp_of_comm (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂) (U : Opens X₂) :
    (Opens.map ι₁).obj ((Opens.map g).obj U) ≤
      (Opens.map φ.hom).obj ((Opens.map ι₂).obj U) :=
  le_of_eq (congrArg (fun k : Z₁ ⟶ X₂ => (Opens.map k).obj U) hcomm)

/-- The comparison that `CategoryTheory.Functor.sheafPushforwardContinuousIso` contributes to
`Stacks.Topology.inverseImageSquareIso` is the restriction map of the sheaf along the inclusion of
opens `le_map_comp_of_comm`: morphisms of opens are unique, so there is nothing else it could
be. -/
theorem sheafPushforwardContinuousIso_hom_app_hom_app (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂)
    (M : Z₁.Sheaf AddCommGrpCat.{u}) (U : Opens X₂) :
    ((Functor.sheafPushforwardContinuousIso (Opens.mapIso _ _ hcomm.symm) AddCommGrpCat.{u}
          (Opens.grothendieckTopology X₂)
          (Opens.grothendieckTopology Z₁)).hom.app M).hom.app (op U) =
      M.presheaf.map (homOfLE (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U)).op := by
  show M.presheaf.map ((Opens.mapIso (φ.hom ≫ ι₂) (ι₁ ≫ g) hcomm.symm).inv.app U).op = _
  exact congrArg (fun m => M.presheaf.map (Opposite.op m)) (Subsingleton.elim _ _)

/-- **`Stacks.Topology.ambientSection` is pseudofunctorial across a commuting square whose left
vertical arrow is an isomorphism.** Taking a section of `F` on `U ⊆ X₂` along `g` and then along
`ι₁`, and transporting it across `Stacks.Topology.inverseImageSquareIso`, is the same as taking it
along `ι₂` and then along `φ`.

This is the content of `inverseImageSquareIso` on sections. The isomorphism itself is
`CategoryTheory.Adjunction.leftAdjointUniq` of two composite adjunctions, so the proof is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read at `U`, with each unit on sections
recognised as `ambientSection` by `Stacks.Topology.ambientSection_eq_unit`. -/
theorem ambientSection_comp_inverseImageSquareIso (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂)
    (F : X₂.Sheaf AddCommGrpCat.{u}) (U : Opens X₂) :
    ambientSection g F (le_refl ((Opens.map g).obj U)) ≫
        ambientSection ι₁ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)
          (le_refl ((Opens.map ι₁).obj ((Opens.map g).obj U))) ≫
        ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
          (op ((Opens.map ι₁).obj ((Opens.map g).obj U))) =
      ambientSection ι₂ F (le_refl ((Opens.map ι₂).obj U)) ≫
        ambientSection φ.hom ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
          (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U) := by
  have key :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app F).hom.app
            (op U) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₁).unit.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)).hom.app
            (op ((Opens.map g).obj U)) ≫
          ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
            (op ((Opens.map ι₁).obj ((Opens.map g).obj U))) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₂).unit.app F).hom.app
            (op U) ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} φ.hom).unit.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)).hom.app
            (op ((Opens.map ι₂).obj U)) ≫
          ((Functor.sheafPushforwardContinuousIso (Opens.mapIso _ _ hcomm.symm)
                AddCommGrpCat.{u} (Opens.grothendieckTopology X₂)
                (Opens.grothendieckTopology Z₁)).hom.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} φ.hom).obj
                ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F))).hom.app (op U) :=
    congrArg
      (fun α : F ⟶ (directImageUnivLE.{u, u} (ι₁ ≫ g)).obj
          ((inverseImageUnivLE.{u, u} ι₂ ⋙ inverseImageUnivLE.{u, u} φ.hom).obj F) =>
        α.hom.app (op U))
      (Adjunction.unit_leftAdjointUniq_hom_app
        ((inverseImageAdjunctionUnivLE.{u, u} g).comp (inverseImageAdjunctionUnivLE.{u, u} ι₁) :
          inverseImageUnivLE.{u, u} g ⋙ inverseImageUnivLE.{u, u} ι₁ ⊣
            directImageUnivLE.{u, u} (ι₁ ≫ g))
        (Adjunction.ofNatIsoRight
          ((inverseImageAdjunctionUnivLE.{u, u} ι₂).comp
              (inverseImageAdjunctionUnivLE.{u, u} φ.hom) :
            inverseImageUnivLE.{u, u} ι₂ ⋙ inverseImageUnivLE.{u, u} φ.hom ⊣
              directImageUnivLE.{u, u} (φ.hom ≫ ι₂))
          (Functor.sheafPushforwardContinuousIso (Opens.mapIso _ _ hcomm.symm) AddCommGrpCat.{u}
            (Opens.grothendieckTopology X₂) (Opens.grothendieckTopology Z₁)))
        F)
  have haux :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} φ.hom).unit.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)).hom.app
            (op ((Opens.map ι₂).obj U)) ≫
          ((Functor.sheafPushforwardContinuousIso (Opens.mapIso _ _ hcomm.symm)
                AddCommGrpCat.{u} (Opens.grothendieckTopology X₂)
                (Opens.grothendieckTopology Z₁)).hom.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} φ.hom).obj
                ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F))).hom.app (op U) =
        ambientSection φ.hom ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
          (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U) :=
    ((congrArg
          (fun z => z ≫ ((Functor.sheafPushforwardContinuousIso (Opens.mapIso _ _ hcomm.symm)
                AddCommGrpCat.{u} (Opens.grothendieckTopology X₂)
                (Opens.grothendieckTopology Z₁)).hom.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} φ.hom).obj
                ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F))).hom.app (op U))
          (ambientSection_eq_unit φ.hom
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
            ((Opens.map ι₂).obj U)).symm).trans
      (congrArg
        (fun z => ambientSection φ.hom ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
          (le_refl ((Opens.map φ.hom).obj ((Opens.map ι₂).obj U))) ≫ z)
        (sheafPushforwardContinuousIso_hom_app_hom_app ι₁ g φ ι₂ hcomm _ U))).trans
      (ambientSection_comp_restrict φ.hom
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
        (le_refl ((Opens.map φ.hom).obj ((Opens.map ι₂).obj U)))
        (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U))
  refine Eq.trans ?_ (key.trans ?_)
  · exact (congrArg
      (fun z => ambientSection g F (le_refl ((Opens.map g).obj U)) ≫ z ≫
        ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
          (op ((Opens.map ι₁).obj ((Opens.map g).obj U))))
      (ambientSection_eq_unit ι₁ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)
        ((Opens.map g).obj U))).trans
      (congrArg
        (fun z => z ≫
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₁).unit.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)).hom.app
            (op ((Opens.map g).obj U)) ≫
          ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
            (op ((Opens.map ι₁).obj ((Opens.map g).obj U))))
        (ambientSection_eq_unit g F U))
  · exact (congrArg
      (fun z => ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} ι₂).unit.app
        F).hom.app (op U) ≫ z) haux).trans
      (congrArg (fun z => z ≫ ambientSection φ.hom
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
          (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U))
        (ambientSection_eq_unit ι₂ F U).symm)

/-- `ambientSection_comp_inverseImageSquareIso` read on the **global** sections of `Z₁` and `Z₂`,
which is the form the fibre-sections comparison of a closed map consumes: the hypotheses say that
`Z₁` lands inside `U` under `ι₁ ≫ g` and `Z₂` lands inside `U` under `ι₂`, which is automatic when
`Z₁` and `Z₂` are fibres over a point of an open whose preimage contains `U`. -/
theorem ambientSection_comp_inverseImageSquareIso_top (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂)
    (F : X₂.Sheaf AddCommGrpCat.{u}) (U : Opens X₂)
    (h₁ : (⊤ : Opens Z₁) ≤ (Opens.map ι₁).obj ((Opens.map g).obj U))
    (h₂ : (⊤ : Opens Z₂) ≤ (Opens.map ι₂).obj U) :
    ambientSection g F (le_refl ((Opens.map g).obj U)) ≫
        ambientSection ι₁ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F) h₁ ≫
        ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
          (op (⊤ : Opens Z₁)) =
      ambientSection ι₂ F h₂ ≫
        ambientSection φ.hom ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
          (le_refl ((Opens.map φ.hom).obj (⊤ : Opens Z₂))) := by
  have e1 := ambientSection_comp_restrict ι₁
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)
    (le_refl ((Opens.map ι₁).obj ((Opens.map g).obj U))) h₁
  have e2 := ambientSection_comp_restrict ι₂ F (le_refl ((Opens.map ι₂).obj U)) h₂
  have e3 := ambientSection_comp_restrict φ.hom
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
    (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U) h₁
  have e4 := ambientSection_map φ.hom
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F) (homOfLE h₂)
    (le_refl ((Opens.map φ.hom).obj (⊤ : Opens Z₂)))
    (h₁.trans (le_map_comp_of_comm ι₁ g φ ι₂ hcomm U))
  have e5 :
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₁).obj
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)).presheaf.map (homOfLE h₁).op ≫
          ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
            (op (⊤ : Opens Z₁)) =
        ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
            (op ((Opens.map ι₁).obj ((Opens.map g).obj U))) ≫
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} φ.hom).obj
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)).presheaf.map
            (homOfLE h₁).op :=
    ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.naturality (homOfLE h₁).op
  have main := ambientSection_comp_inverseImageSquareIso ι₁ g φ ι₂ hcomm F U
  refine (congrArg (fun z => _ ≫ z ≫ _) e1.symm).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (_ ≫ _ ≫ ·) e5).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) main).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) e3).trans ?_
  refine (congrArg (_ ≫ ·) e4.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) e2

end Square


/-! ### Across an isomorphism of spaces -/

section Homeo

variable {Z₁ Z₂ : TopCat.{u}} (φ : Z₁ ≅ Z₂)

/-- **The global sections of the inverse image of a sheaf along an isomorphism of spaces are the
global sections of the sheaf.** This is `Stacks.Topology.inverseImageIsoDirectImageUnivLE` read at
`⊤`, the sections of a direct image over `⊤` being the sections of the original over
`(Opens.map φ.inv).obj ⊤ = ⊤`. -/
def ambientTopIso (G : Z₂.Sheaf AddCommGrpCat.{u}) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} φ.hom).obj G).presheaf.obj (op (⊤ : Opens Z₁)) ≅
      G.presheaf.obj (op (⊤ : Opens Z₂)) :=
  ((TopCat.Sheaf.forget AddCommGrpCat.{u} Z₁).mapIso
    ((inverseImageIsoDirectImageUnivLE.{u, u} φ).app G)).app (op (⊤ : Opens Z₁))

/-- **Along an isomorphism of spaces, `Stacks.Topology.ambientSection` on global sections is a
section of `Stacks.Topology.ambientTopIso`** — hence, `ambientTopIso` being an isomorphism, its
inverse.

As with `ambientSection_comp_inverseImageSquareIso`, the proof is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read at `⊤`: the second adjunction is
the one `CategoryTheory.Adjunction.sheafPushforwardContinuous` builds out of
`Stacks.Topology.opensMapAdjunctionOfIso`, whose unit on sections is a restriction map of `G`
along a morphism of opens — and the only morphism `⊤ ⟶ ⊤` is the identity. -/
theorem ambientSection_comp_ambientTopIso (G : Z₂.Sheaf AddCommGrpCat.{u}) :
    ambientSection φ.hom G (le_refl ((Opens.map φ.hom).obj (⊤ : Opens Z₂))) ≫
        (ambientTopIso φ G).hom =
      𝟙 (G.presheaf.obj (op (⊤ : Opens Z₂))) := by
  have key :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} φ.hom).unit.app G).hom.app
            (op (⊤ : Opens Z₂)) ≫ (ambientTopIso φ G).hom =
        ((Adjunction.sheafPushforwardContinuous (E := AddCommGrpCat.{u})
          (opensMapAdjunctionOfIso φ) (Opens.grothendieckTopology Z₁)
          (Opens.grothendieckTopology Z₂)).unit.app G).hom.app (op (⊤ : Opens Z₂)) :=
    congrArg
      (fun α : G ⟶ (directImageUnivLE.{u, u} φ.hom).obj
          ((directImageUnivLE.{u, u} φ.inv).obj G) => α.hom.app (op (⊤ : Opens Z₂)))
      (Adjunction.unit_leftAdjointUniq_hom_app (inverseImageAdjunctionUnivLE.{u, u} φ.hom)
        (Adjunction.sheafPushforwardContinuous (E := AddCommGrpCat.{u})
          (opensMapAdjunctionOfIso φ) (Opens.grothendieckTopology Z₁)
          (Opens.grothendieckTopology Z₂)) G)
  have hid :
      ((Adjunction.sheafPushforwardContinuous (E := AddCommGrpCat.{u})
            (opensMapAdjunctionOfIso φ) (Opens.grothendieckTopology Z₁)
            (Opens.grothendieckTopology Z₂)).unit.app G).hom.app (op (⊤ : Opens Z₂)) =
        𝟙 (G.presheaf.obj (op (⊤ : Opens Z₂))) := by
    show G.presheaf.map _ = _
    exact (congrArg G.presheaf.map (Subsingleton.elim _ (𝟙 (op (⊤ : Opens Z₂))))).trans
      (G.presheaf.map_id (op (⊤ : Opens Z₂)))
  exact (congrArg (fun z => z ≫ (ambientTopIso φ G).hom)
    (ambientSection_eq_unit φ.hom G (⊤ : Opens Z₂))).trans (key.trans hid)

/-- `Stacks.Topology.ambientSection` on global sections along an isomorphism of spaces **is** the
inverse of `Stacks.Topology.ambientTopIso`. -/
theorem ambientSection_top_eq_ambientTopIso_inv (G : Z₂.Sheaf AddCommGrpCat.{u}) :
    ambientSection φ.hom G (le_refl ((Opens.map φ.hom).obj (⊤ : Opens Z₂))) =
      (ambientTopIso φ G).inv :=
  (ambientTopIso φ G).comp_hom_eq_id.mp (ambientSection_comp_ambientTopIso φ G)

/-- **Along an isomorphism of spaces, `Stacks.Topology.ambientSection` on global sections is an
isomorphism.** This is the surjectivity half of the fibre-sections comparison of
[Stacks, Tag 09V6], and it needs no compactness or separation: it is formal from uniqueness of
left adjoints. -/
instance isIso_ambientSection_top_of_iso (G : Z₂.Sheaf AddCommGrpCat.{u}) :
    IsIso (ambientSection φ.hom G (le_refl ((Opens.map φ.hom).obj (⊤ : Opens Z₂)))) := by
  rw [ambientSection_top_eq_ambientTopIso_inv φ G]
  exact Iso.isIso_inv (ambientTopIso φ G)

end Homeo

/-! ### The two combined: the comparison of fibre sections -/

section Combined

variable {X₁ X₂ Z₁ Z₂ : TopCat.{u}} (ι₁ : Z₁ ⟶ X₁) (g : X₁ ⟶ X₂) (φ : Z₁ ≅ Z₂) (ι₂ : Z₂ ⟶ X₂)

/-- **The canonical isomorphism `Γ(Z₁, ι₁⁻¹ g⁻¹ F) ≅ Γ(Z₂, ι₂⁻¹ F)`** attached to a commuting
square whose left vertical arrow `φ : Z₁ ≅ Z₂` is an isomorphism of spaces: transport across
`Stacks.Topology.inverseImageSquareIso`, then read `φ^{-1}` on global sections by
`Stacks.Topology.ambientTopIso`. -/
def squareSectionsIso (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂) (F : X₂.Sheaf AddCommGrpCat.{u}) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₁).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F)).presheaf.obj (op (⊤ : Opens Z₁)) ≅
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F).presheaf.obj (op (⊤ : Opens Z₂)) :=
  ((TopCat.Sheaf.forget AddCommGrpCat.{u} Z₁).mapIso
      ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F)).app (op (⊤ : Opens Z₁)) ≪≫
    ambientTopIso φ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)

/-- **The comparison of fibre sections is compatible with `Stacks.Topology.ambientSection`.**
Taking a section of `F` on `U` along `g` and then along `ι₁` — to a global section of
`ι₁^{-1} g^{-1} F` on `Z₁` — and comparing across `squareSectionsIso`, gives the global section
of `ι₂^{-1} F` on `Z₂` induced along `ι₂`.

This is the pseudofunctoriality that the stalkwise route to [Stacks, Tag 09V6] needs: the stalk of
a direct image along a closed map is the global sections on the fibre
(`Stacks.Topology.isIso_fiberStalkSectionsMap`) *through* `ambientSection`
(`Stacks.Topology.fiberStalkSectionsMap_germ`), so this says the comparison of the two fibres is
the one the base change morphism induces. -/
theorem ambientSection_comp_squareSectionsIso (hcomm : ι₁ ≫ g = φ.hom ≫ ι₂)
    (F : X₂.Sheaf AddCommGrpCat.{u}) (U : Opens X₂)
    (h₁ : (⊤ : Opens Z₁) ≤ (Opens.map ι₁).obj ((Opens.map g).obj U))
    (h₂ : (⊤ : Opens Z₂) ≤ (Opens.map ι₂).obj U) :
    ambientSection g F (le_refl ((Opens.map g).obj U)) ≫
        ambientSection ι₁ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F) h₁ ≫
        (squareSectionsIso ι₁ g φ ι₂ hcomm F).hom =
      ambientSection ι₂ F h₂ := by
  have htop := ambientSection_comp_inverseImageSquareIso_top ι₁ g φ ι₂ hcomm F U h₁ h₂
  have hhom := ambientSection_comp_ambientTopIso φ
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)
  calc _ = (ambientSection g F (le_refl ((Opens.map g).obj U)) ≫
          ambientSection ι₁ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj F) h₁ ≫
          ((inverseImageSquareIso.{u, u} ι₁ g φ ι₂ hcomm).app F).hom.hom.app
            (op (⊤ : Opens Z₁))) ≫
        (ambientTopIso φ ((TopCat.Sheaf.pullback AddCommGrpCat.{u} ι₂).obj F)).hom :=
        (Category.assoc _ _ _).symm
    _ = _ := (congrArg (· ≫ _) htop).trans
      ((Category.assoc _ _ _).trans ((congrArg _ hhom).trans (Category.comp_id _)))

end Combined

end

end Stacks.Topology

end
