module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ExtComparisonInDegreeZero
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp

/-!
# The composition law of the pullback maps of corepresenting objects

`Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap` is the map
`freeOfOpen U ⟶ f⁻¹ (freeOfOpen V)` of corepresenting objects attached to a continuous map
`f : X ⟶ Y` and opens `U ≤ f⁻¹ V`; it is what
`Stacks.Cohomology.AbelianColimit.H'spacePullback` is built from, so every pullback map on
native sheaf cohomology along a continuous map is built from it.  Before this file the
repository had its *defining property* (`repU_inv_freeOfOpenPullbackMap`: it is the
tautological section carried across the adjunction unit and restricted) and twenty uses, and
**no composition law at all**.

The law is the one a pseudofunctor satisfies, with the comparison
`Stacks.sheafPullbackCompIso` of [Stacks, Tag 008I(2)] in it, because the inverse image is only
functorial up to that canonical isomorphism:

    ρ_{g ∘ f} = ρ_f ≫ f⁻¹(ρ_g) ≫ ((g ∘ f)⁻¹ ≅ f⁻¹ g⁻¹)⁻¹ .

It is needed by the index-functoriality of the stage-side δ-functor of [Stacks, Tag 0A37]
(`SpectralDiagram.stageDeltaDiagram`, whose `map_comp` is exactly this law), and it is the
pseudofunctoriality the base-change comparison of [Stacks, Tag 09V6] also asks for.

## The two halves of the proof, and why they are separate

The composition law of the *direct* images is strict: `(g ∘ f)_* = f_* g_*` on the nose, which
is what `Stacks.sheafPushforwardCompIso` records by being `CategoryTheory.Iso.refl`.  So the
comparison of inverse images is `CategoryTheory.Adjunction.leftAdjointUniq` of two adjunctions
with the *same* right adjoint, and `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`
turns it into an identity between the unit of `(g ∘ f)⁻¹ ⊣ (g ∘ f)_*` and the composite of the
two units.  That is `sheafAdjunction_unit_app_comp`, and it is the only input of the proof that
is not bookkeeping.

The rest is the corepresentation.  A map out of `freeOfOpen U` is a section over `U`, so the law
is an identity between sections, and in that form it is `corep_comp_law`: an identity over
abstract categories with every category, functor, object and natural transformation a
**variable**, so that none of the spelling crossings between `TopCat.Sheaf` and
`CategoryTheory.Sheaf (TopologicalSpace.Opens.grothendieckTopology ·)` is paid inside the
argument.  Its three restriction maps `κ₁`, `κ₂`, `κ₃` are the restriction maps of sections, and
their cocycle law — the only place the opens enter — is `Subsingleton.elim` of arrows of
`(Opens X)ᵒᵖ`, not an `eqToHom` computation.

## Main results

* `Stacks.Cohomology.ExtComparison.corep_comp_law`: the composition law for a comparison map of
  corepresenting objects, over abstract categories.
* `Stacks.Cohomology.ExtComparison.sheafAdjunction_unit_app_comp`: **the unit of the inverse
  image along a composite**, in terms of the two units and the comparison
  `(g ∘ f)⁻¹ ≅ f⁻¹ g⁻¹`.
* `Stacks.Cohomology.ExtComparison.freeOfOpenPullbackMap_comp`: **the composition law of
  `Stacks.Cohomology.AbelianColimit.freeOfOpenPullbackMap`**.

## References

* [Stacks Project, Tag 008I](https://stacks.math.columbia.edu/tag/008I)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ModuleSheafCohomology
open Stacks.Cohomology.AbelianColimit
open Stacks.Cohomology.ModuleComparison

universe u

namespace Stacks.Cohomology.ExtComparison

section Concrete

variable {D : Type*} [Category* D] {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y : D, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]

/-- An isomorphism in a concrete category is injective on elements. -/
theorem eq_of_iso_apply {A₁ A₂ : D} (e : A₁ ≅ A₂) {x y : ToType A₁} (h : e.hom x = e.hom y) :
    x = y := by
  have hz : ∀ z : ToType A₁, e.inv (e.hom z) = z := fun z => by
    rw [← CategoryTheory.comp_apply, e.hom_inv_id, CategoryTheory.id_apply]
  exact ((hz x).symm.trans (congrArg (fun w => e.inv w) h)).trans (hz y)

end Concrete

section Abstract

universe w u₀

variable {A : Type u₀} [Category.{w} A]

/-- Two successive images under a functor into a concrete category, with the composite given. -/
theorem map_map_apply (F : A ⥤ AddCommGrpCat.{w}) {A₁ A₂ A₃ : A} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃)
    (c : A₁ ⟶ A₃) (hc : a ≫ b = c) (x : ToType (F.obj A₁)) :
    F.map b (F.map a x) = F.map c x := by
  rw [← CategoryTheory.comp_apply, ← F.map_comp, hc]

/-- The image of a composite under a functor into a concrete category. -/
theorem functor_map_comp_apply (F : A ⥤ AddCommGrpCat.{w}) {A₁ A₂ A₃ : A} (a : A₁ ⟶ A₂)
    (b : A₂ ⟶ A₃) (x : ToType (F.obj A₁)) : F.map (a ≫ b) x = F.map b (F.map a x) := by
  rw [F.map_comp, CategoryTheory.comp_apply]

variable [Preadditive A] {H : A ⥤ AddCommGrpCat.{w}} {Xo : A}
  (α : H ≅ preadditiveCoyoneda.obj (op Xo))

/-- Reading a composite through a corepresentation. -/
theorem corep_inv_comp {P Q : A} (m : Xo ⟶ P) (k : P ⟶ Q) :
    α.inv.app Q (m ≫ k) = H.map k (α.inv.app P m) :=
  NatTrans.naturality_apply α.inv k m

/-- A morphism out of a corepresenting object is determined by the section it corresponds to. -/
theorem eq_of_corep_inv_eq {P : A} {m m' : Xo ⟶ P}
    (h : α.inv.app P m = α.inv.app P m') : m = m' :=
  eq_of_iso_apply (α.symm.app P) h

end Abstract

section CocycleAux

universe w ua ub uc

variable {Sa : Type ua} {Sb : Type ub} {Sc : Type uc} [Category.{w} Sa] [Category.{w} Sb]
  [Category.{w} Sc] [Preadditive Sa] [Preadditive Sb] [Preadditive Sc]

/-- **The composition law of a comparison map of corepresenting objects**, with every category,
functor, object and natural transformation a variable.

`α₁`, `α₂`, `α₃` corepresent three functors to abelian groups; `η₁`, `η₂` are the two units;
`κ₁`, `κ₂`, `κ₃` are the three restriction maps and `hκ` their cocycle law, needed only at the
one object where it is used; `θ` is the
comparison of the two left adjoints; and `hρ₁`, `hρ₂`, `hρ₃` say that the three comparison maps
of corepresenting objects are the units restricted. -/
theorem corep_comp_law {L₁ : Sb ⥤ Sa} {R₁ : Sa ⥤ Sb} {L₂ : Sc ⥤ Sb} {R₂ : Sb ⥤ Sc}
    {L₃ : Sc ⥤ Sa} {S₁ : Sa ⥤ AddCommGrpCat.{w}} {S₂ : Sb ⥤ AddCommGrpCat.{w}}
    {S₃ : Sc ⥤ AddCommGrpCat.{w}} {A₁ : Sa} {A₂ : Sb} {A₃ : Sc}
    (α₁ : S₁ ≅ preadditiveCoyoneda.obj (op A₁)) (α₂ : S₂ ≅ preadditiveCoyoneda.obj (op A₂))
    (α₃ : S₃ ≅ preadditiveCoyoneda.obj (op A₃))
    (η₁ : 𝟭 Sb ⟶ L₁ ⋙ R₁) (η₂ : 𝟭 Sc ⟶ L₂ ⋙ R₂)
    (κ₁ : R₁ ⋙ S₂ ⟶ S₁) (κ₂ : R₂ ⋙ S₃ ⟶ S₂) (κ₃ : R₁ ⋙ R₂ ⋙ S₃ ⟶ S₁)
    (θ : L₂ ⋙ L₁ ⟶ L₃) (ρ₁ : A₁ ⟶ L₁.obj A₂) (ρ₂ : A₂ ⟶ L₂.obj A₃) (ρ₃ : A₁ ⟶ L₃.obj A₃)
    (hκ : ∀ w : ToType (S₃.obj (R₂.obj (R₁.obj (L₁.obj (L₂.obj A₃))))),
      κ₃.app (L₁.obj (L₂.obj A₃)) w =
        κ₁.app (L₁.obj (L₂.obj A₃)) (κ₂.app (R₁.obj (L₁.obj (L₂.obj A₃))) w))
    (hρ₁ : α₁.inv.app (L₁.obj A₂) ρ₁ =
      κ₁.app (L₁.obj A₂) (α₂.inv.app (R₁.obj (L₁.obj A₂)) (η₁.app A₂)))
    (hρ₂ : α₂.inv.app (L₂.obj A₃) ρ₂ =
      κ₂.app (L₂.obj A₃) (α₃.inv.app (R₂.obj (L₂.obj A₃)) (η₂.app A₃)))
    (hρ₃ : α₁.inv.app (L₃.obj A₃) ρ₃ =
      κ₃.app (L₃.obj A₃) (α₃.inv.app (R₂.obj (R₁.obj (L₃.obj A₃)))
        ((η₂.app A₃ ≫ R₂.map (η₁.app (L₂.obj A₃))) ≫ (R₁ ⋙ R₂).map (θ.app A₃)))) :
    ρ₃ = ρ₁ ≫ L₁.map ρ₂ ≫ θ.app A₃ := by
  refine eq_of_corep_inv_eq α₁ ?_
  have hη : η₁.app A₂ ≫ R₁.map (L₁.map ρ₂) = ρ₂ ≫ η₁.app (L₂.obj A₃) := (η₁.naturality ρ₂).symm
  rw [hρ₃, corep_inv_comp α₃, corep_inv_comp α₃]
  erw [NatTrans.naturality_apply κ₃ (θ.app A₃) _, hκ,
    NatTrans.naturality_apply κ₂, corep_inv_comp α₁, hρ₁, functor_map_comp_apply S₁,
    ← NatTrans.naturality_apply κ₁ (L₁.map ρ₂), ← corep_inv_comp α₂, hη, corep_inv_comp α₂, hρ₂]
  rfl

end CocycleAux

section AdjunctionBookkeeping

variable {C : Type*} {D : Type*} [Category* C] [Category* D]

/-- The unit of an adjunction, read across the comparison of two left adjoints of one right
adjoint. -/
theorem unit_comp_map_leftAdjointUniq_inv {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (Ao : C) :
    adj.unit.app Ao =
      adj'.unit.app Ao ≫ R.map ((Adjunction.leftAdjointUniq adj adj').inv.app Ao) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj adj' Ao
  rw [← h, Category.assoc, ← R.map_comp, Iso.hom_inv_id_app, R.map_id]
  exact (Category.comp_id _).symm

/-- The unit of an adjunction transported along an isomorphism of right adjoints. -/
theorem ofNatIsoRight_unit_app {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (iso : R ≅ R') (Ao : C) :
    (adj.ofNatIsoRight iso).unit.app Ao = adj.unit.app Ao ≫ iso.hom.app (L.obj Ao) :=
  rfl

end AdjunctionBookkeeping

/-! ### The composition law -/

section Comp

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The adjunction `(g ∘ f)⁻¹ ⊣ (g ∘ f)_*` read as a left adjoint of `f_* g_*`. -/
abbrev compAdj :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).ofNatIsoRight
      (sheafPushforwardCompIso f g AddCommGrpCat.{u}).symm

/-- The unit of the transported composite adjunction is the composite of the two units. -/
theorem compAdj_unit_app (G : (Z : TopCat.{u}).Sheaf AddCommGrpCat.{u}) :
    (compAdj f g).unit.app G =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app G ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj G)) := by
  refine (ofNatIsoRight_unit_app _ _ G).trans ?_
  rw [Adjunction.comp_unit_app]
  exact Category.comp_id _

/-- **The unit of the inverse image along a composite**, in terms of the two units and the
comparison `(g ∘ f)⁻¹ ≅ f⁻¹ g⁻¹`. -/
theorem sheafAdjunction_unit_app_comp (G : (Z : TopCat.{u}).Sheaf AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g)).unit.app G =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app G ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj G))) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).map
          ((sheafPullbackCompIso f g AddCommGrpCat.{u}).inv.app G) :=
  (unit_comp_map_leftAdjointUniq_inv
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g))
      (compAdj f g) G).trans
    (congrArg (fun z => z ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).map
      ((sheafPullbackCompIso f g AddCommGrpCat.{u}).inv.app G)) (compAdj_unit_app f g G))

/-- **The composition law of the comparison maps of corepresenting objects.** -/
theorem freeOfOpenPullbackMap_comp (W : Opens ↥Z) (V : Opens ↥Y) (U : Opens ↥X)
    (hV : V ≤ (Opens.map g).obj W) (hU : U ≤ (Opens.map f).obj V)
    (hUW : U ≤ (Opens.map (f ≫ g)).obj W) :
    freeOfOpenPullbackMap (f ≫ g) W U hUW =
      freeOfOpenPullbackMap f V U hU ≫ (sheafPullback f).map (freeOfOpenPullbackMap g W V hV) ≫
        (sheafPullbackCompIso (f := f) (g := g) AddCommGrpCat.{u}).inv.app (freeOfOpen W) :=
  corep_comp_law (repU U) (repU V) (repU W)
    (Spaces.sheafAdjunction f).unit (Spaces.sheafAdjunction g).unit
    ((sheafSections (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).map (homOfLE hU).op)
    ((sheafSections (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}).map (homOfLE hV).op)
    ((sheafSections (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}).map (homOfLE hUW).op)
    (sheafPullbackCompIso f g AddCommGrpCat.{u}).inv
    (freeOfOpenPullbackMap f V U hU) (freeOfOpenPullbackMap g W V hV)
    (freeOfOpenPullbackMap (f ≫ g) W U hUW)
    (fun w => (map_map_apply
      (((sheafPullback f).obj ((sheafPullback g).obj (freeOfOpen W))).obj)
      ((Opens.map f).map (homOfLE hV)).op (homOfLE hU).op (homOfLE hUW).op
      (Subsingleton.elim _ _) w).symm)
    (repU_inv_freeOfOpenPullbackMap f V U hU)
    (repU_inv_freeOfOpenPullbackMap g W V hV)
    ((repU_inv_freeOfOpenPullbackMap (f ≫ g) W U hUW).trans
      (congrArg (fun z =>
          ((sheafPullback (f ≫ g)).obj (freeOfOpen W)).obj.map (homOfLE hUW).op
            ((repU W).inv.app
              ((Spaces.sheafPushforward (f ≫ g)).obj
                ((sheafPullback (f ≫ g)).obj (freeOfOpen W))) z))
        (sheafAdjunction_unit_app_comp f g (freeOfOpen W))))

end Comp

end Stacks.Cohomology.ExtComparison

end
