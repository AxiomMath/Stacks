module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion

/-!
# The relative Hom functor across the relocalization of algebraic spaces

Let `h : W ⟶ S` be a morphism of a big fppf site and `Λ` the lower-shriek extension of
algebraic spaces over `W` to algebraic spaces over `S`.  For an algebraic space `X` over `W`
and two `𝒪_X`-modules `F`, `G`, the Hom sets `Hom(z^*F, z^*G)` over the algebraic spaces
`z : Z ⟶ X` over `X` with `z` representable are the Hom sets
`Hom((Λ z)^*(E F), (Λ z)^*(E G))` over `Λ Z ⟶ Λ X`, naturally in `Z`, where `E` is the
equivalence `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSpacesFunctorSE`: `Λ` as a functor on algebraic spaces.
* `AlgebraicGeometry.Space.relocalizeOver`: `Λ` on the algebraic spaces over `X`.
* `AlgebraicGeometry.Space.relocalizeHomEquiv`: the identification of the two Hom sets.

* `AlgebraicGeometry.Space.relocalizeModuleHomOverIso`: the identification of the relative Hom
  functors, restricted along a functor to the algebraic spaces over `X` whose structure and
  transition morphisms are representable.

## Main results

* `AlgebraicGeometry.Space.relocalizeHomEquiv_conjHom`: the identification is natural, that is
  compatible with pulling homomorphisms back along morphisms over `X`; it is the composition law
  `AlgebraicGeometry.Space.relocalizeModulePullbackIso_triangle`.

## Implementation notes

The relocalized relative Hom functor is `moduleHomOver` at `Λ X`; its implicit algebraic space
is always passed explicitly, since otherwise it must be solved from the module category
`Modules B S hS (Λ.obj X.1) _`, a non-pattern problem that unfolds the structure sheaves.

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- The lower-shriek extension, as a functor from algebraic spaces over `W` to algebraic spaces
over `S`. -/
def relocalizeSpacesFunctorSE : AlgebraicSpaces B W hW ⥤ AlgebraicSpaces B S hS where
  obj := relocalizeSpaceSE B W S hW hS h
  map := relocalizeHomSE B W S hW hS h
  map_id X := ObjectProperty.hom_ext _ ((OverShriek.relocalizePresheafFunctor h).map_id X.1)
  map_comp _ _ := rfl

/-- The lower-shriek extension on the algebraic spaces over `X`: `Z ⟶ X` goes to
`Λ Z ⟶ Λ X`.  It is `CategoryTheory.Over.post` of
`AlgebraicGeometry.Space.relocalizeSpacesFunctorSE`, written out so that the structure morphisms
are `AlgebraicGeometry.Space.relocalizeHomSE` on the nose. -/
abbrev relocalizeOver (X : AlgebraicSpaces B W hW) :
    Over X ⥤ Over (relocalizeSpaceSE B W S hW hS h X) where
  obj Z :=
    { left := relocalizeSpaceSE B W S hW hS h Z.left
      right := Discrete.mk PUnit.unit
      hom := relocalizeHomSE B W S hW hS h Z.hom }
  map m :=
    { left := relocalizeHomSE B W S hW hS h m.left
      right := 𝟙 _
      w := (congrArg (relocalizeHomSE B W S hW hS h) (Over.w m)).trans (Category.comp_id _).symm }
  map_id Z := Over.OverMorphism.ext ((relocalizeSpacesFunctorSE B W S hW hS h).map_id Z.left)
  map_comp _ _ := Over.OverMorphism.ext rfl

variable {X : AlgebraicSpaces B W hW}

/-- **The Hom sets of the pulled-back modules across relocalization.**  For an algebraic space
`z : Z ⟶ X` over `X` with `z` representable, homomorphisms `z^*F ⟶ z^*G` are homomorphisms
`(Λ z)^*(E F) ⟶ (Λ z)^*(E G)`: apply the equivalence `E` and conjugate by
`AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE`. -/
def relocalizeHomEquiv (Z : Over X) (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (F G : Modules.{u, u} B W hW X.1 X.2) :
    ((modulePullback B W hW Z.hom).obj F ⟶ (modulePullback B W hW Z.hom).obj G) ≃
      ((modulePullback B S hS (relocalizeHomSE B W S hW hS h Z.hom)).obj
          ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor.obj F) ⟶
        (modulePullback B S hS (relocalizeHomSE B W S hW hS h Z.hom)).obj
          ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor.obj G)) :=
  ((relocalizeModulesEquivalenceSE B W S hW hS h Z.left.2
      (relocalizeSpaceSE B W S hW hS h Z.left).2).fullyFaithfulFunctor.homEquiv).trans
    (((relocalizeModulePullbackIsoSE B W S hW hS h Z.hom hZ).app F).homCongr
      ((relocalizeModulePullbackIsoSE B W S hW hS h Z.hom hZ).app G))

/-- `AlgebraicGeometry.Space.relocalizeHomEquiv` written out. -/
theorem relocalizeHomEquiv_apply (Z : Over X) (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (F G : Modules.{u, u} B W hW X.1 X.2)
    (a : (modulePullback B W hW Z.hom).obj F ⟶ (modulePullback B W hW Z.hom).obj G) :
    relocalizeHomEquiv B W S hW hS h Z hZ F G a =
      (relocalizeModulePullbackIsoSE B W S hW hS h Z.hom hZ).inv.app F ≫
        (relocalizeModulesEquivalenceSE B W S hW hS h Z.left.2
          (relocalizeSpaceSE B W S hW hS h Z.left).2).functor.map a ≫
        (relocalizeModulePullbackIsoSE B W S hW hS h Z.hom hZ).hom.app G :=
  rfl

/-- **The identification of Hom sets is natural**: pulling a homomorphism back along a
morphism `m : Z' ⟶ Z` over `X` and then relocalizing is relocalizing and then pulling back along
`Λ m`.  This is the composition law `AlgebraicGeometry.Space.relocalizeModulePullbackIso_triangle`
together with the naturality of the identification for `m`. -/
theorem relocalizeHomEquiv_conjHom {Z Z' : Over X} (m : Z' ⟶ Z)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (hZ' : yoneda.relativelyRepresentable Z'.hom.hom)
    (hm : yoneda.relativelyRepresentable m.left.hom)
    (hΛ : relocalizeHomSE B W S hW hS h m.left ≫ relocalizeHomSE B W S hW hS h Z.hom =
      relocalizeHomSE B W S hW hS h Z'.hom)
    (F G : Modules.{u, u} B W hW X.1 X.2)
    (a : (modulePullback B W hW Z.hom).obj F ⟶ (modulePullback B W hW Z.hom).obj G) :
    relocalizeHomEquiv B W S hW hS h Z' hZ' F G
        (Functor.conjHom (modulePullbackTriangle B W hW (Over.w m)) a) =
      Functor.conjHom (modulePullbackTriangle B S hS hΛ)
        (relocalizeHomEquiv B W S hW hS h Z hZ F G a) := by
  rw [relocalizeHomEquiv_apply, relocalizeHomEquiv_apply,
    relocalizeModulePullbackIso_triangle B W S hW hS h m.left Z.hom hm hZ (Over.w m) hZ' hΛ]
  simp only [Functor.conjHom, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Iso.symm_inv, Functor.map_comp, Category.assoc, Functor.comp_obj]
  have nat := (relocalizeModulePullbackIsoSE B W S hW hS h m.left hm).inv.naturality a
  simp only [Functor.comp_map] at nat
  have mid : (relocalizeModulePullbackIsoSE B W S hW hS h m.left hm).inv.app
        ((modulePullback B W hW Z.hom).obj F) ≫
      (relocalizeModulesEquivalenceSE B W S hW hS h Z'.left.2
        (relocalizeSpaceSE B W S hW hS h Z'.left).2).functor.map
          ((modulePullbackTriangle B W hW (Over.w m)).inv.app F) ≫
      (relocalizeModulesEquivalenceSE B W S hW hS h Z'.left.2
        (relocalizeSpaceSE B W S hW hS h Z'.left).2).functor.map
          ((modulePullbackTriangle B W hW (Over.w m)).hom.app F) ≫
      (relocalizeModulesEquivalenceSE B W S hW hS h Z'.left.2
        (relocalizeSpaceSE B W S hW hS h Z'.left).2).functor.map
          ((modulePullback B W hW m.left).map a) ≫
      (relocalizeModulesEquivalenceSE B W S hW hS h Z'.left.2
        (relocalizeSpaceSE B W S hW hS h Z'.left).2).functor.map
          ((modulePullbackTriangle B W hW (Over.w m)).inv.app G) ≫
      (relocalizeModulesEquivalenceSE B W S hW hS h Z'.left.2
        (relocalizeSpaceSE B W S hW hS h Z'.left).2).functor.map
          ((modulePullbackTriangle B W hW (Over.w m)).hom.app G) ≫
      (relocalizeModulePullbackIsoSE B W S hW hS h m.left hm).hom.app
        ((modulePullback B W hW Z.hom).obj G) =
      (modulePullback B S hS (relocalizeHomSE B W S hW hS h m.left)).map
        ((relocalizeModulesEquivalenceSE B W S hW hS h Z.left.2
          (relocalizeSpaceSE B W S hW hS h Z.left).2).functor.map a) := by
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Functor.comp_obj, Category.comp_id]
    rw [← reassoc_of% nat, Iso.inv_hom_id_app]
    exact Category.comp_id _
  simp only [reassoc_of% mid]

/-- The action of the relative Hom functor on the opposite of a morphism over `Y`. -/
theorem moduleHomOver_map_op {Y : AlgebraicSpaces B S hS} {Z Z' : Over Y} (m : Z' ⟶ Z)
    (hc : ModulePushforwardCoherence B S hS) (F G : Modules.{u, u} B S hS Y.1 Y.2) :
    (moduleHomOver hc F G).map m.op =
      ↾(Functor.conjHom (M := F) (N := G) (modulePullbackTriangle B S hS (Over.w m))) :=
  rfl

/-- `AlgebraicGeometry.Space.relocalizeHomEquiv` between the values of the relative Hom
functors. -/
def relocalizeModuleHomOverEquiv (hc : ModulePushforwardCoherence B W hW)
    (hc' : ModulePushforwardCoherence B S hS) (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (F G : Modules.{u, u} B W hW X.1 X.2) :
    (moduleHomOver hc F G).obj (Opposite.op Z) ≃
      (moduleHomOver (X := relocalizeSpaceSE B W S hW hS h X) hc'
          ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor.obj F)
          ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor.obj G)).obj
        (Opposite.op ((relocalizeOver B W S hW hS h X).obj Z)) :=
  relocalizeHomEquiv B W S hW hS h Z hZ F G

/-- `AlgebraicGeometry.Space.relocalizeModuleHomOverEquiv` written out. -/
theorem relocalizeModuleHomOverEquiv_apply (hc : ModulePushforwardCoherence B W hW)
    (hc' : ModulePushforwardCoherence B S hS) (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (F G : Modules.{u, u} B W hW X.1 X.2)
    (a : (moduleHomOver hc F G).obj (Opposite.op Z)) :
    relocalizeModuleHomOverEquiv B W S hW hS h hc hc' Z hZ F G a =
      (relocalizeModulePullbackIsoSE B W S hW hS h Z.hom hZ).inv.app F ≫
        (relocalizeModulesEquivalenceSE B W S hW hS h Z.left.2
          (relocalizeSpaceSE B W S hW hS h Z.left).2).functor.map a ≫
        (relocalizeModulePullbackIsoSE B W S hW hS h Z.hom hZ).hom.app G :=
  rfl

/-- The action of the relocalized relative Hom functor on the image of a morphism over `X`,
with the triangle spelled through `AlgebraicGeometry.Space.relocalizeHomSE`. -/
theorem moduleHomOver_map_relocalizeOver {Z Z' : Over X} (m : Z' ⟶ Z)
    (hc' : ModulePushforwardCoherence B S hS) (F G : Modules.{u, u} B W hW X.1 X.2) :
    (moduleHomOver (X := relocalizeSpaceSE B W S hW hS h X) hc'
        ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
          (relocalizeSpaceSE B W S hW hS h X).2).functor.obj F)
        ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
          (relocalizeSpaceSE B W S hW hS h X).2).functor.obj G)).map
        ((relocalizeOver B W S hW hS h X).map m).op =
      ↾(Functor.conjHom
        (M := ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
          (relocalizeSpaceSE B W S hW hS h X).2).functor.obj F))
        (N := ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
          (relocalizeSpaceSE B W S hW hS h X).2).functor.obj G))
        (modulePullbackTriangle B S hS (f := relocalizeHomSE B W S hW hS h m.left)
          (g := relocalizeHomSE B W S hW hS h Z.hom) (k := relocalizeHomSE B W S hW hS h Z'.hom)
          (congrArg (relocalizeHomSE B W S hW hS h) (Over.w m)))) :=
  rfl

/-- **The identification of the values of the relative Hom functors is natural**, as an
equality of morphisms of types. -/
theorem relocalizeModuleHomOverEquiv_naturality {Z Z' : Over X} (m : Z' ⟶ Z)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom)
    (hZ' : yoneda.relativelyRepresentable Z'.hom.hom)
    (hm : yoneda.relativelyRepresentable m.left.hom)
    (hc : ModulePushforwardCoherence B W hW) (hc' : ModulePushforwardCoherence B S hS)
    (F G : Modules.{u, u} B W hW X.1 X.2) :
    (moduleHomOver hc F G).map m.op ≫
        (relocalizeModuleHomOverEquiv B W S hW hS h hc hc' Z' hZ' F G).toIso.hom =
      (relocalizeModuleHomOverEquiv B W S hW hS h hc hc' Z hZ F G).toIso.hom ≫
        (moduleHomOver (X := relocalizeSpaceSE B W S hW hS h X) hc'
            ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
              (relocalizeSpaceSE B W S hW hS h X).2).functor.obj F)
            ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
              (relocalizeSpaceSE B W S hW hS h X).2).functor.obj G)).map
          ((relocalizeOver B W S hW hS h X).map m).op := by
  rw [moduleHomOver_map_op, moduleHomOver_map_relocalizeOver B W S hW hS h m hc' F G]
  exact ofHom_comp_eq_comp _ _ _ _ fun a =>
    relocalizeHomEquiv_conjHom B W S hW hS h m hZ hZ' hm
      (congrArg (relocalizeHomSE B W S hW hS h) (Over.w m)) F G a

/-- **The relative Hom functors across relocalization.**  Restricted along a functor `P` to the
algebraic spaces over `X` whose structure morphisms and transition morphisms are representable,
the relative Hom functor of `F` and `G` over `W` is the relative Hom functor of `E F` and `E G`
over `S`, restricted along `P ⋙ Λ`. -/
def relocalizeModuleHomOverIso {C : Type*} [Category* C] (P : C ⥤ Over X)
    (hP : ∀ c, yoneda.relativelyRepresentable (P.obj c).hom.hom)
    (hPm : ∀ {c c' : C} (f : c ⟶ c'), yoneda.relativelyRepresentable (P.map f).left.hom)
    (hc : ModulePushforwardCoherence B W hW) (hc' : ModulePushforwardCoherence B S hS)
    (F G : Modules.{u, u} B W hW X.1 X.2) :
    P.op ⋙ moduleHomOver hc F G ≅ (P ⋙ relocalizeOver B W S hW hS h X).op ⋙
      (moduleHomOver (X := relocalizeSpaceSE B W S hW hS h X) hc'
          ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor.obj F)
          ((relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor.obj G)) :=
  NatIso.ofComponents
    (fun c => (relocalizeModuleHomOverEquiv B W S hW hS h hc hc' (P.op.obj c).unop (hP c.unop)
      F G).toIso)
    (fun {c c'} f => relocalizeModuleHomOverEquiv_naturality B W S hW hS h (P.op.map f).unop
      (hP c.unop) (hP c'.unop) (hPm f.unop) hc hc' F G)

end AlgebraicGeometry.Space

end
