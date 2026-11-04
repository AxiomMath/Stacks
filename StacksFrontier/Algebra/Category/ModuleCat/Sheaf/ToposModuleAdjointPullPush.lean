module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Adjoint pullback and pushforward of modules along a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and let `O` be a sheaf of rings on `C`. For a
sheaf of `f_*O`-modules `G` and a sheaf of `O`-modules `F`, Stacks 03D4 asserts a natural
bijection

`Mor_{Mod(O)}(O ⊗_{f⁻¹f_*O} f⁻¹G, F) = Mor_{Mod(f_*O)}(G, f_*F)`,

the tensor product being formed along the canonical map `f⁻¹f_*O ⟶ O`. This file constructs
that canonical map and deduces the bijection.

The proof is the source's: the bijection is the composite of the inverse-image/direct-image
adjunction for modules along `f` (Stacks 03D3, `inverseImageAdjDirectImageModules`) with the
change-of-rings adjunction along `f⁻¹f_*O ⟶ O` (Stacks 03CZ,
`Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction`).

## Main definitions

* `Stacks.Sheaves.ToposPushforward.ringCounit`: the canonical map `f⁻¹f_*O ⟶ O` of sheaves of
  rings. Its underlying map of sheaves of sets is the counit of `f⁻¹ ⊣ f_*`; that it respects
  the ring operations is the comparison between transporting the ring structure in two steps
  along `f_*` and then `f⁻¹`, and transporting it in one step along `f_* ⋙ f⁻¹`.
* `Stacks.Sheaves.RingedToposModules.tensorInverseImageModules`: the functor
  `G ↦ O ⊗_{f⁻¹f_*O} f⁻¹G`.
* `Stacks.Sheaves.RingedToposModules.directImageModulesOverPushforwardRing`: the functor
  `F ↦ f_*F`, valued in sheaves of `f_*O`-modules.

## Main results

* `Stacks.Sheaves.RingedToposModules.tensorInverseImageAdjDirectImageModules` (Stacks 03D4):
  the two functors above are adjoint.
* `Stacks.Sheaves.RingedToposModules.adjointPullPushModulesHomEquiv` (Stacks 03D4): the
  displayed bijection, together with its naturality in each variable.
* `Stacks.Sheaves.ToposPushforward.ringSheafMap_ringCounit`: the underlying map of sheaves of
  sets of `ringCounit` is the counit of `f⁻¹ ⊣ f_*`.
* `Stacks.Sheaves.ToposPushforward.ringSheafMap_ringUnit_comp_pushforward_map_ringCounit`: the
  composite `f_*O ⟶ f_*f⁻¹f_*O ⟶ f_*O` of `ringUnit` and `f_*` of `ringCounit` is the
  identity.

## Implementation notes

`O` is a sheaf of **rings**, not of commutative rings: that is what the source says, here and
in Stacks 03D1 and 03D3, and it is the level at which the inverse- and direct-image
constructions of Stacks 03D1 and 03D2 are available in this library
(`Stacks.Sheaves.ToposPushforward.pushforwardModule`,
`Stacks.Sheaves.ToposPullback.pullbackModule`). No commutativity is used anywhere below.

The right-hand functor is built as restriction of scalars along `ringCounit` followed by
`directImageModules`, rather than as a direct image of `O`-modules over `f_*O` constructed
from scratch. These agree: `directImageModules` restricts the direct image along the unit
`ringUnit : f_*O ⟶ f_*f⁻¹f_*O`, so the resulting `f_*O`-action on `f_*F` goes through the
composite `f_*O ⟶ f_*f⁻¹f_*O ⟶ f_*O` of that unit with `f_*` of `ringCounit`, and
`ringSheafMap_ringUnit_comp_pushforward_map_ringCounit` records that this composite is the
identity. So the action is `f_*` of the `O`-action on `F`, which is the direct image of
Stacks 03D1.

That the left-hand functor really is the tensor product of the source, and not merely some
left adjoint, is `Stacks.Sheaves.ModuleAdjunction.extendScalarsIso`: extension of scalars
along `ringCounit` is the sheafification of the sectionwise `O(U) ⊗_{(f⁻¹f_*O)(U)} -`.

The source site is assumed small, with its objects, morphisms, sheaves of rings and modules
in one universe `u`. This is inherited from the change-of-rings adjunction, and through it
from `PresheafOfModules.pullbackObjIsDefined_eq_top`, whose proof resolves a presheaf of
modules into free modules on representables; see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposModuleAdjunction.lean`. The target site is
unrestricted. The `HasSheafCompose` hypotheses are the size-sensitive existence hypotheses for
the underlying-sheaf functors that the constructions are stated through, exactly as in Stacks
03D1 and 03D2 as formalized here.

## References

* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite
open CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

universe ww ww' vv uu vv' uu'

section RingCounit

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (O : Sheaf J RingCat.{ww})

/-- The counit of the adjunction `f⁻¹ ⊣ f_*`, whiskered with the sections functor over a
fixed object of the source site. -/
noncomputable def counitSections (X : Cᵒᵖ) :
    (f.pushforward ⋙ f.inverseImage) ⋙ Sheaf.sectionsFunctor J X ⟶
      Sheaf.sectionsFunctor J X where
  app A := (Sheaf.sectionsFunctor J X).map (f.adj.counit.app A)
  naturality A B m := by
    dsimp
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg _ (f.adj.counit.naturality m)

/-- The canonical map `f⁻¹f_*O ⟶ O`, on sections over a fixed object, as a map of rings. -/
noncomputable def ringCounitApp (X : Cᵒᵖ) :
    (inverseImageRingSheaf f (pushforwardRingSheaf f O)).obj.obj X ⟶ O.obj.obj X :=
  letI := Sheaf.ringObjRing (pushforwardRingSheaf f O)
    (f.inverseImage ⋙ Sheaf.sectionsFunctor J X)
  RingCat.ofHom
    { toFun := (Sheaf.sectionsFunctor J X).map (f.adj.counit.app (Sheaf.ringSheaf O))
      map_add' := fun x y ↦
        (congrArg ((Sheaf.sectionsFunctor J X).map (f.adj.counit.app (Sheaf.ringSheaf O)))
            (ringAddObj_comp K f.pushforward O
              (f.inverseImage ⋙ Sheaf.sectionsFunctor J X) x y)).trans
          ((Sheaf.ringAddObj_naturality O (counitSections f X) x y).trans
            (Sheaf.sectionsFunctor_map_ringAddHom O X _ _))
      map_mul' := fun x y ↦
        (congrArg ((Sheaf.sectionsFunctor J X).map (f.adj.counit.app (Sheaf.ringSheaf O)))
            (ringMulObj_comp K f.pushforward O
              (f.inverseImage ⋙ Sheaf.sectionsFunctor J X) x y)).trans
          ((Sheaf.ringMulObj_naturality O (counitSections f X) x y).trans
            (Sheaf.sectionsFunctor_map_ringMulHom O X _ _))
      map_zero' :=
        (congrArg ((Sheaf.sectionsFunctor J X).map (f.adj.counit.app (Sheaf.ringSheaf O)))
            (ringZeroObj_comp K f.pushforward O
              (f.inverseImage ⋙ Sheaf.sectionsFunctor J X))).trans
          ((Sheaf.ringZeroObj_naturality O (counitSections f X)).trans
            (Sheaf.sectionsFunctor_map_ringZeroHom O X default))
      map_one' :=
        (congrArg ((Sheaf.sectionsFunctor J X).map (f.adj.counit.app (Sheaf.ringSheaf O)))
            (ringOneObj_comp K f.pushforward O
              (f.inverseImage ⋙ Sheaf.sectionsFunctor J X))).trans
          ((Sheaf.ringOneObj_naturality O (counitSections f X)).trans
            (Sheaf.sectionsFunctor_map_ringOneHom O X default)) }

/-- The canonical map `f⁻¹f_*O ⟶ O` as a morphism of sheaves of rings. -/
noncomputable def ringCounit :
    inverseImageRingSheaf f (pushforwardRingSheaf f O) ⟶ O where
  hom :=
    { app := fun X ↦ ringCounitApp f O X
      naturality := fun X Y g ↦ by
        refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        exact NatTrans.naturality_apply (f.adj.counit.app (Sheaf.ringSheaf O)).hom g x }

/-- The underlying morphism of sheaves of sets of `f⁻¹f_*O ⟶ O` is the counit of
`f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `O`. -/
lemma ringSheafMap_ringCounit :
    (sheafCompose J (forget RingCat.{ww})).map (ringCounit f O) =
      f.adj.counit.app (Sheaf.ringSheaf O) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The composite `f_*O ⟶ f_*f⁻¹f_*O ⟶ f_*O` of the unit `ringUnit` and the direct image of
the counit `ringCounit` is the identity, read on underlying sheaves of sets. This is the
triangle identity of `f⁻¹ ⊣ f_*`, and it is what makes the right-hand functor of Stacks 03D4
the direct image with its own `f_*O`-action: restricting an `O`-module along `ringCounit`,
pushing it forward, and restricting along `ringUnit` acts through this composite. -/
lemma ringSheafMap_ringUnit_comp_pushforward_map_ringCounit :
    (sheafCompose K (forget RingCat.{ww'})).map
          (Stacks.Sheaves.ToposPushforward.ringUnit f (pushforwardRingSheaf f O)) ≫
        f.pushforward.map ((sheafCompose J (forget RingCat.{ww})).map (ringCounit f O)) =
      𝟙 (f.pushforward.obj (Sheaf.ringSheaf O)) := by
  rw [Stacks.Sheaves.RingedToposModules.ringSheafMap_ringUnit f (pushforwardRingSheaf f O),
    ringSheafMap_ringCounit f O]
  exact f.adj.right_triangle_components (Sheaf.ringSheaf O)

end RingCounit

end Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

universe w' v' u' u

section AdjointPullPush

variable {C : Type u} [SmallCategory C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type w')))
  (O : Sheaf J RingCat.{u})

/-- The left-hand functor of Stacks 03D4: `G ↦ O ⊗_{f⁻¹f_*O} f⁻¹G`, the inverse image of a
sheaf of `f_*O`-modules followed by extension of scalars along the canonical map
`f⁻¹f_*O ⟶ O`. -/
noncomputable abbrev tensorInverseImageModules :
    SheafOfModules.{w'} (pushforwardRingSheaf f O) ⥤ SheafOfModules.{u} O :=
  inverseImageModules f (pushforwardRingSheaf f O) ⋙
    Stacks.Sheaves.ModuleAdjunction.extendScalars (ringCounit f O)

/-- The right-hand functor of Stacks 03D4: `F ↦ f_*F`, the direct image of a sheaf of
`O`-modules read as a sheaf of `f_*O`-modules. -/
noncomputable abbrev directImageModulesOverPushforwardRing :
    SheafOfModules.{u} O ⥤ SheafOfModules.{w'} (pushforwardRingSheaf f O) :=
  SheafOfModules.restrictScalars (ringCounit f O) ⋙
    directImageModules f (pushforwardRingSheaf f O)

/-- **Stacks 03D4** as an adjunction: for a morphism of topoi `f : Sh(C) ⟶ Sh(D)` and a sheaf
of rings `O` on `C`, the functor `G ↦ O ⊗_{f⁻¹f_*O} f⁻¹G` from sheaves of `f_*O`-modules to
sheaves of `O`-modules is left adjoint to the direct image `F ↦ f_*F`. -/
@[stacks 03D4]
noncomputable def tensorInverseImageAdjDirectImageModules :
    tensorInverseImageModules f O ⊣ directImageModulesOverPushforwardRing f O :=
  (inverseImageAdjDirectImageModules f (pushforwardRingSheaf f O)).comp
    (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction (ringCounit f O))

/-- **Stacks 03D4** as the displayed bijection
`Mor_{Mod(O)}(O ⊗_{f⁻¹f_*O} f⁻¹G, F) = Mor_{Mod(f_*O)}(G, f_*F)`. -/
@[stacks 03D4]
noncomputable def adjointPullPushModulesHomEquiv
    (G : SheafOfModules.{w'} (pushforwardRingSheaf f O)) (F : SheafOfModules.{u} O) :
    ((tensorInverseImageModules f O).obj G ⟶ F) ≃
      (G ⟶ (directImageModulesOverPushforwardRing f O).obj F) :=
  (tensorInverseImageAdjDirectImageModules f O).homEquiv G F

/-- The bijection of Stacks 03D4 is natural in the sheaf of `f_*O`-modules. -/
theorem adjointPullPushModulesHomEquiv_naturality_left
    {G G' : SheafOfModules.{w'} (pushforwardRingSheaf f O)} {F : SheafOfModules.{u} O}
    (g : G' ⟶ G) (a : (tensorInverseImageModules f O).obj G ⟶ F) :
    adjointPullPushModulesHomEquiv f O G' F
        ((tensorInverseImageModules f O).map g ≫ a) =
      g ≫ adjointPullPushModulesHomEquiv f O G F a :=
  (tensorInverseImageAdjDirectImageModules f O).homEquiv_naturality_left g a

/-- The bijection of Stacks 03D4 is natural in the sheaf of `O`-modules. -/
theorem adjointPullPushModulesHomEquiv_naturality_right
    {G : SheafOfModules.{w'} (pushforwardRingSheaf f O)} {F F' : SheafOfModules.{u} O}
    (a : (tensorInverseImageModules f O).obj G ⟶ F) (k : F ⟶ F') :
    adjointPullPushModulesHomEquiv f O G F' (a ≫ k) =
      adjointPullPushModulesHomEquiv f O G F a ≫
        (directImageModulesOverPushforwardRing f O).map k :=
  (tensorInverseImageAdjDirectImageModules f O).homEquiv_naturality_right a k

end AdjointPullPush

end Stacks.Sheaves.RingedToposModules
