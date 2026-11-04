module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackAssoc
public import StacksFrontier.CategoryTheory.Comma.Over.PullbackCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# The associativity coherence of the composition isomorphisms of direct images

For a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` of morphisms of algebraic spaces, Stacks 03G2,
parts (2) and (3), compare base change and direct images along a composite with the iterated
ones, and Stacks 03LU does the same for direct images of `𝒪`-modules.  For three composable
morphisms there are two ways of comparing the thrice-iterated construction with the one along
the triple composite, and this file proves that they agree, at each level from the spaces-étale
sites up to the direct images of modules along the morphisms of ringed topoi of Stacks 03G8.

## Main definitions

* `CategoryTheory.Equivalence.transportCompApp` is a composition comparison conjugated by
  equivalences of all the categories involved, read on one object.
* `AlgebraicGeometry.Space.pushforwardModulesCompAt` is the comparison of the direct images of
  modules of a composite, at the level of the morphisms of ringed topoi of Stacks 03G8.

## Main results

* `CategoryTheory.Equivalence.transportCompApp_assoc`: conjugating by equivalences preserves
  the associativity cocycle law.
* `AlgebraicGeometry.Space.spacesBaseChange_comp_inv_assoc`,
  `AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU_assoc` and
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`: the cocycle law for base change
  on the spaces-étale sites, for the induced direct images of sheaves of sets, and for the
  direct images of the small étale topoi.
* `AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc`: the cocycle law for the comparison
  of the direct images of modules along the morphisms of ringed topoi of Stacks 03G8.

## Implementation notes

The coherence is transported, layer by layer, from the cocycle law for
`CategoryTheory.Over.pullbackComp` — which holds because `CategoryTheory.Over.map` is a *strict*
functor of the base, see `StacksFrontier/CategoryTheory/Comma/Over/PullbackCoherence.lean`:

* `spacesBaseChange_comp_inv_assoc` is that cocycle law restricted to the objects étale over
  the base, since `AlgebraicGeometry.Space.spacesBaseChange_comp` is
  `CategoryTheory.Over.pullbackComp` so restricted;
* `spacesBaseChange_pushforward_compTypeU_assoc` is its image under taking sheaf direct images,
  which adds nothing because `CategoryTheory.Functor.sheafPushforwardContinuousComp` is the
  identity and the comparison of direct images along isomorphic continuous functors is
  restriction along that isomorphism;
* `smallToposMorphismTypeU_comp_assoc` conjugates by the comparison equivalences of Stacks
  03G1.  The two unit isomorphisms that `MorphismOfTopoi.transport_comp_pushforward` inserts sit
  at different slots, so this step is an interchange law; it is carried out for arbitrary
  equivalences in `CategoryTheory.Equivalence.transportCompApp_assoc`;
* `pushforwardModulesCompAt_assoc` passes to sheaves of modules.  The comparison of direct
  images of modules is the identity on the underlying sheaves of sets and the transport along
  the 2-isomorphism of morphisms of ringed topoi is the previous comparison there, so the
  coherence is tested on the underlying sheaves of sets, by
  `Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`.

Associativity of composition in `AlgebraicGeometry.AlgebraicSpaces` holds by definitional
unfolding, so no transport along `CategoryTheory.Category.assoc` appears below; this is what
makes `AlgebraicGeometry.Space.pullbackComp_hom_assoc_app` a plain cocycle law rather than one
carrying a `CategoryTheory.Over.pullbackCongr'`.

`CategoryTheory.Equivalence.transportCompApp` and its cocycle law are general category theory
and belong with `CategoryTheory.Equivalence`; they are here to keep that file untouched.

## What is not done

The coherence IS carried across from `pushforwardModulesCompAt` to
`AlgebraicGeometry.Space.modulePushforwardCompIso`, and so to
`AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean`: the
transport is performed at the level of isomorphisms of functors, by
`Functor.cocycle_iso_of_eq_compIsoCongr`, so that no `eqToHom` is ever projected to a morphism.
The paragraph below records what made the naive route fail, and is kept for that reason.
What separates the two is bookkeeping and
not mathematics: `modulePushforwardCompIso` is `pushforwardModulesCompAt` conjugated by the two
transports along `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, and a
cocycle law is invariant under such a transport — the statement with the four transports
inserted follows from the one without them by substituting the six equalities of functors.
Formally, however, the two sides are stated in two different spellings of one category of
modules: `AlgebraicGeometry.Space.Modules` presents the sheaf of rings as
`AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed *site*, while
`Stacks.Sheaves.RingedToposModules.pushforwardModules` presents it as
`Stacks.SheafOfModules.Tensor.ringSheaf` of the small étale ringed *topos*.  The two are
definitionally equal but not syntactically so, and
identifying them at the top of a statement of this size exhausts both the elaborator's and the
kernel's budget.  Respelling one of the two — so that a single expression for the category and
its instance is shared — is what the remaining step needs.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules (hom_ext_moduleSheafFunctor
  moduleSheafFunctor_map_ofSheafHom)

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ w₀ w₁ w₂ w₃ u₀ u₁ u₂ u₃ t₀ t₁ t₂ t₃

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]

namespace Equivalence

variable {B₀ : Type t₀} {B₁ : Type t₁} {B₂ : Type t₂} {B₃ : Type t₃}
  [Category.{w₀} B₀] [Category.{w₁} B₁] [Category.{w₂} B₂] [Category.{w₃} B₃]
  (e₀ : A₀ ≌ B₀) (e₁ : A₁ ≌ B₁) (e₂ : A₂ ≌ B₂) (e₃ : A₃ ≌ B₃)

/-- The component of a composition comparison `p ⋙ q ≅ pq` conjugated by equivalences: the
comparison of the conjugated functors, whose composite carries the unit isomorphism of the
equivalence of the middle category. -/
def transportCompApp {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {pq : A₀ ⥤ A₂} (P : p ⋙ q ≅ pq) (M : B₀) :=
  e₂.functor.map (q.map (e₁.unitIso.inv.app (p.obj (e₀.inverse.obj M)))) ≫
    e₂.functor.map (P.hom.app (e₀.inverse.obj M))

/-- The cocycle law for conjugated composition comparisons, before the outer equivalence is
applied: the two unit isomorphisms sit at different slots and commute past one another. -/
private theorem transportCompApp_assoc_aux {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {r : A₂ ⥤ A₃}
    {pq : A₀ ⥤ A₂} {qr : A₁ ⥤ A₃} {pqr : A₀ ⥤ A₃} (P : p ⋙ q ≅ pq) (Q : q ⋙ r ≅ qr)
    (PQ : pq ⋙ r ≅ pqr) (QR : p ⋙ qr ≅ pqr)
    (hcoc : ∀ N, r.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p.obj N) ≫ QR.hom.app N)
    (N : A₀) :
    r.map (e₂.inverse.map (e₂.functor.map (q.map (e₁.unitIso.inv.app (p.obj N))) ≫
          e₂.functor.map (P.hom.app N))) ≫
        (r.map (e₂.unitIso.inv.app (pq.obj N)) ≫ PQ.hom.app N) =
      (r.map (e₂.unitIso.inv.app (q.obj (e₁.inverse.obj (e₁.functor.obj (p.obj N))))) ≫
          Q.hom.app (e₁.inverse.obj (e₁.functor.obj (p.obj N)))) ≫
        (qr.map (e₁.unitIso.inv.app (p.obj N)) ≫ QR.hom.app N) := by
  have hnat := e₂.unitIso.inv.naturality
    (q.map (e₁.unitIso.inv.app (p.obj N)) ≫ P.hom.app N)
  have hQ := Q.hom.naturality (e₁.unitIso.inv.app (p.obj N))
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at hnat hQ
  rw [← Functor.map_comp e₂.functor, ← Category.assoc, ← Functor.map_comp r, hnat,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcoc N,
    reassoc_of% hQ, Category.assoc]

/-- **Conjugating by equivalences preserves the associativity cocycle law.**  If three
composition comparisons satisfy the cocycle law, so do the comparisons of the functors
conjugated by equivalences. -/
theorem transportCompApp_assoc {p : A₀ ⥤ A₁} {q : A₁ ⥤ A₂} {r : A₂ ⥤ A₃} {pq : A₀ ⥤ A₂}
    {qr : A₁ ⥤ A₃} {pqr : A₀ ⥤ A₃} (P : p ⋙ q ≅ pq) (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr)
    (QR : p ⋙ qr ≅ pqr)
    (hcoc : ∀ N, r.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p.obj N) ≫ QR.hom.app N)
    (M : B₀) :
    (e₂.inverse ⋙ r ⋙ e₃.functor).map (transportCompApp e₀ e₁ e₂ P M) ≫
        transportCompApp e₀ e₂ e₃ PQ M =
      transportCompApp e₁ e₂ e₃ Q ((e₀.inverse ⋙ p ⋙ e₁.functor).obj M) ≫
        transportCompApp e₀ e₁ e₃ QR M := by
  have h := congrArg (fun x => e₃.functor.map x)
    (transportCompApp_assoc_aux e₁ e₂ P Q PQ QR hcoc (e₀.inverse.obj M))
  simp only [Functor.map_comp] at h
  simpa only [transportCompApp, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc] using h

end Equivalence

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W X Y Z : AlgebraicSpaces B S hS}

/-! ### The cocycle law on the spaces-étale sites -/

/-- The cocycle law for `CategoryTheory.Over.pullbackComp`, componentwise, in a category where
associativity of composition is definitional. -/
private theorem pullbackComp_hom_assoc_app (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) (U : Over Y) :
    (Over.pullbackComp (f ≫ g) h).hom.app U ≫
        (Over.pullbackComp f g).hom.app ((Over.pullback h).obj U) =
      (Over.pullbackComp f (g ≫ h)).hom.app U ≫
        (Over.pullback f).map ((Over.pullbackComp g h).hom.app U) := by
  have hcongr : (Over.pullbackCongr' (Category.assoc f g h)).hom = 𝟙 _ := by
    rw [Over.pullbackCongr']
    exact CategoryTheory.conjugateEquiv_id (Over.mapPullbackAdj (f ≫ g ≫ h))
  have key := Over.pullbackComp_assoc' f g h
  rw [hcongr, Category.id_comp] at key
  have hU := congrArg (fun τ => NatTrans.app τ U) key
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] using hU

/-- **Stacks 03G2, part (2), associativity.**  The base-change composition isomorphisms of the
spaces-étale sites obey the associativity cocycle law.  This is the cocycle law for
`CategoryTheory.Over.pullbackComp`, restricted to the objects étale over the base. -/
@[stacks 03G2 "part (2), associativity of the composition isomorphism"]
theorem spacesBaseChange_comp_inv_assoc (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y)
    (U : SpacesEtale B S hS Y) :
    (spacesBaseChange_comp B S hS (f ≫ g) h).inv.app U ≫
        (spacesBaseChange_comp B S hS f g).inv.app
          ((spacesBaseChange B S hS h).functor.obj U) =
      (spacesBaseChange_comp B S hS f (g ≫ h)).inv.app U ≫
        (spacesBaseChange B S hS f).functor.map
          ((spacesBaseChange_comp B S hS g h).inv.app U) := by
  refine ObjectProperty.hom_ext _ ?_
  simpa [spacesBaseChange_comp, spacesBaseChange, SpacesEtale.inclusion, IsEtaleOver] using
    pullbackComp_hom_assoc_app B S hS f g h ((SpacesEtale.inclusion B S hS Y).obj U)

/-- The cartesian composition isomorphisms of spaces-étale direct images obey the associativity
cocycle law. -/
theorem spacesBaseChange_pushforward_compTypeU_assoc (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y)
    (M : Sheaf (SpacesEtale.topology B S hS V) (Type u)) :
    ((spacesBaseChange B S hS h).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).map
        ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app M) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS (f ≫ g) h).hom.app M =
      (spacesBaseChange_pushforward_compTypeU B S hS g h).hom.app
          (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS W) (SpacesEtale.topology B S hS V)).obj M) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS f (g ≫ h)).hom.app M := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    spacesBaseChange_pushforward_compTypeU,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map]
  have hs := congrArg (fun q => M.obj.map q.op)
    (spacesBaseChange_comp_inv_assoc B S hS f g h U.unop)
  simp only [op_comp, Functor.map_comp] at hs
  exact hs

/-- **Stacks 03G2, part (3), associativity.**  The composition isomorphisms of the direct images
of the small étale topoi obey the associativity cocycle law. -/
@[stacks 03G2 "part (3), associativity of the composition isomorphism"]
theorem smallToposMorphismTypeU_comp_assoc (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y)
    (M : Sheaf (SmallEtale.topology B S hS V.1) (Type u)) :
    (smallToposMorphismTypeU B S hS h).pushforward.map
          ((smallToposMorphismTypeU_comp B S hS f g).hom.app M) ≫
        (smallToposMorphismTypeU_comp B S hS (f ≫ g) h).hom.app M =
      (smallToposMorphismTypeU_comp B S hS g h).hom.app
          ((smallToposMorphismTypeU B S hS f).pushforward.obj M) ≫
        (smallToposMorphismTypeU_comp B S hS f (g ≫ h)).hom.app M :=
  Equivalence.transportCompApp_assoc (smallEtaleToposEquivTypeU B S hS V)
    (smallEtaleToposEquivTypeU B S hS W) (smallEtaleToposEquivTypeU B S hS X)
    (smallEtaleToposEquivTypeU B S hS Y)
    (spacesBaseChange_pushforward_compTypeU B S hS f g)
    (spacesBaseChange_pushforward_compTypeU B S hS g h)
    (spacesBaseChange_pushforward_compTypeU B S hS (f ≫ g) h)
    (spacesBaseChange_pushforward_compTypeU B S hS f (g ≫ h))
    (spacesBaseChange_pushforward_compTypeU_assoc B S hS f g h) M

/-! ### The cocycle law for the direct image of modules -/

/-- The comparison of the direct images of modules of a composite, at the level of the
morphisms of ringed topoi of Stacks 03G8: the two factors of
`AlgebraicGeometry.Space.modulePushforwardCompIso` that are not transports along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`. -/
def pushforwardModulesCompAt (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS g).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModules :=
  (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫
    pushforwardModulesCompTransport B S hS f g

/-- The comparison of the direct images of modules at the level of morphisms of ringed topoi
obeys the associativity cocycle law.  On the underlying sheaves of sets the first factor is the
identity and the second is the comparison of Stacks 03G2, part (3), so this is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`. -/
theorem pushforwardModulesCompAt_assoc (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Modules.{u, u} B S hS W.1 W.2) :
    (smallEtaleRingedToposHom B S hS h).pushforwardModules.map
          ((pushforwardModulesCompAt B S hS f g).hom.app M) ≫
        (pushforwardModulesCompAt B S hS (f ≫ g) h).hom.app M =
      (pushforwardModulesCompAt B S hS g h).hom.app
          ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj M) ≫
        (pushforwardModulesCompAt B S hS f (g ≫ h)).hom.app M := by
  refine hom_ext_moduleSheafFunctor
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) ?_
  simp only [pushforwardModulesCompAt, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    pushforwardModulesCompTransport, RingedToposHom.pushforwardModulesIsoOfNatIso,
    NatIso.ofComponents_hom_app, RingedToposHom.pushforwardModulesIsoAppOfNatIso,
    RingedToposHom.pushforwardModulesCompIso, NatIso.ofComponents_inv_app,
    RingedToposHom.pushforwardModulesCompIsoApp]
  exact smallToposMorphismTypeU_comp_assoc B S hS f g h
    ((Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).obj M)

end AlgebraicGeometry.Space

end
