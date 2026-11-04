module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonTranspose

/-!
# The two composition cells for the pushforwards of Stacks 070R (2), identified

There are two composition 2-cells for pushforwards of modules: the one for the pushforwards of
*sheaves* of modules along the morphisms of ringed sites `ε` of Stacks 070R (2), and the one for
the pushforwards of *presheaves* of modules along the maps `a_{small}^♯` of Stacks 06WC. Both act
on sections as the same restriction map, and they agree up to the reindexings along
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`. As a
consequence, a composition law for the sheafified Stacks 06WC pullbacks holds as soon as the
corresponding law holds for the presheaf-level adjuncts.

## Main definitions

* `AlgebraicGeometry.Stack.structureMapRingAt`: the structure map of `ε_a`, with the type of the
  comparison map of Stacks 06WC.
* `AlgebraicGeometry.Stack.sheafPushforwardCompCellVal`: the composition cell for the
  pushforwards of sheaves of modules along `ε`, on underlying presheaves of modules.
* `AlgebraicGeometry.Stack.presheafPushforwardCompCellAt`: the composition cell for the
  pushforwards of presheaves of modules along the maps `a_{small}^♯`.

## Main results

* `AlgebraicGeometry.Stack.pushforwardCompCell_bridge`: the two composition cells agree, up to
  the reindexings of the pushforwards along the identification of `a_{small}^♯` with the
  structure map of `ε_a`.
* `AlgebraicGeometry.Stack.pushforwardCompCell_bridge_val`: the same identity with the
  sheaf-level cell written as the underlying morphism of presheaves of modules of the 2-cell.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparison_map_comp_of_presheafHomEquiv`: the
  composition law for the sheafified Stacks 06WC pullbacks, under the presheaf-level hypothesis.

## Implementation notes

The pushforwards are indexed at `AlgebraicGeometry.Stack.structureMapRingAt` throughout, with
each source and target spelled as the pushforwards applied one object at a time: the presheaves
of rings indexing the pushforwards along `ε` and along `a_{small}^♯` are definitionally but not
syntactically equal, and reconciling them on a composite of functors exhausts the heartbeat
limit. For the same reason `AlgebraicGeometry.Stack.pushforwardCompCell_bridge_val` is stated in a
section where `AlgebraicGeometry.smallEtaleBaseChange` and `CategoryTheory.Over.post` are locally
irreducible, and the instances of `Stacks.PresheafOfModules.pushforwardCell_bridge` and
`Stacks.CategoryTheory.paste_transposed_square` are elaborated before being matched against the
goal.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v v₁

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

/-- The structure map `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` of the morphism of
ringed sites `ε_a` of Stacks 070R (2), typed with the structure sheaves by which the comparison
map `a_{small}^♯` of Stacks 06WC is indexed. -/
public noncomputable abbrev structureMapRingAt :
    (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj ⟶
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)).hom

/-- The comparison map `a_{small}^♯` of Stacks 06WC is
`AlgebraicGeometry.Stack.structureMapRingAt`. -/
public theorem smallEtaleStructureComparison_eq_structureMapRingAt :
    smallEtaleStructureComparison B E h S hS p hp φ τ hτ = structureMapRingAt B E h S hS p φ :=
  smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp τ hτ φ

/-- The composition cell for the pushforwards of sheaves of modules along `ε`, at a sheaf of
modules `𝓜`, as a morphism of the underlying presheaves of modules: the comparison of the two
composite pushforwards followed by the reindexing
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso`. -/
public noncomputable abbrev sheafPushforwardCompCellVal
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))) :
    (PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p ψ)).obj
        ((PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p φ)).obj 𝓜.val) ⟶
      (PresheafOfModules.pushforward.{u}
        (structureMapRingAt B E h S hS p (φ ≫ ψ))).obj 𝓜.val :=
  (((SheafOfModules.pushforwardComp.{u}
          (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p ψ))
          (SmallEtale.smallEtaleStructureMapRing E
            (smallEtaleBaseMorphism B E h S hS p φ))).hom ≫
        (SmallEtale.smallEtalePushforwardFactoredCompIso E
          (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
          (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
          (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).inv).app 𝓜).val

/-- `AlgebraicGeometry.Stack.sheafPushforwardCompCellVal` on sections: restriction of the module
along the identification of the two successive base changes. -/
public theorem sheafPushforwardCompCellVal_app_apply
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (m : ((PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p ψ)).obj
      ((PresheafOfModules.pushforward.{u}
        (structureMapRingAt B E h S hS p φ)).obj 𝓜.val)).obj W) :
    (sheafPushforwardCompCellVal B E h S hS p φ ψ 𝓜).app W m =
      𝓜.val.map ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).inv.app W.unop).op m :=
  sheafPushforwardCompCell_val_app_apply B E h S hS p φ ψ 𝓜 W m

/-- The composition cell for the pushforwards of presheaves of modules along the maps
`a_{small}^♯` of Stacks 06WC, at the underlying presheaf of modules of a sheaf of modules `𝓜`. -/
public noncomputable def presheafPushforwardCompCellAt
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))) :
    (PresheafOfModules.pushforward.{u}
          (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj
        ((PresheafOfModules.pushforward.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj 𝓜.val) ⟶
      (PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).obj 𝓜.val :=
  ((PresheafOfModules.pushforwardComp.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
      (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv).app 𝓜.val

/-- `AlgebraicGeometry.Stack.presheafPushforwardCompCellAt` is the comparison of the two composite
pushforwards followed by the inverse of
`AlgebraicGeometry.Stack.smallEtalePushforwardComparisonCompIso`. -/
public theorem presheafPushforwardCompCellAt_eq
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))) :
    presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ 𝓜 =
      ((PresheafOfModules.pushforwardComp.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
          (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv).app 𝓜.val :=
  rfl

/-- `AlgebraicGeometry.Stack.presheafPushforwardCompCellAt` on sections: the same restriction map
as `AlgebraicGeometry.Stack.sheafPushforwardCompCellVal`. -/
public theorem presheafPushforwardCompCellAt_app_apply
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (m : ((PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj
      ((PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj 𝓜.val)).obj W) :
    (presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ 𝓜).app W m =
      𝓜.val.map ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).inv.app W.unop).op m :=
  presheafPushforwardCompCell_app_apply B E h S hS p hp τ hτ φ ψ 𝓜.val W m

/-- The two composition cells for the pushforwards agree, up to the reindexings along
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_structureMapRingAt`. -/
public theorem pushforwardCompCell_bridge
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))) :
    (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
            (smallEtaleStructureComparison_eq_structureMapRingAt
              B E h S hS p hp τ hτ ψ))).hom.app
          ((PresheafOfModules.pushforward.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj 𝓜.val) ≫
        (PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p ψ)).map
            ((eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
              (smallEtaleStructureComparison_eq_structureMapRingAt
                B E h S hS p hp τ hτ φ))).hom.app 𝓜.val) ≫
          sheafPushforwardCompCellVal B E h S hS p φ ψ 𝓜 =
      presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ 𝓜 ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_structureMapRingAt
            B E h S hS p hp τ hτ (φ ≫ ψ)))).hom.app 𝓜.val := by
  have key := Stacks.PresheafOfModules.pushforwardCell_bridge
    (smallEtaleStructureComparison_eq_structureMapRingAt B E h S hS p hp τ hτ φ)
    (smallEtaleStructureComparison_eq_structureMapRingAt B E h S hS p hp τ hτ ψ)
    (smallEtaleStructureComparison_eq_structureMapRingAt B E h S hS p hp τ hτ (φ ≫ ψ))
    𝓜.val (sheafPushforwardCompCellVal B E h S hS p φ ψ 𝓜)
    (presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ 𝓜)
    (fun W m =>
      (sheafPushforwardCompCellVal_app_apply B E h S hS p φ ψ 𝓜 W m).trans
        (presheafPushforwardCompCellAt_app_apply B E h S hS p hp τ hτ φ ψ 𝓜 W m).symm)
  exact key

/-- The underlying morphism of presheaves of modules of the pushforward of `g` along `ε_b` is the
pushforward of `g.val` along `AlgebraicGeometry.Stack.structureMapRingAt`. -/
public theorem pushforward_map_val_at
    (N P : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y))) (g : N ⟶ P) :
    ((SheafOfModules.pushforward.{u}
        (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p ψ))).map g).val =
      (PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p ψ)).map g.val :=
  rfl

/-- `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val`, with the
reindexing of the pushforward along `AlgebraicGeometry.Stack.structureMapRingAt`. -/
public theorem sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val_at
    (M : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y)))
    (G : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (w : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj M.val ⟶ G.val) :
    ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ).homEquiv M G
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _ G).symm w)).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv M.val G.val w ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_structureMapRingAt
            B E h S hS p hp τ hτ φ))).hom.app G.val :=
  sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val B E h S hS p hp τ hτ φ M G w

section BridgeVal

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post

/-- `AlgebraicGeometry.Stack.pushforwardCompCell_bridge` with the sheaf-level cell written as the
underlying morphism of presheaves of modules of the 2-cell itself. -/
public theorem pushforwardCompCell_bridge_val
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))) :
    (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
            (smallEtaleStructureComparison_eq_structureMapRingAt
              B E h S hS p hp τ hτ ψ))).hom.app
          ((PresheafOfModules.pushforward.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj 𝓜.val) ≫
        (PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p ψ)).map
            ((eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
              (smallEtaleStructureComparison_eq_structureMapRingAt
                B E h S hS p hp τ hτ φ))).hom.app 𝓜.val) ≫
          (((SheafOfModules.pushforwardComp.{u}
                  (SmallEtale.smallEtaleStructureMapRing E
                    (smallEtaleBaseMorphism B E h S hS p ψ))
                  (SmallEtale.smallEtaleStructureMapRing E
                    (smallEtaleBaseMorphism B E h S hS p φ))).hom ≫
                (SmallEtale.smallEtalePushforwardFactoredCompIso E
                  (smallEtaleBaseMorphism B E h S hS p φ)
                  (smallEtaleBaseMorphism B E h S hS p ψ)
                  (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
                  (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).inv).app 𝓜).val =
      presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ 𝓜 ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_structureMapRingAt
            B E h S hS p hp τ hτ (φ ≫ ψ)))).hom.app 𝓜.val :=
  pushforwardCompCell_bridge B E h S hS p hp τ hτ φ ψ 𝓜

end BridgeVal

/-- A composition law for the sheafified Stacks 06WC pullbacks: if the presheaf-level adjuncts of
`uψ`, `uφ` and `u` satisfy the composition law through
`AlgebraicGeometry.Stack.presheafPushforwardCompCellAt`, then the sheafifications of `uψ` and `uφ`
compose, through `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso`, to the
sheafification of `u`. -/
public theorem sheafifiedPullbackComparison_map_comp_of_presheafHomEquiv
    {𝒩 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z))}
    {𝒩' : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y))}
    {𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))}
    (uψ : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj 𝒩.val ⟶ 𝒩'.val)
    (uφ : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj 𝒩'.val ⟶ 𝓜.val)
    (u : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).obj 𝒩.val ⟶ 𝓜.val)
    (hadj : ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).homEquiv 𝒩.val 𝒩'.val uψ ≫
          (PresheafOfModules.pushforward.{u}
              (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map
            ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv
                𝒩'.val 𝓜.val uφ)) ≫
        presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ 𝓜 =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).homEquiv
        𝒩.val 𝓜.val u) :
    (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (SmallEtale.structureSheaf E (p.obj y).left.1
              (contains_base B E h S hS p y)).obj)).homEquiv _ 𝒩').symm uψ) ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _ 𝓜).symm uφ =
      (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).hom.app 𝒩 ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _ 𝓜).symm u := by
  refine sheafifiedPullbackComparison_map_comp_of_homEquiv B E h S hS p hp τ hτ φ ψ _ _ _ ?_
  refine SheafOfModules.hom_ext ?_
  have hp' := sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val_at
    B E h S hS p hp τ hτ ψ 𝒩 𝒩' uψ
  have hr := sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val_at
    B E h S hS p hp τ hτ (φ ≫ ψ) 𝒩 𝓜 u
  have hq := (pushforward_map_val_at B E h S hS p ψ 𝒩'
      ((SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ))).obj 𝓜)
      ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ).homEquiv 𝒩' 𝓜
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _ 𝓜).symm uφ))).trans
    ((congrArg (PresheafOfModules.pushforward.{u} (structureMapRingAt B E h S hS p ψ)).map
        (sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val_at
          B E h S hS p hp τ hτ φ 𝒩' 𝓜 uφ)).trans
      (Functor.map_comp _ _ _))
  have hn := (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
      (smallEtaleStructureComparison_eq_structureMapRingAt
        B E h S hS p hp τ hτ ψ))).hom.naturality
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv 𝒩'.val 𝓜.val uφ)
  have hb := pushforwardCompCell_bridge_val B E h S hS p hp τ hτ φ ψ 𝓜
  have key := Stacks.CategoryTheory.paste_transposed_square _ _ _ _ _ _ _ _ _ _ _ _ _
    hp' hq hr hn.symm hb hadj
  exact key

end AlgebraicGeometry.Stack

end
