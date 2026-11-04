module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian modules on the total Zariski site of a simplicial scheme

Let `X` be a simplicial scheme and `F` a sheaf of `𝒪_X`-modules on its total Zariski site. For a
map of simplicial degrees `φ : n ⟶ m` the scheme morphism `X φ : X_n ⟶ X_m` carries the
degree-`m` component `F_m` to a module on `X_n`, and the restriction maps of `F` along the
morphisms of the total site lying over `φ` assemble into a canonical transition
`(X φ)^* F_m ⟶ F_n`. Stacks 07TF (2) calls `F` *cartesian* when every one of these transitions
is an isomorphism.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.componentModuleDirectTransition`: the direct form
  `F_m ⟶ (X φ)_* F_n` of the transition, as a natural transformation of functors on `Modules X`.
* `AlgebraicGeometry.SimplicialScheme.componentModuleTransition`: its mate
  `(X φ)^* F_m ⟶ F_n` under the adjunction `(X φ)^* ⊣ (X φ)_*` of modules on schemes.
* `AlgebraicGeometry.SimplicialScheme.IsCartesianModule`: **Stacks 07TF (2) for the total Zariski
  site of a simplicial scheme.**

## Main results

* `AlgebraicGeometry.SimplicialScheme.transitionStructureHom_eq`: the structure map produced by
  the comparison of the degree-`m` and degree-`n` restrictions is the structure map of the
  composite `(X φ)_* ∘ (-)_n`, so that the two readings of the target of the transition agree.
* `AlgebraicGeometry.SimplicialScheme.componentModuleDirectTransition_app_val_app`: on sections
  over an open `V` of `X_m` the direct transition is the restriction map of `F` along the
  morphism `(n, (X φ)⁻¹V) ⟶ (m, V)` of the total site lying over `φ`.

## Implementation notes

The degree-`n` component `F_n` is restriction along the level inclusion
`levelFunctor (zariskiSpace X) n`, and the composite `(X φ)_* ∘ (-)_n` is restriction along
`Opens.map (X φ) ⋙ levelFunctor (zariskiSpace X) n`, which is `transitionLevelFunctor` below.
The arrows `(n, (X φ)⁻¹V) ⟶ (m, V)` of the total site are natural in `V`, giving
`transitionLevelNatTrans`, and Mathlib's `SheafOfModules.pushforwardNatTrans` turns that natural
transformation of continuous site functors into the direct transition. The one thing that has to
be checked is that the structure map `pushforwardNatTrans` produces — the degree-`m` component of
`𝒪_X`, followed by restriction of `𝒪_X` along the arrows over `φ` — is the structure map of the
composite pushforward, namely `(X φ)^♯` followed by the degree-`n` component of `𝒪_X`. That is
`transitionStructureHom_eq`; both component identifications are identities on sections, and the
remaining content is `Scheme.Hom.appLE_eq_app` for the restriction along `φ` over the inverse
image of `V`.

Two separate difficulties of bookkeeping are worth recording, because both present as
instance-resolution failures with no mathematical content.

First, the site of a simplicial degree is spelled two ways: `Opens ((zariskiSpace X).obj k)`
through the underlying simplicial space, and `Opens ↥(X.obj k)` through the scheme, which is what
`AlgebraicGeometry.Scheme.Modules` uses. The two are definitionally equal but not syntactically,
so a continuity instance stated through one spelling is not found for a goal stated through the
other. The instances are therefore provided in both spellings, and the topologies are passed
explicitly to `SheafOfModules.pushforwardNatTrans` and `SheafOfModules.pushforwardCongr`.

Providing the second spelling takes more than writing the topology in it. `Functor.IsContinuous`
takes the two site *categories* as arguments before the two topologies, and if only the topology
is written through the scheme then the category argument is still inferred from the functor,
giving `Opens ((zariskiSpace X).obj k)`: the instance is then keyed on that category and is never
tried against a goal whose category is `Opens ↥(X.obj k)`, because reaching one spelling from the
other unfolds `Scheme.forgetToTop`, which instance search does not do. Such an instance is
correctly stated, provable by `exact`, and dead to `infer_instance` — which is how every bare
mention of `SheafOfModules.unitToPushforwardObjUnit` at the degree-`k` site used to fail to
elaborate. The category arguments are therefore written out too, in
`levelFunctor_isContinuous_opens` and `transitionLevelFunctor_isContinuous_opens`.

Second, even with those instances in scope the continuity hypotheses of
`SheafOfModules.pushforwardComp` are not synthesized, because at the point where they are
attempted the functors they speak about are still being unified against the expected type. They
are supplied as local instances in the body of `componentModuleDirectTransition` instead.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {n m : SimplexCategoryᵒᵖ}

/-- The site functor of the composite `(X φ)_* ∘ (-)_n`: it sends an open `V` of `X_m` to the
object `(n, (X φ)⁻¹V)` of the total Zariski site. -/
public def transitionLevelFunctor (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m) :
    Opens ((zariskiSpace X).obj m) ⥤ ZariskiOpen X :=
  Opens.map ((zariskiSpace X).map φ) ⋙ levelFunctor (zariskiSpace X) n

/-- The site functor `transitionLevelFunctor X φ` is continuous. -/
public instance transitionLevelFunctor_isContinuous (X : SimplicialObject Scheme.{u})
    (φ : n ⟶ m) :
    (transitionLevelFunctor X φ).IsContinuous
      (Opens.grothendieckTopology ((zariskiSpace X).obj m)) (zariskiTopology X) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ((zariskiSpace X).obj n)) _

/-- The inclusion of one simplicial degree into the total Zariski site is continuous, in the
spelling of the degree site that goes through the scheme. -/
public instance levelFunctor_isContinuous_opens (X : SimplicialObject Scheme.{u})
    (k : SimplexCategoryᵒᵖ) :
    @Functor.IsContinuous (Opens ↥(X.obj k)) _ (ZariskiOpen X) _
      (levelFunctor (zariskiSpace X) k)
      (Opens.grothendieckTopology ↥(X.obj k)) (zariskiTopology X) :=
  levelFunctor_isContinuous (zariskiSpace X) k

/-- The site functor `transitionLevelFunctor X φ` is continuous, in the spelling of the degree site
that goes through the scheme. -/
public instance transitionLevelFunctor_isContinuous_opens (X : SimplicialObject Scheme.{u})
    (φ : n ⟶ m) :
    @Functor.IsContinuous (Opens ↥(X.obj m)) _ (ZariskiOpen X) _
      (transitionLevelFunctor X φ)
      (Opens.grothendieckTopology ↥(X.obj m)) (zariskiTopology X) :=
  transitionLevelFunctor_isContinuous X φ

/-- Pulling back opens along the transition map `X φ : X_n ⟶ X_m` is continuous for the open-set
sites. -/
public instance opensMap_base_isContinuous (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m) :
    (Opens.map (X.map φ).base).IsContinuous
      (Opens.grothendieckTopology ((zariskiSpace X).obj m))
      (Opens.grothendieckTopology ((zariskiSpace X).obj n)) :=
  inferInstanceAs ((Opens.map ((zariskiSpace X).map φ)).IsContinuous
    (Opens.grothendieckTopology ((zariskiSpace X).obj m))
    (Opens.grothendieckTopology ((zariskiSpace X).obj n)))

/-- The arrows `(n, (X φ)⁻¹V) ⟶ (m, V)` of the total Zariski site lying over `φ`, natural in the
open `V` of `X_m`. -/
public def transitionLevelNatTrans (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m) :
    transitionLevelFunctor X φ ⟶ levelFunctor (zariskiSpace X) m where
  app V := SimplicialSheafSystem.transitionHom φ V
  naturality _ _ _ := by
    apply SimplicialOpen.Hom.ext
    change (𝟙 n) ≫ φ = φ ≫ (𝟙 m)
    simp

/-- The structure map of the composite pushforward `(X φ)_* ∘ (-)_n`: the structure map `(X φ)^♯`
of the scheme morphism followed by the identification of the degree-`n` component of `𝒪_X` with
the structure sheaf of `X_n`. -/
public noncomputable def transitionStructureHom (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m) :
    (X.obj m).ringCatSheaf ⟶
      ((transitionLevelFunctor X φ).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ((zariskiSpace X).obj m)) (zariskiTopology X)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O) :=
  (X.map φ).toRingCatSheafHom ≫
    ((Opens.map ((zariskiSpace X).map φ)).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ((zariskiSpace X).obj m))
      (Opens.grothendieckTopology ((zariskiSpace X).obj n))).map (componentStructureHom X n)

/-- Restriction of `𝒪_X` along the arrows of the total Zariski site lying over `φ`, as a
morphism of the two restrictions of `𝒪_X` to the site of degree `m`. -/
public noncomputable def transitionRingNatTrans (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m) :
    ((levelFunctor (zariskiSpace X) m).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ((zariskiSpace X).obj m)) (zariskiTopology X)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O) ⟶
      ((transitionLevelFunctor X φ).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ((zariskiSpace X).obj m)) (zariskiTopology X)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O) :=
  (Functor.sheafPushforwardContinuousNatTrans (transitionLevelNatTrans X φ) RingCat.{u}
      (Opens.grothendieckTopology ((zariskiSpace X).obj m)) (zariskiTopology X)).app
    (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O)

/-- The identification of the degree-`k` component of `𝒪_X` with the structure sheaf of `X_k` is
the identity on sections over every open of `X_k`. -/
public theorem componentStructureHom_app_eq (X : SimplicialObject Scheme.{u})
    (k : SimplexCategoryᵒᵖ) (V : (Opens ((zariskiSpace X).obj k))ᵒᵖ) :
    (componentStructureHom X k).hom.app V = 𝟙 _ :=
  (forget₂ CommRingCat RingCat.{u}).map_id _

/-- On sections over an open `V` of `X_m`, restriction of `𝒪_X` along the arrows over `φ` is the
restriction map of the presheaf of section rings. -/
public theorem transitionRingNatTrans_app (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m)
    (V : (Opens ((zariskiSpace X).obj m))ᵒᵖ) :
    (transitionRingNatTrans X φ).hom.app V =
      (forget₂ CommRingCat RingCat.{u}).map
        ((structurePresheaf X).map (SimplicialSheafSystem.transitionHom φ V.unop).op) :=
  rfl

/-- On sections over an open `V` of `X_m`, the structure map of `X φ` as a morphism of sheaves of
rings is the map `X φ` induces on sections over `V`. -/
public theorem toRingCatSheafHom_app (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m)
    (V : (Opens ((zariskiSpace X).obj m))ᵒᵖ) :
    ((X.map φ).toRingCatSheafHom).hom.app V =
      (forget₂ CommRingCat RingCat.{u}).map ((X.map φ).c.app V) :=
  rfl

/-- The structure map that the comparison of the degree-`m` and degree-`n` restrictions produces
is the structure map of the composite pushforward `(X φ)_* ∘ (-)_n`. -/
public theorem transitionStructureHom_eq (X : SimplicialObject Scheme.{u}) (φ : n ⟶ m) :
    componentStructureHom X m ≫ transitionRingNatTrans X φ = transitionStructureHom X φ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  change (componentStructureHom X m).hom.app V ≫ (transitionRingNatTrans X φ).hom.app V =
    ((X.map φ).toRingCatSheafHom).hom.app V ≫ (componentStructureHom X n).hom.app _
  rw [componentStructureHom_app_eq, componentStructureHom_app_eq, transitionRingNatTrans_app,
    toRingCatSheafHom_app]
  erw [Category.id_comp, Category.comp_id]
  exact congrArg ((forget₂ CommRingCat RingCat.{u}).map)
    (Scheme.Hom.appLE_eq_app (X.map φ) (U := V.unop))

/-- **The direct form of the transition of Stacks 09WF for the total Zariski site.** For a map of
simplicial degrees `φ : n ⟶ m` the restriction maps of a sheaf of `𝒪_X`-modules along the arrows
of the total site lying over `φ` give a morphism `F_m ⟶ (X φ)_* F_n`, natural in `F`. -/
public noncomputable def componentModuleDirectTransition (X : SimplicialObject Scheme.{u})
    (φ : n ⟶ m) :
    componentModule X m ⟶ componentModule X n ⋙ Scheme.Modules.pushforward (X.map φ) := by
  have : (levelFunctor (zariskiSpace X) n).IsContinuous
      (Opens.grothendieckTopology ↥(X.obj n)) (zariskiTopology X) :=
    levelFunctor_isContinuous (zariskiSpace X) n
  have : (Opens.map (X.map φ).base).IsContinuous
      (Opens.grothendieckTopology ↥(X.obj m)) (Opens.grothendieckTopology ↥(X.obj n)) :=
    inferInstanceAs ((Opens.map ((zariskiSpace X).map φ)).IsContinuous
      (Opens.grothendieckTopology ((zariskiSpace X).obj m))
      (Opens.grothendieckTopology ((zariskiSpace X).obj n)))
  exact SheafOfModules.pushforwardNatTrans.{u}
      (J := Opens.grothendieckTopology ((zariskiSpace X).obj m)) (K := zariskiTopology X)
      (componentStructureHom X m) (transitionLevelNatTrans X φ) ≫
    (SheafOfModules.pushforwardCongr.{u}
        (J := Opens.grothendieckTopology ((zariskiSpace X).obj m)) (K := zariskiTopology X)
        (transitionStructureHom_eq X φ)).hom ≫
      (SheafOfModules.pushforwardComp (K' := zariskiTopology X)
        (X.map φ).toRingCatSheafHom (componentStructureHom X n)).inv

/-- On sections over an open `V` of `X_m` the direct transition is the restriction map of `F`
along the morphism `(n, (X φ)⁻¹V) ⟶ (m, V)` of the total Zariski site lying over `φ`. -/
public theorem componentModuleDirectTransition_app_val_app (X : SimplicialObject Scheme.{u})
    (φ : n ⟶ m) (F : Modules X) (V : (Opens ((zariskiSpace X).obj m))ᵒᵖ)
    (x : ((componentModule X m).obj F).val.obj V) :
    (((componentModuleDirectTransition X φ).app F).val.app V) x =
      F.val.map (SimplicialSheafSystem.transitionHom φ V.unop).op x :=
  rfl

/-- **Stacks 09WF for the total Zariski site of a simplicial scheme.** The transition
`(X φ)^* F_m ⟶ F_n` attached to a map of simplicial degrees `φ : n ⟶ m`: the mate of the direct
transition under the adjunction `(X φ)^* ⊣ (X φ)_*` of sheaves of modules on schemes. -/
public noncomputable def componentModuleTransition (X : SimplicialObject Scheme.{u})
    (φ : n ⟶ m) (F : Modules X) :
    (Scheme.Modules.pullback (X.map φ)).obj ((componentModule X m).obj F) ⟶
      (componentModule X n).obj F :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ)).homEquiv _ _).symm
    ((componentModuleDirectTransition X φ).app F)

/-- **Stacks 07TF (2) for the total Zariski site of a simplicial scheme.** A sheaf of
`𝒪_X`-modules on the total Zariski site of a simplicial scheme `X` is *cartesian* when every
transition `(X φ)^* F_m ⟶ F_n` is an isomorphism. -/
@[stacks 07TF "part (2), for the total Zariski site of a simplicial scheme (the site of 09VL, \
which this development does not carry as a term of Situation 09WE), with the component modules \
of `ZariskiModulePushforward` and the transition of 09WF constructed here"]
public def IsCartesianModule (X : SimplicialObject Scheme.{u}) (F : Modules X) : Prop :=
  ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (φ : n ⟶ m), IsIso (componentModuleTransition X φ F)

end AlgebraicGeometry.SimplicialScheme

end
