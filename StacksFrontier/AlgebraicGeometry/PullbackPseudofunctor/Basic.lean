module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Pseudofunctoriality of the ringed-space module pullback

For morphisms of ringed spaces `f : X' ⟶ X` and `f' : X'' ⟶ X'` this file builds the
canonical isomorphism of functors

`modulePullback (f' ≫ f) ≅ modulePullback f ⋙ modulePullback f'`,

that is `(f' ≫ f)^* ≅ f'^* ∘ f^*` (written in diagrammatic order, so `modulePullback f` is
applied first), and identifies its components with the comparison *map*
`Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison` already in the tree.
In particular that map is an isomorphism.

## Main results

* `Stacks.PullbackPseudofunctor.modulePushforward_comp`: the pushforward functors compose on
  the nose, `modulePushforward f' ⋙ modulePushforward f = modulePushforward (f' ≫ f)`.
* `Stacks.PullbackPseudofunctor.modulePushforward_id` and
  `Stacks.PullbackPseudofunctor.modulePullbackIdIso`: pushforward along an identity is the
  identity functor on the nose, and so pullback along an identity is isomorphic to it; with
  `homEquiv_modulePullbackIdIso_hom_app`,
  `unit_comp_map_modulePullbackIdIso_hom_app` and
  `modulePullbackIdIso_hom_app_comp_counit` for its adjoint equations.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso`: the isomorphism.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app`: its components are exactly
  `modulePullbackComparison`.
* `Stacks.PullbackPseudofunctor.isIso_modulePullbackComparison`: hence that map is an
  isomorphism. This is the fact the consumers want.
* `Stacks.PullbackPseudofunctor.homEquiv_modulePullbackCompIso_hom_app`,
  `unit_comp_map_modulePullbackCompIso_hom_app`,
  `modulePullbackCompIso_hom_app_comp_counit`: the compatibility of the isomorphism with the
  units and counits of the two adjunctions. These are the usable equations.
* `Stacks.PullbackPseudofunctor.modulePullbackComparison_naturality` and
  `modulePullbackComparison_unique`: naturality in the module, and the characterization of
  the comparison map by its adjoint description, so that any map with that description is
  it.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso_eq_pullbackComp_symm`: the
  isomorphism is Mathlib's `SheafOfModules.pullbackComp` for the two structure-sheaf
  morphisms, so Mathlib's associativity coherence `SheafOfModules.pullback_assoc` applies to
  it verbatim.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso_assoc`: the associativity coherence of
  the pseudofunctor structure, in component form.

## Route

`modulePullback f` is the left adjoint of `modulePushforward f`
(`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`). The composite of the
two adjunctions is therefore an adjunction

`modulePullback f ⋙ modulePullback f' ⊣ modulePushforward f' ⋙ modulePushforward f`,

and the right-hand side is *definitionally* `modulePushforward (f' ≫ f)`: unwinding
`RingedSpaceModuleAdjunction.modulePushforward`, this is Mathlib's
`SheafOfModules.pushforwardComp`, which is `Iso.refl _`, composed with the two facts
`opensMap (f' ≫ f) = opensMap f ⋙ opensMap f'` and
`structureSheafHom (f' ≫ f) = structureSheafHom f ≫ _ (structureSheafHom f')`, both of which
hold by `rfl` here (`modulePushforward_comp` records the composite statement). So the two
functors `modulePullback (f' ≫ f)` and `modulePullback f ⋙ modulePullback f'` are left
adjoints of *the same* functor, and `CategoryTheory.Adjunction.leftAdjointUniq` identifies
them. Mathlib's `Adjunction.homEquiv_leftAdjointUniq_hom_app` then says the components
correspond, under the adjunction for `f' ≫ f`, to the unit of the composite adjunction,
which by `Adjunction.comp_unit_app` is the composite of units that
`modulePullbackComparison` was defined to be adjoint to.

## What is not done

* No universe generality beyond `RingedSpace.{u, u}`: everything here inherits the
  restriction of `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`, which is forced
  by Mathlib's `PresheafOfModules.instIsRightAdjointPushforward`.
* **The unitality of the composition isomorphism is not proved.** `modulePullbackIdIso`
  identifies `modulePullback (𝟙 X)` with the identity functor, but there is no statement
  that `modulePullbackCompIso (𝟙 X') f'` becomes the identity once the two sides are
  transported along `f' ≫ 𝟙 X' = f'` and along `modulePullbackIdIso`. That transported
  statement is the one a consumer needs in order to normalize a composition isomorphism at a
  factor which is only *provably*, not definitionally, an identity — for instance at
  `AlgebraicGeometry.Scheme.homOfLE (le_refl U)`, which is provably but not definitionally
  `𝟙 U.toScheme`.
* The associativity coherence is stated only in component form
  (`modulePullbackCompIso_assoc`), not as an equality of composites of natural isomorphisms;
  the latter is `SheafOfModules.pullback_assoc` read through
  `modulePullbackCompIso_eq_pullbackComp_symm`.
* No bridge to the other ringed-space spelling.
  `StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors`
  independently builds `pullbackComp` and `pushforwardComp` (tagged `0097`) for its own
  functors `pullback`/`pushforward` over `ringCatSheaf`, by the same `leftAdjointUniq`
  route; and `StacksDraft.Ch17.Sec14.Tag01C8` builds `RS.Modules.pullback_comp_iso` for a
  third set of names. Nothing here relates those to `modulePullback` over `structureSheafRing`.
  They are not interchangeable as written: they are stated for `RingedSpace.{u}` rather than
  `RingedSpace.{u, u}`, and `ModuleFunctors` needs its own
  `toRingCatSheafHom_comp` (proved by `ext`), where the corresponding identification for
  `structureSheafHom` holds here by `rfl`.
* Nothing here is about schemes. The statements are for morphisms of ringed spaces; a
  consumer working with `Scheme.Hom` must pass through `Scheme.Hom.toLRSHom.toShHom` itself.
* No statement about sections: this file does not describe
  `(modulePullbackCompIso f f').hom.app M` on local sections of the two pullbacks. The
  pullback of sheaves of modules is a sheafification of a tensor product, so there is no
  elementwise description of its sections to state one against; the adjoint equations above
  are the available characterization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Functor
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.PullbackPseudofunctor

variable {X X' X'' : RingedSpace.{u, u}}

/-- Pushforward of sheaves of modules along a composite of morphisms of ringed spaces is the
composite of the pushforwards, on the nose. Both functors send a sheaf `F` of
`𝒪_{X''}`-modules to `V ↦ F (f'⁻¹ (f⁻¹ V))` with its `𝒪_X`-module structure restricted along
the composite of the two structure-sheaf morphisms; Mathlib's
`SheafOfModules.pushforwardComp` is `Iso.refl _`, and the two remaining identifications
(`opensMap (f' ≫ f) = opensMap f ⋙ opensMap f'` on sites and
`structureSheafHom (f' ≫ f) = structureSheafHom f ≫ _ (structureSheafHom f')` on structure
sheaves) hold definitionally for a composite of morphisms of ringed spaces. -/
theorem modulePushforward_comp (f : X' ⟶ X) (f' : X'' ⟶ X') :
    modulePushforward f' ⋙ modulePushforward f = modulePushforward (f' ≫ f) :=
  rfl

/-- Pushforward along an identity morphism of ringed spaces is the identity functor, on the
nose. Here the site functor `opensMap (𝟙 X)` is `𝟭 (Opens X)` and the structure-sheaf
morphism `structureSheafHom (𝟙 X)` is `𝟙 (structureSheafRing X)`, both definitionally. -/
theorem modulePushforward_id (X : RingedSpace.{u, u}) :
    modulePushforward (𝟙 X) = 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
  rfl

/-- The identity adjunction, with both functors read as the pullback and pushforward along
`𝟙 X` using `modulePushforward_id`. Naming this fixes the two type identifications once;
elaborating them repeatedly is expensive. -/
noncomputable def idAdjunction (X : RingedSpace.{u, u}) :
    𝟭 (SheafOfModules.{u} (structureSheafRing X)) ⊣ modulePushforward (𝟙 X) :=
  Adjunction.id

/-- **The module pullback along an identity is the identity.** Both `modulePullback (𝟙 X)`
and the identity functor are left adjoints of `modulePushforward (𝟙 X)`, which is the
identity functor by `modulePushforward_id`. -/
noncomputable def modulePullbackIdIso (X : RingedSpace.{u, u}) :
    modulePullback (𝟙 X) ≅ 𝟭 (SheafOfModules.{u} (structureSheafRing X)) :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (𝟙 X)) (idAdjunction X)

/-- The adjoint description of `modulePullbackIdIso`: its components transpose to the unit of
the identity adjunction, which is the identity. -/
theorem homEquiv_modulePullbackIdIso_hom_app (X : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (𝟙 X)).homEquiv M M
        ((modulePullbackIdIso X).hom.app M) = (idAdjunction X).unit.app M :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ (idAdjunction X) M

/-- Compatibility of `modulePullbackIdIso` with the units. -/
theorem unit_comp_map_modulePullbackIdIso_hom_app (X : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
        (modulePushforward (𝟙 X)).map ((modulePullbackIdIso X).hom.app M) =
      (idAdjunction X).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ (idAdjunction X) M

/-- Compatibility of `modulePullbackIdIso` with the counits. -/
theorem modulePullbackIdIso_hom_app_comp_counit (X : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackIdIso X).hom.app ((modulePushforward (𝟙 X)).obj M) ≫
        (idAdjunction X).counit.app M =
      (modulePullbackPushforwardAdjunction (𝟙 X)).counit.app M :=
  Adjunction.leftAdjointUniq_hom_app_counit _ (idAdjunction X) M

/-- The composite of the adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*`, with its right adjoint
read as `(f' ≫ f)_*` using `modulePushforward_comp`. -/
noncomputable def compAdjunction (f : X' ⟶ X) (f' : X'' ⟶ X') :
    modulePullback f ⋙ modulePullback f' ⊣ modulePushforward (f' ≫ f) :=
  (modulePullbackPushforwardAdjunction f).comp (modulePullbackPushforwardAdjunction f')

/-- The unit of `compAdjunction` is the composite of the two units. -/
theorem compAdjunction_unit_app (f : X' ⟶ X) (f' : X'' ⟶ X')
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (compAdjunction f f').unit.app M =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M)) :=
  Adjunction.comp_unit_app _ _ M

/-- The counit of `compAdjunction` is built from the two counits. -/
theorem compAdjunction_counit_app (f : X' ⟶ X) (f' : X'' ⟶ X')
    (N : SheafOfModules.{u} (structureSheafRing X'')) :
    (compAdjunction f f').counit.app N =
      (modulePullback f').map
          ((modulePullbackPushforwardAdjunction f).counit.app
            ((modulePushforward f').obj N)) ≫
        (modulePullbackPushforwardAdjunction f').counit.app N :=
  Adjunction.comp_counit_app _ _ N

/-- **Pseudofunctoriality of the module pullback.** The canonical isomorphism
`(f' ≫ f)^* ≅ f'^* ∘ f^*` of functors `Mod(𝒪_X) ⥤ Mod(𝒪_{X''})`. Both sides are left
adjoints of `(f' ≫ f)_*`, the left-hand side by
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` and the right-hand side by
`compAdjunction`; the isomorphism is the uniqueness of a left adjoint. -/
noncomputable def modulePullbackCompIso (f : X' ⟶ X) (f' : X'' ⟶ X') :
    modulePullback (f' ≫ f) ≅ modulePullback f ⋙ modulePullback f' :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (f' ≫ f))
    (compAdjunction f f')

section Equations

variable (f : X' ⟶ X) (f' : X'' ⟶ X') (M : SheafOfModules.{u} (structureSheafRing X))

/-- The adjoint description of `modulePullbackCompIso`: under the hom-set bijection of
`f^* ⊣ f_*` for the composite `f' ≫ f`, the component of the isomorphism at `M` is the
composite of the two units. -/
theorem homEquiv_modulePullbackCompIso_hom_app :
    (modulePullbackPushforwardAdjunction (f' ≫ f)).homEquiv M
        ((modulePullback f').obj ((modulePullback f).obj M))
        ((modulePullbackCompIso f f').hom.app M) =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M)) :=
  (Adjunction.homEquiv_leftAdjointUniq_hom_app _ (compAdjunction f f') M).trans
    (compAdjunction_unit_app f f' M)

/-- A map out of `(f' ≫ f)^* M` is the comparison map as soon as its adjoint description is the
composite of the two units. -/
private theorem eq_modulePullbackComparison_of_homEquiv
    (c : (modulePullback (f' ≫ f)).obj M ⟶
      (modulePullback f').obj ((modulePullback f).obj M))
    (hc : (modulePullbackPushforwardAdjunction (f' ≫ f)).homEquiv M
        ((modulePullback f').obj ((modulePullback f).obj M)) c =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M))) :
    c = Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M :=
  ((modulePullbackPushforwardAdjunction (f' ≫ f)).homEquiv M
    ((modulePullback f').obj ((modulePullback f).obj M))).injective
    (hc.trans
      (Sheaves.RingedSpaceDifferentials.homEquiv_modulePullbackComparison f f' M).symm)

/-- The components of `modulePullbackCompIso` are the comparison maps
`Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison`. -/
theorem modulePullbackCompIso_hom_app :
    (modulePullbackCompIso f f').hom.app M =
      Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M :=
  eq_modulePullbackComparison_of_homEquiv f f' M _
    (homEquiv_modulePullbackCompIso_hom_app f f' M)

/-- The comparison map `modulePullbackComparison f f' M : (f' ≫ f)^* M ⟶ f'^* (f^* M)` is an
isomorphism. -/
instance isIso_modulePullbackComparison :
    IsIso (Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M) :=
  (modulePullbackCompIso_hom_app f f' M) ▸
    inferInstanceAs (IsIso ((modulePullbackCompIso f f').hom.app M))

/-- The comparison map, packaged as an isomorphism. -/
noncomputable def modulePullbackComparisonIso :
    (modulePullback (f' ≫ f)).obj M ≅
      (modulePullback f').obj ((modulePullback f).obj M) :=
  asIso (Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M)

/-- The forward map of `modulePullbackComparisonIso` is `modulePullbackComparison`. -/
@[simp]
theorem modulePullbackComparisonIso_hom :
    (modulePullbackComparisonIso f f' M).hom =
      Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M :=
  rfl

/-- Compatibility with the units: the unit of `(f' ≫ f)^* ⊣ (f' ≫ f)_*`, followed by the
pushforward of the comparison isomorphism, is the composite of the two units. -/
theorem unit_comp_map_modulePullbackCompIso_hom_app :
    (modulePullbackPushforwardAdjunction (f' ≫ f)).unit.app M ≫
        (modulePushforward (f' ≫ f)).map ((modulePullbackCompIso f f').hom.app M) =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M)) :=
  (Adjunction.unit_leftAdjointUniq_hom_app _ (compAdjunction f f') M).trans
    (compAdjunction_unit_app f f' M)

/-- Compatibility with the counits: the comparison isomorphism at a pushed-forward sheaf,
followed by the composite counit, is the counit of `(f' ≫ f)^* ⊣ (f' ≫ f)_*`. -/
theorem modulePullbackCompIso_hom_app_comp_counit
    (N : SheafOfModules.{u} (structureSheafRing X'')) :
    (modulePullbackCompIso f f').hom.app ((modulePushforward (f' ≫ f)).obj N) ≫
        ((modulePullback f').map
            ((modulePullbackPushforwardAdjunction f).counit.app
              ((modulePushforward f').obj N)) ≫
          (modulePullbackPushforwardAdjunction f').counit.app N) =
      (modulePullbackPushforwardAdjunction (f' ≫ f)).counit.app N :=
  (congrArg _ (compAdjunction_counit_app f f' N).symm).trans
    (Adjunction.leftAdjointUniq_hom_app_counit _ (compAdjunction f f') N)

/-- Naturality of the comparison map in the sheaf of modules. -/
theorem modulePullbackComparison_naturality {M N : SheafOfModules.{u} (structureSheafRing X)}
    (g : M ⟶ N) :
    Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M ≫
        (modulePullback f').map ((modulePullback f).map g) =
      (modulePullback (f' ≫ f)).map g ≫
        Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' N := by
  rw [← modulePullbackCompIso_hom_app, ← modulePullbackCompIso_hom_app]
  exact ((modulePullbackCompIso f f').hom.naturality g).symm

/-- The comparison map is the unique morphism with its adjoint description. Together with
`homEquiv_modulePullbackComparison` this is the characterization a consumer needs in order
to recognize a hand-built map as the comparison map. -/
theorem modulePullbackComparison_unique
    (c : (modulePullback (f' ≫ f)).obj M ⟶
      (modulePullback f').obj ((modulePullback f).obj M))
    (hc : (modulePullbackPushforwardAdjunction (f' ≫ f)).homEquiv M
        ((modulePullback f').obj ((modulePullback f).obj M)) c =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M))) :
    c = Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M :=
  eq_modulePullbackComparison_of_homEquiv f f' M c hc

end Equations

/-- `modulePullbackCompIso` is Mathlib's `SheafOfModules.pullbackComp` for the two
structure-sheaf morphisms of the ringed spaces, read backwards. Stating this is what makes
Mathlib's associativity coherence `SheafOfModules.pullback_assoc` available for
`modulePullbackCompIso` without reproving it. -/
theorem modulePullbackCompIso_eq_pullbackComp_symm (f : X' ⟶ X) (f' : X'' ⟶ X') :
    modulePullbackCompIso f f' =
      letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
        modulePushforward_isRightAdjoint f
      letI : (SheafOfModules.pushforward (structureSheafHom f')).IsRightAdjoint :=
        modulePushforward_isRightAdjoint f'
      (SheafOfModules.pullbackComp (structureSheafHom f) (structureSheafHom f')).symm :=
  rfl

/-- **Associativity of the pullback pseudofunctor.** For `X''' ⟶ X'' ⟶ X' ⟶ X` the two ways
of decomposing `(h ≫ g ≫ f)^* M` as `h^* (g^* (f^* M))` — splitting off `f` first, or `h`
last — agree. -/
theorem modulePullbackCompIso_assoc {X''' : RingedSpace.{u, u}} (f : X' ⟶ X) (g : X'' ⟶ X')
    (h : X''' ⟶ X'') (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackCompIso f (h ≫ g)).hom.app M ≫
        (modulePullbackCompIso g h).hom.app ((modulePullback f).obj M) =
      (modulePullbackCompIso (g ≫ f) h).hom.app M ≫
        (modulePullback h).map ((modulePullbackCompIso f g).hom.app M) := by
  have key := NatTrans.congr_app (congrArg Iso.inv (SheafOfModules.pullback_assoc.{u}
    (structureSheafHom f) (structureSheafHom g) (structureSheafHom h))) M
  simp only [Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    whiskerLeft_app, whiskerRight_app, Iso.symm_inv, Functor.associator_hom_app,
    Category.comp_id, Category.assoc] at key
  simp only [modulePullbackCompIso_eq_pullbackComp_symm, Iso.symm_hom]
  exact key

end Stacks.PullbackPseudofunctor

end
