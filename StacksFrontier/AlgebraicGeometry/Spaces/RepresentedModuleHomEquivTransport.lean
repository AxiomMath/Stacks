module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.HomEquivTransport

/-!
# The transpositions of Stacks 03LU and of Stacks 01US correspond

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` whose represented morphism
`φ : yoneda.obj T' ⟶ yoneda.obj T` of algebraic spaces is relatively representable, and let `α`
be the underlying morphism of schemes.  Three adjunctions compare modules upstairs and
downstairs along it:

* the Zariski one, `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction α`;
* the small-étale one of the two *schemes*, pullback along the morphism of ringed sites
  `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` of Stacks 070R (2);
* the spaces-level one of Stacks 03LU,
  `AlgebraicGeometry.Space.modulePullbackAdjunction φ`.

The first two are joined by the associated-module functor of Stacks 03DU (4) and the second two
by the identification of the small étale site of a representable algebraic space with the small
étale site of the underlying scheme.  Each join carries an isomorphism of the two composite
pullbacks — `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
`AlgebraicGeometry.Space.representedModulePullbackIso` — and **this module proves that the
hom-set bijections of the adjunctions correspond under those isomorphisms.**

A morphism out of a pullback is identified with a morphism out of the other pullback by the
comparison isomorphism; that the two *transposes* then agree is a separate assertion.  The
abstract statement is `Stacks.CategoryTheory.homEquiv_transport`, and this module gives its two
instantiations, with the correcting comparison of right adjoints named in each case.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeMate`: the comparison
  `(α_*𝓖)^a ⟶ ε_*( 𝓖^a )` attached to
  `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`.
* `AlgebraicGeometry.Space.representedSmallEtaleModuleRestrictionAdjunction`: reading a module
  on the small étale site of a representable algebraic space on the small étale site of the
  underlying scheme, as a left adjoint.
* `AlgebraicGeometry.Space.representedModulePullbackMate`: the comparison attached to
  `AlgebraicGeometry.Space.representedModulePullbackIso`, with
  `AlgebraicGeometry.Space.representedModulePullbackMate_eq` for its definition.
* `AlgebraicGeometry.Space.representedModulePullbackFunctorIso`: **the transport of the inverse
  image of Stacks 03LU read in the forward direction**, which
  `AlgebraicGeometry.Space.representedModulePullbackIso` is not and
  `AlgebraicGeometry.Space.representedModuleObjPullbackIso` is only at one module.

## Main results

* `AlgebraicGeometry.SmallEtale.homEquiv_associatedModuleBaseChange` and
  `AlgebraicGeometry.SmallEtale.homEquiv_symm_associatedModuleBaseChange`: **the Zariski
  transposition and the small-étale transposition of two schemes correspond** under
  `AlgebraicGeometry.SmallEtale.associatedModule`.
* `AlgebraicGeometry.Space.homEquiv_representedModulePullback` and
  `AlgebraicGeometry.Space.homEquiv_symm_representedModulePullback`: **the small-étale
  transposition of two schemes and the spaces-level transposition of Stacks 03LU correspond**
  under `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`.
* `AlgebraicGeometry.SmallEtale.unit_associatedModuleBaseChange` and
  `AlgebraicGeometry.Space.unit_representedModulePullback`: **the two units correspond**, each
  square's correspondence read at the identity.
* `AlgebraicGeometry.Space.isIso_representedModulePullbackMate`: the comparison of right
  adjoints of the second square is invertible, the two vertical functors being the two halves
  of an equivalence.

## Implementation notes

The two squares are traversed in opposite directions, and that is forced.  The
associated-module functor is a left adjoint with no left adjoint of its own, so the square it
sits in can only be read with the associated-module functors as the two *vertical left
adjoints*; the identification of the two small étale sites, being an equivalence, can be read
either way, and it is read with its **inverse** as the vertical left adjoint because that is the
direction in which `AlgebraicGeometry.Space.representedModulePullbackIso` is stated — the
direction its proof produces, both sides there being left adjoints of a composite pushforward.
So the first statement transports a Zariski transpose up to the small étale site of the scheme,
and the second transports a spaces-level transpose down to it; composing them is what compares
the two ends, and the small étale site of the scheme is the meeting point.

Each comparison of right adjoints is `Stacks.CategoryTheory.transportMate` of the given
isomorphism of left adjoints, so neither is a new choice and neither has to be identified with
a separately built morphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the spaces-level
  adjunction.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  associated module on the small étale site, and its right adjoint.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), part (2), the morphism
  of small étale ringed sites of a morphism of schemes.
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC), part (1), the
  compatibility of the associated module with pullback.
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8), pullback of modules
  along a morphism of ringed sites.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (r : X ⟶ Y)

/-- **The comparison of right adjoints attached to `(α^*𝓕)^a ≅ ε^*(𝓕^a)`.**  Its component at
an `𝒪_X`-module `𝓖` is a morphism `(α_*𝓖)^a ⟶ ε_*(𝓖^a)` of modules on the small étale site of
`Y`: the associated module of a direct image maps to the direct image of the associated module.

It is `Stacks.CategoryTheory.transportMate` of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, hence determined by it; it is the
unique correction under which the two transpositions correspond, which is
`AlgebraicGeometry.SmallEtale.homEquiv_associatedModuleBaseChange`. -/
noncomputable def associatedModuleBaseChangeMate :
    Scheme.Modules.pushforward (schemeHom B r) ⋙ associatedModule B Y.obj Y.property ⟶
      associatedModule B X.obj X.property ⋙
        SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B r) :=
  Stacks.CategoryTheory.transportMate
    (Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B r))
    (associatedModuleAdjunction B X.obj X.property)
    (associatedModuleAdjunction B Y.obj Y.property)
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B r))
    (associatedModuleBaseChangeIso B r)

/-- **The Zariski transposition and the small-étale transposition correspond.**  Let `𝓕` be an
`𝒪_Y`-module, `𝓖` an `𝒪_X`-module and `u : α^*𝓕 ⟶ 𝓖` a morphism of `𝒪_X`-modules.  Transporting
`u` to the small étale sites by `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
transposing along `ε^* ⊣ ε_*` gives the associated module of the Zariski transpose of `u`,
followed by `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeMate`.

This is `Stacks.CategoryTheory.homEquiv_transport` at the square of ringed sites whose two
routes `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` compares. -/
theorem homEquiv_associatedModuleBaseChange (𝓕 : Y.obj.Modules) (𝓖 : X.obj.Modules)
    (u : (Scheme.Modules.pullback (schemeHom B r)).obj 𝓕 ⟶ 𝓖) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B r)).homEquiv
        ((associatedModule B Y.obj Y.property).obj 𝓕)
        ((associatedModule B X.obj X.property).obj 𝓖)
        ((associatedModuleBaseChangeIso B r).inv.app 𝓕 ≫
          (associatedModule B X.obj X.property).map u) =
      (associatedModule B Y.obj Y.property).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B r)).homEquiv 𝓕 𝓖 u) ≫
        (associatedModuleBaseChangeMate B r).app 𝓖 :=
  Stacks.CategoryTheory.homEquiv_transport _ _ _ _ (associatedModuleBaseChangeIso B r) u

/-- **The same correspondence read through the inverse transpositions.**  For a morphism
`v : 𝓕 ⟶ α_*𝓖` of `𝒪_Y`-modules, the small-étale transpose of the associated module of `v`
corrected by `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeMate` is the transport
along `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` of the associated module of
the Zariski transpose of `v`. -/
theorem homEquiv_symm_associatedModuleBaseChange (𝓕 : Y.obj.Modules) (𝓖 : X.obj.Modules)
    (v : 𝓕 ⟶ (Scheme.Modules.pushforward (schemeHom B r)).obj 𝓖) :
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B r)).homEquiv
        ((associatedModule B Y.obj Y.property).obj 𝓕)
        ((associatedModule B X.obj X.property).obj 𝓖)).symm
        ((associatedModule B Y.obj Y.property).map v ≫
          (associatedModuleBaseChangeMate B r).app 𝓖) =
      (associatedModuleBaseChangeIso B r).inv.app 𝓕 ≫
        (associatedModule B X.obj X.property).map
          (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B r)).homEquiv 𝓕 𝓖).symm
            v) :=
  Stacks.CategoryTheory.homEquiv_symm_transport _ _ _ _ (associatedModuleBaseChangeIso B r) v

/-- **The unit of the Zariski adjunction and the unit of the small-étale adjunction
correspond.**  This is `AlgebraicGeometry.SmallEtale.homEquiv_associatedModuleBaseChange` at the
identity.

It is `Stacks.CategoryTheory.unit_transport` at the same square. -/
theorem unit_associatedModuleBaseChange (𝓕 : Y.obj.Modules) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B r)).unit.app
        ((associatedModule B Y.obj Y.property).obj 𝓕) ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B r)).map
          ((associatedModuleBaseChangeIso B r).inv.app 𝓕) =
      (associatedModule B Y.obj Y.property).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B r)).unit.app 𝓕) ≫
        (associatedModuleBaseChangeMate B r).app
          ((Scheme.Modules.pullback (schemeHom B r)).obj 𝓕) :=
  Stacks.CategoryTheory.unit_transport _ _ _ _ (associatedModuleBaseChangeIso B r) 𝓕

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Reading a module on the small étale site of an algebraic space `yoneda.obj U` on the small
étale site of the scheme underlying `U` is left adjoint to reading one back.**  This is the
inverse of the identification
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, read as an adjunction. -/
noncomputable def representedSmallEtaleModuleRestrictionAdjunction (U : BigFppfOver B S hS) :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse ⊣
      (representedSmallEtaleModuleEquivalence B S hS U).functor :=
  (representedSmallEtaleModuleEquivalence B S hS U).symm.toAdjunction

/-- The unit of `AlgebraicGeometry.Space.representedSmallEtaleModuleRestrictionAdjunction` is an
isomorphism: it is the unit of an adjoint equivalence. -/
instance isIso_unit_representedSmallEtaleModuleRestrictionAdjunction (U : BigFppfOver B S hS) :
    IsIso (representedSmallEtaleModuleRestrictionAdjunction B S hS U).unit :=
  inferInstanceAs (IsIso (representedSmallEtaleModuleEquivalence B S hS U).symm.unit)

/-- The counit of `AlgebraicGeometry.Space.representedSmallEtaleModuleRestrictionAdjunction` is
an isomorphism: it is the counit of an adjoint equivalence. -/
instance isIso_counit_representedSmallEtaleModuleRestrictionAdjunction (U : BigFppfOver B S hS) :
    IsIso (representedSmallEtaleModuleRestrictionAdjunction B S hS U).counit :=
  inferInstanceAs (IsIso (representedSmallEtaleModuleEquivalence B S hS U).symm.counit)

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The comparison of right adjoints attached to the transport of the inverse image of
Stacks 03LU.**  Its component at an `𝒪`-module `N` on the small étale site of `yoneda.obj T'` is
a morphism from the direct image of `N` along `φ`, read on the small étale site of the scheme
underlying `T`, to the direct image along the morphism of small étale ringed sites of Stacks
070R (2) of `N` read on the small étale site of the scheme underlying `T'`.

It is `Stacks.CategoryTheory.transportMate` of
`AlgebraicGeometry.Space.representedModulePullbackIso`, hence determined by it. -/
noncomputable def representedModulePullbackMate :
    modulePushforward B S hS (representedSpaceMap B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).inverse ⟶
      (representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) :=
  Stacks.CategoryTheory.transportMate
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g hg)

/-- `AlgebraicGeometry.Space.representedModulePullbackMate` is
`Stacks.CategoryTheory.transportMate` of
`AlgebraicGeometry.Space.representedModulePullbackIso`. -/
theorem representedModulePullbackMate_eq :
    representedModulePullbackMate B S hS g hg =
      Stacks.CategoryTheory.transportMate
        (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
        (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
        (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS g))
        (representedModulePullbackIso B S hS g hg) :=
  rfl

/-- **The spaces-level transposition of Stacks 03LU and the small-étale transposition of the two
underlying schemes correspond.**  Let `M` be an `𝒪`-module on the small étale site of
`yoneda.obj T`, let `N` be one on the small étale site of `yoneda.obj T'` and let
`f : φ^*M ⟶ N` be a morphism of `𝒪`-modules.  Reading `f` on the small étale sites of the two
schemes through `AlgebraicGeometry.Space.representedModulePullbackIso` and transposing along
`ε^* ⊣ ε_*` gives the reading of the spaces-level transpose of `f`, followed by
`AlgebraicGeometry.Space.representedModulePullbackMate`.

This is `Stacks.CategoryTheory.homEquiv_transport` at the square of small étale ringed sites of
`AlgebraicGeometry.Space.representedModulePullbackIso`. -/
theorem homEquiv_representedModulePullback
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (f : (modulePullback B S hS (representedSpaceMap B S hS g)).obj M ⟶ N) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS g)).homEquiv
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj M)
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj N)
        ((representedModulePullbackIso B S hS g hg).inv.app M ≫
          (representedSmallEtaleModuleEquivalence B S hS T').inverse.map f) =
      (representedSmallEtaleModuleEquivalence B S hS T).inverse.map
          ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv M N f) ≫
        (Stacks.CategoryTheory.transportMate
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
          (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
          (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g))
          (representedModulePullbackIso B S hS g hg)).app N :=
  Stacks.CategoryTheory.homEquiv_transport
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g hg) f

/-- **The same correspondence read through the inverse transpositions.**  For a morphism
`w : M ⟶ φ_*N`, the small-étale transpose of the reading of `w` corrected by
`AlgebraicGeometry.Space.representedModulePullbackMate` is the reading of the spaces-level
transpose of `w`.

Since `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` is an equivalence, its
inverse is faithful, so this equation determines the spaces-level transpose: it is the sense in
which the arrow of Stacks 03LU *is* the arrow of the small étale site of the underlying
scheme. -/
theorem homEquiv_symm_representedModulePullback
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (w : M ⟶ (modulePushforward B S hS (representedSpaceMap B S hS g)).obj N) :
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS g)).homEquiv
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj M)
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj N)).symm
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map w ≫
          (Stacks.CategoryTheory.transportMate
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
          (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
          (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g))
          (representedModulePullbackIso B S hS g hg)).app N) =
      (representedModulePullbackIso B S hS g hg).inv.app M ≫
        (representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          (((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv M N).symm
            w) :=
  Stacks.CategoryTheory.homEquiv_symm_transport
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g hg) w

/-- **The unit of Stacks 03LU and the unit of the small-étale adjunction of the two underlying
schemes correspond.**  This is
`AlgebraicGeometry.Space.homEquiv_representedModulePullback` at the identity. -/
theorem unit_representedModulePullback
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS g)).unit.app
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj M) ≫
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).map
          ((representedModulePullbackIso B S hS g hg).inv.app M) =
      (representedSmallEtaleModuleEquivalence B S hS T).inverse.map
          ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).unit.app M) ≫
        (Stacks.CategoryTheory.transportMate
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
          (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
          (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g))
          (representedModulePullbackIso B S hS g hg)).app
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj M) :=
  Stacks.CategoryTheory.unit_transport
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g hg) M

/-- **The comparison of right adjoints is invertible.**  The two vertical functors of the square
are the two halves of the identification of the small étale site of a representable algebraic
space with the small étale site of the underlying scheme, which is an equivalence, so
`Stacks.CategoryTheory.isIso_transportMate` applies. -/
theorem isIso_representedModulePullbackMate :
    IsIso (representedModulePullbackMate B S hS g hg) :=
  Stacks.CategoryTheory.isIso_transportMate
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T')
    (representedSmallEtaleModuleRestrictionAdjunction B S hS T)
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g hg)
    (isIso_unit_representedSmallEtaleModuleRestrictionAdjunction B S hS T')
    (isIso_counit_representedSmallEtaleModuleRestrictionAdjunction B S hS T)

/-- **The inverse image of modules along a morphism of representable algebraic spaces is the
small étale pullback of the underlying morphism of schemes, in the forward direction.**  Reading
a module on the small étale site of the scheme underlying `T` on the small étale site of
`yoneda.obj T` and then taking the inverse image of Stacks 03LU along `φ` is pulling back along
the morphism of small étale ringed sites of Stacks 070R (2) and then reading the result on the
small étale site of `yoneda.obj T'`, naturally in the module.

`AlgebraicGeometry.Space.representedModulePullbackIso` is this statement with the *inverse* of
the identification of sites on both sides, which is the direction its proof produces, and
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` is this statement at one module, with
no naturality.  The step from either to this one is that the comparison of right adjoints
attached to that isomorphism is invertible — which is
`AlgebraicGeometry.Space.isIso_representedModulePullbackMate` — after which both sides here are
left adjoints of one functor. -/
noncomputable def representedModulePullbackFunctorIso :
    SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').functor ≅
      (representedSmallEtaleModuleEquivalence B S hS T).functor ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) :=
  Adjunction.leftAdjointUniq
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (representedSchemeStructureMapRing B S hS g)).comp
      (representedSmallEtaleModuleEquivalence B S hS T').toAdjunction)
    (((representedSmallEtaleModuleEquivalence B S hS T).toAdjunction.comp
        (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))).ofNatIsoRight
      (@asIso _ _ _ _ _ (isIso_representedModulePullbackMate B S hS g hg)))

end AlgebraicGeometry.Space

end
