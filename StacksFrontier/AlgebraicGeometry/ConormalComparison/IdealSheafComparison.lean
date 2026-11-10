module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Factorization
public import StacksFrontier.AlgebraicGeometry.IdealSheafRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# The conormal sheaf is the pullback of the ideal sheaf of any closed factorization

The conormal sheaf of an immersion `i : Z ⟶ X` is defined from the *canonical* closed
factorization `i.liftCoborder : Z ⟶ i.coborderRange`: it is the module pullback along that
morphism of its ideal sheaf. This file proves that *every* closed-immersion factorization of
`i` through an open subscheme computes the same sheaf, canonically:

`conormalSheaf i ≅ (i')^* I(i')` whenever `i' ≫ U.ι = i` with `i'` a closed immersion.

## Main definitions

* `Stacks.Conormal.conormalSheaf`: the conormal sheaf of an immersion, the module pullback
  along `i.liftCoborder` of the ideal sheaf of `i.liftCoborder`.
* `Stacks.Conormal.pullbackIdealSheafCompIso`: for an arbitrary morphism `k` followed by an
  open immersion `j`, the pullback along `k ≫ j` of the ideal sheaf of `k ≫ j` is the
  pullback along `k` of the ideal sheaf of `k`.
* `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`: the same, with the composite presented as
  a separately named morphism together with the equation identifying it.
* `Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf`: **the comparison**, part (1) of
  [Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3).
* `Stacks.Conormal.conormalQuotientMap`: the canonical map from the ideal sheaf of a closed
  factorization to the pushforward of the conormal sheaf. [Stacks, Tag 01R3] supplies its
  body; the comparison isomorphism was the only ingredient it lacked.

## Main results

* `Stacks.Conormal.epi_conormalQuotientMap_iff`: the quotient map is an epimorphism exactly
  when the unit of the pullback-pushforward adjunction is one at the ideal sheaf. This is the
  whole of what [Stacks, Tag 01R3]'s surjectivity assertion still needs, with the chosen
  factorization eliminated from the question.
* `Stacks.Conormal.pullbackIdealSheafCompIso_comp`: the cocycle condition, comparing along a
  composite of two open immersions is comparing along each in turn. Its input is
  `Stacks.Conormal.pullbackIdealSheafIsoOfEq_cocycle` at the level of ideal sheaves together
  with `Stacks.PullbackPseudofunctor.modulePullbackCompIso_assoc`, packaged here as
  `Stacks.Conormal.modulePullbackCompIso_assoc_comp_map`. The same statement with the two
  composites presented by equations, which is the form a factorization supplies, is
  `Stacks.Conormal.pullbackIdealSheafCompIso_hom_comp_isoOfCompEq_hom`.

## Route

Two inputs, both already in the library, and one composition.

* `Stacks.Conormal.le_coborderRange_of_comp_eq` and
  `Stacks.Conormal.comp_homOfLE_eq_liftCoborder`: the open `U` through which `i` factors is
  contained in `i.coborderRange`, and the factorizing morphism followed by the induced open
  immersion `AlgebraicGeometry.Scheme.homOfLE` is `i.liftCoborder` on the nose. So the
  canonical factorization *is* the given one followed by an open immersion.
* `Stacks.PullbackPseudofunctor.modulePullbackCompIso`: the module pullback along a
  composite is the composite of the module pullbacks.
* `Stacks.IdealSheafRestrict.pullbackIdealSheafIso`: the pullback along an open immersion `j`
  of the ideal sheaf of `k ≫ j` is the ideal sheaf of `k`.

Writing `L = i.liftCoborder`, `j` for the open immersion and `k = i'`, the chain is

`L^* I(L) = (k ≫ j)^* I(k ≫ j) ≅ k^* (j^* I(k ≫ j)) ≅ k^* I(k)`,

the first step by pseudofunctoriality and the second by functoriality of `k^*` applied to the
restriction isomorphism.

## Vocabulary

Tag 01R2's `conormalSheaf` is `Stacks.Conormal.conormalSheaf`
(the same body as that abbreviation, with our name for the ideal sheaf).

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`.

Tag 01R3's `conormalSheafIsoPullbackIdealSheaf` is
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf`.

No hypothesis beyond the tag's is used. `IsImmersion i` is what makes `i.liftCoborder`
available, `IsClosedImmersion i'` is what makes `U ≤ i.coborderRange` true, and `hfac` is the
factorization equation. Nothing is assumed affine, Noetherian, finite or quasi-compact; the
morphism `k` in the two auxiliary definitions is arbitrary, so even the closed-immersion
hypothesis is not used by them.

## Universe situation

A single universe `u`, as in the tagged statement: `Scheme.{u}` and `SheafOfModules.{u}`. This is
forced by `RingedSpaceModuleAdjunction`, whose module pullback exists only for `RingedSpace.{u, u}`.

## What is not done

* **The normalization clause is not proved.**
  [Stacks, Tag 01R3]'s `conormalSheafIsoPullbackIdealSheaf_liftCoborder` asks that
  `conormalSheafIsoPullbackIdealSheaf i i.coborderRange i.liftCoborder i.liftCoborder_ι` be
  `Iso.refl`. With the construction here that unwinds to two statements neither of which is
  available: that `Stacks.IdealSheafRestrict.pullbackIdealSheafIso` along
  `AlgebraicGeometry.Scheme.homOfLE le_rfl` is the canonical transport, and a unitality
  statement for `Stacks.PullbackPseudofunctor.modulePullbackCompIso` — its collapse at a
  factor which is provably but not definitionally an identity. The second is recorded as
  missing in the module docstring of
  `StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic`; its ingredient
  `Stacks.PullbackPseudofunctor.modulePullbackIdIso` is available, but the transported form is
  not. Note that `AlgebraicGeometry.Scheme.homOfLE le_rfl` is not the identity morphism
  definitionally, which is why this cannot be hoped for and has to be built.
* **No independence statement.** There is no proof here that the comparison isomorphisms
  attached to two different factorizations agree on their common opens. [Stacks, Tag 01R3]
  states that as its `conormalQuotientMap_restrict_factorization` clause, and derives it from
  the affine generator formula, which is not available here.
* **The quotient map is not shown to be an epimorphism.** `epi_conormalQuotientMap_iff`
  reduces that to epimorphy of the adjunction unit `I ⟶ i'_*(i'^* I)` at the ideal sheaf of a
  closed immersion, and nothing here proves it. That is a statement about local
  surjectivity of `I ⟶ I ⊗ 𝒪_Z`, which needs the local generation of the ideal sheaf
  recorded in `Stacks.ClosedImmersion.IsClosedImmersion` and the sheafification in the
  definition of the module pullback; no part of it is in this file.
* **Nothing else downstream.** The kernel of the quotient map on affine opens, and the
  identification of the affine sections with `Ideal.Cotangent`, are untouched. Those need the
  affine content of [Stacks, Tag 01IN], not the comparison proved here.
* [Stacks, Tag 01R3] carries twelve labelled assertions across two parts and this file covers
  one of them; only that one clause is tagged here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal

/-- **[Stacks, Tag 01R2].** The conormal sheaf of an immersion: the module pullback, along the
canonical closed immersion `i.liftCoborder` into the coborder neighbourhood of the image, of the
ideal sheaf of that closed immersion.

Keeping it an abbreviation is deliberate: [Stacks, Tag 01R3]'s normalization clause compares an
isomorphism of this object with `Iso.refl`, which requires the two sides to have the same
type without a transport.

Quasi-coherence, the other half of the assertion of [Stacks, Tag 01R2], is
`Stacks.Conormal.conormalSheaf_isQuasicoherent`. -/
@[stacks 01R2 "construction"]
noncomputable abbrev conormalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) :=
  (modulePullback i.liftCoborder.toLRSHom.toShHom).obj
    (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)

/-- For an arbitrary morphism `k : Z ⟶ U` followed by an open immersion `j : U ⟶ V`, the
module pullback along `k ≫ j` of the ideal sheaf of `k ≫ j` is the module pullback along `k`
of the ideal sheaf of `k`.

Pseudofunctoriality of the module pullback splits the left-hand side as `k^* (j^* ...)`, and
`Stacks.IdealSheafRestrict.pullbackIdealSheafIso` identifies the inner pullback. -/
noncomputable def pullbackIdealSheafCompIso {Z U V : Scheme.{u}} (k : Z ⟶ U) (j : U ⟶ V)
    [IsOpenImmersion j] :
    (modulePullback (k ≫ j).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom) ≅
      (modulePullback k.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) :=
  ((Stacks.PullbackPseudofunctor.modulePullbackCompIso j.toLRSHom.toShHom
        k.toLRSHom.toShHom).app
      (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom)).trans
    ((modulePullback k.toLRSHom.toShHom).mapIso
      (Stacks.IdealSheafRestrict.pullbackIdealSheafIso j k))

/-- `pullbackIdealSheafCompIso` with the composite `k ≫ j` presented as a separately named
morphism `L` together with the equation `k ≫ j = L`. This is the form a factorization
statement supplies: the canonical closed immersion into the coborder neighbourhood is given
to us as `i.liftCoborder`, and the equation is a theorem about it. -/
noncomputable def pullbackIdealSheafIsoOfCompEq {Z U V : Scheme.{u}} (k : Z ⟶ U) (j : U ⟶ V)
    [IsOpenImmersion j] (L : Z ⟶ V) (hL : k ≫ j = L) :
    (modulePullback L.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom) ≅
      (modulePullback k.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) := by
  subst hL
  exact pullbackIdealSheafCompIso k j

/-- **[Stacks, Tag 01R3], part (1).** The conormal sheaf of an immersion `i : Z ⟶ X` is the
module pullback of the ideal sheaf of *any* factorization of `i` as a closed immersion into
an open subscheme followed by the inclusion of that open subscheme.

The given open `U` is contained in `i.coborderRange` by
`Stacks.Conormal.le_coborderRange_of_comp_eq`, and the factorizing morphism followed by the
induced open immersion is `i.liftCoborder` by
`Stacks.Conormal.comp_homOfLE_eq_liftCoborder`. So this is
`pullbackIdealSheafIsoOfCompEq` for that open immersion. -/
@[stacks 01R3 "part (1): pullback of the ideal sheaf"]
noncomputable def conormalSheafIsoPullbackIdealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) :
    conormalSheaf i ≅
      (modulePullback i'.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom) :=
  pullbackIdealSheafIsoOfCompEq i'
    (X.homOfLE (le_coborderRange_of_comp_eq i U i' hfac)) i.liftCoborder
    (comp_homOfLE_eq_liftCoborder i U i' hfac)

/-- The canonical map from the ideal sheaf of a closed-immersion factorization of `i` to the
pushforward along that factorization of the conormal sheaf of `i`: the unit of the
pullback-pushforward adjunction, read through `conormalSheafIsoPullbackIdealSheaf`.

This is the body given by [Stacks, Tag 01R3] itself; the comparison isomorphism is the only
ingredient it was waiting for. -/
noncomputable def conormalQuotientMap {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) :
    Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom ⟶
      (modulePushforward i'.toLRSHom.toShHom).obj (conormalSheaf i) :=
  (modulePullbackPushforwardAdjunction i'.toLRSHom.toShHom).unit.app
      (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom) ≫
    (modulePushforward i'.toLRSHom.toShHom).map
      (conormalSheafIsoPullbackIdealSheaf i U i' hfac).inv

/-- **The epimorphy of `conormalQuotientMap` is exactly the epimorphy of the adjunction
unit**, and in particular does not depend on the chosen factorization beyond that unit: the
second factor of `conormalQuotientMap` is the pushforward of an isomorphism, hence an
isomorphism, and an isomorphism may be cancelled from the right of an epimorphism.

This reduces [Stacks, Tag 01R3]'s assertion that the ideal sheaf surjects onto the
pushforward conormal sheaf to the single statement that
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` has epimorphic unit at the
ideal sheaf of a closed immersion — that is, that `I ⟶ i'_*(i'^* I)` is an epimorphism. That
statement is *not* proved here; see the module docstring. -/
theorem epi_conormalQuotientMap_iff {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) :
    Epi (conormalQuotientMap i U i' hfac) ↔
      Epi ((modulePullbackPushforwardAdjunction i'.toLRSHom.toShHom).unit.app
        (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)) :=
  epi_comp_iff_of_isIso _ _

/-! ### Associativity of the ideal sheaf comparison -/

section IdealSheafCocycle

open Stacks.ClosedImmersion Stacks.IdealSheafRestrict Stacks.PullbackPseudofunctor

variable {Z U V W : Scheme.{u}}
/-! ## The general transpose lemma -/

/-- The transpose of a map out of an iterated module pullback, computed through the comparison
isomorphism of the two pullbacks. -/
public theorem unit_comp_map_modulePullbackCompIso_transpose {X X' X'' : RingedSpace.{u, u}}
    (f : X' ⟶ X) (f' : X'' ⟶ X')
    (M : SheafOfModules.{u} (structureSheafRing X)) (N : SheafOfModules.{u} (structureSheafRing X'))
    (ρ : (modulePullback f).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction (f' ≫ f)).unit.app M ≫
        (modulePushforward (f' ≫ f)).map
          ((modulePullbackCompIso f f').hom.app M ≫ (modulePullback f').map ρ) =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          (ρ ≫ (modulePullbackPushforwardAdjunction f').unit.app N) := by
  have h3 : (modulePushforward f).map
          ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M)) ≫
        (modulePushforward (f' ≫ f)).map ((modulePullback f').map ρ) =
      (modulePushforward f).map (ρ ≫ (modulePullbackPushforwardAdjunction f').unit.app N) :=
    ((modulePushforward f).map_comp
        ((modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M))
        ((modulePushforward f').map ((modulePullback f').map ρ))).symm.trans
      (congrArg (modulePushforward f).map
        ((modulePullbackPushforwardAdjunction f').unit.naturality ρ).symm)
  rw [Functor.map_comp, ← Category.assoc, unit_comp_map_modulePullbackCompIso_hom_app]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (modulePullbackPushforwardAdjunction f).unit.app M ≫ z) h3)


variable {Z U V W : Scheme.{u}}

/-- **The adjoint description of the pullback of the structure sheaf.**  The transpose of the
comparison isomorphism for the pullback of the unit module along an open immersion is the
structure map. -/
public theorem unit_comp_map_pullbackUnitModuleIso (j : U ⟶ V) [IsOpenImmersion j] :
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (unitModule V) ≫
      (Scheme.Modules.pushforward j).map (pullbackUnitModuleIso j).hom = structureMap j := by
  have h1 := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) (unitModule V)
  have h3 : (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (unitModule V) ≫
      (pullbackUnitModuleIso j).hom = (restrictUnitModuleIso j).hom := by
    simp [pullbackUnitModuleIso]
  have h2 : (Scheme.Modules.restrictAdjunction j).unit.app (unitModule V) ≫
      (Scheme.Modules.pushforward j).map (restrictUnitModuleIso j).hom = structureMap j := by
    ext O x
    have hap : V.presheaf.map (homOfLE (j.image_preimage_le O)).op ≫
        (j.appIso (j ⁻¹ᵁ O)).hom = j.app O := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]
    exact congr($hap x)
  rw [← h1, Category.assoc, ← Functor.map_comp]
  exact (congrArg (fun z => (Scheme.Modules.restrictAdjunction j).unit.app (unitModule V) ≫
    (Scheme.Modules.pushforward j).map z) h3).trans h2

/-- The comparison isomorphism for the pullback of the unit module along an open immersion is the
canonical map to the unit module. -/
public theorem pullbackUnitIso_hom_eq_modulePullbackUnitToUnit (j : U ⟶ V) [IsOpenImmersion j] :
    (pullbackUnitIso j).hom = modulePullbackUnitToUnit j.toLRSHom.toShHom := by
  refine ((modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).homEquiv _ _).injective ?_
  rw [homEquiv_modulePullbackUnitToUnit, Adjunction.homEquiv_unit]
  exact unit_comp_map_pullbackUnitModuleIso j


/-- The canonical maps to the unit module compose along an iterated pullback, through the
comparison isomorphism of the two pullbacks. -/
public theorem modulePullbackUnitToUnit_comp {X X' X'' : RingedSpace.{u, u}} (f : X' ⟶ X)
    (f' : X'' ⟶ X') :
    (modulePullbackCompIso f f').hom.app (SheafOfModules.unit (structureSheafRing X)) ≫
        ((modulePullback f').map (modulePullbackUnitToUnit f) ≫
          modulePullbackUnitToUnit f') =
      modulePullbackUnitToUnit (f' ≫ f) := by
  have h5 : ∀ {A B : RingedSpace.{u, u}} (g : B ⟶ A),
      (modulePullbackPushforwardAdjunction g).unit.app
            (SheafOfModules.unit (structureSheafRing A)) ≫
          (modulePushforward g).map (modulePullbackUnitToUnit g) =
        structureSheafModuleHom g := fun g =>
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (homEquiv_modulePullbackUnitToUnit g)
  have h4 : (modulePushforward f).map (modulePullbackUnitToUnit f ≫
          (modulePullbackPushforwardAdjunction f').unit.app
            (SheafOfModules.unit (structureSheafRing X'))) ≫
        (modulePushforward (f' ≫ f)).map (modulePullbackUnitToUnit f') =
      (modulePushforward f).map
        (modulePullbackUnitToUnit f ≫ structureSheafModuleHom f') := by
    refine Eq.trans (((modulePushforward f).map_comp
      (modulePullbackUnitToUnit f ≫ (modulePullbackPushforwardAdjunction f').unit.app
        (SheafOfModules.unit (structureSheafRing X')))
      ((modulePushforward f').map (modulePullbackUnitToUnit f'))).symm)
      (congrArg (modulePushforward f).map ?_)
    rw [Category.assoc]
    exact congrArg (fun z => modulePullbackUnitToUnit f ≫ z) (h5 f')
  refine ((modulePullbackPushforwardAdjunction (f' ≫ f)).homEquiv _ _).injective ?_
  rw [homEquiv_modulePullbackUnitToUnit, Adjunction.homEquiv_unit, ← Category.assoc,
    Functor.map_comp, ← Category.assoc, unit_comp_map_modulePullbackCompIso_transpose]
  refine (Category.assoc _ _ _).trans ((congrArg (fun z =>
      (modulePullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (structureSheafRing X)) ≫ z)
    h4).trans ?_)
  refine (congrArg (fun z => (modulePullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit (structureSheafRing X)) ≫ z)
    ((modulePushforward f).map_comp (modulePullbackUnitToUnit f)
      (structureSheafModuleHom f'))).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (modulePushforward f).map (structureSheafModuleHom f')) (h5 f)).trans
      (structureSheafModuleHom_comp f' f).symm)


/-- The pullback along an open immersion of the ideal sheaf of a composite is the ideal sheaf of
the other factor, with the composite presented by an equation. -/
public noncomputable def pullbackIdealSheafIsoOfEq (k : Z ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]
    (P : Z ⟶ V)
    (hP : k ≫ j = P) :
    (modulePullback j.toLRSHom.toShHom).obj (idealSheaf P.toLRSHom.toShHom) ≅
      idealSheaf k.toLRSHom.toShHom := by
  subst hP; exact pullbackIdealSheafIso j k

/-- At a literal composite, `pullbackIdealSheafIsoOfEq` is `pullbackIdealSheafIso`. -/
public theorem pullbackIdealSheafIsoOfEq_rfl (k : Z ⟶ U) (j : U ⟶ V) [IsOpenImmersion j] :
    pullbackIdealSheafIsoOfEq k j (k ≫ j) rfl = pullbackIdealSheafIso j k := rfl

/-- The ideal sheaf comparison isomorphism, read after the inclusion of the ideal sheaf into the
structure sheaf. -/
public theorem pullbackIdealSheafIsoOfEq_hom_comp_ι (k : Z ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]
    (P : Z ⟶ V) (hP : k ≫ j = P) :
    (pullbackIdealSheafIsoOfEq k j P hP).hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom k.toLRSHom.toShHom)) =
      (modulePullback j.toLRSHom.toShHom).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom P.toLRSHom.toShHom))) ≫
        modulePullbackUnitToUnit j.toLRSHom.toShHom := by
  subst hP
  rw [pullbackIdealSheafIsoOfEq_rfl, ← pullbackUnitIso_hom_eq_modulePullbackUnitToUnit]
  exact pullbackIdealSheafIso_hom_comp_ι j k


/-- **Associativity of the ideal sheaf comparison.**  Comparing along a composite of two open
immersions is comparing along each in turn, through the pullback comparison isomorphism. -/
public theorem pullbackIdealSheafIsoOfEq_cocycle (k : Z ⟶ U) (m : U ⟶ W) (n : W ⟶ V)
    [IsOpenImmersion m] [IsOpenImmersion n] (L : Z ⟶ W) (hL : k ≫ m = L) (P : Z ⟶ V)
    (hP : L ≫ n = P) :
    (pullbackIdealSheafIsoOfEq k (m ≫ n) P (by rw [← Category.assoc, hL, hP])).hom =
      (modulePullbackCompIso n.toLRSHom.toShHom m.toLRSHom.toShHom).hom.app
          (idealSheaf P.toLRSHom.toShHom) ≫
        (modulePullback m.toLRSHom.toShHom).map (pullbackIdealSheafIsoOfEq L n P hP).hom ≫
          (pullbackIdealSheafIsoOfEq k m L hL).hom := by
  set κk := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom k.toLRSHom.toShHom)) with hκk
  set κL := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom L.toLRSHom.toShHom)) with hκL
  set κP := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom P.toLRSHom.toShHom)) with hκP
  set C := (modulePullbackCompIso n.toLRSHom.toShHom m.toLRSHom.toShHom).hom.app
    (idealSheaf P.toLRSHom.toShHom) with hC
  set Cu := (modulePullbackCompIso n.toLRSHom.toShHom m.toLRSHom.toShHom).hom.app
    (SheafOfModules.unit (structureSheafRing V.toLocallyRingedSpace.toRingedSpace)) with hCu
  set D := (modulePullback m.toLRSHom.toShHom).map
    (pullbackIdealSheafIsoOfEq L n P hP).hom with hD
  set E := (pullbackIdealSheafIsoOfEq k m L hL).hom with hE
  set Um := modulePullbackUnitToUnit m.toLRSHom.toShHom with hUm
  set Un := modulePullbackUnitToUnit n.toLRSHom.toShHom with hUn
  refine (cancel_mono κk).mp ?_
  refine (pullbackIdealSheafIsoOfEq_hom_comp_ι k (m ≫ n) P
    (by rw [← Category.assoc, hL, hP])).trans ?_
  have hnat : (modulePullback (m ≫ n).toLRSHom.toShHom).map κP ≫ Cu =
      C ≫ (modulePullback m.toLRSHom.toShHom).map
        ((modulePullback n.toLRSHom.toShHom).map κP) :=
    (modulePullbackCompIso n.toLRSHom.toShHom m.toLRSHom.toShHom).hom.naturality κP
  have hlam : Cu ≫ ((modulePullback m.toLRSHom.toShHom).map Un ≫ Um) =
      modulePullbackUnitToUnit (m ≫ n).toLRSHom.toShHom :=
    modulePullbackUnitToUnit_comp n.toLRSHom.toShHom m.toLRSHom.toShHom
  refine Eq.symm (Eq.trans (Category.assoc C (D ≫ E) κk) ?_)
  refine Eq.trans (congrArg (fun z => C ≫ z) (Category.assoc D E κk)) ?_
  refine Eq.trans (congrArg (fun z => C ≫ D ≫ z)
    (pullbackIdealSheafIsoOfEq_hom_comp_ι k m L hL)) ?_
  refine Eq.trans (congrArg (fun z => C ≫ z)
    (Category.assoc D ((modulePullback m.toLRSHom.toShHom).map κL) Um).symm) ?_
  refine Eq.trans (congrArg (fun z => C ≫ z ≫ Um)
    (((modulePullback m.toLRSHom.toShHom).map_comp
      (pullbackIdealSheafIsoOfEq L n P hP).hom κL).symm)) ?_
  refine Eq.trans (congrArg (fun z => C ≫ (modulePullback m.toLRSHom.toShHom).map z ≫ Um)
    (pullbackIdealSheafIsoOfEq_hom_comp_ι L n P hP)) ?_
  refine Eq.trans (congrArg (fun z => C ≫ z ≫ Um)
    ((modulePullback m.toLRSHom.toShHom).map_comp
      ((modulePullback n.toLRSHom.toShHom).map κP) Un)) ?_
  refine Eq.trans (congrArg (fun z => C ≫ z)
    (Category.assoc ((modulePullback m.toLRSHom.toShHom).map
      ((modulePullback n.toLRSHom.toShHom).map κP))
      ((modulePullback m.toLRSHom.toShHom).map Un) Um)) ?_
  refine Eq.trans (Category.assoc C ((modulePullback m.toLRSHom.toShHom).map
    ((modulePullback n.toLRSHom.toShHom).map κP))
    ((modulePullback m.toLRSHom.toShHom).map Un ≫ Um)).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ ((modulePullback m.toLRSHom.toShHom).map Un ≫ Um))
    hnat.symm) ?_
  refine Eq.trans (Category.assoc ((modulePullback (m ≫ n).toLRSHom.toShHom).map κP) Cu
    ((modulePullback m.toLRSHom.toShHom).map Un ≫ Um)) ?_
  exact congrArg (fun z => (modulePullback (m ≫ n).toLRSHom.toShHom).map κP ≫ z) hlam

/-- The composition isomorphism of `RingedSpaceModuleAdjunction` and the one of
`Stacks.PullbackPseudofunctor` are the same isomorphism, with the two factors named in the
opposite order; both are `CategoryTheory.SheafOfModules.pullbackComp` of the two
structure-sheaf morphisms, read backwards. -/
public theorem modulePullbackComp_eq_modulePullbackCompIso {X Y Y' : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Y') :
    modulePullbackComp f g = modulePullbackCompIso g f :=
  rfl

/-- **Associativity of the pullback comparison, applied to a morphism out of the middle
pullback.** For `a : X''' ⟶ X''`, `b : X'' ⟶ X'`, `c : X' ⟶ X` and morphisms
`ρ : c^* M ⟶ N`, `σ : b^* N ⟶ Q`, splitting `a` off `(b ≫ c)` and then `b` off `c` gives the
same morphism `(a ≫ b ≫ c)^* M ⟶ a^* Q` as splitting `a ≫ b` off `c` and then `a` off `b`. -/
public theorem modulePullbackCompIso_assoc_comp_map {X X' X'' X''' : RingedSpace.{u, u}}
    (a : X''' ⟶ X'') (b : X'' ⟶ X') (c : X' ⟶ X)
    (M : SheafOfModules.{u} (structureSheafRing X)) (N : SheafOfModules.{u} (structureSheafRing X'))
    (Q : SheafOfModules.{u} (structureSheafRing X''))
    (ρ : (modulePullback c).obj M ⟶ N) (σ : (modulePullback b).obj N ⟶ Q) :
    (modulePullbackCompIso (b ≫ c) a).hom.app M ≫
        (modulePullback a).map ((modulePullbackCompIso c b).hom.app M ≫
          (modulePullback b).map ρ ≫ σ) =
      ((modulePullbackCompIso c (a ≫ b)).hom.app M ≫ (modulePullback (a ≫ b)).map ρ) ≫
        ((modulePullbackCompIso b a).hom.app N ≫ (modulePullback a).map σ) := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc,
    ← Category.assoc ((modulePullbackCompIso c (a ≫ b)).hom.app M),
    modulePullbackCompIso_assoc c b a M]
  simp only [Functor.comp_map]
  exact (Category.assoc _ _ _).symm

/-- **The cocycle condition for `pullbackIdealSheafCompIso`.** Comparing along a composite of
two open immersions is comparing along each in turn. -/
public theorem pullbackIdealSheafCompIso_comp (k : Z ⟶ U) (m : U ⟶ W) (n : W ⟶ V)
    [IsOpenImmersion m] [IsOpenImmersion n] :
    pullbackIdealSheafCompIso k (m ≫ n) =
      pullbackIdealSheafCompIso (k ≫ m) n ≪≫ pullbackIdealSheafCompIso k m :=
  Iso.ext ((congrArg (fun z => (modulePullbackCompIso (m ≫ n).toLRSHom.toShHom
        k.toLRSHom.toShHom).hom.app (idealSheaf (k ≫ m ≫ n).toLRSHom.toShHom) ≫
      (modulePullback k.toLRSHom.toShHom).map z)
    (pullbackIdealSheafIsoOfEq_cocycle k m n (k ≫ m) rfl (k ≫ m ≫ n) rfl)).trans
    (modulePullbackCompIso_assoc_comp_map k.toLRSHom.toShHom m.toLRSHom.toShHom
      n.toLRSHom.toShHom _ _ _ (pullbackIdealSheafIso n (k ≫ m)).hom
      (pullbackIdealSheafIso m k).hom))

/-- **The cocycle condition with the two composites presented by equations**, which is the form
a factorization statement supplies: comparing along `j = m ≫ n` is comparing along `n` down to
`L = k ≫ m` and then along `m`, up to the canonical transport along `L ≫ n = k ≫ j`. -/
public theorem pullbackIdealSheafCompIso_hom_comp_isoOfCompEq_hom (k : Z ⟶ U) (m : U ⟶ W)
    (n : W ⟶ V) [IsOpenImmersion m] [IsOpenImmersion n] (j : U ⟶ V) [IsOpenImmersion j]
    (hj : m ≫ n = j) (L : Z ⟶ W) (hL : k ≫ m = L) (hE : L ≫ n = k ≫ j) :
    (pullbackIdealSheafCompIso L n).hom ≫ (pullbackIdealSheafIsoOfCompEq k m L hL).hom =
      eqToHom (congrArg (fun f : Z ⟶ V => (modulePullback f.toLRSHom.toShHom).obj
          (idealSheaf f.toLRSHom.toShHom)) hE) ≫ (pullbackIdealSheafCompIso k j).hom := by
  subst hj
  subst hL
  have he : eqToHom (congrArg (fun f : Z ⟶ V => (modulePullback f.toLRSHom.toShHom).obj
      (idealSheaf f.toLRSHom.toShHom)) hE) =
      𝟙 ((modulePullback ((k ≫ m) ≫ n).toLRSHom.toShHom).obj
        (idealSheaf ((k ≫ m) ≫ n).toLRSHom.toShHom)) := rfl
  have hr : pullbackIdealSheafIsoOfCompEq k m (k ≫ m) rfl = pullbackIdealSheafCompIso k m := rfl
  rw [he, hr]
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact (congrArg Iso.hom (pullbackIdealSheafCompIso_comp k m n)).symm

end IdealSheafCocycle

end Stacks.Conormal

end
