module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.StructureSheaf

/-!
# The three site-level inputs of flat base change for the extension algebra are one input

Let `g : X' ⟶ X` be a morphism of schemes and let `W` be a scheme over `X` with structure
morphism `f`.  The base-change clause of [Stacks, Tag 0EY6] asks that
`f'_* 𝒪_{W ×_X X'}` be the extension of scalars `g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}`;  by
`Stacks.FundamentalGroup.isPushout_pushforwardBaseChangeMap_iff_isIso` that clause is
*equivalent* to invertibility of the canonical comparison of algebras
`Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom g W`.  The geometric half of that
invertibility — everything that uses flatness of `g` and quasi-compactness and
quasi-separatedness of `f` — is `Stacks.FundamentalGroup.underlyingModuleFlatBaseChangeIso`:
the `𝒪_{X'}`-module `g^*(f_* 𝒪_W)` *is* the module underlying `f'_* 𝒪_{W ×_X X'}`.

This file closes the gap between the two statements down to a single identification which
mentions no scheme-theoretic hypothesis at all.

**The comparison.**  `algebraPullbackModuleComparison g A` is the canonical morphism
`g^*(module underlying A) ⟶ module underlying (g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'})`.  It is the adjoint
transpose, under `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, of the
module underlying the unit of
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`.  Note that this is one
adjunction, not two:  no factorization of the module pullback into an inverse image followed by
an extension of scalars has to be built, and `Stacks.Sheaves.ModuleAdjunction.extendScalars`
does not occur.

**The bridge.**  `algebraPullbackModuleComparison_comp_underlyingModuleMap` identifies the
composite of the comparison with the module underlying `baseChangeAlgebraHom g W` as the
canonical base-change morphism of the Cartesian square, i.e. as the morphism whose invertibility
`underlyingModuleFlatBaseChangeIso` asserts.  Both sides are morphisms out of a pullback, so the
identity is proved by transposing:  on one side the transpose is the module underlying the
canonical map `f_* 𝒪_W ⟶ (f' ≫ g)_* 𝒪_{W ×_X X'}` of the projection, because
`baseChangeAlgebraHom` is itself defined as a transpose;  on the other it is the mate identity
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pushforward_unit_comp_pushforwardSquareIso`
together with the defining property of `SheafOfModules.pullbackObjUnitToUnit`, and
`underlyingModuleMap_pushforwardAlgebraMapAux` says that those two agree.

**The consequence.**  For flat `g` and quasi-compact quasi-separated `f`, invertibility of
`baseChangeAlgebraHom g W` is *equivalent* to invertibility of the comparison
(`isIso_algebraPullbackModuleComparison_iff`), and — because the comparison is then a split
monomorphism — it already follows from the comparison being an *epimorphism*
(`isIso_baseChangeAlgebraHom_of_epi_comparison`).  Epimorphy of the comparison is the statement
that the sheaf of rings `g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is generated, as an `𝒪_{X'}`-module, by the
image of `g⁻¹A`;  it involves no flatness, no quasi-compactness, and no quasi-separatedness, and
it is the one remaining input of the whole statement.

## Main definitions

* `Stacks.FundamentalGroup.algebraPullbackModuleComparison` — the canonical morphism from the
  module pullback to the module underlying the algebra pullback.
* `Stacks.FundamentalGroup.unitBaseChangeMap` — the canonical base-change morphism of a
  commutative square at a structure sheaf, followed by the identification of the inverse image
  of a structure sheaf with a structure sheaf.  This is the morphism underlying
  `underlyingModuleFlatBaseChangeIso`.

## Main results

* `Stacks.FundamentalGroup.isIso_of_isIso_underlyingModuleMap` — a morphism of algebra sheaves
  whose morphism of underlying modules is invertible is itself invertible.
* `Stacks.FundamentalGroup.algebraPullbackModuleComparison_comp_underlyingModuleMap` — **the
  bridge**: the comparison followed by the module underlying `baseChangeAlgebraHom g W` is the
  canonical base-change morphism of the Cartesian square.
* `Stacks.FundamentalGroup.isIso_baseChangeAlgebraHom_of_epi_comparison` and
  `Stacks.FundamentalGroup.isIso_algebraPullbackModuleComparison_iff` — the base-change clause of
  Tag 0EY6 follows from, and is equivalent to, invertibility of the comparison.
* `Stacks.FundamentalGroup.flatBaseChange_of_epi_comparison` and
  `Stacks.FundamentalGroup.isQuasicoherent_algebraPullback_of_epi_comparison` — **the one
  remaining input gives the whole statement**: epimorphy of the comparison, for every flat morphism and every
  quasi-compact quasi-separated scheme over the base, gives the base-change clause of Tag 0EY6
  in exactly the shape `isQuasicoherent_algebraPullback_of_flatBaseChange` takes as a hypothesis,
  and hence also the `algebraPullback_isQuasicoherent` clause of Tag 01SA along a flat morphism.

## Implementation notes

`isIso_of_isIso_underlyingModuleMap` is proved by hand rather than by exhibiting a functor which
reflects isomorphisms:  restriction of scalars does not change the underlying presheaf of
abelian groups, so a morphism of algebra sheaves and its morphism of underlying modules have
*literally the same* maps on sections, and the two inverse identities of the module isomorphism
read on sections are a two-sided inverse of each map of sections.  Bijectivity then gives
invertibility section by section, `CategoryTheory.NatIso.isIso_of_isIso_app` assembles it, and
`CategoryTheory.fullyFaithfulSheafToPresheaf` and `CategoryTheory.Under.forget` carry it back.

Several steps are in term mode, and not by choice.  A goal mentioning
`SheafOfModules.unit X.ringCatSheaf` is not type-correct under `implicit` transparency, because
`AlgebraicGeometry.Scheme.ringCatSheaf` is spelled `TopCat.Sheaf RingCat ↑X` while
`CategoryTheory.SheafOfModules` expects `CategoryTheory.Sheaf (Opens.grothendieckTopology ↥X)
RingCat`;  the two are definitionally equal and not syntactically equal, so `rw` cannot build a
motive on such a goal at all.  `Eq.trans`, `congrArg` and `exact` check at default transparency
and cross it.  For the same reason `pushforwardSquareIso_hom_app_app` and
`pushforward_map_comp_pushforwardSquareIso_app` are stated with the module and the morphism of
opens as *variables*:  with every object a variable the `simp only` that unfolds
`AffinePushforward.pushforwardSquareIso` into its three components fires, and the concrete
instance is then supplied with `exact`.

Taking the morphism of opens as a variable also removes the only genuinely awkward step.  The
component of `pushforwardSquareIso` over an open `U` is the presheaf map of an `eqToHom`, while
the component of `pushforwardAlgebraMapAux` is `AlgebraicGeometry.Scheme.Hom.appLE`, built from a
`homOfLE`;  the opens of a scheme form a thin category, so `Subsingleton.elim` identifies the two
morphisms inside the general lemma, and the concrete comparison is then closed by `rfl`.

**No `@[stacks]` attribute is placed in this file.**  Tag 0EY6's base-change clause is not proved
here, only reduced further, and a tag on a fraction of a covering set makes the whole tag render
as formalized.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.AlgebraicGeometry

universe u

namespace Stacks.FundamentalGroup

-- `Scheme.unitModule X` is the structure sheaf of `X` read as a module over itself; the statements
-- below spell it `SheafOfModules.unit X.ringCatSheaf`, and `rw` matches syntactically.
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.unitModule

/-! ### Reflecting invertibility from the underlying module -/

section Reflect

variable {X : Scheme.{u}} {A B : AlgebraSheaf X}

/-- A morphism of algebra sheaves whose morphism of underlying modules is invertible is
bijective on sections:  the morphism of underlying modules has literally the same maps on
sections, and its two inverse identities give each of them a two-sided inverse. -/
public theorem bijective_app_of_isIso_underlyingModuleMap (φ : A ⟶ B)
    (h : IsIso (AlgebraSheaf.underlyingModuleMap φ)) (U : (X.Opens)ᵒᵖ) :
    Function.Bijective (φ.right.hom.app U).hom := by
  have hmn := @IsIso.hom_inv_id _ _ _ _ (AlgebraSheaf.underlyingModuleMap φ) h
  have hnm := @IsIso.inv_hom_id _ _ _ _ (AlgebraSheaf.underlyingModuleMap φ) h
  have h1 : ∀ y : A.right.obj.obj U,
      ((@inv _ _ _ _ (AlgebraSheaf.underlyingModuleMap φ) h).val.app U).hom
        ((φ.right.hom.app U).hom y) = y :=
    fun y => congrArg (fun t : AlgebraSheaf.underlyingModule A ⟶
      AlgebraSheaf.underlyingModule A => (t.val.app U).hom y) hmn
  have h2 : ∀ y : B.right.obj.obj U,
      (φ.right.hom.app U).hom
        (((@inv _ _ _ _ (AlgebraSheaf.underlyingModuleMap φ) h).val.app U).hom y) = y :=
    fun y => congrArg (fun t : AlgebraSheaf.underlyingModule B ⟶
      AlgebraSheaf.underlyingModule B => (t.val.app U).hom y) hnm
  exact ⟨Function.LeftInverse.injective h1, fun y => ⟨_, h2 y⟩⟩

/-- **The functor to underlying modules reflects isomorphisms.**  A morphism of sheaves of
commutative `𝒪_X`-algebras whose induced morphism of underlying `𝒪_X`-modules is an isomorphism
is itself an isomorphism. -/
public theorem isIso_of_isIso_underlyingModuleMap (φ : A ⟶ B)
    (h : IsIso (AlgebraSheaf.underlyingModuleMap φ)) : IsIso φ := by
  have happ : ∀ U : (X.Opens)ᵒᵖ, IsIso (φ.right.hom.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_app_of_isIso_underlyingModuleMap φ h U)
  have hpre : IsIso ((sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{u}))
      CommRingCat.{u}).map φ.right) := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ
  have hright : IsIso ((Under.forget X.sheaf).map φ) :=
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{u}))
      CommRingCat.{u}).isIso_of_isIso_map φ.right
  exact isIso_of_reflects_iso φ (Under.forget X.sheaf)

end Reflect

/-! ### The comparison of the module pullback with the module underlying the algebra pullback -/

section Comparison

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **The canonical comparison of the module pullback with the module underlying the algebra
pullback.**  For a sheaf of commutative `𝒪_X`-algebras `A`, this is the morphism of
`𝒪_{X'}`-modules

`g^*(module underlying A) ⟶ module underlying (g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'})`

adjoint to the module underlying the unit `A ⟶ g_*(g⁻¹A ⊗_{g⁻¹𝒪_X} 𝒪_{X'})` of the base-change
adjunction for algebra sheaves. -/
public def algebraPullbackModuleComparison (A : AlgebraSheaf X) :
    (Scheme.Modules.pullback g).obj (AlgebraSheaf.underlyingModule A) ⟶
      AlgebraSheaf.underlyingModule ((algebraPullback g).obj A) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
      (AlgebraSheaf.underlyingModule A)
      (AlgebraSheaf.underlyingModule ((algebraPullback g).obj A))).symm
    (AlgebraSheaf.underlyingModuleMap
      ((algebraPullbackPushforwardAdjunction g).unit.app A))

/-- The adjoint transpose of the comparison is the module underlying the unit of the base-change
adjunction for algebra sheaves. -/
public theorem homEquiv_algebraPullbackModuleComparison (A : AlgebraSheaf X) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (algebraPullbackModuleComparison g A) =
      AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app A) :=
  Equiv.apply_symm_apply _ _

/-- The transpose of `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom` is the canonical map
on pushed-forward structure sheaves induced by the projection `W ×_X X' ⟶ W`:  that is how it is
defined. -/
public theorem unit_comp_map_baseChangeAlgebraHom (W : Over X) :
    (algebraPullbackPushforwardAdjunction g).unit.app (pushforwardAlgebra W.hom) ≫
        (algebraPushforward g).map (baseChangeAlgebraHom g W) =
      pushforwardAlgebraMap (baseChangeProjection g W) :=
  (Adjunction.homEquiv_unit (algebraPullbackPushforwardAdjunction g) _ _ _).symm.trans
    (((algebraPullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _)

/-- The transpose of the comparison followed by the module underlying `baseChangeAlgebraHom` is
the module underlying the canonical map of pushed-forward structure sheaves of the projection.
Restriction of scalars does not change the underlying presheaf of abelian groups, so the direct
image of a morphism of underlying modules *is* the morphism of underlying modules of the direct
image, and the transpose is computed by the adjunction for algebra sheaves. -/
public theorem homEquiv_algebraPullbackModuleComparison_comp (W : Over X) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom) ≫
          AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W)) =
      AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMap (baseChangeProjection g W)) := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_algebraPullbackModuleComparison]
  have h1 : AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app (pushforwardAlgebra W.hom)) ≫
      (Scheme.Modules.pushforward g).map
        (AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W)) =
      AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app (pushforwardAlgebra W.hom) ≫
          (algebraPushforward g).map (baseChangeAlgebraHom g W)) := rfl
  exact h1.trans (congrArg AlgebraSheaf.underlyingModuleMap
    (unit_comp_map_baseChangeAlgebraHom g W))

end Comparison

/-! ### The transpose of the geometric base-change morphism -/

section Square

variable {W W' X X' : Scheme.{u}} {f : W ⟶ X} {f' : W' ⟶ X'} {g : X' ⟶ X} {g' : W' ⟶ W}

/-- **The canonical base-change morphism at a structure sheaf.**  For a commutative square
`g' ≫ f = f' ≫ g` this is `g^* f_* 𝒪_W ⟶ f'_* 𝒪_{W'}`:  the base-change morphism of the square
at the unit module, followed by the direct image of the identification of `(g')^* 𝒪_W` with
`𝒪_{W'}`.  It is the morphism underlying
`Stacks.FundamentalGroup.underlyingModuleFlatBaseChangeIso`. -/
public def unitBaseChangeMap (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (Scheme.Modules.pushforward f').obj (SheafOfModules.unit W'.ringCatSheaf) :=
  (AffinePushforward.baseChangeNatTrans w).app (SheafOfModules.unit W.ringCatSheaf) ≫
    (Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').hom

/-- The transpose of the identification of `(g')^* 𝒪_W` with `𝒪_{W'}` is the canonical morphism
`𝒪_W ⟶ (g')_* 𝒪_{W'}` of unit modules:  this is the defining property of
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, of which
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` is the inverse-free form. -/
public theorem unit_comp_map_pullbackUnitIso :
    (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
          (SheafOfModules.unit W.ringCatSheaf) ≫
        (Scheme.Modules.pushforward g').map (Scheme.Modules.pullbackUnitIso g').hom =
      SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom := by
  have : (SheafOfModules.pushforward g'.toRingCatSheafHom).IsRightAdjoint := by
    show (Scheme.Modules.pushforward g').IsRightAdjoint
    infer_instance
  rw [← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g'.toRingCatSheafHom, Adjunction.homEquiv_unit]
  rfl

/-- **The transpose of the canonical base-change morphism at a structure sheaf.**  It is the
direct image along `f` of the canonical morphism `𝒪_W ⟶ (g')_* 𝒪_{W'}`, followed by the
identification of the two composite direct images around the square.  The proof is the mate
identity for `AffinePushforward.baseChangeNatTrans`, naturality of the square identification,
and `unit_comp_map_pullbackUnitIso`. -/
public theorem homEquiv_unitBaseChangeMap (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ (unitBaseChangeMap w) =
      (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom) ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app
          (SheafOfModules.unit W'.ringCatSheaf) := by
  have nat : (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pushforward g').map (Scheme.Modules.pullbackUnitIso g').hom) ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app
          (SheafOfModules.unit W'.ringCatSheaf) =
      (AffinePushforward.pushforwardSquareIso w).hom.app
          ((Scheme.Modules.pullback g').obj (SheafOfModules.unit W.ringCatSheaf)) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').hom) :=
    (AffinePushforward.pushforwardSquareIso w).hom.naturality _
  rw [unitBaseChangeMap, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    ← FlatBaseChangeCohomology.pushforward_unit_comp_pushforwardSquareIso w
      (SheafOfModules.unit W.ringCatSheaf),
    Category.assoc, ← nat, ← Category.assoc, ← Functor.map_comp,
    unit_comp_map_pullbackUnitIso]
  rfl

/-- The sections over an open `U` of the identification of the two composite direct images
around a commutative square:  it is the presheaf map of *any* morphism of opens
`(f' ≫ g) ⁻¹ᵁ U ⟶ g' ⁻¹ᵁ (f ⁻¹ᵁ U)`, the opens of a scheme forming a thin category. -/
public theorem pushforwardSquareIso_hom_app_app (w : g' ≫ f = f' ≫ g) (N : W'.Modules)
    (U : X.Opens) (i : ((f' ≫ g) ⁻¹ᵁ U) ⟶ (g' ⁻¹ᵁ (f ⁻¹ᵁ U))) :
    ((AffinePushforward.pushforwardSquareIso w).hom.app N).app U = N.presheaf.map i.op := by
  simp only [AffinePushforward.pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app]
  exact (Category.id_comp _).trans ((Category.comp_id _).trans
    (congrArg N.presheaf.map (Subsingleton.elim _ _)))

/-- The sections over an open `U` of the direct image along `f` of a morphism
`M ⟶ (g')_* N`, followed by the square identification. -/
public theorem pushforward_map_comp_pushforwardSquareIso_app {M : W.Modules} {N : W'.Modules}
    (η : M ⟶ (Scheme.Modules.pushforward g').obj N) (w : g' ≫ f = f' ≫ g) (U : X.Opens)
    (i : ((f' ≫ g) ⁻¹ᵁ U) ⟶ (g' ⁻¹ᵁ (f ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforward f).map η ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app N).app U =
      η.app (f ⁻¹ᵁ U) ≫ N.presheaf.map i.op := by
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    pushforwardSquareIso_hom_app_app w N U i]
  rfl

/-- **The two canonical morphisms `f_* 𝒪_W ⟶ (f' ≫ g)_* 𝒪_{W'}` of a commutative square
agree.**  The one built from unit modules and the square identification is the module underlying
the one built from the map on pushed-forward structure sheaves.  On sections over `U` both are
the map on sections of `g'` over `f ⁻¹ᵁ U` followed by a restriction, and the two restrictions
are the same morphism of opens. -/
public theorem underlyingModuleMap_pushforwardAlgebraMapAux (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pushforward f).map
        (SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom) ≫
      (AffinePushforward.pushforwardSquareIso w).hom.app
        (SheafOfModules.unit W'.ringCatSheaf) =
      AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMapAux f g' ≫ eqToHom (congrArg pushforwardAlgebra w)) := by
  refine Scheme.Modules.hom_ext _ _ (fun U => ?_)
  have hle : (f' ≫ g) ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U) := by rw [← w]; exact le_rfl
  refine (pushforward_map_comp_pushforwardSquareIso_app
    (SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom) w U (homOfLE hle)).trans ?_
  have hR : (AlgebraSheaf.underlyingModuleMap
        (pushforwardAlgebraMapAux f g' ≫ eqToHom (congrArg pushforwardAlgebra w))).app U =
      AddCommGrpCat.ofHom (RingHom.toAddMonoidHom (CommRingCat.Hom.hom
        ((pushforwardAlgebraMapAux f g' ≫
          eqToHom (congrArg pushforwardAlgebra w)).right.hom.app (op U)))) := rfl
  refine Eq.trans ?_ hR.symm
  refine Eq.trans ?_ (congrArg (fun t => AddCommGrpCat.ofHom
      (RingHom.toAddMonoidHom (CommRingCat.Hom.hom t)))
    (pushforwardAlgebraMapAux_app f g' (f' ≫ g) w U hle)).symm
  rfl

end Square

/-! ### The bridge, and the reduction of the base-change clause to one comparison -/

section Bridge

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (W : Over X)

/-- **The bridge.**  The canonical comparison of the module pullback with the module underlying
the algebra pullback, followed by the module underlying the canonical comparison of algebras, is
the canonical base-change morphism `g^* f_* 𝒪_W ⟶ f'_* 𝒪_{W ×_X X'}` of the Cartesian square.
Both are morphisms out of a module pullback, so the identity is an identity of their adjoint
transposes, and both transposes are the canonical map `f_* 𝒪_W ⟶ (f' ≫ g)_* 𝒪_{W ×_X X'}` of the
projection. -/
public theorem algebraPullbackModuleComparison_comp_underlyingModuleMap :
    algebraPullbackModuleComparison g (pushforwardAlgebra W.hom) ≫
        AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W) =
      unitBaseChangeMap (IsPullback.of_hasPullback W.hom g).w := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective ?_
  refine (homEquiv_algebraPullbackModuleComparison_comp g W).trans ?_
  refine Eq.trans ?_
    (homEquiv_unitBaseChangeMap (IsPullback.of_hasPullback W.hom g).w).symm
  exact (underlyingModuleMap_pushforwardAlgebraMapAux
    (IsPullback.of_hasPullback W.hom g).w).symm

/-- The bridge, with the target named as the isomorphism
`Stacks.FundamentalGroup.underlyingModuleFlatBaseChangeIso`. -/
public theorem algebraPullbackModuleComparison_comp_underlyingModuleMap_eq_iso
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    algebraPullbackModuleComparison g (pushforwardAlgebra W.hom) ≫
        AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W) =
      (underlyingModuleFlatBaseChangeIso g W).hom :=
  algebraPullbackModuleComparison_comp_underlyingModuleMap g W

/-- **The comparison is a split monomorphism** when `g` is flat and the structure morphism of `W`
is quasi-compact and quasi-separated:  composing it with the module underlying
`baseChangeAlgebraHom g W` gives the isomorphism `underlyingModuleFlatBaseChangeIso g W`. -/
public theorem isSplitMono_algebraPullbackModuleComparison
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    IsSplitMono (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom)) :=
  IsSplitMono.mk' ⟨AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W) ≫
    (underlyingModuleFlatBaseChangeIso g W).inv,
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (underlyingModuleFlatBaseChangeIso g W).inv)
          (algebraPullbackModuleComparison_comp_underlyingModuleMap_eq_iso g W)).trans
        (underlyingModuleFlatBaseChangeIso g W).hom_inv_id)⟩

/-- The comparison followed by the module underlying `baseChangeAlgebraHom` is invertible. -/
private theorem isIso_comparison_comp_underlyingModuleMap
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    IsIso (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom) ≫
      AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W)) := by
  rw [algebraPullbackModuleComparison_comp_underlyingModuleMap_eq_iso]
  infer_instance

/-- **The base-change clause of [Stacks, Tag 0EY6] follows from invertibility of the
comparison.**  For a flat `g` and a quasi-compact quasi-separated scheme `W` over `X`, if the
canonical comparison `g^*(f_* 𝒪_W) ⟶ g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is an isomorphism then the
canonical comparison of algebras `baseChangeAlgebraHom g W` is an isomorphism. -/
public theorem isIso_baseChangeAlgebraHom_of_isIso_comparison
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (h : IsIso (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom))) :
    IsIso (baseChangeAlgebraHom g W) := by
  have := isIso_comparison_comp_underlyingModuleMap g W
  have := h
  exact isIso_of_isIso_underlyingModuleMap (baseChangeAlgebraHom g W)
    (IsIso.of_isIso_comp_left (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom))
      (AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W)))

/-- **The base-change clause of [Stacks, Tag 0EY6] follows from the comparison being an
epimorphism.**  The comparison is a split monomorphism by
`isSplitMono_algebraPullbackModuleComparison`, so it is enough that it be epi — which is the
assertion that `g⁻¹(f_* 𝒪_W) ⊗_{g⁻¹𝒪_X} 𝒪_{X'}` is generated as an `𝒪_{X'}`-module by the image
of `g⁻¹(f_* 𝒪_W)`, a statement about sheaves of rings on a site which mentions neither flatness
nor quasi-compactness. -/
public theorem isIso_baseChangeAlgebraHom_of_epi_comparison
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (h : Epi (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom))) :
    IsIso (baseChangeAlgebraHom g W) :=
  have := h
  have := isSplitMono_algebraPullbackModuleComparison g W
  isIso_baseChangeAlgebraHom_of_isIso_comparison g W
    (isIso_of_epi_of_isSplitMono (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom)))

/-- **Invertibility of the comparison is equivalent to the base-change clause of
[Stacks, Tag 0EY6].**  So the hypothesis of `isIso_baseChangeAlgebraHom_of_isIso_comparison` is
not a strengthening of the tag's content:  it is a reformulation of it which mentions no
scheme-theoretic property of `g` or of `f`, those having been consumed by
`underlyingModuleFlatBaseChangeIso`. -/
public theorem isIso_algebraPullbackModuleComparison_iff
    [Flat g] [QuasiCompact W.hom] [QuasiSeparated W.hom] :
    IsIso (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom)) ↔
      IsIso (baseChangeAlgebraHom g W) := by
  refine ⟨isIso_baseChangeAlgebraHom_of_isIso_comparison g W, fun h => ?_⟩
  have hm : IsIso (AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W)) :=
    have := h
    (AlgebraSheaf.underlyingModuleFunctor X').map_isIso (baseChangeAlgebraHom g W)
  have := isIso_comparison_comp_underlyingModuleMap g W
  exact IsIso.of_isIso_comp_right
    (algebraPullbackModuleComparison g (pushforwardAlgebra W.hom))
    (AlgebraSheaf.underlyingModuleMap (baseChangeAlgebraHom g W))

end Bridge

/-! ### The one remaining input gives the whole statement -/

section Closure

/-- **The comparison being an epimorphism, for every flat morphism and every quasi-compact
quasi-separated scheme over the base, is the base-change clause of [Stacks, Tag 0EY6].**  The
conclusion is stated with exactly the binders, instance arguments and universe of the hypothesis
of `Stacks.FundamentalGroup.isQuasicoherent_algebraPullback_of_flatBaseChange`, so it discharges
that hypothesis by `exact`. -/
public theorem flatBaseChange_of_epi_comparison
    (H : ∀ {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] (V : Over Y)
      [QuasiCompact V.hom] [QuasiSeparated V.hom],
      Epi (algebraPullbackModuleComparison q (pushforwardAlgebra V.hom)))
    {V Y Y' : Scheme.{u}} (f : V ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (q : Y' ⟶ Y) [Flat q] :
    IsPushout
      ((TopCat.Sheaf.pullback CommRingCat q.base).map (pushforwardAlgebra f).hom)
      (inverseImageStructureMap q)
      (pushforwardBaseChangeMap q (Over.mk f))
      (pushforwardAlgebra ((Over.pullback q).obj (Over.mk f)).hom).hom :=
  have h1 : QuasiCompact (Over.mk f).hom := ‹QuasiCompact f›
  have h2 : QuasiSeparated (Over.mk f).hom := ‹QuasiSeparated f›
  (isPushout_pushforwardBaseChangeMap_iff_isIso q (Over.mk f)).mpr
    (isIso_baseChangeAlgebraHom_of_epi_comparison q (Over.mk f) (H q (Over.mk f)))

/-- **The comparison being an epimorphism also gives the `algebraPullback_isQuasicoherent` clause
of [Stacks, Tag 01SA] along a flat morphism**, which is what makes the pulled-back extension
algebra of [Stacks, Tag 0EY6] statable.  Composed with `flatBaseChange_of_epi_comparison` this
says that epimorphy of the comparison is the only remaining input of the whole statement. -/
public theorem isQuasicoherent_algebraPullback_of_epi_comparison
    (H : ∀ {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q] (V : Over Y)
      [QuasiCompact V.hom] [QuasiSeparated V.hom],
      Epi (algebraPullbackModuleComparison q (pushforwardAlgebra V.hom)))
    {X X' : Scheme.{u}} (g : X' ⟶ X) [Flat g] (A : AlgebraSheaf X) [A.IsQuasicoherent] :
    AlgebraSheaf.IsQuasicoherent ((algebraPullback g).obj A) :=
  isQuasicoherent_algebraPullback_of_flatBaseChange g
    (fun f _ _ q _ => flatBaseChange_of_epi_comparison H f q) A

end Closure

end Stacks.FundamentalGroup

end
