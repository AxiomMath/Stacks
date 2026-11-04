module

public import StacksFrontier.AlgebraicGeometry.Conormal.AffineModel
public import StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictIdealSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections of the pushforward conormal sheaf on an affine open

Let `i : Z ⟶ X` be an immersion of schemes factored as a closed immersion `i' : Z ⟶ U` through an
open subscheme `U` of `X`, let `V ⊆ U` be an affine open and suppose the scheme-theoretic
intersection `Z ∩ V` is `Spec (Γ(U, V) ⧸ I)` for an ideal `I ⊆ Γ(U, V)`. This file identifies the
sections over `V` of the pushforward `(i')_* 𝒞_{Z/X}` of the conormal sheaf with `I/I²`.

This is the glue between `StacksFrontier.AlgebraicGeometry.Conormal.AffineModel`, which computes the
global sections of the pushforward conormal sheaf of `Spec (R ⧸ I) ⟶ Spec R`, and the statement of
[Stacks Project, Tag 01R3] part (1), which is about an arbitrary immersion. The module docstring of
`AffineModel` lists the two comparisons that were missing; both are now available, and this file is
their composition:

* locality of the conormal sheaf on the ambient space, from
  `StacksFrontier.AlgebraicGeometry.Conormal.RestrictIdealSheaf`, which turns `𝒞_{Z/X}` restricted to
  `(i')⁻¹V` into the conormal sheaf of the *restricted* morphism `i' ∣_ V`;
* transport along an isomorphism square, from
  `StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare`, which turns that into the conormal sheaf of
  `Spec (Γ(U, V) ⧸ I) ⟶ Spec Γ(U, V)` through `AlgebraicGeometry.IsAffineOpen.isoSpec`.

## Main definitions

* `Stacks.Immersion.conormalSheafMorphismRestrictIso` is `𝒞_{Z/X}|_{(i')⁻¹V} ≅ 𝒞_{i' ∣_ V}`.
* `Stacks.Immersion.pushforwardConormalScalarIso` is the scalar bookkeeping of the affine
  computation: the sections of `(i')_* 𝒞_{Z/X}` over `V`, read as a `Γ(U, V)`-module through
  `AlgebraicGeometry.Scheme.ΓSpecIso`.
* `Stacks.Immersion.pushforwardConormalIsoCotangent` is [Stacks Project, Tag 01R3] part (1)'s
  affine computation: `((i')_* 𝒞_{Z/X})(V) ≅ I/I²` as `Γ(U, V)`-modules.

## Main results

* `Stacks.Immersion.pushforwardConormalScalarIso_hom_apply` says that the scalar bookkeeping is
  restriction of sections along an equality of opens and nothing else. It holds by `rfl` only
  because the ring-map identity is passed as the hypothesis of
  `CategoryTheory.ModuleCat.restrictScalarsComp'App`; see the implementation notes.

* `RingedSpaceModuleAdjunction.unit_modulePullbackComp` reads the composition isomorphism
  for pullbacks on the units of the two adjunctions. It is the first step of the two
  unit-compatibility statements that the *normalization* of the affine computation still needs;
  see the end of these notes.
* `AlgebraicGeometry.RingedSpace.restrictHom_eq_morphismRestrict` identifies the ringed-space
  restriction `AlgebraicGeometry.RingedSpace.restrictHom` of a morphism of schemes with Mathlib's
  scheme-level `AlgebraicGeometry.morphismRestrict`. The two are built differently —
  `morphismRestrict` goes through a pullback — so this is not a definitional identity; both
  composites with the monomorphism `ι_V` are the same, which proves it.
* `Stacks.Immersion.morphismRestrict_comp_isoSpec` turns the statement's hypothesis on
  `CategoryTheory.Limits.pullback.snd` into the isomorphism square that the transport consumes.
* `Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop` is the ring-map identity that makes the two
  `Γ(U, V)`-module structures on the sections agree: restricting `(i')^♯` to the affine open and
  going around through `Spec Γ(U, V)` give the same map.
## Implementation notes

Every object in sight is a module over a different ring: the sections of a pushforward are the
sections of the source sheaf with scalars restricted along the structure-sheaf map, and the affine
model lands in `ModuleCat R` through `AlgebraicGeometry.moduleSpecΓFunctor`, which restricts
scalars along `AlgebraicGeometry.Scheme.ΓSpecIso`. The underlying modules are *the same*
throughout — restriction of scalars does not change the carrier — so the whole comparison is
assembled from `CategoryTheory.ModuleCat.restrictScalarsComp'App` together with one equality of
ring maps, `Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop`. No semilinear algebra is needed.

That equality of ring maps is handed to `CategoryTheory.ModuleCat.restrictScalarsComp'App` **as
its `hgf` hypothesis**, not wrapped in a separate `CategoryTheory.eqToIso`. The two composites are
equal either way, but only this one has an underlying map that reduces to the identity, because
`CategoryTheory.eqToHom` of a non-`rfl` equality does not reduce — and that is exactly what
`Stacks.Immersion.pushforwardConormalScalarIso_hom_apply` needs, and with it any generator formula
for the affine computation.

The one place where sections genuinely move is the passage from the open `(i')⁻¹V` of `Z` to the
top open of its restriction, whose sections are those over `ι ''ᵁ ⊤`. That open equals `(i')⁻¹V`,
by `TopologicalSpace.Opens.isOpenEmbedding_obj_top`, and
`AlgebraicGeometry.RingedSpace.isIso_val_map_op_eqToHom` says the corresponding restriction map of
a sheaf of modules is an isomorphism.

What is **not** proved here is the generator formula for
`Stacks.Immersion.pushforwardConormalIsoCotangent`: that it carries the image of a section of the
ideal sheaf under `Stacks.Conormal.conormalQuotientMap` to that section modulo `I²`. Each
ingredient of the composite is pinned on its own — the affine model
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso` by
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso_unit_toOpen`, which is already a generator
formula, and the transports by their ideal-sheaf characterisations — but the *composite* is not,
because two unit-compatibility statements are missing: that
`Stacks.ClosedImmersion.restrictConormalSheafIso` and
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare` carry the unit of one
pullback-pushforward adjunction to the unit of the other. Both reduce, through
`RingedSpaceModuleAdjunction.unit_modulePullbackComp` proved below, to the mate
correspondence for `RingedSpaceModuleAdjunction.modulePullbackComp`; neither is carried out
here.

**Both of those unit-compatibility statements are now available elsewhere**, so the only thing
still missing for the generator formula of `Stacks.Immersion.pushforwardConormalIsoCotangent` is
its assembly. They are `Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit` of
`StacksFrontier/AlgebraicGeometry/Conormal/RestrictSquareUnit.lean` — with the scheme-level
restatement `Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit_scheme` next to it — and
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare_comp_unit` of
`StacksFrontier/AlgebraicGeometry/Conormal/SquareMate.lean`, whose reading on a global section is
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare_val_app_unit` of
`StacksFrontier/AlgebraicGeometry/Conormal/AffineGenerators.lean`.

A consumer that wants the affine computation of [Stacks Project, Tag 01R3] part (1) **pinned**
should not wait for that assembly: `Stacks.Conormal.affineConormalIsoCotangent` of
`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/AffineIdentification.lean` is the same
identification already pinned on generators, by
`Stacks.Conormal.affineConormalIsoCotangent_inv_toCotangent_canonical`, and compatible with
restriction of sections, by `Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Equal morphisms of schemes have equal underlying morphisms of ringed spaces. -/
private theorem toShHom_congr {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) :
    f.toLRSHom.toShHom = g.toLRSHom.toShHom :=
  congrArg (fun g : A ⟶ B => g.toLRSHom.toShHom) h

/-- **The ringed-space restriction of a morphism of schemes is the scheme-level restriction.**
`AlgebraicGeometry.RingedSpace.restrictHom` and Mathlib's `AlgebraicGeometry.morphismRestrict` are
built in different ways — the latter through `CategoryTheory.Limits.pullback` and
`AlgebraicGeometry.pullbackRestrictIsoRestrict` — so this is not a definitional identity.

Both become the same morphism after composing with the open immersion `ι_U`, by
`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict` and
`AlgebraicGeometry.morphismRestrict_ι` respectively, and `ι_U` is a monomorphism of ringed spaces;
cancelling it proves the identity. -/
theorem restrictHom_eq_morphismRestrict {Z X : Scheme.{u}} (f : Z ⟶ X) (U : X.Opens) :
    restrictHom f.toLRSHom.toShHom U = (f ∣_ U).toLRSHom.toShHom := by
  refine (cancel_mono (X.toLocallyRingedSpace.toRingedSpace.ofRestrict U.isOpenEmbedding)).1 ?_
  rw [restrictHom_comp_ofRestrict]
  exact (toShHom_congr (morphismRestrict_ι f U)).symm

/-- **An isomorphism of schemes is an isomorphism of the underlying ringed spaces.** Passing from
schemes to ringed spaces is functorial on the nose, so both triangles are the image of the
corresponding triangle for schemes. -/
def ringedSpaceIso {A B : Scheme.{u}} (f : A ≅ B) :
    A.toLocallyRingedSpace.toRingedSpace ≅ B.toLocallyRingedSpace.toRingedSpace where
  hom := f.hom.toLRSHom.toShHom
  inv := f.inv.toLRSHom.toShHom
  hom_inv_id := congrArg (fun g : A ⟶ A => g.toLRSHom.toShHom) f.hom_inv_id
  inv_hom_id := congrArg (fun g : B ⟶ B => g.toLRSHom.toShHom) f.inv_hom_id

/-- The forward direction of `AlgebraicGeometry.RingedSpace.ringedSpaceIso`. -/
@[simp]
theorem ringedSpaceIso_hom {A B : Scheme.{u}} (f : A ≅ B) :
    (ringedSpaceIso f).hom = f.hom.toLRSHom.toShHom := rfl

/-- The backward direction of `AlgebraicGeometry.RingedSpace.ringedSpaceIso`. -/
@[simp]
theorem ringedSpaceIso_inv {A B : Scheme.{u}} (f : A ≅ B) :
    (ringedSpaceIso f).inv = f.inv.toLRSHom.toShHom := rfl

/-- **Restriction of sections along an equality of opens is an isomorphism.** For a sheaf of
modules on a ringed space and two equal opens, the restriction map between their sections is
invertible.

This cannot be stated as an isomorphism of `CategoryTheory.ModuleCat` objects directly: the two
sections live over different (though equal) rings, and the restriction map of a presheaf of
modules carries a `CategoryTheory.ModuleCat.restrictScalars` in its type. -/
theorem isIso_val_map_op_eqToHom {Zr : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Zr))
    {A B : Opens Zr.carrier} (h : A = B) : IsIso (M.val.map (eqToHom h).op) := by
  subst h
  rw [eqToHom_refl, op_id, M.val.map_id]
  infer_instance

/-- `AlgebraicGeometry.RingedSpace.isIso_val_map_op_eqToHom` as a bundled isomorphism.

The type is deliberately left inferred: writing it out would mean naming the
`CategoryTheory.ModuleCat.restrictScalars` that the restriction map of a presheaf of modules
carries in its type, and instance resolution does not see through the two spellings of the ring
of sections. -/
def valMapEqToIso {Zr : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing Zr))
    {A B : Opens Zr.carrier} (h : A = B) :=
  @asIso _ _ _ _ _ (isIso_val_map_op_eqToHom M h)

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceModuleAdjunction

/-- **`RingedSpaceModuleAdjunction.modulePullbackComp` read on units.** The unit of
`g^* ⊣ g_*` followed by `g_*` of the unit of `f^* ⊣ f_*` is the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`
followed by `(f ≫ g)_*` of the composition isomorphism for pullbacks.

This is the only description of `RingedSpaceModuleAdjunction.modulePullbackComp` a consumer
needs, and it is exactly what its characterisation
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom` says once the mate
correspondence is read on units by `CategoryTheory.unit_conjugateEquiv_symm`. The composition
isomorphism for *pushforwards* has identity components, which is why no comparison survives on the
left-hand side. -/
theorem unit_modulePullbackComp {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (M : SheafOfModules.{u} (structureSheafRing W)) :
    (modulePullbackPushforwardAdjunction g).unit.app M ≫
        (modulePushforward g).map
          ((modulePullbackPushforwardAdjunction f).unit.app ((modulePullback g).obj M)) =
      (modulePullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (modulePushforward (f ≫ g)).map ((modulePullbackComp f g).hom.app M) := by
  have hc : ((conjugateEquiv ((modulePullbackPushforwardAdjunction g).comp
          (modulePullbackPushforwardAdjunction f))
        (modulePullbackPushforwardAdjunction (f ≫ g))).symm)
      (modulePushforwardComp f g).hom = (modulePullbackComp f g).hom :=
    (Equiv.symm_apply_eq _).mpr (conjugateEquiv_modulePullbackComp_hom f g).symm
  have h := CategoryTheory.unit_conjugateEquiv_symm
    ((modulePullbackPushforwardAdjunction g).comp (modulePullbackPushforwardAdjunction f))
    (modulePullbackPushforwardAdjunction (f ≫ g)) (modulePushforwardComp f g).hom M
  rw [hc, Adjunction.comp_unit_app, modulePushforwardComp_hom_app] at h
  exact (Category.comp_id _).symm.trans h

end RingedSpaceModuleAdjunction

namespace Stacks.Immersion

/-! ### The conormal sheaf of a restricted factorization -/

/-- **`𝒞_{Z/X}|_{(i')⁻¹V} ≅ 𝒞_{i' ∣_ V}`.** For a closed-immersion factorization `i = i' ≫ ι_U` of
an immersion of schemes and an open `V` of `U`, the conormal sheaf of `i` restricted to
`(i')⁻¹V` is the conormal sheaf of the restricted morphism `i' ∣_ V`.

It is `Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` — the first assertion of
[Stacks Project, Tag 01R3] part (1) — restricted to `(i')⁻¹V`, followed by
`Stacks.ClosedImmersion.restrictConormalSheafIso`, the statement that the conormal sheaf is local
on the ambient space, read at the scheme-level restriction through
`AlgebraicGeometry.RingedSpace.restrictHom_eq_morphismRestrict`.

Both inputs are pinned (by
`Stacks.Immersion.conormalSheafFactorIso_hom_comp_conormalSheafIsoPullbackIdealSheaf_hom` and
`Stacks.ClosedImmersion.restrictConormalSheafIso_hom_comp_pullback_ι`), and the third factor is a
`CategoryTheory.eqToIso` along an equality of morphisms, so this composite is canonical. -/
def conormalSheafMorphismRestrictIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) (V : U.toScheme.Opens) :
    (moduleRestrict Z.toLocallyRingedSpace.toRingedSpace (i' ⁻¹ᵁ V)).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≅
      conormalSheaf (i' ∣_ V).toLRSHom.toShHom :=
  (moduleRestrict Z.toLocallyRingedSpace.toRingedSpace (i' ⁻¹ᵁ V)).mapIso
      (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac) ≪≫
    restrictConormalSheafIso i'.toLRSHom.toShHom V ≪≫
    eqToIso (congrArg (fun p => conormalSheaf p) (restrictHom_eq_morphismRestrict i' V))

/-! ### The isomorphism square over an affine open -/

/-- **The isomorphism square the affine computation is transported along.** The hypothesis of
[Stacks Project, Tag 01R3] part (2) is given in terms of
`CategoryTheory.Limits.pullback.snd i' V.ι`; composing with
`AlgebraicGeometry.pullbackRestrictIsoRestrict` turns it into a statement about the restricted
morphism `i' ∣_ V`, which is the one whose conormal sheaf is computed by
`Stacks.Immersion.conormalSheafMorphismRestrictIso`. -/
theorem morphismRestrict_comp_isoSpec {Z Y : Scheme.{u}} (i' : Z ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(Y, V)) (e : pullback i' V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i' V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(Y, V) I) :
    (i' ∣_ V) ≫ hV.isoSpec.hom =
      ((pullbackRestrictIsoRestrict i' V).symm ≪≫ e).hom ≫ quotImmersion Γ(Y, V) I := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he,
    ← pullbackRestrictIsoRestrict_hom_morphismRestrict i' V, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- `Stacks.Immersion.morphismRestrict_comp_isoSpec` on the underlying ringed spaces, which is the
form `Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare` consumes. -/
theorem morphismRestrict_comp_isoSpec_toShHom {Z Y : Scheme.{u}} (i' : Z ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(Y, V)) (e : pullback i' V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i' V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(Y, V) I) :
    (i' ∣_ V).toLRSHom.toShHom ≫ (ringedSpaceIso hV.isoSpec).hom =
      (ringedSpaceIso ((pullbackRestrictIsoRestrict i' V).symm ≪≫ e)).hom ≫
        (quotImmersion Γ(Y, V) I).toLRSHom.toShHom :=
  toShHom_congr (morphismRestrict_comp_isoSpec i' V hV I e he)

/-! ### The comparison of the two module structures -/

/-- **The ring-map identity behind the affine computation.** Restricting a section of `𝒪_Y` over an
affine open `V` along `i'` and then to the top open of `(i')⁻¹V` is the same as transporting it to
`Γ(Spec Γ(Y, V), ⊤)` and pulling it back along `(i' ∣_ V) ≫ isoSpec`.

Both sides are `AlgebraicGeometry.Scheme.Hom.appLE` of `i'` between the same two opens:
`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop` cancels the `Spec`-`Γ` adjunction isomorphism
against `AlgebraicGeometry.Scheme.Opens.topIso`, and
`AlgebraicGeometry.morphismRestrict_appTop` rewrites the restricted morphism. -/
theorem appLE_eq_ΓSpecIso_inv_comp_appTop {Z Y : Scheme.{u}} (i' : Z ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) :
    i'.app V ≫ Z.presheaf.map (eqToHom (i' ⁻¹ᵁ V).ι_image_top).op =
      (Scheme.ΓSpecIso Γ(Y, V)).inv ≫ ((i' ∣_ V) ≫ hV.isoSpec.hom).appTop := by
  rw [Scheme.Hom.comp_appTop, hV.isoSpec_hom_appTop, ← Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Scheme.Opens.topIso_inv, morphismRestrict_appTop,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map]
  exact (Scheme.Hom.map_appLE' i' _ V.ι_image_top).symm

/-- `Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop` as an equality of ring homomorphisms,
which is the form `CategoryTheory.ModuleCat.restrictScalars` consumes. -/
theorem appLE_eq_ΓSpecIso_inv_comp_appTop_hom {Z Y : Scheme.{u}} (i' : Z ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) :
    (Z.presheaf.map (eqToHom (i' ⁻¹ᵁ V).ι_image_top).op).hom.comp (i'.app V).hom =
      (((i' ∣_ V) ≫ hV.isoSpec.hom).appTop).hom.comp (Scheme.ΓSpecIso Γ(Y, V)).inv.hom :=
  (CommRingCat.hom_comp _ _).symm.trans
    ((congrArg CommRingCat.Hom.hom (appLE_eq_ΓSpecIso_inv_comp_appTop i' V hV)).trans
      (CommRingCat.hom_comp _ _))

/-! ### The affine computation -/

/-- **The scalar bookkeeping of the affine computation of part (1).** The sections of
`(i')_* 𝒞_{Z/X}` over `V` are a module over `Γ(U, V)` through `(i')^♯_V`; the sections of the
sheaf transported to `Spec Γ(U, V)` over the top open are a module over `Γ(U, V)` through
`AlgebraicGeometry.Scheme.ΓSpecIso`. The underlying modules are the same — restriction of scalars
does not change the carrier — and the two scalar actions agree by
`Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop_hom`.

That ring-map identity is used *as the hypothesis of*
`CategoryTheory.ModuleCat.restrictScalarsComp'App` rather than as a separate
`CategoryTheory.eqToIso`: the two composites are equal, but only this one has an underlying map
that reduces to the identity, which is what
`Stacks.Immersion.pushforwardConormalScalarIso_hom_apply` needs. The one place where sections
genuinely move is the passage from `(i')⁻¹V` to the top open of its restriction, whose sections
are those over `ι ''ᵁ ⊤`; that open equals `(i')⁻¹V`, and
`AlgebraicGeometry.RingedSpace.isIso_val_map_op_eqToHom` makes the restriction map invertible. -/
def pushforwardConormalScalarIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
    (i' : Z ⟶ U.toScheme) (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    ((modulePushforward i'.toLRSHom.toShHom).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).val.obj (op V) ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(U.toScheme, V)).inv.hom).obj
        ((SheafOfModules.evaluation _ (op ⊤)).obj
          ((modulePushforward (ringedSpaceIso hV.isoSpec).hom).obj
            ((modulePushforward (i' ∣_ V).toLRSHom.toShHom).obj
              ((moduleRestrict Z.toLocallyRingedSpace.toRingedSpace (i' ⁻¹ᵁ V)).obj
                (conormalSheaf i.liftCoborder.toLRSHom.toShHom))))) :=
  (ModuleCat.restrictScalars (i'.app V).hom).mapIso
        (valMapEqToIso (conormalSheaf i.liftCoborder.toLRSHom.toShHom)
          (i' ⁻¹ᵁ V).ι_image_top) ≪≫
      (ModuleCat.restrictScalarsComp'App (i'.app V).hom
        (Z.presheaf.map (eqToHom (i' ⁻¹ᵁ V).ι_image_top).op).hom _ rfl _).symm ≪≫
      ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso Γ(U.toScheme, V)).inv.hom
        (((i' ∣_ V) ≫ hV.isoSpec.hom).appTop).hom _
        (appLE_eq_ΓSpecIso_inv_comp_appTop_hom i' V hV) _

/-- **`Stacks.Immersion.pushforwardConormalScalarIso` on sections.** It is restriction of sections
along the equality `((i')⁻¹V).ι ''ᵁ ⊤ = (i')⁻¹V` of opens of `Z`, and nothing else: the two
`CategoryTheory.ModuleCat.restrictScalarsComp'App` factors have the identity as their underlying
map. This is what dropping the `CategoryTheory.eqToIso` buys; see the docstring above. -/
theorem pushforwardConormalScalarIso_hom_apply {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (w : ((modulePushforward i'.toLRSHom.toShHom).obj
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).val.obj (op V)) :
    (pushforwardConormalScalarIso i U i' V hV).hom.hom w =
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (eqToHom (i' ⁻¹ᵁ V).ι_image_top).op w := rfl

/-- **Stacks Project, Tag 01R3 part (1): the pushforward conormal sheaf is `I/I²` on affine
opens.** Let `i = i' ≫ ι_U` be a closed-immersion factorization of an immersion of schemes, let
`V ⊆ U` be an affine open, and suppose `Z ∩ V = Spec (Γ(U, V) ⧸ I)` compatibly with `V ≅ Spec
Γ(U, V)`. Then the sections over `V` of `(i')_* 𝒞_{Z/X}` are `Ideal.Cotangent I`, that is `I/I²`.

The proof is the composition of four identifications. The conormal sheaf of `i` restricted to
`(i')⁻¹V` is the conormal sheaf of `i' ∣_ V`
(`Stacks.Immersion.conormalSheafMorphismRestrictIso`); that is transported across the isomorphism
square of `Stacks.Immersion.morphismRestrict_comp_isoSpec_toShHom` by
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare`, landing at the closed immersion
`Spec (Γ(U, V) ⧸ I) ⟶ Spec Γ(U, V)`, whose global sections are computed by
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso`. The fourth is the comparison of the
`Γ(U, V)`-module structures, which is `Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop_hom`
read through `CategoryTheory.ModuleCat.restrictScalarsComp'App`.

Every ingredient of the composite is itself pinned down by a characterising lemma, so this is a
canonical isomorphism and not an arbitrary witness of its type; the single equation that would
pin the composite — the generator formula through
`Stacks.Conormal.conormalQuotientMap` — is not available yet, for the reason given in the module
docstring. -/
@[sga "4 XII 6.13" "partial", sga "5 III 6.8" "partial", sga "6 0 2.1" "partial"]
def pushforwardConormalIsoCotangent {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(U.toScheme, V))
    (e : pullback i' V.ι ≅ Spec (.of (Γ(U.toScheme, V) ⧸ I)))
    (he : pullback.snd i' V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((modulePushforward i'.toLRSHom.toShHom).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).val.obj (op V) ≅
      ModuleCat.of (Γ(U.toScheme, V)) I.Cotangent :=
  pushforwardConormalScalarIso i U i' V hV ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(U.toScheme, V)).inv.hom).mapIso
        ((SheafOfModules.evaluation _ (op ⊤)).mapIso
          ((modulePushforward (ringedSpaceIso hV.isoSpec).hom).mapIso
              ((modulePushforward (i' ∣_ V).toLRSHom.toShHom).mapIso
                (conormalSheafMorphismRestrictIso i U i' hfac V)) ≪≫
            ambientPushforwardConormalIsoOfSquare
              (ringedSpaceIso ((pullbackRestrictIsoRestrict i' V).symm ≪≫ e))
              (ringedSpaceIso hV.isoSpec) (i' ∣_ V).toLRSHom.toShHom
              (quotImmersion Γ(U.toScheme, V) I).toLRSHom.toShHom
              (morphismRestrict_comp_isoSpec_toShHom i' V hV I e he))) ≪≫
      conormalΓIso Γ(U.toScheme, V) I

end Stacks.Immersion

end
